//! WebGPU execution of the dealiased rotational Fourier IFRK4 method.
//!
//! This backend keeps the spectral state and every Runge--Kutta stage in GPU
//! storage buffers. Its WGSL kernels perform the separable Fourier transforms,
//! curl, physical-space rotational product, 2/3 filter, Leray projection,
//! viscous integrating factors, and RK4 combination. Readback happens only
//! when a caller requests a render frame or diagnostics.

use crate::{convention::SpectralConventionMetadata, core::MAX_BROWSER_GRID};
use bytemuck::{Pod, Zeroable};
use serde::Serialize;
use std::{
    cell::Cell,
    num::NonZeroU64,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};
use wgpu::util::DeviceExt;

const COMPONENTS: usize = 3;
const COMPLEX_FLOATS: usize = 2;
const WORKGROUP_SIZE: u32 = 64;
const PARAMETER_STRIDE: u64 = 256;
const PARAMETER_SLOTS: u64 = 64;
const MAX_INTERACTIVE_GRID: usize = MAX_BROWSER_GRID;

fn validate_grid(n: usize) -> Result<(), String> {
    if n < 4 || !n.is_multiple_of(2) || n > MAX_INTERACTIVE_GRID {
        return Err(format!(
            "WebGPU grid must be an even integer from 4 through {MAX_INTERACTIVE_GRID}"
        ));
    }
    Ok(())
}

#[repr(C)]
#[derive(Clone, Copy, Pod, Zeroable)]
struct Params {
    n: u32,
    len: u32,
    axis: u32,
    inverse: u32,
    dt: f32,
    viscosity: f32,
    coefficient: f32,
    _pad: f32,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct GpuDiagnostics {
    pub time: f64,
    pub energy: f64,
    pub enstrophy: f64,
    pub velocity_rms: f64,
    pub vorticity_rms: f64,
    pub divergence_rms: f64,
    pub max_speed: f64,
    pub max_vorticity: f64,
    pub energy_dissipation_rate: f64,
    pub high_frequency_energy_fraction: f64,
    pub tail_start_fraction_of_dealias_cutoff: f64,
    pub tail_tolerance: f64,
    pub underresolved: bool,
    pub finite: bool,
}

struct Pipelines {
    copy_filtered: wgpu::ComputePipeline,
    dft_axis: wgpu::ComputePipeline,
    curl_filtered: wgpu::ComputePipeline,
    rotational_cross: wgpu::ComputePipeline,
    project_scaled: wgpu::ComputePipeline,
    project_only: wgpu::ComputePipeline,
    stage_half: wgpu::ComputePipeline,
    stage_half_increment_outside: wgpu::ComputePipeline,
    stage_full: wgpu::ComputePipeline,
    combine_initial_a: wgpu::ComputePipeline,
    accumulate: wgpu::ComputePipeline,
}

struct MaxSpeedPipeline {
    layout: wgpu::BindGroupLayout,
    pipeline: wgpu::ComputePipeline,
}

/// GPU-resident spectral solver. WebGPU guarantees f32 arithmetic; the CPU
/// implementation remains the f64 reference and fallback.
pub struct WebGpuSpectralSolver {
    n: usize,
    len: usize,
    viscosity: f32,
    time: f64,
    steps: u64,
    max_tail_energy_fraction: Cell<f64>,
    underresolved: Cell<bool>,
    device_lost: Arc<AtomicBool>,
    adapter_name: String,
    adapter_backend: String,
    device: wgpu::Device,
    queue: wgpu::Queue,
    layout: wgpu::BindGroupLayout,
    pipelines: Pipelines,
    max_speed_pipeline: MaxSpeedPipeline,
    parameters: wgpu::Buffer,
    max_speed_reduction: wgpu::Buffer,
    dummy: wgpu::Buffer,
    state: wgpu::Buffer,
    a: wgpu::Buffer,
    b: wgpu::Buffer,
    c: wgpu::Buffer,
    d: wgpu::Buffer,
    stage: wgpu::Buffer,
    work0: wgpu::Buffer,
    work1: wgpu::Buffer,
    work2: wgpu::Buffer,
    next: wgpu::Buffer,
}

impl WebGpuSpectralSolver {
    pub async fn new(n: usize, viscosity: f64) -> Result<Self, String> {
        validate_grid(n)?;
        if !viscosity.is_finite() || viscosity < 0.0 || viscosity > f32::MAX as f64 {
            return Err("viscosity must be finite, nonnegative, and representable as f32".into());
        }
        let len = n.checked_pow(3).ok_or("grid allocation overflow")?;
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor {
            backends: if cfg!(target_arch = "wasm32") {
                wgpu::Backends::BROWSER_WEBGPU
            } else {
                wgpu::Backends::PRIMARY
            },
            ..Default::default()
        });
        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                compatible_surface: None,
                force_fallback_adapter: false,
            })
            .await
            .ok_or("WebGPU has no high-performance adapter")?;
        let info = adapter.get_info();
        let required_limits = wgpu::Limits::downlevel_defaults().using_resolution(adapter.limits());
        let (device, queue) = adapter
            .request_device(
                &wgpu::DeviceDescriptor {
                    label: Some("Navier WebGPU spectral solver"),
                    required_features: wgpu::Features::empty(),
                    required_limits,
                    memory_hints: wgpu::MemoryHints::Performance,
                },
                None,
            )
            .await
            .map_err(|error| format!("WebGPU device request failed: {error}"))?;
        let device_lost = Arc::new(AtomicBool::new(false));
        let lost_flag = Arc::clone(&device_lost);
        device.set_device_lost_callback(move |_reason, _message| {
            lost_flag.store(true, Ordering::Release);
        });

        device.push_error_scope(wgpu::ErrorFilter::Validation);
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("Navier spectral operators"),
            source: wgpu::ShaderSource::Wgsl(include_str!("shaders/spectral.wgsl").into()),
        });
        let layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("Navier spectral operation layout"),
            entries: &[
                wgpu::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Uniform,
                        has_dynamic_offset: true,
                        min_binding_size: NonZeroU64::new(std::mem::size_of::<Params>() as u64),
                    },
                    count: None,
                },
                storage_layout_entry(1, true),
                storage_layout_entry(2, true),
                storage_layout_entry(3, false),
            ],
        });
        let pipeline_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("Navier spectral pipeline layout"),
            bind_group_layouts: &[&layout],
            push_constant_ranges: &[],
        });
        let make_pipeline = |entry_point: &str| {
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry_point),
                layout: Some(&pipeline_layout),
                module: &shader,
                entry_point: Some(entry_point),
                compilation_options: Default::default(),
                cache: None,
            })
        };
        let pipelines = Pipelines {
            copy_filtered: make_pipeline("copy_filtered"),
            dft_axis: make_pipeline("dft_axis"),
            curl_filtered: make_pipeline("curl_filtered"),
            rotational_cross: make_pipeline("rotational_cross"),
            project_scaled: make_pipeline("project_scaled"),
            project_only: make_pipeline("project_only"),
            stage_half: make_pipeline("stage_half"),
            stage_half_increment_outside: make_pipeline("stage_half_increment_outside"),
            stage_full: make_pipeline("stage_full"),
            combine_initial_a: make_pipeline("combine_initial_a"),
            accumulate: make_pipeline("accumulate"),
        };
        let max_speed_shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("Navier maximum-speed reduction"),
            source: wgpu::ShaderSource::Wgsl(include_str!("shaders/max_speed.wgsl").into()),
        });
        let max_speed_layout = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("Navier maximum-speed layout"),
            entries: &[
                wgpu::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Uniform,
                        has_dynamic_offset: true,
                        min_binding_size: NonZeroU64::new(std::mem::size_of::<Params>() as u64),
                    },
                    count: None,
                },
                storage_layout_entry(1, true),
                wgpu::BindGroupLayoutEntry {
                    binding: 2,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: NonZeroU64::new(8),
                    },
                    count: None,
                },
            ],
        });
        let max_speed_pipeline_layout =
            device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("Navier maximum-speed pipeline layout"),
                bind_group_layouts: &[&max_speed_layout],
                push_constant_ranges: &[],
            });
        let max_speed_pipeline = MaxSpeedPipeline {
            layout: max_speed_layout,
            pipeline: device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("reduce_max_speed"),
                layout: Some(&max_speed_pipeline_layout),
                module: &max_speed_shader,
                entry_point: Some("reduce_max_speed"),
                compilation_options: Default::default(),
                cache: None,
            }),
        };
        if let Some(error) = device.pop_error_scope().await {
            return Err(format!("WebGPU rejected the spectral kernels: {error}"));
        }

        let complex_values = COMPONENTS * len;
        let buffer_bytes = (complex_values * std::mem::size_of::<[f32; 2]>()) as u64;
        if buffer_bytes > device.limits().max_storage_buffer_binding_size as u64 {
            return Err("grid exceeds this WebGPU adapter's storage-buffer limit".into());
        }
        let storage = |label: &'static str| {
            device.create_buffer(&wgpu::BufferDescriptor {
                label: Some(label),
                size: buffer_bytes,
                usage: wgpu::BufferUsages::STORAGE
                    | wgpu::BufferUsages::COPY_SRC
                    | wgpu::BufferUsages::COPY_DST,
                mapped_at_creation: false,
            })
        };
        let parameters = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("Navier dispatch parameters"),
            size: PARAMETER_STRIDE * PARAMETER_SLOTS,
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let max_speed_reduction = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("Navier maximum-speed reduction result"),
            size: 8,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_SRC
                | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let dummy = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("Navier unused storage binding"),
            contents: &[0; 8],
            usage: wgpu::BufferUsages::STORAGE,
        });
        let state = storage("Navier state");
        let a = storage("Navier RK a");
        let b = storage("Navier RK b");
        let c = storage("Navier RK c");
        let d = storage("Navier RK d");
        let stage = storage("Navier RK stage");
        let work0 = storage("Navier work 0");
        let work1 = storage("Navier work 1");
        let work2 = storage("Navier work 2");
        let next = storage("Navier next");
        let mut solver = Self {
            n,
            len,
            viscosity: viscosity as f32,
            time: 0.0,
            steps: 0,
            max_tail_energy_fraction: Cell::new(0.0),
            underresolved: Cell::new(false),
            device_lost,
            adapter_name: info.name,
            adapter_backend: format!("{:?}", info.backend),
            device,
            queue,
            layout,
            pipelines,
            max_speed_pipeline,
            parameters,
            max_speed_reduction,
            dummy,
            state,
            a,
            b,
            c,
            d,
            stage,
            work0,
            work1,
            work2,
            next,
        };
        solver.reset_taylor_green();
        Ok(solver)
    }

    pub fn n(&self) -> usize {
        self.n
    }
    pub fn viscosity(&self) -> f64 {
        self.viscosity as f64
    }
    pub fn metadata(&self) -> SpectralConventionMetadata {
        SpectralConventionMetadata::new(self.n, self.viscosity())
    }
    pub fn time(&self) -> f64 {
        self.time
    }
    pub fn steps(&self) -> u64 {
        self.steps
    }
    pub fn adapter_name(&self) -> &str {
        &self.adapter_name
    }
    pub fn adapter_backend(&self) -> &str {
        &self.adapter_backend
    }

    pub fn reset_taylor_green(&mut self) {
        let mut physical = vec![[0.0_f32; 2]; COMPONENTS * self.len];
        for i in 0..self.n {
            let x = std::f32::consts::TAU * i as f32 / self.n as f32;
            for j in 0..self.n {
                let y = std::f32::consts::TAU * j as f32 / self.n as f32;
                for k in 0..self.n {
                    let z = std::f32::consts::TAU * k as f32 / self.n as f32;
                    let q = self.index(i, j, k);
                    physical[q][0] = x.sin() * y.cos() * z.cos();
                    physical[self.len + q][0] = -x.cos() * y.sin() * z.cos();
                }
            }
        }
        self.upload_physical(&physical);
    }

    pub fn reset_zero(&mut self) {
        let zeros = vec![[0.0_f32; 2]; COMPONENTS * self.len];
        self.queue
            .write_buffer(&self.state, 0, bytemuck::cast_slice(&zeros));
        self.time = 0.0;
        self.steps = 0;
        self.max_tail_energy_fraction.set(0.0);
        self.underresolved.set(false);
    }

    pub fn reset_shear(&mut self, mode: usize) -> Result<(), String> {
        if mode == 0 || mode as f64 >= self.n as f64 / 3.0 {
            return Err("shear mode must satisfy 0 < mode < n/3".into());
        }
        let mut physical = vec![[0.0_f32; 2]; COMPONENTS * self.len];
        for i in 0..self.n {
            for j in 0..self.n {
                let y = std::f32::consts::TAU * j as f32 / self.n as f32;
                for k in 0..self.n {
                    physical[self.index(i, j, k)][0] = (mode as f32 * y).sin();
                }
            }
        }
        self.upload_physical(&physical);
        let is_tail = mode as f64 >= 0.75 * self.n as f64 / 3.0;
        self.max_tail_energy_fraction
            .set(if is_tail { 1.0 } else { 0.0 });
        self.underresolved.set(is_tail);
        Ok(())
    }

    pub fn step(&mut self, dt: f64) -> Result<(), String> {
        self.ensure_device()?;
        if !dt.is_finite() || dt <= 0.0 || dt > f32::MAX as f64 {
            return Err("dt must be finite, positive, and representable as f32".into());
        }
        let dt = dt as f32;
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Navier IFRK4 step"),
            });
        let mut slot = 0;
        self.encode_rhs(&mut encoder, &self.state, &self.a, dt, &mut slot);
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.stage_half,
            &self.state,
            &self.a,
            &self.stage,
            self.params(dt, 0.0, 0, false),
            &mut slot,
        );
        self.encode_rhs(&mut encoder, &self.stage, &self.b, dt, &mut slot);
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.stage_half_increment_outside,
            &self.state,
            &self.b,
            &self.stage,
            self.params(dt, 0.0, 0, false),
            &mut slot,
        );
        self.encode_rhs(&mut encoder, &self.stage, &self.c, dt, &mut slot);
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.stage_full,
            &self.state,
            &self.c,
            &self.stage,
            self.params(dt, 0.0, 0, false),
            &mut slot,
        );
        self.encode_rhs(&mut encoder, &self.stage, &self.d, dt, &mut slot);
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.combine_initial_a,
            &self.state,
            &self.a,
            &self.next,
            self.params(dt, 0.0, 0, false),
            &mut slot,
        );
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.accumulate,
            &self.b,
            &self.dummy,
            &self.next,
            self.params(dt, 1.0 / 3.0, 0, false),
            &mut slot,
        );
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.accumulate,
            &self.c,
            &self.dummy,
            &self.next,
            self.params(dt, 1.0 / 3.0, 0, false),
            &mut slot,
        );
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.accumulate,
            &self.d,
            &self.dummy,
            &self.next,
            self.params(dt, 1.0 / 6.0, 0, false),
            &mut slot,
        );
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.project_only,
            &self.next,
            &self.dummy,
            &self.work0,
            self.params(dt, 0.0, 0, false),
            &mut slot,
        );
        encoder.copy_buffer_to_buffer(&self.work0, 0, &self.state, 0, self.buffer_bytes());
        self.queue.submit(Some(encoder.finish()));
        self.time += dt as f64;
        self.steps += 1;
        Ok(())
    }

    pub fn step_many(&mut self, dt: f64, steps: usize) -> Result<(), String> {
        if steps > 10_000 {
            return Err("step count exceeds the bounded limit of 10000".into());
        }
        for _ in 0..steps {
            self.step(dt)?;
        }
        Ok(())
    }

    pub async fn velocity_f32_interleaved(&self) -> Result<Vec<f32>, String> {
        self.ensure_device()?;
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Navier velocity readback transform"),
            });
        let mut slot = 0;
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.copy_filtered,
            &self.state,
            &self.dummy,
            &self.work0,
            self.params(0.0, 0.0, 0, false),
            &mut slot,
        );
        let physical =
            self.encode_transform(&mut encoder, &self.work0, &self.work1, true, &mut slot);
        self.queue.submit(Some(encoder.finish()));
        let values = self.read_complex_buffer(physical).await?;
        let mut result = Vec::with_capacity(COMPONENTS * self.len);
        for q in 0..self.len {
            result.extend_from_slice(&[
                values[q][0],
                values[self.len + q][0],
                values[2 * self.len + q][0],
            ]);
        }
        Ok(result)
    }

    /// Maximum physical-space speed for the CFL guard. The velocity remains
    /// GPU-resident and only the maximum plus a non-finite flag are read back.
    pub async fn max_speed(&self) -> Result<f64, String> {
        self.ensure_device()?;
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Navier CFL maximum-speed reduction"),
            });
        let mut slot = 0;
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.copy_filtered,
            &self.state,
            &self.dummy,
            &self.work0,
            self.params(0.0, 0.0, 0, false),
            &mut slot,
        );
        let physical =
            self.encode_transform(&mut encoder, &self.work0, &self.work1, true, &mut slot);
        encoder.clear_buffer(&self.max_speed_reduction, 0, Some(8));

        assert!((slot as u64) < PARAMETER_SLOTS);
        let offset = slot as u64 * PARAMETER_STRIDE;
        self.queue.write_buffer(
            &self.parameters,
            offset,
            bytemuck::bytes_of(&self.params(0.0, 0.0, 0, false)),
        );
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("Navier maximum-speed reduction bind group"),
            layout: &self.max_speed_pipeline.layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::Buffer(wgpu::BufferBinding {
                        buffer: &self.parameters,
                        offset: 0,
                        size: NonZeroU64::new(std::mem::size_of::<Params>() as u64),
                    }),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: physical.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: self.max_speed_reduction.as_entire_binding(),
                },
            ],
        });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("Navier maximum-speed reduction pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.max_speed_pipeline.pipeline);
            pass.set_bind_group(0, &bind_group, &[offset as u32]);
            pass.dispatch_workgroups((self.len as u32).div_ceil(WORKGROUP_SIZE), 1, 1);
        }
        self.queue.submit(Some(encoder.finish()));
        let reduction = self.read_u32_pair(&self.max_speed_reduction).await?;
        if reduction[1] != 0 {
            return Err("non-finite velocity encountered during WebGPU CFL reduction".into());
        }
        let maximum_squared = f32::from_bits(reduction[0]);
        if !maximum_squared.is_finite() {
            return Err("non-finite speed encountered during WebGPU CFL reduction".into());
        }
        Ok(maximum_squared.sqrt() as f64)
    }

    pub async fn diagnostics(&self) -> Result<GpuDiagnostics, String> {
        self.ensure_device()?;
        let velocity = self.velocity_f32_interleaved().await?;
        let state = self.read_complex_buffer(&self.state).await?;
        let mut energy_sum = 0.0_f64;
        let mut max_speed2 = 0.0_f64;
        let mut finite = true;
        for value in velocity.chunks_exact(COMPONENTS) {
            let speed2 = value.iter().map(|x| (*x as f64).powi(2)).sum::<f64>();
            energy_sum += 0.5 * speed2;
            max_speed2 = max_speed2.max(speed2);
            finite &= speed2.is_finite();
        }

        // Parseval gives physical means after division by N^6 because forward
        // DFTs are unscaled. Tail energy uses the same componentwise band as
        // the CPU reference, while max vorticity is measured in physical space.
        let mut divergence_spectral_sum = 0.0_f64;
        let mut enstrophy_spectral_sum = 0.0_f64;
        let mut spectral_energy_sum = 0.0_f64;
        let mut tail_energy_sum = 0.0_f64;
        let tail_edge = 0.75 * self.n as f64 / 3.0;
        for q in 0..self.len {
            let [kx, ky, kz] = self.wave(q);
            let ux = complex64(state[q]);
            let uy = complex64(state[self.len + q]);
            let uz = complex64(state[2 * self.len + q]);
            let dot_re = kx * ux[0] + ky * uy[0] + kz * uz[0];
            let dot_im = kx * ux[1] + ky * uy[1] + kz * uz[1];
            divergence_spectral_sum += dot_re * dot_re + dot_im * dot_im;
            let density = norm2(ux) + norm2(uy) + norm2(uz);
            spectral_energy_sum += density;
            if [kx, ky, kz].into_iter().any(|k| k.abs() >= tail_edge) {
                tail_energy_sum += density;
            }
            let wx = complex_sub(complex_scale(uz, ky), complex_scale(uy, kz));
            let wy = complex_sub(complex_scale(ux, kz), complex_scale(uz, kx));
            let wz = complex_sub(complex_scale(uy, kx), complex_scale(ux, ky));
            enstrophy_spectral_sum += norm2(wx) + norm2(wy) + norm2(wz);
        }
        let divergence_rms = divergence_spectral_sum.sqrt() / self.len as f64;
        let enstrophy = 0.5 * enstrophy_spectral_sum / (self.len * self.len) as f64;
        let tail = if spectral_energy_sum == 0.0 {
            0.0
        } else {
            tail_energy_sum / spectral_energy_sum
        };
        self.max_tail_energy_fraction
            .set(self.max_tail_energy_fraction.get().max(tail));
        self.underresolved
            .set(self.underresolved.get() || tail > 1.0e-8);

        let vorticity = self.vorticity_f32_interleaved().await?;
        let mut max_vorticity2 = 0.0_f64;
        for value in vorticity.chunks_exact(COMPONENTS) {
            let magnitude2 = value.iter().map(|x| (*x as f64).powi(2)).sum::<f64>();
            max_vorticity2 = max_vorticity2.max(magnitude2);
            finite &= magnitude2.is_finite();
        }
        finite &= state.iter().all(|z| z[0].is_finite() && z[1].is_finite());
        let energy = energy_sum / self.len as f64;
        Ok(GpuDiagnostics {
            time: self.time,
            energy,
            enstrophy,
            velocity_rms: (2.0 * energy).max(0.0).sqrt(),
            vorticity_rms: (2.0 * enstrophy).max(0.0).sqrt(),
            divergence_rms,
            max_speed: max_speed2.sqrt(),
            max_vorticity: max_vorticity2.sqrt(),
            energy_dissipation_rate: 2.0 * self.viscosity as f64 * enstrophy,
            high_frequency_energy_fraction: tail,
            tail_start_fraction_of_dealias_cutoff: 0.75,
            tail_tolerance: 1.0e-8,
            underresolved: self.underresolved.get(),
            finite: finite && divergence_rms.is_finite(),
        })
    }

    async fn vorticity_f32_interleaved(&self) -> Result<Vec<f32>, String> {
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Navier vorticity readback transform"),
            });
        let mut slot = 0;
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.curl_filtered,
            &self.state,
            &self.dummy,
            &self.work0,
            self.params(0.0, 0.0, 0, false),
            &mut slot,
        );
        let physical =
            self.encode_transform(&mut encoder, &self.work0, &self.work1, true, &mut slot);
        self.queue.submit(Some(encoder.finish()));
        let values = self.read_complex_buffer(physical).await?;
        let mut result = Vec::with_capacity(COMPONENTS * self.len);
        for q in 0..self.len {
            result.extend_from_slice(&[
                values[q][0],
                values[self.len + q][0],
                values[2 * self.len + q][0],
            ]);
        }
        Ok(result)
    }

    fn upload_physical(&mut self, physical: &[[f32; 2]]) {
        self.queue
            .write_buffer(&self.work0, 0, bytemuck::cast_slice(physical));
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Navier initial condition transform"),
            });
        let mut slot = 0;
        let spectral =
            self.encode_transform(&mut encoder, &self.work0, &self.work1, false, &mut slot);
        let projected = if std::ptr::eq(spectral, &self.work0) {
            &self.work1
        } else {
            &self.work0
        };
        self.encode_dispatch(
            &mut encoder,
            &self.pipelines.project_only,
            spectral,
            &self.dummy,
            projected,
            self.params(0.0, 0.0, 0, false),
            &mut slot,
        );
        encoder.copy_buffer_to_buffer(projected, 0, &self.state, 0, self.buffer_bytes());
        self.queue.submit(Some(encoder.finish()));
        self.time = 0.0;
        self.steps = 0;
        self.max_tail_energy_fraction.set(0.0);
        self.underresolved.set(false);
    }

    fn encode_rhs<'a>(
        &'a self,
        encoder: &mut wgpu::CommandEncoder,
        input: &'a wgpu::Buffer,
        output: &'a wgpu::Buffer,
        dt: f32,
        slot: &mut u32,
    ) {
        self.encode_dispatch(
            encoder,
            &self.pipelines.copy_filtered,
            input,
            &self.dummy,
            &self.work0,
            self.params(dt, 0.0, 0, false),
            slot,
        );
        self.encode_dispatch(
            encoder,
            &self.pipelines.curl_filtered,
            input,
            &self.dummy,
            &self.work1,
            self.params(dt, 0.0, 0, false),
            slot,
        );
        let velocity = self.encode_transform(encoder, &self.work0, &self.work2, true, slot);
        let curl_target = if std::ptr::eq(velocity, &self.work0) {
            &self.work2
        } else {
            &self.work0
        };
        let curl = self.encode_transform(encoder, &self.work1, curl_target, true, slot);
        let cross_target = if std::ptr::eq(curl, &self.work1) {
            &self.work0
        } else {
            &self.work1
        };
        self.encode_dispatch(
            encoder,
            &self.pipelines.rotational_cross,
            velocity,
            curl,
            cross_target,
            self.params(dt, 0.0, 0, false),
            slot,
        );
        let transform_target = if std::ptr::eq(cross_target, &self.work0) {
            &self.work1
        } else {
            &self.work0
        };
        let cross_hat = self.encode_transform(encoder, cross_target, transform_target, false, slot);
        self.encode_dispatch(
            encoder,
            &self.pipelines.project_scaled,
            cross_hat,
            &self.dummy,
            output,
            self.params(dt, 0.0, 0, false),
            slot,
        );
    }

    /// Three separable transforms. `first` and `second` must be distinct.
    fn encode_transform<'a>(
        &'a self,
        encoder: &mut wgpu::CommandEncoder,
        first: &'a wgpu::Buffer,
        second: &'a wgpu::Buffer,
        inverse: bool,
        slot: &mut u32,
    ) -> &'a wgpu::Buffer {
        let mut source = first;
        let mut destination = second;
        for axis in 0..3 {
            self.encode_dispatch(
                encoder,
                &self.pipelines.dft_axis,
                source,
                &self.dummy,
                destination,
                self.params(0.0, 0.0, axis, inverse),
                slot,
            );
            std::mem::swap(&mut source, &mut destination);
        }
        source
    }

    #[allow(clippy::too_many_arguments)]
    fn encode_dispatch(
        &self,
        encoder: &mut wgpu::CommandEncoder,
        pipeline: &wgpu::ComputePipeline,
        source: &wgpu::Buffer,
        auxiliary: &wgpu::Buffer,
        destination: &wgpu::Buffer,
        params: Params,
        slot: &mut u32,
    ) {
        assert!(
            (*slot as u64) < PARAMETER_SLOTS,
            "parameter slot capacity exceeded"
        );
        let offset = *slot as u64 * PARAMETER_STRIDE;
        self.queue
            .write_buffer(&self.parameters, offset, bytemuck::bytes_of(&params));
        let bind_group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("Navier spectral dispatch"),
            layout: &self.layout,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: wgpu::BindingResource::Buffer(wgpu::BufferBinding {
                        buffer: &self.parameters,
                        offset: 0,
                        size: NonZeroU64::new(std::mem::size_of::<Params>() as u64),
                    }),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: source.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: auxiliary.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: destination.as_entire_binding(),
                },
            ],
        });
        let count = if std::ptr::eq(pipeline, &self.pipelines.curl_filtered)
            || std::ptr::eq(pipeline, &self.pipelines.rotational_cross)
        {
            self.len as u32
        } else {
            (COMPONENTS * self.len) as u32
        };
        let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
            label: Some("Navier spectral pass"),
            timestamp_writes: None,
        });
        pass.set_pipeline(pipeline);
        pass.set_bind_group(0, &bind_group, &[offset as u32]);
        pass.dispatch_workgroups(count.div_ceil(WORKGROUP_SIZE), 1, 1);
        *slot += 1;
    }

    fn params(&self, dt: f32, coefficient: f32, axis: u32, inverse: bool) -> Params {
        Params {
            n: self.n as u32,
            len: self.len as u32,
            axis,
            inverse: inverse as u32,
            dt,
            viscosity: self.viscosity,
            coefficient,
            _pad: 0.0,
        }
    }

    async fn read_complex_buffer(&self, source: &wgpu::Buffer) -> Result<Vec<[f32; 2]>, String> {
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("Navier GPU readback"),
            size: self.buffer_bytes(),
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Navier GPU readback copy"),
            });
        encoder.copy_buffer_to_buffer(source, 0, &staging, 0, self.buffer_bytes());
        self.queue.submit(Some(encoder.finish()));
        let slice = staging.slice(..);
        let (sender, receiver) = futures_channel::oneshot::channel();
        slice.map_async(wgpu::MapMode::Read, move |result| {
            let _ = sender.send(result);
        });
        #[cfg(not(target_arch = "wasm32"))]
        self.device.poll(wgpu::Maintain::Wait);
        let map_result = receiver
            .await
            .map_err(|_| "GPU readback callback was dropped".to_string())?;
        map_result.map_err(|error| format!("GPU readback map failed: {error}"))?;
        let mapped = slice.get_mapped_range();
        let values = bytemuck::cast_slice::<u8, [f32; 2]>(&mapped).to_vec();
        drop(mapped);
        staging.unmap();
        Ok(values)
    }

    async fn read_u32_pair(&self, source: &wgpu::Buffer) -> Result<[u32; 2], String> {
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("Navier scalar GPU readback"),
            size: 8,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("Navier scalar GPU readback copy"),
            });
        encoder.copy_buffer_to_buffer(source, 0, &staging, 0, 8);
        self.queue.submit(Some(encoder.finish()));
        let slice = staging.slice(..);
        let (sender, receiver) = futures_channel::oneshot::channel();
        slice.map_async(wgpu::MapMode::Read, move |result| {
            let _ = sender.send(result);
        });
        #[cfg(not(target_arch = "wasm32"))]
        self.device.poll(wgpu::Maintain::Wait);
        receiver
            .await
            .map_err(|_| "GPU scalar readback callback was dropped".to_string())?
            .map_err(|error| format!("GPU scalar readback map failed: {error}"))?;
        let mapped = slice.get_mapped_range();
        let values = *bytemuck::from_bytes::<[u32; 2]>(&mapped);
        drop(mapped);
        staging.unmap();
        Ok(values)
    }

    fn buffer_bytes(&self) -> u64 {
        (COMPONENTS * self.len * COMPLEX_FLOATS * std::mem::size_of::<f32>()) as u64
    }

    #[inline]
    fn index(&self, i: usize, j: usize, k: usize) -> usize {
        (i * self.n + j) * self.n + k
    }

    fn wave(&self, q: usize) -> [f64; 3] {
        let plane = self.n * self.n;
        let coordinates = [q / plane, (q / self.n) % self.n, q % self.n];
        coordinates.map(|index| {
            if index < self.n / 2 {
                index as f64
            } else {
                index as f64 - self.n as f64
            }
        })
    }

    fn ensure_device(&self) -> Result<(), String> {
        if self.device_lost.load(Ordering::Acquire) {
            Err(
                "WebGPU device was lost; construct a new solver or use the CPU-WASM fallback"
                    .into(),
            )
        } else {
            Ok(())
        }
    }
}

fn complex64(value: [f32; 2]) -> [f64; 2] {
    [value[0] as f64, value[1] as f64]
}

fn complex_scale(value: [f64; 2], scale: f64) -> [f64; 2] {
    [scale * value[0], scale * value[1]]
}

fn complex_sub(left: [f64; 2], right: [f64; 2]) -> [f64; 2] {
    [left[0] - right[0], left[1] - right[1]]
}

fn norm2(value: [f64; 2]) -> f64 {
    value[0] * value[0] + value[1] * value[1]
}

fn storage_layout_entry(binding: u32, read_only: bool) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty: wgpu::BufferBindingType::Storage { read_only },
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SpectralSolver;

    #[test]
    fn interactive_grid_capacity_accepts_64_without_requesting_an_adapter() {
        assert!(validate_grid(64).is_ok());
        assert!(validate_grid(66).is_err());
        assert!(validate_grid(63).is_err());
    }

    const NO_ADAPTER: &str = "WebGPU has no high-performance adapter";

    fn gpu_with(n: usize, viscosity: f64) -> Option<WebGpuSpectralSolver> {
        let solver = match pollster::block_on(WebGpuSpectralSolver::new(n, viscosity)) {
            Ok(solver) => solver,
            Err(error)
                if error == NO_ADAPTER
                    && std::env::var("NAVIER_REQUIRE_GPU").as_deref() != Ok("1") =>
            {
                eprintln!("SKIPPED: no WebGPU adapter: {error}");
                return None;
            }
            Err(error) => panic!("WebGPU solver initialization failed: {error}"),
        };
        eprintln!(
            "WebGPU adapter: {} ({})",
            solver.adapter_name(),
            solver.adapter_backend()
        );
        Some(solver)
    }

    fn gpu() -> Option<WebGpuSpectralSolver> {
        gpu_with(8, 0.05)
    }

    #[test]
    fn gpu_taylor_green_matches_cpu_at_initial_time() {
        let Some(gpu) = gpu() else {
            return;
        };
        let cpu = SpectralSolver::new(8, 0.05).unwrap();
        let actual = pollster::block_on(gpu.velocity_f32_interleaved()).unwrap();
        let expected = cpu.velocity_f32_interleaved();
        let max_error = actual
            .iter()
            .zip(&expected)
            .map(|(a, b)| (a - b).abs())
            .fold(0.0_f32, f32::max);
        assert!(
            max_error < 2.0e-5,
            "initial transform max error {max_error:e}"
        );
    }

    #[test]
    fn gpu_step_tracks_cpu_reference_and_projection() {
        let Some(mut gpu) = gpu() else {
            return;
        };
        let mut cpu = SpectralSolver::new(8, 0.05).unwrap();
        for _ in 0..3 {
            gpu.step(0.0025).unwrap();
            cpu.step(0.0025).unwrap();
        }
        let actual = pollster::block_on(gpu.velocity_f32_interleaved()).unwrap();
        let expected = cpu.velocity_f32_interleaved();
        let max_error = actual
            .iter()
            .zip(&expected)
            .map(|(a, b)| (a - b).abs())
            .fold(0.0_f32, f32::max);
        assert!(max_error < 2.5e-4, "three-step max error {max_error:e}");
        let reduced_max_speed = pollster::block_on(gpu.max_speed()).unwrap();
        let diagnostics = pollster::block_on(gpu.diagnostics()).unwrap();
        let reference = cpu.diagnostics();
        assert!(diagnostics.finite);
        assert!((reduced_max_speed - diagnostics.max_speed).abs() < 2.0e-6);
        assert!((diagnostics.energy - reference.energy).abs() < 2.0e-5);
        assert!((diagnostics.enstrophy - reference.enstrophy).abs() < 8.0e-5);
        assert!((diagnostics.max_speed - reference.max_speed).abs() < 8.0e-5);
        assert!((diagnostics.max_vorticity - reference.max_vorticity).abs() < 3.0e-4);
        assert!(
            (diagnostics.high_frequency_energy_fraction - reference.high_frequency_energy_fraction)
                .abs()
                < 2.0e-5
        );
        assert!(
            diagnostics.divergence_rms < 2.0e-5,
            "divergence rms {}",
            diagnostics.divergence_rms
        );
    }

    #[test]
    fn gpu_exact_shear_decays_at_viscous_rate() {
        let Some(mut gpu) = gpu() else {
            return;
        };
        gpu.reset_shear(1).unwrap();
        gpu.step_many(0.002, 5).unwrap();
        let diagnostics = pollster::block_on(gpu.diagnostics()).unwrap();
        let expected = 0.25 * (-2.0 * 0.05 * diagnostics.time).exp();
        assert!(
            (diagnostics.energy - expected).abs() < 8.0e-5,
            "energy {} expected {expected}",
            diagnostics.energy
        );
    }

    #[test]
    fn gpu_tail_warning_matches_componentwise_cutoff_and_latches() {
        let Some(mut gpu) = gpu_with(12, 0.05) else {
            return;
        };
        gpu.reset_shear(3).unwrap();
        let diagnostics = pollster::block_on(gpu.diagnostics()).unwrap();
        assert!((diagnostics.high_frequency_energy_fraction - 1.0).abs() < 1.0e-5);
        assert!(diagnostics.underresolved);
        gpu.reset_taylor_green();
        let reset = pollster::block_on(gpu.diagnostics()).unwrap();
        assert!(!reset.underresolved);
    }

    #[test]
    fn gpu_fixed_input_is_repeatable() {
        let Some(mut left) = gpu_with(8, 0.03) else {
            return;
        };
        let mut right = gpu_with(8, 0.03)
            .expect("the second WebGPU adapter request failed after the first succeeded");
        left.step_many(0.007, 3).unwrap();
        right.step_many(0.007, 3).unwrap();
        let left_frame = pollster::block_on(left.velocity_f32_interleaved()).unwrap();
        let right_frame = pollster::block_on(right.velocity_f32_interleaved()).unwrap();
        assert_eq!(left_frame, right_frame);
    }

    #[test]
    fn gpu_max_speed_rejects_nonfinite_velocity() {
        let Some(gpu) = gpu() else {
            return;
        };
        gpu.queue
            .write_buffer(&gpu.state, 0, bytemuck::bytes_of(&[f32::INFINITY, 0.0]));
        let error = pollster::block_on(gpu.max_speed()).unwrap_err();
        assert!(
            error.contains("non-finite velocity"),
            "unexpected error: {error}"
        );
    }

    #[test]
    #[ignore]
    fn gpu_cfl_reduction_benchmark() {
        use std::time::Instant;
        let mut gpu = gpu_with(24, 0.05).expect("benchmark requires a WebGPU adapter");
        gpu.step(0.001).unwrap();
        pollster::block_on(gpu.max_speed()).unwrap();
        pollster::block_on(gpu.diagnostics()).unwrap();

        let fast_start = Instant::now();
        for _ in 0..8 {
            pollster::block_on(gpu.max_speed()).unwrap();
        }
        let fast = fast_start.elapsed() / 8;
        let full_start = Instant::now();
        for _ in 0..8 {
            pollster::block_on(gpu.diagnostics()).unwrap();
        }
        let full = full_start.elapsed() / 8;
        eprintln!("N=24 CFL maxSpeed={fast:?} full diagnostics={full:?}");
        assert!(fast < full, "CFL reduction did not beat full diagnostics");
    }

    /// Hardware timing probe, kept ignored so ordinary correctness tests stay
    /// deterministic. Run with `cargo test --release gpu_grid_benchmark --
    /// --ignored --nocapture` on each publication target.
    #[test]
    #[ignore]
    fn gpu_grid_benchmark() {
        use std::time::Instant;
        for n in [12, 24, 36, 48, 64] {
            let mut gpu = pollster::block_on(WebGpuSpectralSolver::new(n, 0.05))
                .unwrap_or_else(|error| panic!("N={n} GPU initialization failed: {error}"));
            gpu.step(0.001).unwrap();
            pollster::block_on(gpu.velocity_f32_interleaved()).unwrap();
            let step_start = Instant::now();
            gpu.step(0.001).unwrap();
            let step_submit = step_start.elapsed();
            let read_start = Instant::now();
            let frame = pollster::block_on(gpu.velocity_f32_interleaved()).unwrap();
            let step_and_read = step_start.elapsed();
            let readback = read_start.elapsed();
            assert_eq!(frame.len(), 3 * n * n * n);
            eprintln!(
                "N={n} adapter={} submit={step_submit:?} readback={readback:?} total={step_and_read:?}",
                gpu.adapter_name()
            );
        }
    }
}
