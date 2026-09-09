mod core;
mod gpu;

pub use core::{AdvanceReport, Diagnostics, SpectralSolver};
pub use gpu::{GpuDiagnostics, WebGpuSpectralSolver};
use wasm_bindgen::prelude::*;

#[derive(serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct Metadata<'a> {
    backend: &'a str,
    equation: &'a str,
    spatial_method: &'a str,
    time_integrator: &'a str,
    precision: &'a str,
    grid: usize,
    viscosity: f64,
    dealiasing: bool,
    continuum_certificate: bool,
    adaptive_recording: bool,
}

#[wasm_bindgen]
pub struct NavierSolver {
    inner: SpectralSolver,
}

#[derive(serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct GpuMetadata {
    backend: &'static str,
    equation: &'static str,
    spatial_method: &'static str,
    time_integrator: &'static str,
    precision: &'static str,
    grid: usize,
    viscosity: f64,
    dealiasing: bool,
    adapter_name: String,
    adapter_backend: String,
    continuum_certificate: bool,
    adaptive_recording: bool,
}

#[wasm_bindgen]
pub struct WebGpuNavierSolver {
    inner: WebGpuSpectralSolver,
}

#[wasm_bindgen]
impl NavierSolver {
    #[wasm_bindgen(constructor)]
    pub fn new(grid: usize, viscosity: f64) -> Result<NavierSolver, JsError> {
        Ok(Self {
            inner: SpectralSolver::new(grid, viscosity).map_err(|e| JsError::new(&e))?,
        })
    }

    #[wasm_bindgen(js_name = resetTaylorGreen)]
    pub fn reset_taylor_green(&mut self) {
        self.inner.reset_taylor_green();
    }

    #[wasm_bindgen(js_name = resetZero)]
    pub fn reset_zero(&mut self) {
        self.inner.reset_zero();
    }

    #[wasm_bindgen(js_name = resetShear)]
    pub fn reset_shear(&mut self, mode: usize) -> Result<(), JsError> {
        self.inner.reset_shear(mode).map_err(|e| JsError::new(&e))
    }

    pub fn step(&mut self, dt: f64) -> Result<(), JsError> {
        self.inner.step(dt).map_err(|e| JsError::new(&e))
    }

    #[wasm_bindgen(js_name = stepMany)]
    pub fn step_many(&mut self, dt: f64, steps: usize) -> Result<(), JsError> {
        self.inner
            .step_many(dt, steps)
            .map_err(|e| JsError::new(&e))
    }

    #[wasm_bindgen(js_name = advanceBounded)]
    pub fn advance_bounded(
        &mut self,
        duration: f64,
        max_dt: f64,
        cfl: f64,
        max_substeps: usize,
    ) -> Result<JsValue, JsError> {
        let report = self
            .inner
            .advance_bounded(duration, max_dt, cfl, max_substeps)
            .map_err(|e| JsError::new(&e))?;
        serde_wasm_bindgen::to_value(&report).map_err(|e| JsError::new(&e.to_string()))
    }

    pub fn velocity(&self) -> Vec<f32> {
        self.inner.velocity_f32_interleaved()
    }

    pub fn diagnostics(&self) -> Result<JsValue, JsError> {
        serde_wasm_bindgen::to_value(&self.inner.diagnostics())
            .map_err(|e| JsError::new(&e.to_string()))
    }

    pub fn metadata(&self) -> Result<JsValue, JsError> {
        let value = Metadata {
            backend: "cpu-wasm-spectral-ifrk4",
            equation: "3D periodic incompressible Navier-Stokes",
            spatial_method: "dealiased rotational Fourier pseudo-spectral with Leray projection",
            time_integrator: "fixed-step integrating-factor RK4",
            precision: "f64 compute / f32 render output",
            grid: self.inner.n(),
            viscosity: self.inner.viscosity(),
            dealiasing: true,
            continuum_certificate: false,
            adaptive_recording: false,
        };
        serde_wasm_bindgen::to_value(&value).map_err(|e| JsError::new(&e.to_string()))
    }
}

#[wasm_bindgen]
impl WebGpuNavierSolver {
    #[wasm_bindgen(js_name = create)]
    pub async fn create(grid: usize, viscosity: f64) -> Result<WebGpuNavierSolver, JsError> {
        let inner = WebGpuSpectralSolver::new(grid, viscosity)
            .await
            .map_err(|error| JsError::new(&error))?;
        Ok(Self { inner })
    }

    #[wasm_bindgen(js_name = resetTaylorGreen)]
    pub fn reset_taylor_green(&mut self) {
        self.inner.reset_taylor_green();
    }

    #[wasm_bindgen(js_name = resetZero)]
    pub fn reset_zero(&mut self) {
        self.inner.reset_zero();
    }

    #[wasm_bindgen(js_name = resetShear)]
    pub fn reset_shear(&mut self, mode: usize) -> Result<(), JsError> {
        self.inner
            .reset_shear(mode)
            .map_err(|error| JsError::new(&error))
    }

    pub fn step(&mut self, dt: f64) -> Result<(), JsError> {
        self.inner.step(dt).map_err(|error| JsError::new(&error))
    }

    #[wasm_bindgen(js_name = stepMany)]
    pub fn step_many(&mut self, dt: f64, steps: usize) -> Result<(), JsError> {
        self.inner
            .step_many(dt, steps)
            .map_err(|error| JsError::new(&error))
    }

    pub async fn velocity(&self) -> Result<Vec<f32>, JsError> {
        self.inner
            .velocity_f32_interleaved()
            .await
            .map_err(|error| JsError::new(&error))
    }

    #[wasm_bindgen(js_name = maxSpeed)]
    pub async fn max_speed(&self) -> Result<f64, JsError> {
        self.inner
            .max_speed()
            .await
            .map_err(|error| JsError::new(&error))
    }

    pub async fn diagnostics(&self) -> Result<JsValue, JsError> {
        let diagnostics = self
            .inner
            .diagnostics()
            .await
            .map_err(|error| JsError::new(&error))?;
        serde_wasm_bindgen::to_value(&diagnostics).map_err(|error| JsError::new(&error.to_string()))
    }

    pub fn metadata(&self) -> Result<JsValue, JsError> {
        let value = GpuMetadata {
            backend: "webgpu-spectral-ifrk4",
            equation: "3D periodic incompressible Navier-Stokes",
            spatial_method: "dealiased rotational Fourier pseudo-spectral with Leray projection",
            time_integrator: "fixed-step integrating-factor RK4",
            precision: "f32 WebGPU compute / f32 render output",
            grid: self.inner.n(),
            viscosity: self.inner.viscosity(),
            dealiasing: true,
            adapter_name: self.inner.adapter_name().to_owned(),
            adapter_backend: self.inner.adapter_backend().to_owned(),
            continuum_certificate: false,
            adaptive_recording: false,
        };
        serde_wasm_bindgen::to_value(&value).map_err(|error| JsError::new(&error.to_string()))
    }
}
