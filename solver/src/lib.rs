mod construction;
mod convention;
mod core;
mod gpu;

pub use construction::{
    AxisConstruction, AxisConstructionConfig, AxisConstructionDiagnostics, AxisConstructionMetadata,
};
pub use convention::SpectralConventionMetadata;
pub use core::{AdvanceReport, Diagnostics, SpectralSolver};
pub use gpu::{GpuDiagnostics, WebGpuSpectralSolver};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct ConstructionAxis {
    inner: AxisConstruction,
    velocity: Vec<f32>,
    pressure: Vec<f32>,
    residual: Vec<f32>,
    domain_extent: [f64; 3],
    diagnostics: Option<AxisConstructionDiagnostics>,
}

#[wasm_bindgen]
impl ConstructionAxis {
    #[wasm_bindgen(constructor)]
    pub fn new(order: usize, iterations: usize) -> Result<ConstructionAxis, JsError> {
        let config = AxisConstructionConfig {
            radial_order: order,
            iterations,
            ..AxisConstructionConfig::default()
        };
        Ok(Self {
            inner: AxisConstruction::new(config).map_err(|error| JsError::new(&error))?,
            velocity: Vec::new(),
            pressure: Vec::new(),
            residual: Vec::new(),
            domain_extent: [0.0; 3],
            diagnostics: None,
        })
    }

    pub fn sample(&mut self, grid: usize, tau: f64) -> Result<(), JsError> {
        let (velocity, pressure, residual, half_extent, diagnostics) = self
            .inner
            .evaluate_grid(grid, tau)
            .map_err(|error| JsError::new(&error))?;
        self.velocity = velocity;
        self.pressure = pressure;
        self.residual = residual;
        self.domain_extent = half_extent.map(|value| 2.0 * value);
        self.diagnostics = Some(diagnostics);
        Ok(())
    }

    pub fn velocity(&self) -> Vec<f32> {
        self.velocity.clone()
    }

    pub fn pressure(&self) -> Vec<f32> {
        self.pressure.clone()
    }

    pub fn residual(&self) -> Vec<f32> {
        self.residual.clone()
    }

    #[wasm_bindgen(js_name = domainExtent)]
    pub fn domain_extent(&self) -> Vec<f64> {
        self.domain_extent.to_vec()
    }

    pub fn diagnostics(&self) -> Result<JsValue, JsError> {
        let diagnostics = self
            .diagnostics
            .as_ref()
            .ok_or_else(|| JsError::new("sample must be called before diagnostics"))?;
        serde_wasm_bindgen::to_value(diagnostics).map_err(|error| JsError::new(&error.to_string()))
    }

    pub fn metadata(&self) -> Result<JsValue, JsError> {
        serde_wasm_bindgen::to_value(&self.inner.metadata())
            .map_err(|error| JsError::new(&error.to_string()))
    }
}

#[derive(serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct Metadata<'a> {
    backend: &'a str,
    precision: &'a str,
    #[serde(flatten)]
    convention: SpectralConventionMetadata,
}

#[wasm_bindgen]
pub struct NavierSolver {
    inner: SpectralSolver,
}

#[derive(serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct GpuMetadata {
    backend: &'static str,
    precision: &'static str,
    adapter_name: String,
    adapter_backend: String,
    #[serde(flatten)]
    convention: SpectralConventionMetadata,
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
            precision: "f64 compute / f32 render output",
            convention: self.inner.metadata(),
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
            precision: "f32 WebGPU compute / f32 render output",
            adapter_name: self.inner.adapter_name().to_owned(),
            adapter_backend: self.inner.adapter_backend().to_owned(),
            convention: self.inner.metadata(),
        };
        serde_wasm_bindgen::to_value(&value).map_err(|error| JsError::new(&error.to_string()))
    }
}
