use serde::Serialize;
use std::f64::consts::TAU;

pub const SPECTRAL_EQUATION: &str = "3D periodic incompressible Navier-Stokes";
pub const SPECTRAL_SPATIAL_METHOD: &str =
    "dealiased rotational Fourier pseudo-spectral with Leray projection";
pub const SPECTRAL_TIME_INTEGRATOR: &str = "fixed-step integrating-factor RK4";

/// Coordinate and coefficient conventions shared by every spectral backend.
///
/// `viscosity` is the coefficient used by the solver on `[0, 2π)^3`. The
/// period-one and Lean-raw values are derived from that same stored value, so
/// serialized metadata cannot silently mix coordinate systems.
#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SpectralConventionMetadata {
    pub equation: &'static str,
    pub spatial_method: &'static str,
    pub time_integrator: &'static str,
    pub grid: usize,
    pub viscosity: f64,
    pub dealiasing: bool,
    pub spatial_domain: &'static str,
    pub box_length: f64,
    pub fourier_series_convention: &'static str,
    pub stored_spectrum_convention: &'static str,
    pub viscosity_convention: &'static str,
    pub period_one_coordinate_map: &'static str,
    pub period_one_velocity_scale: f64,
    pub period_one_viscosity: f64,
    pub lean_raw_amplitude_convention: &'static str,
    pub lean_raw_viscosity: f64,
    pub continuum_certificate: bool,
    pub adaptive_recording: bool,
}

impl SpectralConventionMetadata {
    pub fn new(grid: usize, viscosity: f64) -> Self {
        Self {
            equation: SPECTRAL_EQUATION,
            spatial_method: SPECTRAL_SPATIAL_METHOD,
            time_integrator: SPECTRAL_TIME_INTEGRATOR,
            grid,
            viscosity,
            dealiasing: true,
            spatial_domain: "[0, 2π)^3",
            box_length: TAU,
            fourier_series_convention: "u_R(x) = sum_k uHat_R(k) exp(i k dot x)",
            stored_spectrum_convention: "U(k) = N^3 uHat_R(k) (unnormalized forward DFT)",
            viscosity_convention: "nu_R in the [0, 2π)^3 coordinate",
            period_one_coordinate_map: "u_P(y,t) = u_R(2π y,t) / (2π)",
            period_one_velocity_scale: 1.0 / TAU,
            period_one_viscosity: viscosity / TAU.powi(2),
            lean_raw_amplitude_convention: "A(k) = -i U(k) / N^3",
            lean_raw_viscosity: viscosity,
            continuum_certificate: false,
            adaptive_recording: false,
        }
    }
}
