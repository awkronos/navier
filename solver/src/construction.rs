//! Finite numerical realization of the analytic axis construction in Appendix B.
//!
//! This module evaluates the fixed-point map in equations (B.12)--(B.15) of
//! the OpenAI Navier--Stokes manuscript.  It is deliberately a finite axis
//! stage: the annular matching, Borel summation, primary waves, and correction
//! cycles used by the full construction are not represented here.

use serde::Serialize;

const Y_LIMIT: f64 = 3.2;
const ETA_LIMIT: f64 = 0.8;

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AxisConstructionConfig {
    pub h: f64,
    pub j0: f64,
    pub schedule_lambda: f64,
    pub schedule_m: f64,
    pub radial_scale: f64,
    pub pressure_amplitude: f64,
    pub radial_order: usize,
    pub eta_nodes: usize,
    pub iterations: usize,
}

impl Default for AxisConstructionConfig {
    fn default() -> Self {
        Self {
            h: 0.001,
            j0: 0.001,
            schedule_lambda: 0.04,
            schedule_m: 1.0,
            radial_scale: 48.0,
            pressure_amplitude: 2.0,
            radial_order: 12,
            eta_nodes: 257,
            iterations: 18,
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct PointValue {
    velocity: [f64; 3],
    pressure: f64,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AxisConstructionDiagnostics {
    pub finite: bool,
    pub fixed_point_delta: f64,
    pub angular_equation_rms: f64,
    pub axial_equation_rms: f64,
    pub pressure_equation_rms: f64,
    pub divergence_rms: f64,
    pub momentum_residual_rms: f64,
    pub max_speed: f64,
    pub domain_kinetic_energy: f64,
    pub min_normalized_swirl: f64,
    pub max_y: f64,
    pub max_abs_eta: f64,
    pub radial_order: usize,
    pub iterations: usize,
}

/// Physical coordinates and normalization used by the finite axis evaluator.
#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AxisConstructionCoordinates {
    pub physical_axes: [&'static str; 3],
    pub radial_plane_axes: [usize; 2],
    pub axial_axis: usize,
    pub tau_definition: &'static str,
    pub singular_time: f64,
    pub normalized_viscosity: f64,
    pub unit_convention: &'static str,
}

/// Browser-facing shape and memory layout of a sampled construction grid.
#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AxisConstructionGridLayout {
    pub topology: &'static str,
    pub wasm_domain_extent_kind: &'static str,
    pub native_evaluate_grid_extent_kind: &'static str,
    pub bounds_from_wasm_domain_extent: &'static str,
    pub includes_both_endpoints: bool,
    pub point_axis_order: [&'static str; 3],
    pub scalar_point_index: &'static str,
    pub vector_component_order: [&'static str; 3],
    pub vector_layout: &'static str,
}

/// Meaning of scalar diagnostics and fields exposed with a sampled grid.
#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AxisConstructionScalarSemantics {
    pub residual_symbol: &'static str,
    pub residual_formula: &'static str,
    pub residual_meaning: &'static str,
    pub residual_is_selected_smooth_force: bool,
    pub pressure_meaning: &'static str,
    pub pressure_absolute_level_is_gauge_invariant: bool,
    pub max_speed_meaning: &'static str,
    pub max_speed_is_continuum_supremum: bool,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct AxisConstructionMetadata {
    pub parameters: AxisConstructionConfig,
    pub sigma: f64,
    pub swirl_normalization: f64,
    pub model: &'static str,
    pub equations: &'static str,
    pub domain: &'static str,
    pub pressure_seed: &'static str,
    pub included_terms: &'static [&'static str],
    pub omitted_terms: &'static [&'static str],
    pub interpretation: &'static str,
    pub coordinates: AxisConstructionCoordinates,
    pub grid_layout: AxisConstructionGridLayout,
    pub scalar_semantics: AxisConstructionScalarSemantics,
}

pub type AxisConstructionGrid = (
    Vec<f32>,
    Vec<f32>,
    Vec<f32>,
    [f64; 3],
    AxisConstructionDiagnostics,
);

#[derive(Clone, Debug)]
pub struct AxisConstruction {
    config: AxisConstructionConfig,
    eta: Vec<f64>,
    phi: Vec<f64>,
    axial: Vec<f64>,
    axial_average: Vec<f64>,
    pressure_increment: Vec<f64>,
    phi_star: Vec<f64>,
    pressure_axis: Vec<f64>,
    chi: Vec<f64>,
    z_star: Vec<f64>,
    angular_remainder: Vec<f64>,
    axial_remainder: Vec<f64>,
    swirl_normalization: f64,
    sigma: f64,
    fixed_point_delta: f64,
}

fn idx(order: usize, node: usize, degree: usize) -> usize {
    node * (order + 1) + degree
}

fn eta_derivative(values: &[f64], nodes: usize, order: usize, spacing: f64) -> Vec<f64> {
    let mut out = vec![0.0; values.len()];
    for degree in 0..=order {
        for node in 0..nodes {
            let at = |n: usize| values[idx(order, n, degree)];
            out[idx(order, node, degree)] = if node >= 2 && node + 2 < nodes {
                (at(node - 2) - 8.0 * at(node - 1) + 8.0 * at(node + 1) - at(node + 2))
                    / (12.0 * spacing)
            } else if node == 0 {
                (-25.0 * at(0) + 48.0 * at(1) - 36.0 * at(2) + 16.0 * at(3) - 3.0 * at(4))
                    / (12.0 * spacing)
            } else if node == 1 {
                (-3.0 * at(0) - 10.0 * at(1) + 18.0 * at(2) - 6.0 * at(3) + at(4))
                    / (12.0 * spacing)
            } else if node + 1 == nodes {
                (25.0 * at(node) - 48.0 * at(node - 1) + 36.0 * at(node - 2) - 16.0 * at(node - 3)
                    + 3.0 * at(node - 4))
                    / (12.0 * spacing)
            } else {
                (3.0 * at(node + 1) + 10.0 * at(node) - 18.0 * at(node - 1) + 6.0 * at(node - 2)
                    - at(node - 3))
                    / (12.0 * spacing)
            };
        }
    }
    out
}

fn multiply(a: &[f64], b: &[f64], nodes: usize, order: usize) -> Vec<f64> {
    let mut out = vec![0.0; a.len()];
    for node in 0..nodes {
        for n in 0..=order {
            let mut sum = 0.0;
            for k in 0..=n {
                sum += a[idx(order, node, k)] * b[idx(order, node, n - k)];
            }
            out[idx(order, node, n)] = sum;
        }
    }
    out
}

fn j_operator(source: &[f64], nodes: usize, order: usize, nu: usize) -> Vec<f64> {
    let mut out = vec![0.0; source.len()];
    for node in 0..nodes {
        for n in 0..order {
            out[idx(order, node, n + 1)] =
                source[idx(order, node, n)] / ((n + 1) as f64 * (n + nu) as f64);
        }
    }
    out
}

fn radial_average(source: &[f64], nodes: usize, order: usize) -> Vec<f64> {
    let mut out = source.to_vec();
    for node in 0..nodes {
        for n in 0..=order {
            out[idx(order, node, n)] /= (n + 1) as f64;
        }
    }
    out
}

fn radial_integral(source: &[f64], nodes: usize, order: usize) -> Vec<f64> {
    let mut out = vec![0.0; source.len()];
    for node in 0..nodes {
        for n in 0..order {
            out[idx(order, node, n + 1)] = source[idx(order, node, n)] / (n + 1) as f64;
        }
    }
    out
}

fn radial_log_derivative(source: &[f64], nodes: usize, order: usize) -> Vec<f64> {
    let mut out = source.to_vec();
    for node in 0..nodes {
        for n in 0..=order {
            out[idx(order, node, n)] *= n as f64;
        }
    }
    out
}

fn evaluate(coefficients: &[f64], node: usize, order: usize, y: f64) -> f64 {
    (0..=order).rev().fold(0.0, |value, n| {
        value * y + coefficients[idx(order, node, n)]
    })
}

fn evaluate_derivative(coefficients: &[f64], node: usize, order: usize, y: f64) -> f64 {
    (1..=order).rev().fold(0.0, |value, n| {
        value * y + n as f64 * coefficients[idx(order, node, n)]
    })
}

fn evaluate_second_derivative(coefficients: &[f64], node: usize, order: usize, y: f64) -> f64 {
    (2..=order).rev().fold(0.0, |value, n| {
        value * y + (n * (n - 1)) as f64 * coefficients[idx(order, node, n)]
    })
}

fn smooth_step(x: f64) -> f64 {
    if x <= 0.0 {
        0.0
    } else if x >= 1.0 {
        1.0
    } else {
        let left = (-1.0 / (x * x)).exp();
        let right = (-1.0 / ((1.0 - x) * (1.0 - x))).exp();
        left / (left + right)
    }
}

fn smooth_step_derivative(x: f64) -> f64 {
    if !(0.0..1.0).contains(&x) {
        0.0
    } else {
        let value = smooth_step(x);
        value * (1.0 - value) * (2.0 / x.powi(3) + 2.0 / (1.0 - x).powi(3))
    }
}

fn simpson<F: Fn(f64) -> f64>(start: f64, end: f64, intervals: usize, f: F) -> f64 {
    let intervals = intervals + intervals % 2;
    let step = (end - start) / intervals as f64;
    let mut sum = f(start) + f(end);
    for i in 1..intervals {
        sum += if i % 2 == 0 { 2.0 } else { 4.0 } * f(start + i as f64 * step);
    }
    sum * step / 3.0
}

/// The exact Appendix-A schedule used in (A.21), evaluated by deterministic
/// midpoint quadrature after analytically integrating its two infinite tails.
fn build_pressure_axis(
    eta: &[f64],
    h: f64,
    lambda: f64,
    m: f64,
    pressure_amplitude: f64,
) -> Result<(Vec<f64>, Vec<f64>), String> {
    let step_bound = 8.0;
    let rho = (-5.0f64).exp() * h / (16.0 * (step_bound + 1.0));
    let drop_length = m.exp() + 10.0;
    let wait = 60.0 * (1.0 / lambda).ln();
    let endpoint = drop_length + 2.0 + wait + 13.0 / lambda;
    let flatten_length = 10.0 * (step_bound + 1.0) * 2.0f64.ln() + 1.0;
    let flatten_end = endpoint + flatten_length;
    let release_start = flatten_end + 30.0 * (1.0 / lambda).ln();
    let second_ramp_start = 1.0 + 4.0 * (1.0 / h).ln();
    let ramp_end = second_ramp_start + 1.0;
    let tail_shape = |t: f64| 1.0 - rho + rho * smooth_step((t - 1.0) / 2.0);
    let tail_shape_derivative = |t: f64| 0.5 * rho * smooth_step_derivative((t - 1.0) / 2.0);
    let tail_debt = simpson(0.0, 3.0, 2048, |t| {
        ((1.0 - h) * t).exp() * tail_shape_derivative(t)
    }) / (1.0 - rho);
    let release_slope = |t: f64| {
        -lambda - (1.0 - lambda) * smooth_step(t) + (1.0 - h) * smooth_step(t - second_ramp_start)
    };
    let mut lag = (lambda - h) / (1.0 - lambda);
    let ode_steps = 32768usize;
    let ode_step = ramp_end / ode_steps as f64;
    let rhs = |t: f64, value: f64| {
        let slope = release_slope(t);
        (-slope - h) - (1.0 + slope) * value
    };
    for i in 0..ode_steps {
        let t = i as f64 * ode_step;
        let k1 = rhs(t, lag);
        let k2 = rhs(t + ode_step / 2.0, lag + ode_step * k1 / 2.0);
        let k3 = rhs(t + ode_step / 2.0, lag + ode_step * k2 / 2.0);
        let k4 = rhs(t + ode_step, lag + ode_step * k3);
        lag += ode_step * (k1 + 2.0 * k2 + 2.0 * k3 + k4) / 6.0;
    }
    let decay_hold = (lag / tail_debt).ln() / (1.0 - h);
    let tail_start = release_start + ramp_end + decay_hold;
    let tail_end = tail_start + 3.0;

    let quadrature_step = 0.025;
    let requested_steps = (tail_end / quadrature_step).ceil();
    if !requested_steps.is_finite() || !(1.0..=1_000_000.0).contains(&requested_steps) {
        return Err(
            "Appendix-A pressure schedule exceeds the finite quadrature budget; increase schedule_lambda or reduce schedule_m"
                .into(),
        );
    }
    let quadrature_steps = requested_steps as usize;
    let dy = tail_end / quadrature_steps as f64;
    let mut pressure = vec![0.0; eta.len()];
    let mut pressure_eta = vec![0.0; eta.len()];
    let mut log_radial = pressure_amplitude.ln();
    let mut release_adjustment = 0.0;
    for step in 0..quadrature_steps {
        let y = (step as f64 + 0.5) * dy;
        let slope = 0.6 * (1.0 - smooth_step(y)) - lambda * smooth_step(y - drop_length - 1.0);
        let log_radial_midpoint = log_radial + (slope - 0.5) * dy / 2.0;
        let release_t = y - release_start;
        let release_midpoint = release_adjustment + (release_slope(release_t) + lambda) * dy / 2.0;
        let flatten = smooth_step((y - endpoint) / flatten_length);
        let tail = tail_shape(y - tail_start) / (1.0 - rho);
        for (node, &e) in eta.iter().enumerate() {
            let log_shape = (flatten - 1.0) * (1.0 + e * e).ln() - flatten * 2.0f64.ln();
            let angular = (log_radial_midpoint + log_shape + release_midpoint).exp() * tail;
            let square = angular * angular;
            pressure[node] += square * dy;
            pressure_eta[node] += (1.0 - flatten) * square * dy;
        }
        log_radial += (slope - 0.5) * dy;
        release_adjustment += (release_slope(release_t) + lambda) * dy;
    }
    // y<0 is the A.7 power law and can be integrated exactly.
    for (node, &e) in eta.iter().enumerate() {
        let f = 1.0 / (1.0 + e * e);
        pressure[node] += 5.0 * pressure_amplitude * pressure_amplitude * f * f;
        pressure_eta[node] += 5.0 * pressure_amplitude * pressure_amplitude * f * f;
        // For y>=tail_end the profile is eta-independent, so its eta derivative is zero.
        let tail_value = pressure_amplitude
            * (log_radial - pressure_amplitude.ln() + release_adjustment).exp()
            * 0.5
            / (1.0 - rho);
        pressure[node] += tail_value * tail_value / (1.0 + 2.0 * h);
        pressure[node] *= -0.5;
        pressure_eta[node] *= 2.0 * e / (1.0 + e * e);
    }
    if pressure
        .iter()
        .chain(&pressure_eta)
        .any(|value| !value.is_finite())
    {
        return Err("Appendix-A pressure quadrature produced a non-finite profile".into());
    }
    Ok((pressure, pressure_eta))
}

impl AxisConstruction {
    pub fn new(config: AxisConstructionConfig) -> Result<Self, String> {
        if !(0.0 < config.h && config.h < 0.01) {
            return Err("h must lie strictly between 0 and 0.01".into());
        }
        if !(0.0 < config.j0 && config.j0 <= 0.05) {
            return Err("j0 must lie in (0, 0.05]".into());
        }
        if !config.radial_scale.is_finite() || config.radial_scale < 1.0 {
            return Err("radial_scale must be finite and at least one".into());
        }
        if !config.pressure_amplitude.is_finite() || config.pressure_amplitude <= 0.0 {
            return Err("pressure amplitude must be finite and positive".into());
        }
        if config.pressure_amplitude > f64::MAX.sqrt() {
            return Err("pressure amplitude is too large for finite squared pressure data".into());
        }
        if !(0.0 < config.schedule_lambda && config.schedule_lambda < 0.1)
            || 2.0 * config.h >= config.schedule_lambda
        {
            return Err("schedule_lambda must lie in (2h, 0.1)".into());
        }
        if !config.schedule_m.is_finite() || config.schedule_m <= 0.0 {
            return Err("schedule_m must be finite and positive".into());
        }
        if !(4..=32).contains(&config.radial_order) {
            return Err("radial order must lie in 4..=32".into());
        }
        if !(33..=4097).contains(&config.eta_nodes) || config.eta_nodes.is_multiple_of(2) {
            return Err("eta_nodes must be an odd integer in 33..=4097".into());
        }
        if !(1..=100).contains(&config.iterations) {
            return Err("iterations must lie in 1..=100".into());
        }

        let nodes = config.eta_nodes;
        let order = config.radial_order;
        let spacing = 2.0 / (nodes - 1) as f64;
        let eta: Vec<_> = (0..nodes).map(|i| -1.0 + i as f64 * spacing).collect();
        let a = 0.5 + config.h;
        let d_exp = 0.5 - config.h;
        let (pressure_axis, pressure_axis_eta) = build_pressure_axis(
            &eta,
            config.h,
            config.schedule_lambda,
            config.schedule_m,
            config.pressure_amplitude,
        )?;

        let mut zeta = vec![0.0; nodes];
        let mut chi = vec![0.0; nodes];
        let mut u_star = vec![0.0; nodes];
        let mut h_star = vec![0.0; nodes];
        let mut w_star = vec![0.0; nodes];
        let mut z_star = vec![0.0; nodes];
        for (i, &e) in eta.iter().enumerate() {
            let d = 1.0 - e * e;
            let l = 1.0 - 2.0 * config.h * e * e;
            u_star[i] = 4.0 * e + config.j0;
            h_star[i] = d_exp * e + d * u_star[i];
            w_star[i] = 1.0 - 4.0 * d - 2.0 * d_exp * e * u_star[i];
            z_star[i] = -a * (1.0 - 2.0 * e * u_star[i]) * u_star[i]
                - 4.0 * h_star[i]
                - d * pressure_axis_eta[i]
                + 4.0 * a * e * pressure_axis[i];
            let _ = l;
        }

        let delta = config.j0 / 10.0;
        let mut minimum_h2 = f64::INFINITY;
        for i in 0..nodes - 1 {
            if z_star[i].abs() <= delta {
                minimum_h2 = minimum_h2.min(h_star[i] * h_star[i]);
            }
            if z_star[i] * z_star[i + 1] <= 0.0 {
                let weight =
                    z_star[i].abs() / (z_star[i].abs() + z_star[i + 1].abs()).max(1.0e-300);
                let value = h_star[i] + weight * (h_star[i + 1] - h_star[i]);
                minimum_h2 = minimum_h2.min(value * value);
            }
        }
        if !minimum_h2.is_finite() || minimum_h2 <= 0.0 {
            return Err(
                "could not locate the Appendix-B Z* transition used to choose sigma".into(),
            );
        }
        let sigma = minimum_h2.sqrt() / 20.0;
        for i in 0..nodes {
            let e = eta[i];
            let l = 1.0 - 2.0 * config.h * e * e;
            let denominator = h_star[i] * h_star[i] + sigma * sigma;
            chi[i] = h_star[i] * h_star[i] / denominator;
            zeta[i] = -l * h_star[i] / denominator;
        }

        let zero = (nodes - 1) / 2;
        let mut primitive = vec![0.0; nodes];
        for i in zero + 1..nodes {
            primitive[i] = primitive[i - 1] + 0.5 * spacing * (zeta[i - 1] + zeta[i]);
        }
        for i in (0..zero).rev() {
            primitive[i] = primitive[i + 1] - 0.5 * spacing * (zeta[i + 1] + zeta[i]);
        }
        let phi_star: Vec<_> = primitive
            .iter()
            .map(|&value| (config.radial_scale * value).exp())
            .collect();
        if phi_star.iter().any(|value| !value.is_finite()) {
            return Err(
                "axis azimuthal datum overflowed; increase swirl_normalization or lower lambda"
                    .into(),
            );
        }

        let size = nodes * (order + 1);
        let mut phi0 = vec![0.0; size];
        let mut axial0 = vec![0.0; size];
        for node in 0..nodes {
            let mut factorial = 1.0;
            let mut next_factorial = 1.0;
            let mut power = 1.0;
            for n in 0..=order {
                if n > 0 {
                    factorial *= n as f64;
                    next_factorial *= (n + 1) as f64;
                    power *= -0.5 * chi[node];
                }
                phi0[idx(order, node, n)] = power / (factorial * next_factorial);
            }
            axial0[idx(order, node, 1)] =
                -z_star[node] / (2.0 * (1.0 - 2.0 * config.h * eta[node] * eta[node]));
        }

        let swirl_normalization = 4.0 * phi_star.iter().copied().fold(1.0, f64::max);

        let mut phi = phi0.clone();
        let mut axial = axial0.clone();
        let mut fixed_point_delta = f64::INFINITY;
        let mut pressure_increment = vec![0.0; size];
        let mut angular_remainder = vec![0.0; size];
        let mut axial_remainder = vec![0.0; size];

        for iteration in 0..=config.iterations {
            let phi_eta = eta_derivative(&phi, nodes, order, spacing);
            let axial_eta = eta_derivative(&axial, nodes, order, spacing);
            let axial_average = radial_average(&axial, nodes, order);
            let axial_average_eta = eta_derivative(&axial_average, nodes, order, spacing);
            let axial_dx = radial_log_derivative(&axial, nodes, order);
            let phi_dx = radial_log_derivative(&phi, nodes, order);
            let phi_sq = multiply(&phi, &phi, nodes, order);
            let axial_sq = multiply(&axial, &axial, nodes, order);
            let axial_axial_eta = multiply(&axial, &axial_eta, nodes, order);

            let mut pressure_source = phi_sq;
            for node in 0..nodes {
                let g = phi_star[node] / swirl_normalization;
                for n in 0..=order {
                    pressure_source[idx(order, node, n)] *= g * g;
                }
            }
            pressure_increment = radial_integral(&pressure_source, nodes, order);
            let pressure_eta = eta_derivative(&pressure_increment, nodes, order, spacing);
            let pressure_dx = radial_log_derivative(&pressure_increment, nodes, order);

            let mut b = vec![0.0; size];
            let mut w = vec![0.0; size];
            let mut hc = vec![0.0; size];
            for node in 0..nodes {
                let e = eta[node];
                let d = 1.0 - e * e;
                for n in 0..=order {
                    b[idx(order, node, n)] = -2.0 * d_exp * e * axial_average[idx(order, node, n)]
                        - d * axial_average_eta[idx(order, node, n)];
                    w[idx(order, node, n)] = b[idx(order, node, n)] / config.radial_scale;
                    hc[idx(order, node, n)] = d * axial[idx(order, node, n)] / config.radial_scale;
                }
                w[idx(order, node, 0)] += w_star[node];
                hc[idx(order, node, 0)] += h_star[node];
            }

            let w_phi_dx = multiply(&w, &phi_dx, nodes, order);
            let hc_phi_eta = multiply(&hc, &phi_eta, nodes, order);
            let w_axial_dx = multiply(&w, &axial_dx, nodes, order);
            let mut r1 = vec![0.0; size];
            let mut r2 = vec![0.0; size];
            for node in 0..nodes {
                let e = eta[node];
                let d = 1.0 - e * e;
                let l = 1.0 - 2.0 * config.h * e * e;
                for n in 0..=order {
                    let u_n = axial[idx(order, node, n)];
                    let u_full_n =
                        u_n / config.radial_scale + if n == 0 { u_star[node] } else { 0.0 };
                    let bracket = w[idx(order, node, n)] - 2.0 * config.h * e * u_full_n
                        + d * zeta[node] * u_n
                        + if n == 0 { config.h } else { 0.0 };
                    // Multiplication of the bracket by Phi is completed below.
                    r1[idx(order, node, n)] = bracket;

                    r2[idx(order, node, n)] = (a * (1.0 - 4.0 * e * u_star[node]) + 4.0 * d) * u_n
                        - 2.0 * a * e * axial_sq[idx(order, node, n)] / config.radial_scale
                        + w_axial_dx[idx(order, node, n)]
                        + h_star[node] * axial_eta[idx(order, node, n)]
                        + d * axial_axial_eta[idx(order, node, n)] / config.radial_scale
                        - 4.0 * a * e * pressure_increment[idx(order, node, n)]
                        + d * pressure_eta[idx(order, node, n)]
                        - 2.0 * e * pressure_dx[idx(order, node, n)];
                    r2[idx(order, node, n)] /= l;
                }
            }
            r1 = multiply(&r1, &phi, nodes, order);
            for i in 0..size {
                r1[i] = (r1[i] + w_phi_dx[i] + hc_phi_eta[i])
                    / (1.0 - 2.0 * config.h * eta[i / (order + 1)].powi(2));
            }
            angular_remainder = r1.clone();
            axial_remainder = r2.clone();
            if iteration == config.iterations {
                break;
            }

            let correction_phi = j_operator(&r1, nodes, order, 2);
            let correction_axial = j_operator(&r2, nodes, order, 1);
            let mut next_phi = phi0.clone();
            let mut next_axial = axial0.clone();
            for node in 0..nodes {
                // (1 + J2 chi/2)^-1 is lower triangular in radial degree.
                let mut solved = vec![0.0; order + 1];
                for n in 0..=order {
                    let rhs = correction_phi[idx(order, node, n)] / (2.0 * config.radial_scale);
                    solved[n] = if n == 0 {
                        rhs
                    } else {
                        rhs - chi[node] * solved[n - 1] / (2.0 * n as f64 * (n + 1) as f64)
                    };
                    next_phi[idx(order, node, n)] += solved[n];
                    next_axial[idx(order, node, n)] +=
                        correction_axial[idx(order, node, n)] / (2.0 * config.radial_scale);
                }
            }
            fixed_point_delta = next_phi
                .iter()
                .zip(&phi)
                .chain(next_axial.iter().zip(&axial))
                .map(|(a, b)| (a - b).abs())
                .fold(0.0, f64::max);
            phi = next_phi;
            axial = next_axial;
        }

        let axial_average = radial_average(&axial, nodes, order);
        Ok(Self {
            config,
            eta,
            phi,
            axial,
            axial_average,
            pressure_increment,
            phi_star,
            pressure_axis,
            chi,
            z_star,
            angular_remainder,
            axial_remainder,
            swirl_normalization,
            sigma,
            fixed_point_delta,
        })
    }

    pub fn config(&self) -> &AxisConstructionConfig {
        &self.config
    }

    pub fn metadata(&self) -> AxisConstructionMetadata {
        AxisConstructionMetadata {
            parameters: self.config.clone(),
            sigma: self.sigma,
            swirl_normalization: self.swirl_normalization,
            model: "finite Appendix-B analytic axis-profile iteration",
            equations: "OpenAI manuscript (4.1)-(4.7), (B.5), (B.12)-(B.15)",
            domain: "whole-space similarity chart restricted to tau>0, |eta|<=0.8, Lambda*X<=3.2",
            pressure_seed: "deterministic quadrature of the complete Appendix-A schedule in A.5/A.21, with analytic infinite tails",
            included_terms: &[
                "finite radial power series",
                "nonlinear Appendix-B fixed-point iteration",
                "incompressible physical reconstruction",
                "centrifugal pressure balance",
            ],
            omitted_terms: &[
                "annular moment matching and cone modulation",
                "positive-order Borel background",
                "primary covariance waves",
                "particular, signed, and mean correction cycles",
                "final space-time localization",
            ],
            interpretation: "A finite numerical construction stage; it is not the completed solution and is not a blowup certificate.",
            coordinates: AxisConstructionCoordinates {
                physical_axes: ["x", "y", "z"],
                radial_plane_axes: [0, 1],
                axial_axis: 2,
                tau_definition: "tau = 1 - t",
                singular_time: 1.0,
                normalized_viscosity: 1.0,
                unit_convention: "manuscript-normalized physical coordinates; no SI unit conversion",
            },
            grid_layout: AxisConstructionGridLayout {
                topology: "open",
                wasm_domain_extent_kind: "full side lengths [Lx, Ly, Lz]",
                native_evaluate_grid_extent_kind: "positive half extents [Lx/2, Ly/2, Lz/2]",
                bounds_from_wasm_domain_extent: "coordinate[i] in [-domainExtent[i]/2, +domainExtent[i]/2]",
                includes_both_endpoints: true,
                point_axis_order: ["x", "y", "z"],
                scalar_point_index: "(xIndex * N + yIndex) * N + zIndex",
                vector_component_order: ["x", "y", "z"],
                vector_layout: "interleaved xyz components at 3 * scalarPointIndex",
            },
            scalar_semantics: AxisConstructionScalarSemantics {
                residual_symbol: "R",
                residual_formula: "R = partial_t u + (u dot grad)u - Delta u + grad p",
                residual_meaning: "force required by the finite reconstructed axis stage at normalized viscosity 1; not an error estimate",
                residual_is_selected_smooth_force: false,
                pressure_meaning: "selected representative fixed by pressureSeed; same-time pressure differences and spatial gradients are gauge-invariant",
                pressure_absolute_level_is_gauge_invariant: false,
                max_speed_meaning: "maximum Euclidean speed over the sampled grid; a grid-dependent lower observation of the chart supremum",
                max_speed_is_continuum_supremum: false,
            },
        }
    }

    fn node_fraction(&self, eta: f64) -> (usize, f64) {
        let scaled = ((eta + 1.0) * 0.5 * (self.config.eta_nodes - 1) as f64)
            .clamp(0.0, (self.config.eta_nodes - 1) as f64);
        let left = (scaled.floor() as usize).min(self.config.eta_nodes - 2);
        (left, scaled - left as f64)
    }

    fn interpolate_polynomial(&self, coefficients: &[f64], eta: f64, y: f64) -> f64 {
        let (left, weight) = self.node_fraction(eta);
        let i0 = left.saturating_sub(1);
        let i1 = left;
        let i2 = left + 1;
        let i3 = (left + 2).min(self.config.eta_nodes - 1);
        let p0 = evaluate(coefficients, i0, self.config.radial_order, y);
        let p1 = evaluate(coefficients, i1, self.config.radial_order, y);
        let p2 = evaluate(coefficients, i2, self.config.radial_order, y);
        let p3 = evaluate(coefficients, i3, self.config.radial_order, y);
        let w2 = weight * weight;
        let w3 = w2 * weight;
        0.5 * ((2.0 * p1)
            + (-p0 + p2) * weight
            + (2.0 * p0 - 5.0 * p1 + 4.0 * p2 - p3) * w2
            + (-p0 + 3.0 * p1 - 3.0 * p2 + p3) * w3)
    }

    fn interpolate_scalar(&self, values: &[f64], eta: f64) -> f64 {
        let (left, weight) = self.node_fraction(eta);
        let p0 = values[left.saturating_sub(1)];
        let p1 = values[left];
        let p2 = values[left + 1];
        let p3 = values[(left + 2).min(self.config.eta_nodes - 1)];
        let w2 = weight * weight;
        let w3 = w2 * weight;
        0.5 * ((2.0 * p1)
            + (-p0 + p2) * weight
            + (2.0 * p0 - 5.0 * p1 + 4.0 * p2 - p3) * w2
            + (-p0 + 3.0 * p1 - 3.0 * p2 + p3) * w3)
    }

    fn interpolate_polynomial_eta_derivative(&self, coefficients: &[f64], eta: f64, y: f64) -> f64 {
        let (left, weight) = self.node_fraction(eta);
        let i0 = left.saturating_sub(1);
        let i1 = left;
        let i2 = left + 1;
        let i3 = (left + 2).min(self.config.eta_nodes - 1);
        let p0 = evaluate(coefficients, i0, self.config.radial_order, y);
        let p1 = evaluate(coefficients, i1, self.config.radial_order, y);
        let p2 = evaluate(coefficients, i2, self.config.radial_order, y);
        let p3 = evaluate(coefficients, i3, self.config.radial_order, y);
        let derivative_weight = 0.5
            * ((-p0 + p2)
                + 2.0 * (2.0 * p0 - 5.0 * p1 + 4.0 * p2 - p3) * weight
                + 3.0 * (-p0 + 3.0 * p1 - 3.0 * p2 + p3) * weight * weight);
        derivative_weight * (self.config.eta_nodes - 1) as f64 / 2.0
    }

    pub fn similarity_q(&self, tau: f64, z: f64) -> Result<f64, String> {
        if !tau.is_finite() || tau <= 0.0 || !z.is_finite() {
            return Err("tau must be finite and positive and z must be finite".into());
        }
        let z2 = z * z;
        if !z2.is_finite() {
            return Err("z is too large for a finite similarity-coordinate root".into());
        }
        if z2 == 0.0 {
            return Ok(tau);
        }
        let d_exp = 0.5 - self.config.h;
        let root_floor = z.abs().powf(1.0 / d_exp);
        if !root_floor.is_finite() {
            return Err("similarity-coordinate lower bracket overflowed".into());
        }
        let equation = |q: f64| {
            let nonlinear = z2 * q.powf(2.0 * self.config.h);
            (q - nonlinear - tau, nonlinear)
        };
        // The manuscript's physical branch has q>|z|^(1/D), and its defining
        // function equals -tau at that lower endpoint.
        let mut lo = tau;
        let mut hi = tau.max(root_floor);
        loop {
            let (value, _) = equation(hi);
            if !value.is_finite() {
                return Err("similarity-coordinate bracket produced a non-finite residual".into());
            }
            if value > 0.0 {
                break;
            }
            if hi > f64::MAX / 2.0 {
                return Err("similarity-coordinate root overflowed".into());
            }
            hi *= 2.0;
        }
        // Newton from the upper bracket converges rapidly: on and above the
        // root the derivative is positive and the defining function is convex.
        // Retain the bracket as a guard against floating-point cancellation.
        let mut q = hi;
        for _ in 0..64 {
            let power = q.powf(2.0 * self.config.h);
            let nonlinear = z2 * power;
            let value = q - nonlinear - tau;
            let scale = q.abs().max(nonlinear.abs()).max(tau);
            if value.is_finite() && value.abs() <= 8.0 * f64::EPSILON * scale {
                if tau <= 32.0 * f64::EPSILON * scale {
                    return Err(
                        "tau is below floating-point resolution at the similarity root".into(),
                    );
                }
                return Ok(q);
            }
            if value > 0.0 {
                hi = q;
            } else {
                lo = q;
            }
            let derivative = 1.0 - 2.0 * self.config.h * z2 * power / q;
            let next = q - value / derivative;
            q = if next.is_finite() && next > lo && next < hi {
                next
            } else {
                0.5 * (lo + hi)
            };
        }
        let q = 0.5 * (lo + hi);
        let (value, nonlinear) = equation(q);
        let scale = q.abs().max(nonlinear.abs()).max(tau);
        if value.is_finite() && value.abs() <= 16.0 * f64::EPSILON * scale {
            if tau <= 32.0 * f64::EPSILON * scale {
                Err("tau is below floating-point resolution at the similarity root".into())
            } else {
                Ok(q)
            }
        } else {
            Err("similarity-coordinate root did not converge to a finite residual".into())
        }
    }

    fn point(&self, tau: f64, xyz: [f64; 3]) -> Result<PointValue, String> {
        if xyz.iter().any(|coordinate| !coordinate.is_finite()) {
            return Err("physical coordinates must be finite".into());
        }
        let q = self.similarity_q(tau, xyz[2])?;
        let d_exp = 0.5 - self.config.h;
        let a = 0.5 + self.config.h;
        let eta = xyz[2] / q.powf(d_exp);
        let x = (xyz[0] * xyz[0] + xyz[1] * xyz[1]) / (2.0 * q);
        let y = self.config.radial_scale * x;
        if eta.abs() > 0.98 || y > 4.05 {
            return Err("point lies outside the finite analytic axis-profile chart".into());
        }
        let phi = self.interpolate_polynomial(&self.phi, eta, y);
        let u_correction = self.interpolate_polynomial(&self.axial, eta, y);
        let u_star = 4.0 * eta + self.config.j0;
        let axial = u_star + u_correction / self.config.radial_scale;
        let averaged = self.interpolate_polynomial(&self.axial_average, eta, y);
        let averaged_eta = self.interpolate_polynomial_eta_derivative(&self.axial_average, eta, y);
        let d = 1.0 - eta * eta;
        let l = 1.0 - 2.0 * self.config.h * eta * eta;
        let v0 = (2.0 * eta * axial
            - 2.0 * d_exp * eta * (u_star + averaged / self.config.radial_scale)
            - d * (4.0 + averaged_eta / self.config.radial_scale))
            / l;
        let f = self.interpolate_scalar(&self.phi_star, eta) * phi / self.swirl_normalization;
        let pressure_profile = self.interpolate_scalar(&self.pressure_axis, eta)
            + self.interpolate_polynomial(&self.pressure_increment, eta, y)
                / self.config.radial_scale;
        let swirl_scale = q.powf(-a - 0.5) * f;
        let value = PointValue {
            velocity: [
                v0 * xyz[0] / (2.0 * q) - swirl_scale * xyz[1],
                v0 * xyz[1] / (2.0 * q) + swirl_scale * xyz[0],
                q.powf(-a) * axial,
            ],
            pressure: q.powf(-2.0 * a) * pressure_profile,
        };
        if value
            .velocity
            .iter()
            .chain(std::iter::once(&value.pressure))
            .any(|component| !component.is_finite())
        {
            return Err("physical reconstruction produced a non-finite field".into());
        }
        Ok(value)
    }

    pub fn sample(&self, tau: f64, xyz: [f64; 3]) -> Result<([f64; 3], f64), String> {
        let value = self.point(tau, xyz)?;
        Ok((value.velocity, value.pressure))
    }

    pub fn domain_half_extent(&self, tau: f64) -> Result<[f64; 3], String> {
        if !tau.is_finite() || tau <= 0.0 {
            return Err("tau must be finite and positive".into());
        }
        let xy = (tau * Y_LIMIT / self.config.radial_scale).sqrt();
        let qz = tau / (1.0 - ETA_LIMIT * ETA_LIMIT);
        let z = ETA_LIMIT * qz.powf(0.5 - self.config.h);
        let extent = [xy, xy, z];
        if extent
            .iter()
            .any(|value| !value.is_finite() || *value <= 0.0)
        {
            return Err("tau is outside the finite physical chart range".into());
        }
        Ok(extent)
    }

    fn point_residual(
        &self,
        tau: f64,
        xyz: [f64; 3],
        scale: [f64; 3],
    ) -> Result<([f64; 3], f64), String> {
        self.point_residual_with_step(tau, xyz, scale, 2.0e-4)
    }

    fn point_residual_with_step(
        &self,
        tau: f64,
        xyz: [f64; 3],
        scale: [f64; 3],
        relative_step: f64,
    ) -> Result<([f64; 3], f64), String> {
        if !relative_step.is_finite() || relative_step <= 0.0 || relative_step > 0.01 {
            return Err("residual relative step must lie in (0, 0.01]".into());
        }
        let center = self.point(tau, xyz)?;
        let mut gradient = [[0.0; 3]; 3];
        let mut laplacian = [0.0; 3];
        let mut pressure_gradient = [0.0; 3];
        for direction in 0..3 {
            let step = scale[direction] * relative_step;
            if !step.is_finite() || step <= 0.0 {
                return Err("physical residual step is not representable".into());
            }
            let mut plus = xyz;
            let mut minus = xyz;
            plus[direction] += step;
            minus[direction] -= step;
            let vp = self.point(tau, plus)?;
            let vm = self.point(tau, minus)?;
            for component in 0..3 {
                gradient[component][direction] =
                    (vp.velocity[component] - vm.velocity[component]) / (2.0 * step);
                laplacian[component] += (vp.velocity[component] - 2.0 * center.velocity[component]
                    + vm.velocity[component])
                    / (step * step);
            }
            pressure_gradient[direction] = (vp.pressure - vm.pressure) / (2.0 * step);
        }
        let dtau = tau * relative_step;
        if !dtau.is_finite() || dtau <= 0.0 || tau - dtau <= 0.0 {
            return Err("temporal residual step is not representable".into());
        }
        let later = self.point(tau + dtau, xyz)?;
        let earlier = self.point(tau - dtau, xyz)?;
        let mut residual = [0.0; 3];
        for component in 0..3 {
            // t = 1 - tau.
            let temporal =
                -(later.velocity[component] - earlier.velocity[component]) / (2.0 * dtau);
            let advection = (0..3)
                .map(|direction| center.velocity[direction] * gradient[component][direction])
                .sum::<f64>();
            residual[component] =
                temporal + advection - laplacian[component] + pressure_gradient[component];
        }
        let divergence = gradient[0][0] + gradient[1][1] + gradient[2][2];
        Ok((residual, divergence))
    }

    pub fn evaluate_grid(&self, grid: usize, tau: f64) -> Result<AxisConstructionGrid, String> {
        if !(5..=48).contains(&grid) {
            return Err("grid must lie in 5..=48".into());
        }
        let extent = self.domain_half_extent(tau)?;
        let count = grid * grid * grid;
        let mut velocity = Vec::with_capacity(3 * count);
        let mut pressure = Vec::with_capacity(count);
        let mut force = Vec::with_capacity(3 * count);
        let mut residual_sum = 0.0;
        let mut divergence_sum = 0.0;
        let mut energy_sum = 0.0;
        let mut max_speed: f64 = 0.0;
        for i in 0..grid {
            let x = -extent[0] + 2.0 * extent[0] * i as f64 / (grid - 1) as f64;
            for j in 0..grid {
                let y = -extent[1] + 2.0 * extent[1] * j as f64 / (grid - 1) as f64;
                for k in 0..grid {
                    let z = -extent[2] + 2.0 * extent[2] * k as f64 / (grid - 1) as f64;
                    let point = self.point(tau, [x, y, z])?;
                    let (residual, divergence) = self.point_residual(tau, [x, y, z], extent)?;
                    let speed2 = point.velocity.iter().map(|v| v * v).sum::<f64>();
                    max_speed = max_speed.max(speed2.sqrt());
                    let trapezoid_weight = (if i == 0 || i + 1 == grid { 0.5 } else { 1.0 })
                        * (if j == 0 || j + 1 == grid { 0.5 } else { 1.0 })
                        * (if k == 0 || k + 1 == grid { 0.5 } else { 1.0 });
                    energy_sum += 0.5 * speed2 * trapezoid_weight;
                    residual_sum += residual.iter().map(|v| v * v).sum::<f64>();
                    divergence_sum += divergence * divergence;
                    velocity.extend(point.velocity.map(|value| value as f32));
                    pressure.push(point.pressure as f32);
                    force.extend(residual.map(|value| value as f32));
                }
            }
        }
        let finite = velocity
            .iter()
            .chain(&pressure)
            .chain(&force)
            .all(|v| v.is_finite());
        if !finite
            || !residual_sum.is_finite()
            || !divergence_sum.is_finite()
            || !energy_sum.is_finite()
            || !max_speed.is_finite()
        {
            return Err(
                "construction grid exceeds the finite f32 output or f64 diagnostic range".into(),
            );
        }
        let cell_volume = (2.0 * extent[0] / (grid - 1) as f64)
            * (2.0 * extent[1] / (grid - 1) as f64)
            * (2.0 * extent[2] / (grid - 1) as f64);
        let (angular_equation_rms, axial_equation_rms, pressure_equation_rms) =
            self.profile_equation_rms();
        let diagnostics = AxisConstructionDiagnostics {
            finite,
            fixed_point_delta: self.fixed_point_delta,
            angular_equation_rms,
            axial_equation_rms,
            pressure_equation_rms,
            divergence_rms: (divergence_sum / count as f64).sqrt(),
            momentum_residual_rms: (residual_sum / count as f64).sqrt(),
            max_speed,
            domain_kinetic_energy: energy_sum * cell_volume,
            min_normalized_swirl: self.min_normalized_swirl(),
            max_y: Y_LIMIT,
            max_abs_eta: ETA_LIMIT,
            radial_order: self.config.radial_order,
            iterations: self.config.iterations,
        };
        Ok((velocity, pressure, force, extent, diagnostics))
    }

    pub fn min_normalized_swirl(&self) -> f64 {
        let mut minimum = f64::INFINITY;
        for node in 0..self.config.eta_nodes {
            if self.eta[node].abs() <= ETA_LIMIT {
                for sample in 0..=32 {
                    minimum = minimum.min(evaluate(
                        &self.phi,
                        node,
                        self.config.radial_order,
                        Y_LIMIT * sample as f64 / 32.0,
                    ));
                }
            }
        }
        minimum
    }

    pub fn profile_equation_rms(&self) -> (f64, f64, f64) {
        let mut angular_sum = 0.0;
        let mut axial_sum = 0.0;
        let mut pressure_sum = 0.0;
        let mut count = 0usize;
        let order = self.config.radial_order;
        for node in 2..self.config.eta_nodes - 2 {
            if self.eta[node].abs() > ETA_LIMIT {
                continue;
            }
            let eta = self.eta[node];
            let l = 1.0 - 2.0 * self.config.h * eta * eta;
            let g = self.phi_star[node] / self.swirl_normalization;
            for sample in 0..=32 {
                let y = Y_LIMIT * sample as f64 / 32.0;
                let phi = evaluate(&self.phi, node, order, y);
                let phi_y = evaluate_derivative(&self.phi, node, order, y);
                let phi_yy = evaluate_second_derivative(&self.phi, node, order, y);
                let axial_y = evaluate_derivative(&self.axial, node, order, y);
                let axial_yy = evaluate_second_derivative(&self.axial, node, order, y);
                let angular_remainder = evaluate(&self.angular_remainder, node, order, y);
                let axial_remainder = evaluate(&self.axial_remainder, node, order, y);
                let pressure_y = evaluate_derivative(&self.pressure_increment, node, order, y);
                let angular = 2.0 * (y * phi_yy + 2.0 * phi_y) + self.chi[node] * phi
                    - angular_remainder / self.config.radial_scale;
                let axial = 2.0 * (y * axial_yy + axial_y) + self.z_star[node] / l
                    - axial_remainder / self.config.radial_scale;
                let pressure = pressure_y - g * g * phi * phi;
                angular_sum += angular * angular;
                axial_sum += axial * axial;
                pressure_sum += pressure * pressure;
                count += 1;
            }
        }
        let divisor = count.max(1) as f64;
        (
            (angular_sum / divisor).sqrt(),
            (axial_sum / divisor).sqrt(),
            (pressure_sum / divisor).sqrt(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn vector_distance(left: [f64; 3], right: [f64; 3]) -> f64 {
        left.into_iter()
            .zip(right)
            .map(|(a, b)| (a - b).powi(2))
            .sum::<f64>()
            .sqrt()
    }

    #[test]
    fn eta_derivative_is_fourth_order_at_interior_and_boundary_nodes() {
        let nodes = 9;
        let order = 2;
        let spacing = 2.0 / (nodes - 1) as f64;
        let mut values = vec![0.0; nodes * (order + 1)];
        for node in 0..nodes {
            let eta = -1.0 + node as f64 * spacing;
            for degree in 0..=order {
                values[idx(order, node, degree)] =
                    (degree + 1) as f64 * (eta.powi(4) - 2.0 * eta.powi(2) + 0.5 * eta);
            }
        }
        let derivative = eta_derivative(&values, nodes, order, spacing);
        for node in 0..nodes {
            let eta = -1.0 + node as f64 * spacing;
            for degree in 0..=order {
                let expected = (degree + 1) as f64 * (4.0 * eta.powi(3) - 4.0 * eta + 0.5);
                assert!(
                    (derivative[idx(order, node, degree)] - expected).abs() < 2.0e-12,
                    "node={node} degree={degree}"
                );
            }
        }
    }

    #[test]
    fn serialized_metadata_declares_the_sampled_field_contract() {
        let construction = AxisConstruction::new(AxisConstructionConfig::default()).unwrap();
        let value = serde_json::to_value(construction.metadata()).unwrap();

        let coordinates = &value["coordinates"];
        assert_eq!(
            coordinates["physicalAxes"],
            serde_json::json!(["x", "y", "z"])
        );
        assert_eq!(coordinates["radialPlaneAxes"], serde_json::json!([0, 1]));
        assert_eq!(coordinates["axialAxis"], 2);
        assert_eq!(coordinates["tauDefinition"], "tau = 1 - t");
        assert_eq!(coordinates["singularTime"], 1.0);
        assert_eq!(coordinates["normalizedViscosity"], 1.0);

        let layout = &value["gridLayout"];
        assert_eq!(layout["topology"], "open");
        assert_eq!(layout["includesBothEndpoints"], true);
        assert_eq!(layout["pointAxisOrder"], serde_json::json!(["x", "y", "z"]));
        assert_eq!(
            layout["scalarPointIndex"],
            "(xIndex * N + yIndex) * N + zIndex"
        );
        assert_eq!(
            layout["vectorComponentOrder"],
            serde_json::json!(["x", "y", "z"])
        );

        let scalars = &value["scalarSemantics"];
        assert_eq!(scalars["residualSymbol"], "R");
        assert_eq!(scalars["residualIsSelectedSmoothForce"], false);
        assert_eq!(scalars["pressureAbsoluteLevelIsGaugeInvariant"], false);
        assert_eq!(scalars["maxSpeedIsContinuumSupremum"], false);

        assert!(value.get("grid_layout").is_none());
        assert!(coordinates.get("normalized_viscosity").is_none());
    }

    #[test]
    fn similarity_coordinates_satisfy_the_defining_equation() {
        let construction = AxisConstruction::new(AxisConstructionConfig::default()).unwrap();
        for &(tau, z) in &[
            (0.1, 0.0),
            (0.01, 0.03),
            (1.0e-4, -0.004),
            (1.0e-12, 1.0e-6),
            (1.0e4, 300.0),
        ] {
            let q = construction
                .similarity_q(tau, z)
                .unwrap_or_else(|error| panic!("tau={tau:e} z={z:e}: {error}"));
            let nonlinear = z * z * q.powf(2.0 * construction.config().h);
            let defect = q - nonlinear - tau;
            let scale = q.max(nonlinear).max(tau);
            let root_floor = z.abs().powf(1.0 / (0.5 - construction.config().h));
            assert!(defect.abs() <= 16.0 * f64::EPSILON * scale);
            assert!(
                q + 8.0 * f64::EPSILON * q >= tau.max(root_floor),
                "tau={tau:e} z={z:e} q={q:e} floor={root_floor:e}"
            );
            assert_eq!(q, construction.similarity_q(tau, -z).unwrap());
        }
    }

    #[test]
    fn invalid_or_unbounded_inputs_fail_before_evaluation() {
        let invalid_nodes = AxisConstruction::new(AxisConstructionConfig {
            eta_nodes: usize::MAX,
            ..AxisConstructionConfig::default()
        });
        assert!(invalid_nodes.is_err());
        let invalid_schedule = AxisConstruction::new(AxisConstructionConfig {
            schedule_m: 1000.0,
            ..AxisConstructionConfig::default()
        });
        assert!(invalid_schedule.is_err());
        let invalid_amplitude = AxisConstruction::new(AxisConstructionConfig {
            pressure_amplitude: f64::MAX,
            ..AxisConstructionConfig::default()
        });
        assert!(invalid_amplitude.is_err());

        let construction = AxisConstruction::new(AxisConstructionConfig::default()).unwrap();
        assert!(construction.similarity_q(0.1, f64::MAX).is_err());
        assert!(construction.similarity_q(1.0e-100, 1.0e-40).is_err());
        assert!(construction.sample(0.1, [f64::NAN, 0.0, 0.0]).is_err());
        assert!(construction.domain_half_extent(f64::MAX).is_err());
        assert!(construction.evaluate_grid(5, 1.0e-80).is_err());
    }

    #[test]
    fn physical_reconstruction_has_the_similarity_scaling() {
        let construction = AxisConstruction::new(AxisConstructionConfig::default()).unwrap();
        let tau_large = 0.08;
        let tau_small = 0.02;
        let extent_large = construction.domain_half_extent(tau_large).unwrap();
        let extent_small = construction.domain_half_extent(tau_small).unwrap();
        let ratio = 0.02_f64 / 0.08;
        let h = construction.config().h;
        let large_xyz = [0.17 * extent_large[0], 0.0, 0.13 * extent_large[2]];
        let small_xyz = [0.17 * extent_small[0], 0.0, 0.13 * extent_small[2]];
        let (large_velocity, large_pressure) = construction.sample(tau_large, large_xyz).unwrap();
        let (small_velocity, small_pressure) = construction.sample(tau_small, small_xyz).unwrap();
        // At fixed (X,eta), radial velocity scales as q^-1/2, while swirl and
        // axial velocity scale as q^-A and pressure as q^-2A (4.3)-(4.5).
        assert!((small_velocity[0] / large_velocity[0] - ratio.powf(-0.5)).abs() < 2.0e-12);
        for component in 1..3 {
            assert!(
                (small_velocity[component] / large_velocity[component] - ratio.powf(-0.5 - h))
                    .abs()
                    < 2.0e-12
            );
        }
        assert!((small_pressure / large_pressure - ratio.powf(-1.0 - 2.0 * h)).abs() < 2.0e-12);
        assert!((extent_small[0] / extent_large[0] - ratio.sqrt()).abs() < 2.0e-14);
        assert!((extent_small[2] / extent_large[2] - ratio.powf(0.5 - h)).abs() < 2.0e-14);
    }

    #[test]
    fn physical_residual_stabilizes_under_centered_step_refinement() {
        let construction = AxisConstruction::new(AxisConstructionConfig::default()).unwrap();
        let tau = 0.05;
        let extent = construction.domain_half_extent(tau).unwrap();
        let xyz = [0.17 * extent[0], -0.11 * extent[1], 0.13 * extent[2]];
        let estimates: Vec<_> = [8.0e-4, 4.0e-4, 2.0e-4, 1.0e-4]
            .into_iter()
            .map(|step| {
                construction
                    .point_residual_with_step(tau, xyz, extent, step)
                    .unwrap()
            })
            .collect();
        let residual_differences: Vec<_> = estimates
            .windows(2)
            .map(|pair| vector_distance(pair[0].0, pair[1].0))
            .collect();
        let divergence_differences: Vec<_> = estimates
            .windows(2)
            .map(|pair| (pair[0].1 - pair[1].1).abs())
            .collect();
        eprintln!(
            "residual refinement: residual={residual_differences:?} divergence={divergence_differences:?}"
        );
        for pair in residual_differences.windows(2) {
            assert!(pair[1] < 0.45 * pair[0]);
        }
        for pair in divergence_differences.windows(2) {
            assert!(pair[1] < 0.45 * pair[0]);
        }
    }

    #[test]
    fn finite_axis_iteration_is_positive_and_converged() {
        let construction = AxisConstruction::new(AxisConstructionConfig::default()).unwrap();
        assert!(construction.min_normalized_swirl() > 0.2);
        assert!(construction.fixed_point_delta.is_finite());
        assert!(
            construction.fixed_point_delta < 1.0e-8,
            "{}",
            construction.fixed_point_delta
        );
    }

    #[test]
    fn fixed_point_updates_contract_with_iteration_budget() {
        let deltas: Vec<_> = [1, 2, 4, 8]
            .into_iter()
            .map(|iterations| {
                AxisConstruction::new(AxisConstructionConfig {
                    iterations,
                    ..AxisConstructionConfig::default()
                })
                .unwrap()
                .fixed_point_delta
            })
            .collect();
        eprintln!("fixed-point update deltas: {deltas:?}");
        assert!(deltas.iter().all(|delta| delta.is_finite()));
        assert!(deltas.windows(2).all(|pair| pair[1] < pair[0]));
        assert!(deltas[3] < 1.0e-6 * deltas[0]);
    }

    #[test]
    fn reconstructed_field_is_finite_and_numerically_solenoidal() {
        let construction = AxisConstruction::new(AxisConstructionConfig::default()).unwrap();
        let (_, _, force, _, diagnostics) = construction.evaluate_grid(7, 0.05).unwrap();
        eprintln!("axis construction diagnostics: {diagnostics:?}");
        assert!(diagnostics.finite);
        assert!(diagnostics.divergence_rms < 2.0e-3 * diagnostics.max_speed / 0.05f64.sqrt());
        assert!(force.iter().any(|value| value.abs() > 0.0));
        assert!(diagnostics.momentum_residual_rms.is_finite());
    }

    #[test]
    fn radial_refinement_reduces_the_profile_equation_defect() {
        let defects: Vec<_> = [8, 12, 16]
            .into_iter()
            .map(|radial_order| {
                let model = AxisConstruction::new(AxisConstructionConfig {
                    radial_order,
                    ..AxisConstructionConfig::default()
                })
                .unwrap();
                let (angular, axial, pressure) = model.profile_equation_rms();
                (angular, axial, pressure)
            })
            .collect();
        eprintln!("radial refinement defects: {defects:?}");
        for pair in defects.windows(2) {
            assert!(pair[1].0 < pair[0].0);
            assert!(pair[1].1 < pair[0].1);
            assert!(pair[1].2 < pair[0].2);
        }
    }
}
