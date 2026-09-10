//! Dealiased Fourier pseudo-spectral Navier--Stokes solver.
//!
//! This is a direct Rust implementation of `navier_spectral_core.py`: the
//! periodic box is `[0, 2π)^3`, the nonlinear term is the rotational form
//! `P_L[(curl u) × u]`, componentwise Orszag 2/3 dealiasing is applied before
//! and after the physical-space product, and viscosity is integrated by the
//! same integrating-factor RK4 formula.

use crate::convention::SpectralConventionMetadata;
use num_complex::Complex64;
use rustfft::{Fft, FftPlanner};
use serde::Serialize;
use std::{cell::Cell, f64::consts::TAU, sync::Arc};

const COMPONENTS: usize = 3;
pub(crate) const MAX_BROWSER_GRID: usize = 64;
const MAX_NATIVE_GRID: usize = 128;

fn validate_grid(n: usize, maximum: usize) -> Result<(), String> {
    if n < 4 || !n.is_multiple_of(2) || n > maximum {
        return Err(format!(
            "grid must be an even integer from 4 through {maximum} on this target"
        ));
    }
    Ok(())
}

pub(crate) const ENERGY_BUDGET_QUADRATURE: &str = "trapezoidal-diagnostics-observations";

#[derive(Clone, Copy, Debug)]
pub(crate) struct EnergyBudgetSnapshot {
    pub initial_energy: f64,
    pub cumulative_energy_dissipation: f64,
    pub energy_balance_defect: f64,
    pub energy_balance_relative_error: f64,
    pub mean_energy_dissipation_rate: f64,
    pub minimum_sampled_energy_dissipation_rate: f64,
    pub minimum_sampled_dissipation_time: f64,
    pub start_time: f64,
    pub end_time: f64,
    pub max_interval: f64,
    pub samples: u32,
    pub applicable: bool,
}

impl EnergyBudgetSnapshot {
    pub(crate) fn finite(self) -> bool {
        !self.applicable
            || [
                self.initial_energy,
                self.cumulative_energy_dissipation,
                self.energy_balance_defect,
                self.energy_balance_relative_error,
                self.mean_energy_dissipation_rate,
                self.minimum_sampled_energy_dissipation_rate,
                self.minimum_sampled_dissipation_time,
                self.start_time,
                self.end_time,
                self.max_interval,
            ]
            .into_iter()
            .all(f64::is_finite)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct EnergyBudgetTracker {
    initial_energy: Cell<f64>,
    cumulative_energy_dissipation: Cell<f64>,
    last_time: Cell<f64>,
    last_rate: Cell<f64>,
    minimum_rate: Cell<f64>,
    minimum_rate_time: Cell<f64>,
    start_time: Cell<f64>,
    max_interval: Cell<f64>,
    samples: Cell<u32>,
    applicable: Cell<bool>,
}

impl EnergyBudgetTracker {
    pub(crate) fn new(initial_energy: f64, initial_rate: f64) -> Self {
        Self {
            initial_energy: Cell::new(initial_energy),
            cumulative_energy_dissipation: Cell::new(0.0),
            last_time: Cell::new(0.0),
            last_rate: Cell::new(initial_rate),
            minimum_rate: Cell::new(initial_rate),
            minimum_rate_time: Cell::new(0.0),
            start_time: Cell::new(0.0),
            max_interval: Cell::new(0.0),
            samples: Cell::new(1),
            applicable: Cell::new(true),
        }
    }

    pub(crate) fn reset(&self, time: f64, initial_energy: f64, initial_rate: f64) {
        self.initial_energy.set(initial_energy);
        self.cumulative_energy_dissipation.set(0.0);
        self.last_time.set(time);
        self.last_rate.set(initial_rate);
        self.minimum_rate.set(initial_rate);
        self.minimum_rate_time.set(time);
        self.start_time.set(time);
        self.max_interval.set(0.0);
        self.samples.set(1);
        self.applicable.set(true);
    }

    pub(crate) fn invalidate(&self) {
        self.applicable.set(false);
    }

    pub(crate) fn observe(
        &self,
        time: f64,
        energy: f64,
        energy_dissipation_rate: f64,
    ) -> EnergyBudgetSnapshot {
        let last_time = self.last_time.get();
        if self.applicable.get()
            && self.samples.get() == 1
            && time == self.start_time.get()
            && last_time == time
        {
            self.initial_energy.set(energy);
            self.last_rate.set(energy_dissipation_rate);
            self.minimum_rate.set(energy_dissipation_rate);
            self.minimum_rate_time.set(time);
        }
        if self.applicable.get() && time > last_time {
            let width = time - last_time;
            let increment = 0.5 * width * (self.last_rate.get() + energy_dissipation_rate);
            self.max_interval.set(self.max_interval.get().max(width));
            self.cumulative_energy_dissipation
                .set(self.cumulative_energy_dissipation.get() + increment);
            self.last_time.set(time);
            self.last_rate.set(energy_dissipation_rate);
            self.samples.set(self.samples.get().saturating_add(1));
        }
        if self.applicable.get() && energy_dissipation_rate < self.minimum_rate.get() {
            self.minimum_rate.set(energy_dissipation_rate);
            self.minimum_rate_time.set(time);
        }

        let applicable = self.applicable.get();
        let initial_energy = self.initial_energy.get();
        let cumulative = self.cumulative_energy_dissipation.get();
        let end_time = self.last_time.get();
        let width = end_time - self.start_time.get();
        let defect = if applicable {
            energy + cumulative - initial_energy
        } else {
            f64::NAN
        };
        let relative_error = if !applicable {
            f64::NAN
        } else if initial_energy != 0.0 {
            defect / initial_energy
        } else if defect == 0.0 {
            0.0
        } else {
            f64::NAN
        };
        let mean_rate = if !applicable {
            f64::NAN
        } else if width > 0.0 {
            cumulative / width
        } else {
            energy_dissipation_rate
        };
        EnergyBudgetSnapshot {
            initial_energy,
            cumulative_energy_dissipation: if applicable { cumulative } else { f64::NAN },
            energy_balance_defect: defect,
            energy_balance_relative_error: relative_error,
            mean_energy_dissipation_rate: mean_rate,
            minimum_sampled_energy_dissipation_rate: if applicable {
                self.minimum_rate.get()
            } else {
                f64::NAN
            },
            minimum_sampled_dissipation_time: if applicable {
                self.minimum_rate_time.get()
            } else {
                f64::NAN
            },
            start_time: self.start_time.get(),
            end_time,
            max_interval: self.max_interval.get(),
            samples: self.samples.get(),
            applicable,
        }
    }
}

#[derive(Clone, Copy, Debug, Serialize)]
pub struct Diagnostics {
    pub time: f64,
    pub energy: f64,
    pub enstrophy: f64,
    pub velocity_rms: f64,
    pub vorticity_rms: f64,
    pub divergence_rms: f64,
    pub max_speed: f64,
    pub max_vorticity: f64,
    pub energy_dissipation_rate: f64,
    #[serde(rename = "initialEnergy")]
    pub initial_energy: f64,
    #[serde(rename = "cumulativeEnergyDissipation")]
    pub cumulative_energy_dissipation: f64,
    #[serde(rename = "energyBalanceDefect")]
    pub energy_balance_defect: f64,
    #[serde(rename = "energyBalanceRelativeError")]
    pub energy_balance_relative_error: f64,
    #[serde(rename = "meanEnergyDissipationRate")]
    pub mean_energy_dissipation_rate: f64,
    #[serde(rename = "minimumSampledEnergyDissipationRate")]
    pub minimum_sampled_energy_dissipation_rate: f64,
    #[serde(rename = "minimumSampledDissipationTime")]
    pub minimum_sampled_dissipation_time: f64,
    #[serde(rename = "energyBudgetStartTime")]
    pub energy_budget_start_time: f64,
    #[serde(rename = "energyBudgetEndTime")]
    pub energy_budget_end_time: f64,
    #[serde(rename = "energyBudgetMaxInterval")]
    pub energy_budget_max_interval: f64,
    #[serde(rename = "energyBudgetSamples")]
    pub energy_budget_samples: u32,
    #[serde(rename = "energyBudgetQuadrature")]
    pub energy_budget_quadrature: &'static str,
    #[serde(rename = "energyBalanceApplicable")]
    pub energy_balance_applicable: bool,
    pub high_frequency_energy_fraction: f64,
    pub tail_start_fraction_of_dealias_cutoff: f64,
    pub tail_tolerance: f64,
    pub underresolved: bool,
    pub finite: bool,
}

#[derive(Clone, Copy, Debug, Serialize)]
pub struct AdvanceReport {
    pub elapsed: f64,
    pub substeps: usize,
    pub rejected_steps: usize,
    pub min_dt: f64,
    pub max_dt: f64,
    pub max_cfl: f64,
    pub max_tail_energy_fraction: f64,
    pub underresolved: bool,
}

#[derive(Clone)]
pub struct SpectralSolver {
    n: usize,
    len: usize,
    viscosity: f64,
    time: f64,
    steps: u64,
    max_tail_energy_fraction: f64,
    underresolved: bool,
    energy_budget: EnergyBudgetTracker,
    state: Vec<Complex64>,
    wave: Vec<[f64; 3]>,
    k2: Vec<f64>,
    dealias: Vec<bool>,
    fft_forward: Arc<dyn Fft<f64>>,
    fft_inverse: Arc<dyn Fft<f64>>,
}

impl SpectralSolver {
    pub fn new(n: usize, viscosity: f64) -> Result<Self, String> {
        let maximum = if cfg!(target_arch = "wasm32") {
            MAX_BROWSER_GRID
        } else {
            MAX_NATIVE_GRID
        };
        validate_grid(n, maximum)?;
        if !viscosity.is_finite() || viscosity < 0.0 {
            return Err("viscosity must be finite and nonnegative".into());
        }
        let len = n.checked_pow(3).ok_or("grid allocation overflow")?;
        let mut planner = FftPlanner::<f64>::new();
        let fft_forward = planner.plan_fft_forward(n);
        let fft_inverse = planner.plan_fft_inverse(n);
        let cutoff = n as f64 / 3.0;
        let frequencies: Vec<f64> = (0..n)
            .map(|i| {
                if i < n / 2 {
                    i as f64
                } else {
                    i as f64 - n as f64
                }
            })
            .collect();
        let mut wave = Vec::with_capacity(len);
        let mut k2 = Vec::with_capacity(len);
        let mut dealias = Vec::with_capacity(len);
        for i in 0..n {
            for j in 0..n {
                for k in 0..n {
                    let w = [frequencies[i], frequencies[j], frequencies[k]];
                    wave.push(w);
                    k2.push(w[0] * w[0] + w[1] * w[1] + w[2] * w[2]);
                    dealias.push(w.into_iter().all(|value| value.abs() < cutoff));
                }
            }
        }
        let mut result = Self {
            n,
            len,
            viscosity,
            time: 0.0,
            steps: 0,
            max_tail_energy_fraction: 0.0,
            underresolved: false,
            energy_budget: EnergyBudgetTracker::new(0.0, 0.0),
            state: vec![Complex64::default(); COMPONENTS * len],
            wave,
            k2,
            dealias,
            fft_forward,
            fft_inverse,
        };
        result.reset_taylor_green();
        Ok(result)
    }

    pub fn n(&self) -> usize {
        self.n
    }
    pub fn viscosity(&self) -> f64 {
        self.viscosity
    }
    pub fn metadata(&self) -> SpectralConventionMetadata {
        SpectralConventionMetadata::new(self.n, self.viscosity)
    }
    pub fn time(&self) -> f64 {
        self.time
    }
    pub fn steps(&self) -> u64 {
        self.steps
    }
    pub fn state_hat(&self) -> &[Complex64] {
        &self.state
    }

    pub fn reset_taylor_green(&mut self) {
        let mut physical = vec![Complex64::default(); COMPONENTS * self.len];
        for i in 0..self.n {
            let x = TAU * i as f64 / self.n as f64;
            for j in 0..self.n {
                let y = TAU * j as f64 / self.n as f64;
                for k in 0..self.n {
                    let z = TAU * k as f64 / self.n as f64;
                    let q = self.index(i, j, k);
                    physical[q] = Complex64::new(x.sin() * y.cos() * z.cos(), 0.0);
                    physical[self.len + q] = Complex64::new(-x.cos() * y.sin() * z.cos(), 0.0);
                }
            }
        }
        self.transform_components(&mut physical, false);
        self.project(&mut physical);
        self.state = physical;
        self.time = 0.0;
        self.steps = 0;
        self.reset_resolution_warning();
        self.energy_budget.reset(0.0, 0.125, 0.75 * self.viscosity);
    }

    pub fn reset_zero(&mut self) {
        self.state.fill(Complex64::default());
        self.time = 0.0;
        self.steps = 0;
        self.reset_resolution_warning();
        self.energy_budget.reset(0.0, 0.0, 0.0);
    }

    /// Divergence-free shear `u=(sin(mode*y),0,0)`, an exact viscous mode.
    pub fn reset_shear(&mut self, mode: usize) -> Result<(), String> {
        if mode == 0 || mode as f64 >= self.n as f64 / 3.0 {
            return Err("shear mode must satisfy 0 < mode < n/3".into());
        }
        let mut physical = vec![Complex64::default(); COMPONENTS * self.len];
        for i in 0..self.n {
            for j in 0..self.n {
                let y = TAU * j as f64 / self.n as f64;
                for k in 0..self.n {
                    physical[self.index(i, j, k)] = Complex64::new((mode as f64 * y).sin(), 0.0);
                }
            }
        }
        self.transform_components(&mut physical, false);
        self.project(&mut physical);
        self.state = physical;
        self.time = 0.0;
        self.steps = 0;
        self.reset_resolution_warning();
        self.energy_budget
            .reset(0.0, 0.25, 0.5 * self.viscosity * (mode as f64).powi(2));
        Ok(())
    }

    pub fn set_state_hat(&mut self, mut state: Vec<Complex64>) -> Result<(), String> {
        if state.len() != COMPONENTS * self.len {
            return Err(format!(
                "spectral state must have {} complex values",
                COMPONENTS * self.len
            ));
        }
        if state.iter().any(|z| !z.re.is_finite() || !z.im.is_finite()) {
            return Err("spectral state must be finite".into());
        }
        self.project(&mut state);
        if state.iter().any(|z| !z.re.is_finite() || !z.im.is_finite()) {
            return Err("Leray projection produced a non-finite spectral state".into());
        }
        self.state = state;
        self.time = 0.0;
        self.steps = 0;
        self.reset_resolution_warning();
        let (energy, enstrophy) = self.spectral_energy_enstrophy();
        self.energy_budget
            .reset(0.0, energy, 2.0 * self.viscosity * enstrophy);
        Ok(())
    }

    pub fn step(&mut self, dt: f64) -> Result<(), String> {
        self.step_internal(dt, None)
    }

    pub fn step_with_forcing<F>(&mut self, dt: f64, forcing: F) -> Result<(), String>
    where
        F: Fn(f64) -> Vec<Complex64>,
    {
        self.step_internal(dt, Some(&forcing))
    }

    fn step_internal(
        &mut self,
        dt: f64,
        forcing: Option<&dyn Fn(f64) -> Vec<Complex64>>,
    ) -> Result<(), String> {
        if !dt.is_finite() || dt <= 0.0 {
            return Err("dt must be finite and positive".into());
        }
        let next_time = self.time + dt;
        if !next_time.is_finite() || next_time == self.time {
            return Err("dt cannot be represented at the current time".into());
        }
        let e_full: Vec<f64> = self
            .k2
            .iter()
            .map(|&v| (-self.viscosity * v * dt).exp())
            .collect();
        let e_half: Vec<f64> = self
            .k2
            .iter()
            .map(|&v| (-0.5 * self.viscosity * v * dt).exp())
            .collect();
        let initial = self.state.clone();
        let a = self.scaled_rhs(&initial, dt, forcing, self.time)?;
        let stage_b = self.stage_half(&initial, &a, &e_half);
        let b = self.scaled_rhs(&stage_b, dt, forcing, self.time + 0.5 * dt)?;
        let stage_c = self.stage_half_increment_outside(&initial, &b, &e_half);
        let c = self.scaled_rhs(&stage_c, dt, forcing, self.time + 0.5 * dt)?;
        let stage_d = self.stage_full(&initial, &c, &e_full, &e_half);
        let d = self.scaled_rhs(&stage_d, dt, forcing, self.time + dt)?;
        let mut next = vec![Complex64::default(); COMPONENTS * self.len];
        for component in 0..COMPONENTS {
            let offset = component * self.len;
            for q in 0..self.len {
                let idx = offset + q;
                next[idx] = e_full[q] * initial[idx]
                    + (e_full[q] * a[idx] + 2.0 * e_half[q] * (b[idx] + c[idx]) + d[idx]) / 6.0;
            }
        }
        self.project(&mut next);
        if next.iter().any(|z| !z.re.is_finite() || !z.im.is_finite()) {
            return Err("non-finite spectral state produced".into());
        }
        self.state = next;
        self.time = next_time;
        self.steps += 1;
        self.update_resolution_warning();
        if forcing.is_some() {
            self.energy_budget.invalidate();
        }
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

    pub fn stable_dt(&self, cfl: f64) -> Result<f64, String> {
        if !cfl.is_finite() || cfl <= 0.0 {
            return Err("CFL limit must be finite and positive".into());
        }
        let speed = self.max_speed()?;
        Ok(if speed == 0.0 {
            f64::INFINITY
        } else {
            cfl * (TAU / self.n as f64) / speed
        })
    }

    /// Advance an exact duration with bounded fixed IFRK4 substeps and an
    /// independent advective CFL guard. This is not an error-adaptive solve.
    pub fn advance_bounded(
        &mut self,
        duration: f64,
        max_dt: f64,
        cfl: f64,
        max_substeps: usize,
    ) -> Result<AdvanceReport, String> {
        if !duration.is_finite() || duration < 0.0 {
            return Err("duration must be finite and nonnegative".into());
        }
        if !max_dt.is_finite() || max_dt <= 0.0 {
            return Err("max_dt must be finite and positive".into());
        }
        if !cfl.is_finite() || cfl <= 0.0 {
            return Err("CFL limit must be finite and positive".into());
        }
        if max_substeps == 0 || max_substeps > 10_000 {
            return Err("max_substeps must be in 1..=10000".into());
        }
        if duration == 0.0 {
            return Ok(AdvanceReport {
                elapsed: 0.0,
                substeps: 0,
                rejected_steps: 0,
                min_dt: 0.0,
                max_dt: 0.0,
                max_cfl: 0.0,
                max_tail_energy_fraction: self.max_tail_energy_fraction,
                underresolved: self.underresolved,
            });
        }
        let start_time = self.time;
        let target = start_time + duration;
        if !target.is_finite() || target == start_time {
            return Err("duration cannot be represented at the current time".into());
        }
        let dx = TAU / self.n as f64;
        let mut accepted = 0usize;
        let mut rejected = 0usize;
        let mut min_used = f64::INFINITY;
        let mut max_used: f64 = 0.0;
        let mut max_cfl: f64 = 0.0;
        let mut proposed = max_dt;
        let mut start_speed = self.max_speed()?;
        while self.time < target {
            if accepted + rejected >= max_substeps {
                return Err(format!(
                    "bounded advance exceeded max_substeps={max_substeps}"
                ));
            }
            let remaining = target - self.time;
            let start_bound = if start_speed == 0.0 {
                f64::INFINITY
            } else {
                cfl * dx / start_speed
            };
            let dt = proposed.min(max_dt).min(start_bound).min(remaining);
            if dt <= 0.0 || self.time + dt == self.time {
                return Err("bounded timestep underflow".into());
            }
            let snapshot = (
                self.state.clone(),
                self.time,
                self.steps,
                self.max_tail_energy_fraction,
                self.underresolved,
            );
            self.step(dt)?;
            let end_speed = self.max_speed()?;
            let trial_cfl = start_speed.max(end_speed) * dt / dx;
            if trial_cfl > cfl * (1.0 + 32.0 * f64::EPSILON) {
                self.state = snapshot.0;
                self.time = snapshot.1;
                self.steps = snapshot.2;
                self.max_tail_energy_fraction = snapshot.3;
                self.underresolved = snapshot.4;
                proposed = 0.9 * cfl * dx / start_speed.max(end_speed);
                rejected += 1;
                continue;
            }
            accepted += 1;
            min_used = min_used.min(dt);
            max_used = max_used.max(dt);
            max_cfl = max_cfl.max(trial_cfl);
            proposed = max_dt;
            start_speed = end_speed;
        }
        Ok(AdvanceReport {
            elapsed: self.time - start_time,
            substeps: accepted,
            rejected_steps: rejected,
            min_dt: min_used,
            max_dt: max_used,
            max_cfl,
            max_tail_energy_fraction: self.max_tail_energy_fraction,
            underresolved: self.underresolved,
        })
    }

    pub fn velocity_f64(&self) -> Vec<f64> {
        let mut physical = self.state.clone();
        self.transform_components(&mut physical, true);
        physical.into_iter().map(|z| z.re).collect()
    }

    /// Peak physical-space velocity magnitude. This is the narrow reduction
    /// needed by the CFL guard and avoids computing vorticity, divergence, and
    /// spectral-tail diagnostics at every trial substep.
    pub fn max_speed(&self) -> Result<f64, String> {
        let mut velocity = self.state.clone();
        self.transform_components(&mut velocity, true);
        let mut maximum_squared: f64 = 0.0;
        let mut speed_squared_sum: f64 = 0.0;
        for q in 0..self.len {
            let speed_squared = velocity[q].re.powi(2)
                + velocity[self.len + q].re.powi(2)
                + velocity[2 * self.len + q].re.powi(2);
            if !speed_squared.is_finite() {
                return Err("cannot compute a stable timestep from non-finite velocity".into());
            }
            speed_squared_sum += speed_squared;
            if !speed_squared_sum.is_finite() {
                return Err("cannot compute a stable timestep from non-finite velocity".into());
            }
            maximum_squared = maximum_squared.max(speed_squared);
        }
        Ok(maximum_squared.sqrt())
    }

    /// Interleaved xyz values for rendering, one triplet per grid point.
    pub fn velocity_f32_interleaved(&self) -> Vec<f32> {
        let components = self.velocity_f64();
        let mut result = Vec::with_capacity(COMPONENTS * self.len);
        for q in 0..self.len {
            result.extend_from_slice(&[
                components[q] as f32,
                components[self.len + q] as f32,
                components[2 * self.len + q] as f32,
            ]);
        }
        result
    }

    pub fn diagnostics(&self) -> Diagnostics {
        let velocity = self.velocity_f64();
        let mut vorticity_hat = vec![Complex64::default(); COMPONENTS * self.len];
        self.curl_into(&self.state, &mut vorticity_hat);
        self.transform_components(&mut vorticity_hat, true);
        let mut energy_sum = 0.0;
        let mut enstrophy_sum = 0.0;
        let mut max_speed2: f64 = 0.0;
        let mut max_vorticity2: f64 = 0.0;
        let mut finite = true;
        for q in 0..self.len {
            let speed2 = (0..COMPONENTS)
                .map(|c| velocity[c * self.len + q].powi(2))
                .sum::<f64>();
            let vorticity2 = (0..COMPONENTS)
                .map(|c| vorticity_hat[c * self.len + q].re.powi(2))
                .sum::<f64>();
            energy_sum += 0.5 * speed2;
            enstrophy_sum += 0.5 * vorticity2;
            max_speed2 = max_speed2.max(speed2);
            max_vorticity2 = max_vorticity2.max(vorticity2);
            finite &= speed2.is_finite() && vorticity2.is_finite();
        }
        let mut div_hat = vec![Complex64::default(); self.len];
        for (q, out) in div_hat.iter_mut().enumerate() {
            let dot = self.wave[q][0] * self.state[q]
                + self.wave[q][1] * self.state[self.len + q]
                + self.wave[q][2] * self.state[2 * self.len + q];
            *out = Complex64::new(-dot.im, dot.re);
        }
        self.transform_scalar(&mut div_hat, true);
        let divergence_rms =
            (div_hat.iter().map(|z| z.re * z.re).sum::<f64>() / self.len as f64).sqrt();
        let energy = energy_sum / self.len as f64;
        let enstrophy = enstrophy_sum / self.len as f64;
        let velocity_rms = (2.0 * energy).max(0.0).sqrt();
        let vorticity_rms = (2.0 * enstrophy).max(0.0).sqrt();
        let max_speed = max_speed2.sqrt();
        let max_vorticity = max_vorticity2.sqrt();
        let energy_dissipation_rate = 2.0 * self.viscosity * enstrophy;
        let energy_budget = self
            .energy_budget
            .observe(self.time, energy, energy_dissipation_rate);
        let high_frequency_energy_fraction = self.high_frequency_energy_fraction(0.75);
        finite &= [
            self.time,
            energy,
            enstrophy,
            velocity_rms,
            vorticity_rms,
            divergence_rms,
            max_speed,
            max_vorticity,
            energy_dissipation_rate,
            energy_budget.initial_energy,
            energy_budget.cumulative_energy_dissipation,
            energy_budget.energy_balance_defect,
            energy_budget.energy_balance_relative_error,
            energy_budget.mean_energy_dissipation_rate,
            energy_budget.minimum_sampled_energy_dissipation_rate,
            energy_budget.minimum_sampled_dissipation_time,
            energy_budget.start_time,
            energy_budget.end_time,
            energy_budget.max_interval,
            high_frequency_energy_fraction,
        ]
        .into_iter()
        .all(f64::is_finite);
        Diagnostics {
            time: self.time,
            energy,
            enstrophy,
            velocity_rms,
            vorticity_rms,
            divergence_rms,
            max_speed,
            max_vorticity,
            energy_dissipation_rate,
            initial_energy: energy_budget.initial_energy,
            cumulative_energy_dissipation: energy_budget.cumulative_energy_dissipation,
            energy_balance_defect: energy_budget.energy_balance_defect,
            energy_balance_relative_error: energy_budget.energy_balance_relative_error,
            mean_energy_dissipation_rate: energy_budget.mean_energy_dissipation_rate,
            minimum_sampled_energy_dissipation_rate: energy_budget
                .minimum_sampled_energy_dissipation_rate,
            minimum_sampled_dissipation_time: energy_budget.minimum_sampled_dissipation_time,
            energy_budget_start_time: energy_budget.start_time,
            energy_budget_end_time: energy_budget.end_time,
            energy_budget_max_interval: energy_budget.max_interval,
            energy_budget_samples: energy_budget.samples,
            energy_budget_quadrature: ENERGY_BUDGET_QUADRATURE,
            energy_balance_applicable: energy_budget.applicable,
            high_frequency_energy_fraction,
            tail_start_fraction_of_dealias_cutoff: 0.75,
            tail_tolerance: 1.0e-8,
            underresolved: self.underresolved,
            finite: finite && energy_budget.finite(),
        }
    }

    fn spectral_energy_enstrophy(&self) -> (f64, f64) {
        let mut energy_sum = 0.0;
        let mut enstrophy_sum = 0.0;
        for q in 0..self.len {
            let density = (0..COMPONENTS)
                .map(|component| self.state[component * self.len + q].norm_sqr())
                .sum::<f64>();
            energy_sum += density;
            enstrophy_sum += self.k2[q] * density;
        }
        let normalization = (self.len as f64).powi(2);
        (
            0.5 * energy_sum / normalization,
            0.5 * enstrophy_sum / normalization,
        )
    }

    pub fn high_frequency_energy_fraction(&self, tail_start: f64) -> f64 {
        if !(tail_start.is_finite() && 0.0 < tail_start && tail_start <= 1.0) {
            return f64::NAN;
        }
        let edge = tail_start * self.n as f64 / 3.0;
        let mut total = 0.0;
        let mut tail = 0.0;
        for q in 0..self.len {
            let density = (0..COMPONENTS)
                .map(|component| self.state[component * self.len + q].norm_sqr())
                .sum::<f64>();
            total += density;
            if self.wave[q].into_iter().any(|value| value.abs() >= edge) {
                tail += density;
            }
        }
        if total == 0.0 { 0.0 } else { tail / total }
    }

    fn reset_resolution_warning(&mut self) {
        let tail = self.high_frequency_energy_fraction(0.75);
        self.max_tail_energy_fraction = tail;
        self.underresolved = tail > 1.0e-8;
    }

    fn update_resolution_warning(&mut self) {
        let tail = self.high_frequency_energy_fraction(0.75);
        self.max_tail_energy_fraction = self.max_tail_energy_fraction.max(tail);
        self.underresolved |= tail > 1.0e-8;
    }

    pub fn project_state(&mut self) {
        let mut state = std::mem::take(&mut self.state);
        self.project(&mut state);
        self.state = state;
        let (energy, enstrophy) = self.spectral_energy_enstrophy();
        self.energy_budget
            .reset(self.time, energy, 2.0 * self.viscosity * enstrophy);
    }

    fn nonlinear_hat(&self, state: &[Complex64]) -> Vec<Complex64> {
        let mut velocity_hat = state.to_vec();
        for component in 0..COMPONENTS {
            for q in 0..self.len {
                if !self.dealias[q] {
                    velocity_hat[component * self.len + q] = Complex64::default();
                }
            }
        }
        let mut curl_hat = vec![Complex64::default(); COMPONENTS * self.len];
        self.curl_into(&velocity_hat, &mut curl_hat);
        self.transform_components(&mut velocity_hat, true);
        self.transform_components(&mut curl_hat, true);
        let mut cross = vec![Complex64::default(); COMPONENTS * self.len];
        for q in 0..self.len {
            let ux = velocity_hat[q].re;
            let uy = velocity_hat[self.len + q].re;
            let uz = velocity_hat[2 * self.len + q].re;
            let wx = curl_hat[q].re;
            let wy = curl_hat[self.len + q].re;
            let wz = curl_hat[2 * self.len + q].re;
            cross[q] = Complex64::new(wy * uz - wz * uy, 0.0);
            cross[self.len + q] = Complex64::new(wz * ux - wx * uz, 0.0);
            cross[2 * self.len + q] = Complex64::new(wx * uy - wy * ux, 0.0);
        }
        self.transform_components(&mut cross, false);
        for component in 0..COMPONENTS {
            for q in 0..self.len {
                if !self.dealias[q] {
                    cross[component * self.len + q] = Complex64::default();
                }
            }
        }
        self.project(&mut cross);
        cross
    }

    fn curl_into(&self, state: &[Complex64], out: &mut [Complex64]) {
        let imaginary = Complex64::new(0.0, 1.0);
        for q in 0..self.len {
            let [kx, ky, kz] = self.wave[q];
            let ux = state[q];
            let uy = state[self.len + q];
            let uz = state[2 * self.len + q];
            out[q] = imaginary * (ky * uz - kz * uy);
            out[self.len + q] = imaginary * (kz * ux - kx * uz);
            out[2 * self.len + q] = imaginary * (kx * uy - ky * ux);
        }
    }

    fn scaled_rhs(
        &self,
        state: &[Complex64],
        dt: f64,
        forcing: Option<&dyn Fn(f64) -> Vec<Complex64>>,
        time: f64,
    ) -> Result<Vec<Complex64>, String> {
        let mut result: Vec<_> = self
            .nonlinear_hat(state)
            .into_iter()
            .map(|z| -dt * z)
            .collect();
        if let Some(sample) = forcing {
            let mut force = sample(time);
            if force.len() != result.len() {
                return Err(format!("forcing must have {} complex values", result.len()));
            }
            if force.iter().any(|z| !z.re.is_finite() || !z.im.is_finite()) {
                return Err("forcing must be finite".into());
            }
            self.project(&mut force);
            for (value, force_value) in result.iter_mut().zip(force) {
                *value += dt * force_value;
            }
        }
        Ok(result)
    }

    fn stage_half(
        &self,
        state: &[Complex64],
        increment: &[Complex64],
        e_half: &[f64],
    ) -> Vec<Complex64> {
        let mut out = vec![Complex64::default(); state.len()];
        for c in 0..COMPONENTS {
            for (q, factor) in e_half.iter().enumerate() {
                let idx = c * self.len + q;
                out[idx] = *factor * (state[idx] + 0.5 * increment[idx]);
            }
        }
        out
    }

    fn stage_half_increment_outside(
        &self,
        state: &[Complex64],
        increment: &[Complex64],
        e_half: &[f64],
    ) -> Vec<Complex64> {
        let mut out = vec![Complex64::default(); state.len()];
        for c in 0..COMPONENTS {
            for (q, factor) in e_half.iter().enumerate() {
                let idx = c * self.len + q;
                out[idx] = *factor * state[idx] + 0.5 * increment[idx];
            }
        }
        out
    }

    fn stage_full(
        &self,
        state: &[Complex64],
        increment: &[Complex64],
        e_full: &[f64],
        e_half: &[f64],
    ) -> Vec<Complex64> {
        let mut out = vec![Complex64::default(); state.len()];
        for c in 0..COMPONENTS {
            for q in 0..self.len {
                let idx = c * self.len + q;
                out[idx] = e_full[q] * state[idx] + e_half[q] * increment[idx];
            }
        }
        out
    }

    fn project(&self, vector: &mut [Complex64]) {
        for q in 0..self.len {
            let [kx, ky, kz] = self.wave[q];
            let norm2 = self.k2[q];
            if norm2 == 0.0 {
                continue;
            }
            let dot = kx * vector[q] + ky * vector[self.len + q] + kz * vector[2 * self.len + q];
            let scale = dot / norm2;
            vector[q] -= kx * scale;
            vector[self.len + q] -= ky * scale;
            vector[2 * self.len + q] -= kz * scale;
        }
    }

    fn transform_components(&self, data: &mut [Complex64], inverse: bool) {
        for component in 0..COMPONENTS {
            self.transform_scalar(
                &mut data[component * self.len..(component + 1) * self.len],
                inverse,
            );
        }
    }

    fn transform_scalar(&self, data: &mut [Complex64], inverse: bool) {
        let fft = if inverse {
            &self.fft_inverse
        } else {
            &self.fft_forward
        };
        let mut line = vec![Complex64::default(); self.n];
        for i in 0..self.n {
            for j in 0..self.n {
                for k in 0..self.n {
                    line[k] = data[self.index(i, j, k)];
                }
                fft.process(&mut line);
                for k in 0..self.n {
                    data[self.index(i, j, k)] = line[k];
                }
            }
        }
        for i in 0..self.n {
            for k in 0..self.n {
                for j in 0..self.n {
                    line[j] = data[self.index(i, j, k)];
                }
                fft.process(&mut line);
                for j in 0..self.n {
                    data[self.index(i, j, k)] = line[j];
                }
            }
        }
        for j in 0..self.n {
            for k in 0..self.n {
                for i in 0..self.n {
                    line[i] = data[self.index(i, j, k)];
                }
                fft.process(&mut line);
                for i in 0..self.n {
                    data[self.index(i, j, k)] = line[i];
                }
            }
        }
        if inverse {
            let scale = 1.0 / self.len as f64;
            for value in data {
                *value *= scale;
            }
        }
    }

    #[inline]
    fn index(&self, i: usize, j: usize, k: usize) -> usize {
        (i * self.n + j) * self.n + k
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn amplitude(t: f64) -> f64 {
        (-0.3 * t).exp() * (1.7 * t).cos()
    }

    fn amplitude_dot(t: f64) -> f64 {
        (-0.3 * t).exp() * (-0.3 * (1.7 * t).cos() - 1.7 * (1.7 * t).sin())
    }

    #[test]
    fn browser_grid_capacity_accepts_64_and_rejects_larger_or_odd_grids() {
        assert!(validate_grid(64, MAX_BROWSER_GRID).is_ok());
        assert!(validate_grid(66, MAX_BROWSER_GRID).is_err());
        assert!(validate_grid(63, MAX_BROWSER_GRID).is_err());
    }

    #[test]
    fn narrow_max_speed_matches_full_diagnostics() {
        let solver = SpectralSolver::new(12, 0.05).unwrap();
        let narrow = solver.max_speed().unwrap();
        let full = solver.diagnostics().max_speed;
        assert!((narrow - full).abs() <= 8.0 * f64::EPSILON);
    }

    /// Manual timing probe for the reduction used by every bounded CFL step.
    /// Kept ignored so ordinary correctness tests remain timing-independent.
    #[test]
    #[ignore]
    fn cpu_cfl_reduction_benchmark() {
        use std::time::Instant;

        let solver = SpectralSolver::new(24, 0.05).unwrap();
        solver.max_speed().unwrap();
        solver.diagnostics();

        let narrow_start = Instant::now();
        for _ in 0..8 {
            solver.max_speed().unwrap();
        }
        let narrow = narrow_start.elapsed() / 8;

        let full_start = Instant::now();
        for _ in 0..8 {
            solver.diagnostics();
        }
        let full = full_start.elapsed() / 8;

        eprintln!("N=24 CFL max_speed={narrow:?} full diagnostics={full:?}");
        assert!(
            narrow < full,
            "narrow CFL reduction did not beat diagnostics"
        );
    }

    #[test]
    fn manufactured_solution_with_live_nonlinearity_matches_python() {
        let mut solver = SpectralSolver::new(8, 0.05).unwrap();
        let base = solver.state.clone();
        let nonlinear = solver.nonlinear_hat(&base);
        let viscosity = solver.viscosity;
        let k2 = solver.k2.clone();
        let len = solver.len;
        for _ in 0..4 {
            solver
                .step_with_forcing(0.05, |time| {
                    let s = amplitude(time);
                    let sd = amplitude_dot(time);
                    let mut force = vec![Complex64::default(); base.len()];
                    for component in 0..COMPONENTS {
                        for (q, wave_number2) in k2.iter().enumerate() {
                            let idx = component * len + q;
                            force[idx] = sd * base[idx]
                                + s * s * nonlinear[idx]
                                + viscosity * *wave_number2 * s * base[idx];
                        }
                    }
                    force
                })
                .unwrap();
        }
        let exact: Vec<_> = base.iter().map(|z| amplitude(0.2) * z).collect();
        let numerator = solver
            .state
            .iter()
            .zip(&exact)
            .map(|(a, b)| (*a - *b).norm_sqr())
            .sum::<f64>()
            .sqrt();
        let denominator = exact.iter().map(|z| z.norm_sqr()).sum::<f64>().sqrt();
        let relative_l2 = numerator / denominator;
        assert!((relative_l2 - 1.8953385027576588e-8).abs() < 2e-12);
        assert!((solver.diagnostics().energy - 0.09853534649002092).abs() < 3e-12);
    }

    #[test]
    fn imported_state_rejects_projection_overflow_without_mutating_solver() {
        let mut solver = SpectralSolver::new(4, 0.05).unwrap();
        let original = solver.state.clone();
        let mut state = vec![Complex64::default(); COMPONENTS * solver.len];
        let q = solver.index(1, 1, 0);
        state[q] = Complex64::new(f64::MAX, 0.0);
        state[solver.len + q] = Complex64::new(f64::MAX, 0.0);

        assert!(solver.set_state_hat(state).is_err());
        assert_eq!(solver.state, original);
    }

    #[test]
    fn overflowing_diagnostics_are_unhealthy_and_cannot_drive_cfl() {
        let mut solver = SpectralSolver::new(4, 0.05).unwrap();
        let mut state = vec![Complex64::default(); COMPONENTS * solver.len];
        state[0] = Complex64::new(5.0e155, 0.0);
        solver.set_state_hat(state).unwrap();

        let diagnostics = solver.diagnostics();
        assert!(diagnostics.energy.is_infinite());
        assert!(!diagnostics.finite);
        assert!(solver.stable_dt(0.4).is_err());
    }

    #[test]
    fn step_rejects_an_unrepresentable_time_increment_before_mutation() {
        let mut solver = SpectralSolver::new(4, 0.05).unwrap();
        solver.time = f64::MAX;
        let original = solver.state.clone();

        assert!(solver.step(1.0).is_err());
        assert_eq!(solver.time, f64::MAX);
        assert_eq!(solver.state, original);
        assert_eq!(solver.steps, 0);
    }

    #[test]
    fn forced_evolution_invalidates_unforced_budget_until_reset() {
        let mut solver = SpectralSolver::new(8, 0.05).unwrap();
        let state_len = solver.state.len();
        solver
            .step_with_forcing(0.01, |_| vec![Complex64::default(); state_len])
            .unwrap();
        let forced = solver.diagnostics();
        assert!(!forced.energy_balance_applicable);
        assert!(forced.energy_balance_relative_error.is_nan());
        assert!(!forced.finite);

        solver.step(0.01).unwrap();
        assert!(!solver.diagnostics().energy_balance_applicable);

        solver.reset_taylor_green();
        let reset = solver.diagnostics();
        assert!(reset.energy_balance_applicable);
        assert_eq!(reset.energy_budget_samples, 1);
        assert!(reset.energy_balance_relative_error.abs() <= f64::EPSILON);
        assert!(reset.finite);
    }
}
