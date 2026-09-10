use navier_web::SpectralSolver;
use num_complex::Complex64;
use serde_json::Value;
use std::f64::consts::TAU;

fn fixture() -> Value {
    serde_json::from_str(include_str!("fixtures/python_reference.json")).unwrap()
}

fn close(actual: f64, expected: f64, tolerance: f64) {
    assert!(
        (actual - expected).abs() <= tolerance,
        "actual={actual:.17e} expected={expected:.17e} tolerance={tolerance:.1e}"
    );
}

#[test]
fn taylor_green_trajectory_matches_canonical_python() {
    let reference = fixture();
    let mut solver = SpectralSolver::new(8, 0.05).unwrap();
    close(
        solver.diagnostics().energy,
        reference["tgv"]["initial"]["energy"].as_f64().unwrap(),
        2e-14,
    );
    solver.step_many(0.01, 2).unwrap();
    let diagnostics = solver.diagnostics();
    close(
        diagnostics.energy,
        reference["tgv"]["final"]["energy"].as_f64().unwrap(),
        3e-13,
    );
    close(
        diagnostics.max_speed,
        reference["tgv"]["final"]["velocity_linf"].as_f64().unwrap(),
        3e-12,
    );
    assert!(diagnostics.divergence_rms < 2e-14);

    let velocity = solver.velocity_f64();
    let n = 8usize;
    let len = n * n * n;
    let points = [(0, 0, 0), (1, 2, 3), (3, 4, 5), (7, 6, 2)];
    let expected = reference["tgv"]["samples_xyz"].as_array().unwrap();
    let mut sample = 0;
    for (i, j, k) in points {
        let q = (i * n + j) * n + k;
        for component in 0..3 {
            close(
                velocity[component * len + q],
                expected[sample].as_f64().unwrap(),
                3e-12,
            );
            sample += 1;
        }
    }
}

#[test]
fn zero_and_viscous_fourier_mode_have_known_evolution() {
    let mut zero = SpectralSolver::new(8, 0.2).unwrap();
    zero.reset_zero();
    zero.step_many(0.05, 4).unwrap();
    assert!(
        zero.state_hat()
            .iter()
            .all(|z| *z == Complex64::new(0.0, 0.0))
    );
    assert_eq!(zero.diagnostics().energy, 0.0);

    let reference = fixture();
    let mut shear = SpectralSolver::new(8, 0.2).unwrap();
    shear.reset_shear(2).unwrap();
    let initial = shear.diagnostics().energy;
    shear.step_many(0.05, 4).unwrap();
    close(
        initial,
        reference["shear"]["initial_energy"].as_f64().unwrap(),
        2e-14,
    );
    close(
        shear.diagnostics().energy,
        reference["shear"]["final_energy"].as_f64().unwrap(),
        3e-13,
    );
    close(
        shear.diagnostics().energy / initial,
        reference["shear"]["expected_ratio"].as_f64().unwrap(),
        3e-13,
    );
}

#[test]
fn sampled_shear_energy_budget_converges_and_resets() {
    fn run(dt: f64, steps: usize) -> f64 {
        let mut solver = SpectralSolver::new(8, 0.2).unwrap();
        solver.reset_shear(2).unwrap();
        let initial = solver.diagnostics();
        close(initial.initial_energy, 0.25, 2e-14);
        assert_eq!(initial.energy_budget_samples, 1);
        assert_eq!(initial.energy_budget_max_interval, 0.0);
        assert_eq!(initial.cumulative_energy_dissipation, 0.0);
        assert_eq!(initial.energy_balance_relative_error, 0.0);
        assert_eq!(
            initial.energy_budget_quadrature,
            "trapezoidal-diagnostics-observations"
        );

        let repeated = solver.diagnostics();
        assert_eq!(repeated.energy_budget_samples, 1);
        let mut expected_quadrature = 0.0;
        let mut previous_rate = initial.energy_dissipation_rate;
        for _ in 0..steps {
            solver.step(dt).unwrap();
            let observed = solver.diagnostics();
            expected_quadrature += 0.5 * dt * (previous_rate + observed.energy_dissipation_rate);
            previous_rate = observed.energy_dissipation_rate;
        }
        let diagnostics = solver.diagnostics();
        close(
            diagnostics.cumulative_energy_dissipation,
            expected_quadrature,
            2e-14,
        );
        assert_eq!(diagnostics.energy_budget_samples, steps as u32 + 1);
        assert_eq!(diagnostics.energy_budget_start_time, 0.0);
        close(diagnostics.energy_budget_end_time, steps as f64 * dt, 2e-15);
        close(diagnostics.energy_budget_max_interval, dt, 2e-15);
        assert_eq!(
            diagnostics.minimum_sampled_dissipation_time,
            diagnostics.time
        );
        assert!(
            diagnostics.minimum_sampled_energy_dissipation_rate
                <= diagnostics.mean_energy_dissipation_rate
        );
        assert!(diagnostics.energy_balance_applicable);
        assert!(diagnostics.finite);

        solver.reset_zero();
        let reset = solver.diagnostics();
        assert_eq!(reset.initial_energy, 0.0);
        assert_eq!(reset.cumulative_energy_dissipation, 0.0);
        assert_eq!(reset.energy_balance_defect, 0.0);
        assert_eq!(reset.energy_balance_relative_error, 0.0);
        assert_eq!(reset.energy_budget_samples, 1);
        assert_eq!(reset.energy_budget_max_interval, 0.0);
        assert!(reset.finite);
        diagnostics.energy_balance_relative_error.abs()
    }

    let coarse_error = run(0.02, 10);
    let fine_error = run(0.01, 20);
    assert!(fine_error < 0.26 * coarse_error);
    assert!(fine_error < 1.0e-5);
}

#[test]
fn cpu_budget_fields_use_the_cross_backend_camel_case_schema() {
    let diagnostics = SpectralSolver::new(8, 0.05).unwrap().diagnostics();
    let value = serde_json::to_value(diagnostics).unwrap();
    close(value["initialEnergy"].as_f64().unwrap(), 0.125, 2e-14);
    assert_eq!(value["energyBudgetSamples"], 1);
    assert_eq!(value["energyBalanceApplicable"], true);
    assert!(value.get("energy_balance_relative_error").is_none());
    assert!(value.get("energy_dissipation_rate").is_some());
}

#[test]
fn fixed_input_is_bitwise_repeatable_and_finite() {
    let mut left = SpectralSolver::new(8, 0.03).unwrap();
    let mut right = SpectralSolver::new(8, 0.03).unwrap();
    left.step_many(0.007, 3).unwrap();
    right.step_many(0.007, 3).unwrap();
    assert_eq!(left.state_hat(), right.state_hat());
    assert!(left.diagnostics().finite);
    assert!(left.velocity_f64().iter().all(|value| value.is_finite()));
}

#[test]
fn bounded_advance_enforces_cfl_and_preserves_tail_warning() {
    let mut solver = SpectralSolver::new(12, 0.05).unwrap();
    solver.reset_shear(3).unwrap();
    assert_eq!(solver.diagnostics().high_frequency_energy_fraction, 1.0);
    assert!(solver.diagnostics().underresolved);
    let report = solver.advance_bounded(0.2, 0.2, 0.1, 32).unwrap();
    close(report.elapsed, 0.2, 2e-15);
    assert!(report.substeps > 1);
    assert!(report.max_cfl <= 0.1 * (1.0 + 1e-12));
    assert!(report.underresolved);
    assert_eq!(report.max_tail_energy_fraction, 1.0);
}

#[test]
fn bounded_advance_is_temporally_converged_at_the_interactive_step() {
    let mut interactive = SpectralSolver::new(16, 0.05).unwrap();
    let mut reference = SpectralSolver::new(16, 0.05).unwrap();

    let interactive_report = interactive
        .advance_bounded(0.1, 1.0 / 60.0, 0.42, 64)
        .unwrap();
    let reference_report = reference
        .advance_bounded(0.1, 1.0 / 180.0, 0.42, 64)
        .unwrap();

    close(interactive_report.elapsed, 0.1, 2e-15);
    close(reference_report.elapsed, 0.1, 2e-15);
    assert!(interactive_report.max_cfl <= 0.42 * (1.0 + 1e-12));
    assert!(reference_report.max_cfl <= 0.42 * (1.0 + 1e-12));

    let interactive_velocity = interactive.velocity_f64();
    let reference_velocity = reference.velocity_f64();
    let error = interactive_velocity
        .iter()
        .zip(&reference_velocity)
        .map(|(value, expected)| (value - expected).powi(2))
        .sum::<f64>()
        .sqrt();
    let reference_norm = reference_velocity
        .iter()
        .map(|value| value.powi(2))
        .sum::<f64>()
        .sqrt();
    let relative_l2 = error / reference_norm;
    assert!(
        relative_l2 < 1.0e-8,
        "interactive timestep relative L2 error {relative_l2:e}"
    );
}

#[test]
fn native_grid_allocation_has_an_explicit_bound() {
    assert!(SpectralSolver::new(130, 0.05).is_err());
}

#[test]
fn leray_projection_reduces_divergence_and_matches_python_energy() {
    let reference = fixture();
    let n = 8usize;
    let len = n * n * n;
    let mut raw = vec![0.0; 3 * len];
    for i in 0..n {
        for j in 0..n {
            for k in 0..n {
                let x = TAU * i as f64 / n as f64;
                let y = TAU * j as f64 / n as f64;
                let z = TAU * k as f64 / n as f64;
                let q = (i * n + j) * n + k;
                raw[q] = x.sin() + 0.2 * y.cos();
                raw[len + q] = 0.3 * x.cos() + 0.1 * z.sin();
                raw[2 * len + q] = 0.4 * z.cos();
            }
        }
    }
    // Feed a Fourier transform through the same public state boundary by using
    // a zero-viscosity solver's deterministic DFT convention.
    let mut probe = SpectralSolver::new(n, 0.0).unwrap();
    let mut spectrum = vec![Complex64::new(0.0, 0.0); 3 * len];
    for component in 0..3 {
        for kx in 0..n {
            for ky in 0..n {
                for kz in 0..n {
                    let mut sum = Complex64::new(0.0, 0.0);
                    for x in 0..n {
                        for y in 0..n {
                            for z in 0..n {
                                let phase = -TAU * ((kx * x + ky * y + kz * z) as f64) / n as f64;
                                sum += Complex64::from_polar(
                                    raw[component * len + (x * n + y) * n + z],
                                    phase,
                                );
                            }
                        }
                    }
                    spectrum[component * len + (kx * n + ky) * n + kz] = sum;
                }
            }
        }
    }
    probe.set_state_hat(spectrum).unwrap();
    let diagnostics = probe.diagnostics();
    close(
        diagnostics.energy,
        reference["projection"]["projected_energy"]
            .as_f64()
            .unwrap(),
        3e-13,
    );
    assert!(diagnostics.divergence_rms < 2e-14);
    assert!(
        reference["projection"]["raw_divergence_linf"]
            .as_f64()
            .unwrap()
            > 1.0
    );
}
