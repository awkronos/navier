use navier_web::{SpectralSolver, WebGpuSpectralSolver};
use num_complex::Complex64;
use std::f64::consts::TAU;

fn mode_index(n: usize, wave: [isize; 3]) -> usize {
    let slot = |value: isize| value.rem_euclid(n as isize) as usize;
    (slot(wave[0]) * n + slot(wave[1])) * n + slot(wave[2])
}

fn set_real_cosine_pair(
    state: &mut [Complex64],
    n: usize,
    wave: [isize; 3],
    coefficient: f64,
    polarization: [f64; 3],
) {
    let len = n.pow(3);
    let positive = mode_index(n, wave);
    let negative = mode_index(n, wave.map(|value| -value));
    for component in 0..3 {
        // Rust stores the unnormalized forward DFT U=N^3 u_hat. Equal real
        // coefficients at opposite modes reconstruct 2*c*cos(k.x).
        let value = Complex64::new(len as f64 * coefficient * polarization[component], 0.0);
        state[component * len + positive] = value;
        state[component * len + negative] = value;
    }
}

fn raw_coefficient(state: &[Complex64], n: usize, wave: [isize; 3]) -> [Complex64; 3] {
    let len = n.pow(3);
    let q = mode_index(n, wave);
    let raw_scale = Complex64::new(0.0, -1.0) / len as f64;
    [
        raw_scale * state[q],
        raw_scale * state[len + q],
        raw_scale * state[2 * len + q],
    ]
}

fn assert_complex_close(actual: Complex64, expected: Complex64, tolerance: f64) {
    assert!(
        (actual - expected).norm() <= tolerance,
        "actual={actual:?} expected={expected:?} tolerance={tolerance:e}"
    );
}

#[test]
fn viscous_mode_matches_period_one_raw_carrier_scaling() {
    let n = 8usize;
    let len = n.pow(3);
    let wave = [0, 2, 0];
    let rust_viscosity = 0.2;
    let period_one_viscosity = rust_viscosity / TAU.powi(2);
    let raw_mu = TAU.powi(2) * period_one_viscosity;
    let dt = 0.125;
    let mut solver = SpectralSolver::new(n, rust_viscosity).unwrap();
    let metadata = solver.metadata();
    assert_eq!(metadata.grid, n);
    assert_eq!(metadata.spatial_domain, "[0, 2π)^3");
    assert_eq!(metadata.box_length, TAU);
    assert_eq!(metadata.viscosity, rust_viscosity);
    assert_eq!(metadata.period_one_velocity_scale, 1.0 / TAU);
    assert_eq!(metadata.period_one_viscosity, period_one_viscosity);
    assert!((metadata.lean_raw_viscosity - raw_mu).abs() <= 2.0 * f64::EPSILON);
    assert_eq!(
        metadata.stored_spectrum_convention,
        "U(k) = N^3 uHat_R(k) (unnormalized forward DFT)"
    );
    assert_eq!(
        metadata.lean_raw_amplitude_convention,
        "A(k) = -i U(k) / N^3"
    );
    let serialized = serde_json::to_value(metadata).unwrap();
    assert_eq!(serialized["boxLength"], TAU);
    assert_eq!(serialized["periodOneViscosity"], period_one_viscosity);
    assert_eq!(serialized["leanRawViscosity"], rust_viscosity);

    let mut state = vec![Complex64::default(); 3 * len];
    set_real_cosine_pair(&mut state, n, wave, 0.3, [1.0, 0.0, 0.0]);
    solver.set_state_hat(state).unwrap();
    let initial = raw_coefficient(solver.state_hat(), n, wave);

    solver.step(dt).unwrap();
    let final_coefficient = raw_coefficient(solver.state_hat(), n, wave);
    let expected_decay = (-raw_mu * 4.0 * dt).exp();

    assert!((raw_mu - rust_viscosity).abs() <= 2.0 * f64::EPSILON);
    for component in 0..3 {
        assert_complex_close(
            final_coefficient[component],
            expected_decay * initial[component],
            2.0e-15,
        );
    }
}

fn measured_raw_triad_derivative(n: usize, dt: f64) -> ([Complex64; 3], [Complex64; 3]) {
    let len = n.pow(3);
    let mut solver = SpectralSolver::new(n, 0.0).unwrap();
    let mut state = vec![Complex64::default(); 3 * len];

    // k=(1,0,0), a=(0,1,1) and l=(0,1,0), b=(1,0,1) are transverse.
    // Both ordered pairs contribute at q=k+l. Their unprojected sum is
    // a+b=(1,1,2), whose Leray projection at q=(1,1,0) is (0,0,2).
    set_real_cosine_pair(&mut state, n, [1, 0, 0], 0.25, [0.0, 1.0, 1.0]);
    set_real_cosine_pair(&mut state, n, [0, 1, 0], 0.20, [1.0, 0.0, 1.0]);
    solver.set_state_hat(state).unwrap();
    let wave = [1, 1, 0];
    let before = raw_coefficient(solver.state_hat(), n, wave);
    let before_negative = raw_coefficient(solver.state_hat(), n, wave.map(|value| -value));
    solver.step(dt).unwrap();
    let after = raw_coefficient(solver.state_hat(), n, wave);
    let after_negative = raw_coefficient(solver.state_hat(), n, wave.map(|value| -value));
    (
        std::array::from_fn(|component| (after[component] - before[component]) / dt),
        std::array::from_fn(|component| {
            (after_negative[component] - before_negative[component]) / dt
        }),
    )
}

#[test]
fn rotational_triad_has_the_lean_raw_sign_phase_and_dft_normalization() {
    // The Lean raw carrier omits the physical derivative phase and uses
    // A=-2*pi*i*u_hat_P. Since u_P(y)=u_R(2*pi*y)/(2*pi), this is
    // A=-i*u_hat_R=-i*U/N^3 for Rust's stored DFT U.
    //
    // For the two inputs above, B_raw(A,A) at q is
    // (-i*0.25)(-i*0.20) P_q(a+b) = (0,0,-0.10).
    let expected = [
        Complex64::new(0.0, 0.0),
        Complex64::new(0.0, 0.0),
        Complex64::new(-0.10, 0.0),
    ];
    for n in [8, 12] {
        let (coarse, _) = measured_raw_triad_derivative(n, 2.0e-4);
        let (refined, refined_negative) = measured_raw_triad_derivative(n, 1.0e-4);
        eprintln!("n={n} raw triad derivative coarse={coarse:?} refined={refined:?}");
        for component in 0..3 {
            // A first derivative from a finite RK trajectory has O(dt)
            // contamination from newly generated modes. Step halving must
            // approach the independently calculated instantaneous symbol.
            assert!(
                (refined[component] - expected[component]).norm()
                    < 0.6
                        * (coarse[component] - expected[component])
                            .norm()
                            .max(1.0e-14)
            );
            assert_complex_close(refined[component], expected[component], 2.0e-9);
            // Multiplication by -i maps a Hermitian physical spectrum to the
            // anti-Hermitian reality law required by the no-i raw carrier.
            assert_complex_close(
                refined_negative[component],
                -refined[component].conj(),
                2.0e-14,
            );
        }
    }
}

#[test]
fn webgpu_metadata_uses_the_shared_convention() {
    let requested_viscosity = 0.2;
    let gpu = match pollster::block_on(WebGpuSpectralSolver::new(8, requested_viscosity)) {
        Ok(gpu) => gpu,
        Err(error)
            if error == "WebGPU has no high-performance adapter"
                && std::env::var("NAVIER_REQUIRE_GPU").as_deref() != Ok("1") =>
        {
            eprintln!("SKIPPED: no WebGPU adapter: {error}");
            return;
        }
        Err(error) => panic!("WebGPU solver initialization failed: {error}"),
    };
    let metadata = gpu.metadata();
    // WebGPU exposes the actual f32 coefficient used by its kernels. Every
    // derived convention must use that same value rather than the f64 input.
    assert_eq!(metadata.viscosity, gpu.viscosity());
    assert_eq!(
        metadata.period_one_viscosity,
        metadata.viscosity / TAU.powi(2)
    );
    assert_eq!(metadata.lean_raw_viscosity, metadata.viscosity);
    assert_eq!(metadata.box_length, TAU);
    assert_eq!(
        metadata.lean_raw_amplitude_convention,
        "A(k) = -i U(k) / N^3"
    );
}

fn interacting_real_state(n: usize) -> Vec<Complex64> {
    let len = n.pow(3);
    let mut state = vec![Complex64::default(); 3 * len];
    set_real_cosine_pair(&mut state, n, [1, 0, 0], 0.25, [0.0, 1.0, 1.0]);
    set_real_cosine_pair(&mut state, n, [0, 1, 0], 0.20, [1.0, 0.0, 1.0]);
    // A sine phase makes the completed triad exchange energy at first order.
    state[2 * len + mode_index(n, [1, 1, 0])] = Complex64::new(0.0, 0.15 * len as f64);
    state[2 * len + mode_index(n, [-1, -1, 0])] = Complex64::new(0.0, -0.15 * len as f64);
    state
}

#[test]
fn nonlinear_physical_triad_exchanges_modal_energy_without_creating_total_energy() {
    // Numerical counterpart of PhysicalPeriodicGlobalControl's paired triad
    // cancellation, on a real, divergence-free, dealiased Fourier state.
    for n in [8, 12] {
        let mut solver = SpectralSolver::new(n, 0.0).unwrap();
        solver.set_state_hat(interacting_real_state(n)).unwrap();
        let energy = solver.diagnostics().energy;
        let before = raw_coefficient(solver.state_hat(), n, [1, 1, 0])[2].norm_sqr();
        solver.step(0.001).unwrap();
        let after = raw_coefficient(solver.state_hat(), n, [1, 1, 0])[2].norm_sqr();
        assert!(
            (after - before).abs() > 1e-6,
            "the triad must actually exchange energy"
        );
        assert!((solver.diagnostics().energy - energy).abs() < 1e-12);
        assert!(solver.diagnostics().divergence_rms < 1e-12);
    }
}

#[test]
fn physical_mean_changes_modal_phase_without_exponential_amplitude_growth() {
    let n = 8usize;
    let len = n.pow(3);
    let mean = [0.7, -0.3, 0.2];
    let dt = 0.001;
    let mut stationary = SpectralSolver::new(n, 0.07).unwrap();
    let mut moving = SpectralSolver::new(n, 0.07).unwrap();
    let mut state = interacting_real_state(n);
    stationary.set_state_hat(state.clone()).unwrap();
    for component in 0..3 {
        state[component * len] = Complex64::new(mean[component] * len as f64, 0.0);
    }
    moving.set_state_hat(state).unwrap();
    stationary.step(dt).unwrap();
    moving.step(dt).unwrap();
    for wave in [[1, 0, 0], [0, 1, 0], [1, 1, 0]] {
        let frequency = (0..3).map(|i| wave[i] as f64 * mean[i]).sum::<f64>();
        let phase = Complex64::from_polar(1.0, -dt * frequency);
        let rest = raw_coefficient(stationary.state_hat(), n, wave);
        let drift = raw_coefficient(moving.state_hat(), n, wave);
        for component in 0..3 {
            assert_complex_close(drift[component], phase * rest[component], 2e-12);
        }
    }
}
