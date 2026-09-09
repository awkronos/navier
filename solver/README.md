# Navier numerical crate

This crate exposes two distinct numerical instruments:

1. `AxisConstruction` evaluates the finite analytic-axis profile iteration in
   Appendix B of the construction, reconstructs a velocity-pressure field in a
   bounded similarity chart, and samples its equation defects.
2. `SpectralSolver` advances unforced incompressible Navier–Stokes benchmark
   flows on `[0, 2π)^3` using the rotational nonlinearity, Fourier-space Leray
   projection, componentwise Orszag 2/3 dealiasing, and integrating-factor RK4.

Both compile for native Rust and WebAssembly. The periodic solver also has an
independent WebGPU backend. These are numerical instruments; the Lean theorem
and its compiler receipts are the proof-bearing artifacts.

## Fourier conventions shared with Lean

The stored forward transform is `U(k) = N³ û_R(k)` on `[0, 2π)³`.
To use period-one coordinates at the same time, set
`u_P(y,t) = u_R(2πy,t)/(2π)` and `ν_P = ν_R/(2π)²`.
The raw Lean evolution then uses `A(k) = -i U(k)/N³` and `μ = ν_R`:

```text
A' = -μ |k|² A + P_k B_raw(A,A)
B_raw(A,A)(k) = sum_(p+q=k) (q·A(p)) A(q).
```

Real velocity corresponds to `A(-k) = -conj(A(k))`. Literal physical Fourier
coefficients require this phase encoding before entering the raw evolution.
The finite grid still truncates the continuum series and discretizes time.

CPU, WebGPU, and their WASM exports share the typed metadata in
[`src/convention.rs`](src/convention.rs). Derived viscosity values use the
actual backend coefficient, including GPU rounding to `f32`. The browser reads
that metadata from its running solver. `cargo test --test fourier_convention`
checks viscous decay and a projected nonlinear triad on two grids; set
`NAVIER_REQUIRE_GPU=1` to require the real GPU metadata check.

## Finite analytic-axis evaluator

The default construction evaluator uses radial order 12, 257 equally spaced
axial-similarity nodes, and 18 nonlinear iterations. It evaluates the exact
coefficient integration rule used by the Appendix-B fixed-point map, computes
the axis pressure datum by deterministic quadrature of the Appendix-A schedule,
and reconstructs physical velocity and pressure from the similarity variables.
The sampled chart is

```text
tau > 0,    |eta| <= 0.8,    Lambda X <= 3.2.
```

The remaining default parameters are `h = 0.001`, `j0 = 0.001`, schedule
parameters `lambda = 0.04` and `m = 1`, radial scale `Lambda = 48`, and pressure
amplitude `2`. These are deterministic numerical settings inside the analytic
parameter ranges used by the implementation. A finite run does not certify all
existential smallness and largeness thresholds of the completed construction.

For every sampled point it returns velocity, pressure, and

```text
R = ∂t u + (u·∇)u − Δu + ∇p.
```

`R` is the force required by this finite reconstructed field. The reported
momentum-residual RMS therefore measures the size of that field; it is not an
error bound against the completed selected witness and is not the selected
globally smooth force. The much smaller profile-equation RMS values measure the
finite Appendix-B equations directly; these quantities have different units
and purposes. Divergence and momentum residuals use centered finite differences
in physical coordinates; the domain energy uses a tensor trapezoidal rule on
the displayed bounded chart.

The evaluator intentionally omits annular moment matching, cone modulation,
the positive-order Borel background, primary covariance waves, the particular,
signed and mean correction cycles, and final spacetime localization. Those
layers are essential to the proof's globally smooth compact force. See the
[computed-construction note](../docs/COMPUTED_AXIS_CONSTRUCTION.md) for the
equations, algorithm, default parameters, validation, and interpretation of
every diagnostic.

Native Rust:

```rust
use navier_web::{AxisConstruction, AxisConstructionConfig};

let axis = AxisConstruction::new(AxisConstructionConfig::default())?;
let (velocity, pressure, residual, half_extent, diagnostics) =
    axis.evaluate_grid(17, 0.05)?;
```

Browser JavaScript initializes the generated ES module and then calls:

```js
const axis = new ConstructionAxis(12, 18);
axis.sample(17, 0.05);
const velocity = axis.velocity();
const pressure = axis.pressure();
const residual = axis.residual();
const diagnostics = axis.diagnostics();
const metadata = axis.metadata();
```

## Periodic spectral solver

The periodic browser experiment defaults to the Taylor–Green vortex. The
returned velocity is an interleaved `Float32Array` of `(u, v, w)` values; the
CPU-WASM calculation itself uses `f64`. Browser grids are bounded to `N ≤ 36`
(`N ≤ 128` natively).
Diagnostics report volume-mean energy and enstrophy,
spectral divergence RMS, peak speed and vorticity, the retained-band tail-energy
fraction and its resolution warning, simulated time, and finiteness.

```bash
cargo test
NAVIER_REQUIRE_GPU=1 cargo test gpu::tests -- --nocapture
cargo test --release gpu_grid_benchmark -- --ignored --nocapture
cargo test --release gpu_cfl_reduction_benchmark -- --ignored --nocapture
cargo build --release --target wasm32-unknown-unknown
WASM_BINDGEN=/path/to/wasm-bindgen ./build-web.sh ../site/solver
```

`build-web.sh` uses the `wasm-bindgen` version selected by `WASM_BINDGEN`
(which must match `Cargo.lock`), remaps machine-local Rust source roots to stable
virtual paths, records the build pipeline digest, and rejects a browser module
that still contains a user-home path marker.

The strict GPU command requires a real adapter and fails on adapter absence,
device or pipeline creation errors, shader validation failures, and numerical
parity failures. Ordinary test runs may skip only when no WebGPU adapter exists;
every other initialization error remains a test failure.

For the periodic solver, JavaScript constructs
`new NavierSolver(grid, viscosity)`, calls `step(dt)`, `stepMany(dt, count)`, or
`advanceBounded(duration, maxDt, cfl, maxSubsteps)`,
then reads `velocity()`, `diagnostics()`, and `metadata()`.

When `navigator.gpu` is available, `await WebGpuNavierSolver.create(grid,
viscosity)` creates the independent GPU-resident implementation of those same
spectral operators. Its `step` methods only submit compute work; `velocity()`
and `diagnostics()` are asynchronous because they are the explicit readback
points. `maxSpeed()` performs the CFL maximum reduction on the GPU and reads
back eight bytes: the nonnegative maximum-speed-squared bits and an explicit
non-finite flag. Failure to create the GPU solver is reported to the caller so a CPU
fallback cannot be mislabeled as GPU execution.

The backend metadata identifies CPU-WASM and WebGPU runs separately. These are
finite-grid numerical experiments. They do not certify continuum regularity,
and fixed-step browser runs are distinct from the repository's verified
adaptive IFRK4 recordings.
