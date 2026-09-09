# Navier browser solver

This crate ports the numerical method in
`reality/solvers/navier/navier_spectral_core.py` to Rust for native, WebAssembly,
and WebGPU execution. It advances the unforced incompressible Navier–Stokes
equations on `[0, 2π)^3` with the rotational nonlinearity, Fourier-space Leray
projection, componentwise Orszag 2/3 dealiasing, and integrating-factor RK4.

The browser defaults to the Taylor–Green vortex. The returned velocity is an
interleaved `Float32Array` of `(u, v, w)` values; the CPU-WASM calculation itself
uses `f64`. Browser grids are bounded to `N ≤ 36` (`N ≤ 128` natively).
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

The strict GPU command requires a real adapter and fails on adapter absence,
device or pipeline creation errors, shader validation failures, and numerical
parity failures. Ordinary test runs may skip only when no WebGPU adapter exists;
every other initialization error remains a test failure.

JavaScript initializes the generated ES module, constructs
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
