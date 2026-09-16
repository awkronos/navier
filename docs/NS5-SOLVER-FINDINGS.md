# NS5-SOLVER findings — numerical half audit (OBSERVATIONS ONLY)

Lane NS5-SOLVER, 2026-09-16. Per `docs/FALSIFICATION_LEDGER.md` F-012 every
number in this note is an observation or a falsifiable-inequality proposal;
nothing here certifies a continuum regularity or breakdown statement.
Interpretation rule: an interval certificate bounds **round-off of a declared
expression at reported operands**, never a PDE residual.

Branch: `lane/NS5-SOLVER-2026-09-16`, base `origin/main` =
`3ed567cd440d3bb2286eb9f7fffdd4c7dcced9a9` (re-hashed at worktree creation).
Reality lane branch `lane/NS5-SOLVER-rl-2026-09-16` at
`26b83df059964bb4b00e9f6fb3461ee9a1b03210` (origin/main) — NO reality changes
were required; see §1.

## 1. Solver-surface inventory (measured at worktree creation)

- **Canonical home = `~/reality/solvers/navier/`** by Tim's 2026-09-01
  unification directive (navier commit `ac40ccd`):
  `navier/scripts/{navier_spectral_core,navier_accel,navier_solver_bench,navier_adaptive_bench}.py`
  are importlib re-export shims loading the reality body from absolute paths;
  the shim header fails loudly if the reality checkout is absent.
- Bodies (reality): `navier_spectral_core.py` 1165 ln (IFRK4 pseudo-spectral
  torus solver, `flow_diagnostics`), `navier_accel.py` 271 ln,
  `navier_solver_bench.py` 719 ln, `navier_xcarrier.py` 564 ln (whole-space
  X¹ Picard engine, reality-only), `test_navier_spectral_core.py` 337 ln,
  `navier_kernels.c`.
- `navier/scripts/navier_kernels.c` vs reality copy: byte-identical
  (`/usr/bin/diff` exit 0).
- **No stale fork found** — the two repos are one unified surface with a
  re-export adapter; nothing to consolidate by deletion.
- navier-side bodies: `solver/` is the Rust crate `navier-web` (IFRK4
  spectral + `AxisConstruction` evaluator + WebGPU/WASM);
  `scripts/navier_diagnostic_score.py` (436 ln) scores the Rust solver's
  emitted energy-budget diagnostics.
- Consolidation PROPOSAL (not acted — safe-act boundary): move
  `navier_diagnostic_score.py` and this lane's `solver/interval_cert/` into
  `reality/solvers/navier/` with shims, completing the 2026-09-01 pattern.
  Placement here follows the dispatch fence (`navier/solver` only).

## 2. Test suites + bench (all exit codes captured without pipes)

Interpreter: `/opt/homebrew/bin/python3` 3.14.7, numpy 2.5.0, scipy 1.17.1,
mpmath 1.3.0, pytest 9.0.3. reality has NO `.venv` — reality's python routes
through the system interpreter (measured: `ls /Users/schizodactyl/reality`
shows no venv; tests green with it).

| surface | command (in worktree) | result |
| --- | --- | --- |
| reality body | `python3 -m pytest solvers/navier/test_navier_spectral_core.py -q` | 17 passed + 21 subtests, 0.59 s, EXIT=0 |
| navier scorer + shim equivalence | `python3 -m pytest tests/test_navier_diagnostic_score.py tests/test_navier_solver_equivalence.py -q` | 18 passed + 6 subtests, 1.08 s, EXIT=0 |
| adaptive bench | `python3 -m pytest tests/test_navier_adaptive_bench.py -q` | 3 passed + 6 subtests, 0.39 s, EXIT=0 |
| certificates (new) | `python3 -m pytest solver/interval_cert/test_float64_cert.py -q` | 9 passed, 0.18 s, EXIT=0 |

Bench (`solvers/navier/navier_solver_bench.py --grid G`, default steps/dt;
grids 16/32/64, all `status: PASS`, EXIT=0, each < 0.5 s):

- load conditions: 18-core MacBook, loadavg 5.4–7.6 during the window (lean
  lanes + kagami daemon active); the bench's own guard self-reported
  `quiet_host: true` for every timed section (≤ 0.33 load/core vs 0.75
  threshold), single-threaded CPU-time best-of-5 timing, `timing_cpu_over_wall
  ≈ 0.999`. Throughput numbers are therefore bounded by THIS probe
  configuration only — no speedup claims are made.
- residuals: `divergence_linf` 2.46e-17 (n16) / 1.92e-17 (n32) / 2.01e-17
  (n64); `hodge_divergence_linf` ≤ 1.7e-30; inviscid energy drift
  6.9e-9 / 7.05e-9 / 7.05e-9; IFRK4 temporal order 4.0193 (pair) /
  4.0111 (multi-dt); MMS relative L2 6.09e-7 with dt/2 → 3.76e-8 (reduction
  factor 16.2, i.e. observed order ≈ 4).
- throughput (grid updates/s, CPU best-of-5): 1.58e7 / 1.51e7 / 1.15e7.
- accelerator: `accelerator: ok` (C kernel path loaded).

## 3. Interval certificate module (LANDED: `solver/interval_cert/`)

`float64_cert.py`: outward-rounded float64 intervals (every operation widened
1 ulp per side via `math.nextafter`). Soundness: monotone correct rounding ⇒
by induction the interval contains the exact expression value AND the float64
evaluation **in the same fixed operation order**; other orders (numpy
pairwise) are explicitly NOT covered — stated in the docstring, and a test
(`test_cumulative_dissipation_trapezoid`) demonstrates the distinction.
Certificates emitted for the periodic solver's diagnostic score:

- `certify_energy_balance_defect(E, D, E0)` — mirrors the recomputation in
  `scripts/navier_diagnostic_score.py` lines ~174–182; optional
  `input_radius` inflates operands to cover upstream (FFT/backend)
  uncertainty the in-expression envelope cannot see.
- `certify_cumulative_dissipation(rates, dt)` — the trapezoidal quadrature
  itself enclosed, so the whole budget expression `E_end + ∫D − E_0` gets one
  composed envelope.
- `certificate_record` fails closed: `finite_certification` requires finite,
  well-ordered endpoints AND point-containment.

Live demo (`energy_budget_demo.py`, grid 16, ν=0.05, dt=0.02, 11 observations
on [0, 2.0], Taylor–Green through the canonical reality body via the navier
shim, EXIT=0):

- observed budget defect **+1.6569860135e-5**, rounding envelope width
  **4.58e-16** — i.e. the score's algebra contributes ≲ 3e-11 of the observed
  defect; the remainder is model/temporal error. `finite_certification: true`.
- Falsifiable inequality proposed: for this configuration, |defect| ∈
  [1.6569860135123845e-5, 1.656986013512430e-5] (interval record emitted).
- Field evidence of fail-closed behaviour: the demo's first version
  mis-sliced the rates (one trapezoid interval short); the certificate
  refused (`finite_certification: false`) although every float64 point
  computed self-consistently — the enclosure caught a genuine expression
  mismatch that no point-value check would have flagged.
- What this is NOT: no continuum residual, no FFT-internal bound (declare an
  input radius; default 0), no closure claim (F-012).

## 4. Mild-multiplier conditioning (OBSERVATION; `conditioning_probe.py`, EXIT=0)

Measured crossover of `np.exp` on float64 (numpy 2.5.0, same machine):

- `X_MAX = 709.782712893384` — largest finite argument; `exp(X_MAX)` =
  1.7976931348622732e308 (= DBL_MAX); the NEXT representable argument (1 ulp
  up) already gives `inf`. Crossover located within 1 ulp.
- `X_MIN = -745.1332191019411` — most negative argument with nonzero result;
  below it `exp` returns the exact zero float.
- Proposed falsifiable inequality for the formal side:
  `float64 exp(ν|ξ|²(−t)) < inf  ⇔  ν|ξ|²(−t) ≤ 709.782712893384` — the exact
  t<0 explosion domain behind the OPEN_FRONTIER_MAP domain repair, at cutoff
  `|ξ| ≤ K`: overflow for `|t| > X_MAX/(νK²)`, high-mode damping saturation
  to exact 0.0 for `t ≥ |X_MIN|/(νK²)`.
- Grid probes (max|ξ|² = 3·(N/2−1)², torus lattice): ν=0.05: N16 →
  |t|_overflow 96.57, t_underflow 101.38; N32 → 21.03 / 22.08; N64 → 4.924 /
  5.169. The two thresholds straddle the same domain and tighten linearly in
  1/K² — mild-solver backward evolution loses representable time-domain
  width quadratically in the cutoff.

## 5. COMPUTED_AXIS_CONSTRUCTION reproduction (cargo, tree = base SHA)

`cargo test construction::tests -- --nocapture` in `/tmp/wt-ns5-solver/solver`
(= navier `3ed567cd`, rust 1.98.1, deterministic — no seed; defaults per the
docs table): **10 passed, 0 failed, EXIT=0**, build 12.79 s, tests 0.82 s,
machine under concurrent lean-lane load (loadavg ≈ 4–7; wall timings not
comparable across machines; no speedup claim).

Numbers vs the docs' table: angular/axial/pressure RMS, max speed, domain
energy, min swirl reproduce **bit-exactly** (1.9921418144623968e-6,
1.7733879359490666e-8, 3.3903453327861445e-9, 10.04429420038561,
0.24958636773964515, 0.26162692837448365). Two drift ~5e-13 relative:
`divergence_rms` 8.500463463624519e-3 (docs) → 8.500463463628559e-3;
`momentum_residual_rms` 1.4123532691928133e5 → 1.4123532691935662e5.
Classification: last-bits regression drift (toolchain/optimizer dependent),
consistent with the docs' own "regression observations at one coarse grid"
label. Recommendation: pin the docs numbers as an interval/ulp tolerance
(±1 ulp at these magnitudes would have absorbed it) or regenerate the table
at the pinned toolchain — prose-restated floats silently rot otherwise.

## 6. Residuals / next

- Certificate covers the ENERGY-BUDGET score only; spectral-tail and
  `divergence_rms` (physical-space, post-FFT) scores still need a
  declared-envelope version (needs per-kernel FFT error bound or input radius).
- Rust-axis evaluator emits point values only; an interval-certificate port
  (`interval_cert`-style) or rustfftw bounds would close the F-012 successor
  gap there.
- Reality-side consolidation of `navier_diagnostic_score.py` + `interval_cert`
  awaits a root-fold ownership call (§1 proposal).
