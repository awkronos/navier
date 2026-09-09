# Native breakdown mathematics and adaptive simulation

The September 8, 2026 [OpenAI paper](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
claims smooth compact forcing, zero initial velocity, finite-time unbounded
speed, and bounded energy. Section 10 excludes a global smooth bounded-energy
competitor. This is forced Clay alternative C, with a periodic D consequence.
It does not prove or refute this repository's unforced statement A.

The [released source](https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538)
was adapted at that exact revision into 577 native source modules. It is not a
Lake dependency or proof oracle. The port retains the construction's Euclidean
carriers, equations, compact-support claims, finite-energy comparison, and
selected witness. A native coordinate isometry then transports the data into
this repository's official `Fin 3 → ℝ` carrier.

The checked public endpoint is
`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown`, whose type is the
original `Navier.ProblemStatements.WholeSpaceBreakdown`. Its proof selects the
constructed compact candidate, excludes every admissible global competitor by
the full finite-energy comparison argument, transports the result to the native
carrier, and uses viscosity covariance to cover every positive viscosity. It
has no construction, agreement, or coordinate-equivalence premise.

Every adapted construction file carries its upstream revision and license
header. The adapted sources remain under the upstream
[Apache-2.0 license](../references/licenses/OpenAI-Apache-2.0.txt); native bridge
and endpoint files remain under this repository's license. The exact boundary
and mechanical port details are recorded in
[OpenAI construction provenance](OPENAI_CONSTRUCTION_PROVENANCE.md).

## Native mathematical inputs

- `Navier/Breakdown/CompactSmoothForce.lean` proves that global smoothness and
  compact spacetime support imply **all** weighted mixed-derivative bounds in
  `ForcedDataRapidDecay`, including within derivatives at initial time.
  `wholeSpaceBreakdown_of_compact_observable` consumes this result, an actual
  observable breakdown witness, and existing viscosity transport to reach C.
- `Navier/Analysis/ForcedEnergyBalance.lean` proves the local energy law with
  force work and derives its differentiability premises from an actual
  `PartialClassicalSolution` at interior times. It never assumes a global
  solution. Spatial integration and differentiation under an integral still
  require their own integrability and boundary estimates.
- `Navier/Breakdown/CompactPathBreakdown.lean` handles blowup along spatial points in a compact
  region. Global smoothness supplies a uniform bound there; a fixed spatial
  blowup point need not be assumed.
- `Navier/Construction/R3ActualCandidate.lean` extracts the actual velocity,
  pressure, and compact force from the completed correction construction.
- `Navier/Construction/R3FiniteEnergyComparison.lean` proves whole-space
  uniqueness on each pre-singular time slab and uses it to exclude every
  globally smooth finite-energy competitor.
- `Navier/Analysis/EuclideanPDETransport.lean` proves the derivative,
  equation, energy, support, and admissibility transport between the Euclidean
  construction carrier and the official native carrier.
- `Navier/Breakdown/ConstructedBreakdown.lean` consumes those results and
  proves the original forced whole-space alternative C.
- `Navier/Analysis/ConstructedForceExtension.lean` extracts global smoothness
  of the actual selected force, preserves it through localization, coordinate
  transport and viscosity scaling, and supplies its explicit smooth extension
  across time zero. No general Seeley extension assumption is needed.
- `Navier/Analysis/ForceRecursivePartials.lean` identifies actual successive
  coordinate differentiation with the multilinear jet and derives weighted
  estimates for every ordering. The constructed endpoint consumes these
  estimates; no slot-permutation convention is required for their bounds.

## Useful conditional results

This is an inventory by mathematical consumer, not a project-wide census.
`Navier/ConditionalAudit.lean` prints exact types and transitive axioms
for the selected existing declarations. Imported-object checks require any
changed providers to be rebuilt before they establish current-source status.
New proof sources print their own axiom dependencies when compiled.

| Result / family | What it supplies | Remaining input or scope |
| --- | --- | --- |
| `ConstructedBreakdown.wholeSpaceBreakdown` | Original forced whole-space alternative C for every positive viscosity | Closed; this says nothing about unforced A |
| `R3CompactCandidate.selected_compact_candidate` | Constructed Euclidean velocity, pressure, compact force, PDE identities, and singular growth | Consumed by the native endpoint; its property bundle does not itself include a uniform energy bound |
| `ConstructedBreakdown.selectedFiniteEnergyCandidate` | The constructed unit-viscosity Euclidean candidate with globally smooth force and uniform finite energy on `0 ≤ t < 1` | Connects the compact-support energy estimate to the actual selected witness; no global continuation is asserted |
| `ComparatorBridge.compact_candidate_excludes_global_solution` | Finite-energy comparison between smooth classical fields against every admissible global competitor | Consumed by the native endpoint; no agreement premise remains |
| `EuclideanPDETransport` | Exact coordinate transport for PDE derivatives, support, energy, and global competitors | Finite-dimensional carrier bridge only; it preserves the source statement |
| `CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_continuation_apriori` | Whole-space global solution from compatible finite-energy pieces | Local existence, normalized continuation, and a priori critical control for the same quantity; forced blowup supplies none of these unforced universal inputs |
| `Breakdown.noWholeSpaceGlobal_of_pointEvaluationBreakdown` | Exclusion of a global competitor | An actual local solution, agreement with competitors, and unbounded evaluation; compact-path transport allows a moving location |
| `ViscosityEndpoints.wholeSpaceBreakdown_iff_atViscosityOne` | Admissible forcing/data and nonexistence at every positive viscosity | One genuine viscosity-one witness |
| `CriticalMildRestartFixedPoint.existsUnique_criticalMildTerminalRestart_fixedPoint` | Unique local Fourier-lattice restart | Explicit radius budget and contraction inequality |
| `CriticalMildBoundedContinuation.bounded_global_mild_of_terminalNormBound` | Coherent global lattice mild trajectory | Uniform `CriticalMildTerminalNormBound`; whole-space PDE reconstruction is separate |
| `LeiLinCoerciveTerminal.criticalMildTerminalNormBound_of_mixed` | Terminal norm control from mixed control | `CriticalMildMixedTerminalBound` on the actual trajectories |
| `LeiLinCoerciveTerminal.terminal_X1_le_of_trailingMass_and_X2Mass` | Quantitative terminal frequency control | Trailing-time mass and higher-frequency moments, not merely energy |
| `LerayWeak.exists_galerkinLimit_energy_le` | Strong local L2 subsequential limit and inherited energy bound | A `GalerkinApproximation` with its compactness/equicontinuity data |
| `LerayWeak.exists_lerayLimitData_of_weakClauses` | Weak solution data for that limit | Complete weak-form limit passage; weak existence does not imply smoothness |
| `HeatSemigroupSmoothing.heatKernel_convolution_smoothing_le` | Concrete heat smoothing with time decay | Measurable Lr input; Duhamel representation of an arbitrary classical flow is extra work |
| `BealeKatoMajda.exists_fderivSupBound_of_sobolevH3` | Gradient control from H3 on Schwartz slices | Actual H3 and slice-regularity control along a flow |
| Integrated energy, pressure and convection identities | Cancellation and dissipation after spatial integration | Explicit integrability, boundary-flux and time-differentiation hypotheses |
| Exact triads and generated Fourier support | Algebraic transfer, cancellation and leakage tests | A closed full nonlinear construction; one transferring triad is not a self-sustaining cascade |

The energy-only, arbitrary-pressure, bare-integral and small-data-only
obstructions remain useful rejection tests. Removing an admitted theorem or
proving its conditional replacement never supplies its missing analytic input.

## Solver use

The self-contained [`solver/`](../solver/README.md) Rust crate implements the
same periodic rotational Fourier method for CPU, WebAssembly, and WebGPU.
CPU/WASM uses f64 arithmetic; WebGPU uses f32 storage-buffer kernels with
separable Fourier transforms. Both apply componentwise 2/3 dealiasing, Leray
projection, and the same integrating-factor RK4 stages. The browser worker
keeps numerical stepping off the rendering thread and reports the actual
backend. Live fixed-step/CFL runs and adaptive recorded runs are distinct.

The Rust tests compare Taylor–Green trajectories, exact shear decay, Leray
projection, and a manufactured solution with active nonlinearity against the
canonical Python implementation. GPU tests compare velocity and diagnostics
against Rust f64 and include repeatability and warning latching. Run with
`NAVIER_REQUIRE_GPU=1` to require actual device execution. The browser build
records source, toolchain, lockfile, and output hashes in `provenance.json`.

The canonical solver remains `~/reality/solvers/navier`, re-exported by the
existing `~/navier/scripts` entry points. The adaptive IFRK4 path combines
step-doubling error estimation with an independent advective CFL guard and
retains the fixed-step API. Diagnostics cover peak velocity, vorticity, strain,
enstrophy, energy injection/dissipation, and the retained Fourier edge. A
transient underresolution flag is retained even if its final tail decays.
Peak vorticity is integrated by a sampled trapezoidal rule as a BKM-inspired
diagnostic. Its finite numerical value is not a continuum continuation proof.

The paper's core scales motivate separating energy from concentration: for
remaining time τ, radial width is order τ^(1/2), axial width τ^(1/2−h),
and speed τ^(−1/2−h), while energy is order τ^(1/2−3h) for small positive h.
These are diagnostic motivation, not a numerical implementation of the full
vortex construction.

```bash
python3 scripts/navier_adaptive_bench.py --case mms --grids 12 18 24
python3 scripts/navier_adaptive_bench.py --case tgv --grids 12 18 24
```

The new continuum-manufactured test uses pressure zero and
`u=s(t)v`, where `v=(sin x cos y cos z, -cos x sin y cos z, 0)`.
Its force `f=s'v+s²(v·∇)v+3νsv` is derived analytically and never calls the
solver's nonlinear operator to define the answer. It supplements the earlier
discrete manufactured test, which intentionally isolates temporal error.
The finest-grid result is a numerical reference, not ground truth. Temporal
tolerances and a spectral-tail flag are not rigorous continuum error bounds.
No finite-grid run proves or disproves blowup.

The checked default runs (`ν=0.05`, terminal time `0.5`, `rtol=1e-6`,
`atol=1e-9`, tail threshold `1e-8`) gave:

| Grid | Analytic-forcing relative L2 error | Unforced maximum tail fraction | Unforced threshold exceeded |
| --- | --- | --- | --- |
| 12 | 1.336e-6 | 2.988e-4 | yes |
| 18 | 1.011e-6 | 2.884e-7 | yes |
| 24 | 2.252e-7 | 9.619e-9 | no |

Local step tolerances do not bound the accumulated global error. Staying
below this tail threshold alone does not establish spatial convergence.

## Verification

The native port was checked with Lean 4.31.0 in dependency order: 511
construction modules and the 66-module finite-energy comparison closure all
compiled from current source. Raw transitive axiom output for the selected
candidate, comparison theorem, transport endpoint, and final alternative-C
consumer contains only `propext`, `Classical.choice`, and `Quot.sound`.
The audit concerns these named declarations and does not convert the unresolved
alternative A into a theorem. The solver core's 17 tests and this repository's
21 tests passed.

```bash
lake env lean Navier/Breakdown/CompactSmoothForce.lean
lake env lean Navier/Breakdown/CompactPathBreakdown.lean
lake env lean Navier/Breakdown/ConstructedBreakdown.lean
lake env lean Navier/Analysis/ForcedEnergyBalance.lean
lake env lean Navier/ConditionalAudit.lean
python3 -m unittest discover -s tests -v
python3 -m unittest discover -s ../reality/solvers/navier -p 'test_*.py' -v
```

The original A/C endpoints remain distinct: C is constructed here and A remains
open. No external dependency or unverified analytic axiom is added by this
integration.

## Final private review, 2026-09-08

`SelectedCandidateEnergy.lean` now derives a uniform Lebesgue finite-energy
bound for the actual selected Euclidean candidate on `[0,1)`. The construction
uses the energy identity, compact support and Gronwall; its public consumer is
`ConstructedBreakdown.selectedFiniteEnergyCandidate`. This is a pre-singular,
unit-viscosity candidate result, not a smooth continuation through breakdown.
The incremental construction verifier checked the two changed modules in its
613-module source closure and audited all five advertised declarations with
only `propext`, `Classical.choice`, and `Quot.sound`.

The Rust GPU solver exposes `maxSpeed()` through an eight-byte reduction
readback, including a non-finite flag. The interactive worker can therefore
check CFL bounds before and after every step without reading the full field.
Six GPU correctness tests passed on Apple M5 Max Metal. The Python suite now
passes 29 tests, including artifact tampering, complete ABI inventory and
automatic shader provenance coverage. These numerical checks do not certify
the infinite-dimensional PDE solution.
