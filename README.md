# Navier

A native Lean reconstruction of OpenAI’s forced three-dimensional Navier–Stokes
breakdown construction, with analytical continuation criteria and reproducible
spectral fluid solvers.

The checked theorem
[`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown`](Navier/Breakdown/ConstructedBreakdown.lean)
inhabits the repository’s original **whole-space alternative C**: for every
positive viscosity, there are admissible initial data and a smooth rapidly
decaying force for which no global smooth bounded-energy classical solution
exists. The proof supplies the constructed candidate and derives comparison
with every hypothetical global competitor. Its transitive axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The native **periodic alternative D** is also inhabited by
[`PeriodicConstructedBreakdown.periodicBreakdown`](Navier/Analysis/PeriodicConstructedBreakdown.lean).
For every positive viscosity, the selected periodic construction supplies
admissible forcing excluding every global smooth periodic velocity-pressure
pair. The exact consumer, transitive axioms and all 538 dependency receipts
were independently checked; see the [D receipt](reports/receipts/2026-09-09-periodic-constructed-breakdown/README.md).

The analytical construction is OpenAI’s. The [native source adaptation](docs/OPENAI_CONSTRUCTION_PROVENANCE.md)
pins their released revision, preserves Apache-2.0 notices, and compiles with
this repository’s Lean 4.31.0 toolchain. There is no OpenAI Lake dependency.
Awkronos contributes the transport into the original native PDE carrier,
additional force-derivative comparisons, solver work, and interactive explanation.

The separate **unforced global regularity statements A and B remain open here**.
Comparison before the singular time does not assert uniqueness of a weak
continuation after it. The numerical tools include a finite analytic-axis stage
of the construction and a separate periodic spectral solver. Their computed
fields and residuals are numerical evidence, not the continuum proof. See the
[computed construction method](docs/COMPUTED_AXIS_CONSTRUCTION.md).

The logical shape is easiest to see as two different paths:

```text
FORCED CONSTRUCTION (proved)
selected compact (u, p, f)
  -> smooth, rapidly decaying force
  -> classical solution on 0 <= t < 1 with uniformly bounded energy
  -> uniqueness among smooth finite-energy competitors on every closed slab before t = 1
  -> unbounded speed as t approaches 1
  -> no same-force continuation that is smooth before t = 1, continuous through it,
     and finite-energy on every closed pre-singular slab

UNFORCED REGULARITY (open)
every admissible u0, with f = 0
  -> local classical solution                                  [native input required]
  -> continuation controlled by one critical quantity           [native input required]
  -> a uniform bound for that quantity, for arbitrary large data    [missing]
  -> global smooth bounded-energy solution
```

“Globally smooth” in the completed result applies to the **force**. The
constructed velocity is smooth on every pre-singular time interval and is
proved not to possess a global classical continuation satisfying the official
energy contract. This distinction is part of the theorem types, not a prose
caveat.

The terminal obstruction is stronger than the global endpoint needs: the
excluded competitor may choose a different finite energy bound on each closed
pre-singular slab. No single energy constant uniform as the slabs approach the
deadline is assumed.

The periodic research now has checked native Fourier initialization and exact
initial reconstruction, classical velocity uniqueness, energy and enstrophy
identities, and local smoothing estimates for the raw complex mild equation.
Its physical evolution bridge is under repair: raw convolution must be related
to the physical Fourier equation through an explicit phase, amplitude and
viscosity normalization. The [result map](docs/RESULT_MAP.md) records this
boundary and the still-unproved arbitrary-data global estimate.

## Mathematics

| Entry point | Content |
| --- | --- |
| [Problem.lean](Navier/Problem.lean), [OfficialProblem.lean](Navier/OfficialProblem.lean) | Exact PDE, data, smoothness, energy, and alternative statements |
| [ConstructedBreakdown.lean](Navier/Breakdown/ConstructedBreakdown.lean) | Constructed C endpoint and bounds for successive coordinate partials |
| [ConstructedFiniteTimeObstruction.lean](Navier/Analysis/ConstructedFiniteTimeObstruction.lean) | One selected witness carrying finite energy, slab uniqueness, compact support, and terminal nonextension |
| [EuclideanPDETransport.lean](Navier/Analysis/EuclideanPDETransport.lean) | Coordinate isometry, derivatives, energy, and force transport |
| [R3FiniteEnergyComparison.lean](Navier/Construction/R3FiniteEnergyComparison.lean) | Comparison on every pre-singular time interval |
| [ForceRecursivePartials.lean](Navier/Analysis/ForceRecursivePartials.lean) | Actual successive differentiation versus multilinear jets, including the initial boundary |
| [ForceCoordinateEquivalence.lean](Navier/Analysis/ForceCoordinateEquivalence.lean) | Exact equivalence between the force predicate and decay of every genuine ordered coordinate partial |
| [ConstructedForceExtension.lean](Navier/Analysis/ConstructedForceExtension.lean) | The selected force is globally smooth across time zero at every positive viscosity |
| [ConditionalAudit.lean](Navier/ConditionalAudit.lean) | Selected theorem types and raw transitive axioms |
| [Result and frontier map](docs/RESULT_MAP.md) | Authoritative claim-to-declaration map, trust evidence, and current status |
| [Native mathematics and solver guide](docs/NATIVE_BREAKDOWN_AND_SOLVER.md) | Detailed construction, useful conditional results, and numerical validation |
| [Documentation index](docs/README.md) | Current evidence, open obligations, interpretation notes, and historical records |

[Formalization conventions](docs/FORMALIZATION.md), the
[construction carrier review](docs/CONSTRUCTION_REVIEW.md), the
[open-obligation map](docs/OPEN_FRONTIER_MAP.md), and the
[falsification ledger](docs/FALSIFICATION_LEDGER.md) preserve the distinction
between completed endpoints, conditional estimates, and rejected approaches.

## Reproduce the proof

With the pinned Lean toolchain and Mathlib cache installed as described in
[REPRODUCIBILITY.md](REPRODUCIBILITY.md):

```bash
python3 scripts/verify_construction.py
```

The verifier compiles the endpoint’s local source dependencies in order and
prints its exact type and raw axiom closure. Receipts include source and
dependency fingerprints; source parsing determines build order, never proof
status. Existing `.olean` files alone are not evidence of a current source check.

## Run the solver

[`solver/`](solver/README.md) contains the Rust crate and browser build. Its
Fourier method uses the rotational nonlinearity, Leray projection, componentwise
2/3 dealiasing, and integrating-factor RK4. CPU/WASM and WebGPU backends identify
their precision and diagnostics explicitly.

```bash
cd solver
cargo test
cargo build --release --target wasm32-unknown-unknown
```

The Python adaptive solver remains canonical in the Reality development
workspace. [`scripts/build_solver_release.py`](scripts/build_solver_release.py)
exports a deterministic standalone bundle with provenance and tests, so a
release does not require access to that private workspace. The Rust crate is
self-contained and tested against independently generated Python fixtures.

The pop-science companion is prepared for `navier.awkronos.com` in the Awkronos
Hub. The repository and website remain private pending publication review.
