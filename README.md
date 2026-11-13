# Navier: forced whole-space alternative C (`wholeSpaceBreakdown`) is proved

**The claimed proved object of this repository is forced whole-space alternative
C**, inhabited by the checked Lean theorem
`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown`. **The Clay
Millennium problem — unforced three-dimensional Navier–Stokes existence and
smoothness, alternatives A and B at zero force — is `OPEN`**, in this repository
and in the literature. No theorem, solver result, or picture here proves any
part of it, and nothing on this page should be read as claiming that it does.

Manifest counts, recomputed from [`formalization.yaml`](formalization.yaml) at
this head: 6 `THEOREM`, 4 `OPEN`, 5 `CONDITIONAL_THEOREM`, 15 rows total. The
status summary below states the same claim in table form, and
[`scripts/test_readme_scope_truth.py`](scripts/test_readme_scope_truth.py)
recomputes those counts from the manifest and fails this page if the headline,
either summary, or those numbers drift.

Alongside the proof, the repository is a native Lean reconstruction of OpenAI’s
forced three-dimensional Navier–Stokes breakdown construction, with analytical
continuation criteria and reproducible spectral fluid solvers.

The checked theorem
[`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown`](Navier/Breakdown/ConstructedBreakdown.lean)
inhabits the repository’s original **whole-space alternative C**: for every
positive viscosity, there are admissible initial data and a smooth rapidly
decaying force for which no global smooth bounded-energy classical solution
exists. The proof supplies the constructed candidate and derives comparison
with every hypothetical global competitor. Its transitive axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

Measured today: verified against `f521f79` on 2026-11-13 (source census:
rg over `.lean` outside `.lake`; the central `navier` row is UNMEASURED —
no compiler run at report time): 30002 theorem/lemma declarations, 120
`sorry` token occurrences and 0 sorry sites in tactic/term position across
the library; the two headline files
(`Navier/Breakdown/ConstructedBreakdown.lean`,
`Navier/Analysis/PeriodicConstructedBreakdown.lean`) carry no `sorry`.
The exact-axioms statements above are carried compiler receipts: a fresh
`#print axioms` probe at this date could not run against this checkout
(module olean absent; full `lake build` required), so as of 2026-11-13
the axiom sets of `wholeSpaceBreakdown` and `periodicBreakdown` are
UNCHECKED-at-date — carried, not contradicted. Unforced global regularity
(A, B) remains open, as stated below.

The native **periodic alternative D** is also inhabited by
[`PeriodicConstructedBreakdown.periodicBreakdown`](Navier/Analysis/PeriodicConstructedBreakdown.lean).
For every positive viscosity, the selected periodic construction supplies
admissible forcing excluding every global smooth periodic velocity-pressure
pair. The exact consumer and transitive axioms were independently checked.
Raw compiler receipts are retained locally under `reports/receipts/` and are
excluded from Git history; the proof sources remain reproducible.

The analytical construction is OpenAI’s. The [native source adaptation](docs/OPENAI_CONSTRUCTION_PROVENANCE.md)
pins their released revision, preserves Apache-2.0 notices, and compiles on
this repository’s currently pinned toolchain (`v4.35.0-rc4` in
`lean-toolchain`), authored against 4.31.0 APIs and migrated in `ad12c3d`.
There is no OpenAI Lake dependency.
Awkronos contributes the transport into the original native PDE carrier,
additional force-derivative comparisons, solver work, and interactive explanation.

The separate **unforced global regularity statements A and B remain `OPEN`
here**, and together they are the Clay Millennium problem named above: the
forced construction does not settle either of them.
Comparison before the singular time does not assert uniqueness of a weak
continuation after it. The numerical tools include a finite analytic-axis stage
of the construction and a separate periodic spectral solver. Their computed
fields and residuals are numerical evidence, not the continuum proof. See the
[computed construction method](docs/COMPUTED_AXIS_CONSTRUCTION.md).

The logical shape is easiest to see as two different paths:

```text
FORCED CONSTRUCTION (proved: whole-space alternative C)
selected compact (u, p, f)
  -> smooth, rapidly decaying force
  -> classical solution on 0 <= t < 1 with uniformly bounded energy
  -> uniqueness among smooth finite-energy competitors on every closed slab before t = 1
  -> unbounded speed as t approaches 1
  -> no same-force continuation that is smooth before t = 1, continuous through it,
     and finite-energy on every closed pre-singular slab

UNFORCED REGULARITY (OPEN: the Clay Millennium problem, alternatives A and B)
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
initial reconstruction, a correctly normalized local physical trajectory with
pointwise Fourier balance, classical velocity uniqueness, energy and enstrophy
identities, and local smoothing estimates. It still lacks the arbitrary-data,
horizon-independent critical bound and all-order joint spacetime reconstruction
needed for B. The [result map](docs/RESULT_MAP.md) records that boundary.

## Status summary

| Object | Status claimed by this repository | Manifest row and evidence |
| --- | --- | --- |
| Forced whole-space alternative C, `Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown` | **proved** — this is the claimed object named in the headline | `crown_C_whole_space_forced`, status `THEOREM`, transitive axioms `propext`, `Classical.choice`, `Quot.sound` |
| Forced periodic alternative D, `Navier.Analysis.PeriodicConstructedBreakdown.periodicBreakdown` | proved | `crown_D_periodic_forced`, status `THEOREM` |
| Clay unforced three-dimensional Navier–Stokes Millennium problem: alternatives A (`ProblemStatements.WholeSpaceGlobalRegularity`) and B (`ProblemStatements.PeriodicGlobalRegularity`) at zero force | **`OPEN`** — neither proved nor claimed here | `open_A_whole_space_unforced`, `open_B_periodic_unforced`, status `OPEN` |

Manifest counts recomputed from [`formalization.yaml`](formalization.yaml) at this
head: 6 `THEOREM`, 4 `OPEN`, 5 `CONDITIONAL_THEOREM`, 15 rows total. The structure
behind those numbers is validated by

```bash
python3 scripts/check_formalization.py --check --manifest formalization.yaml --root .
```

and the claim-to-declaration mapping by [`scripts/test_readme_scope_truth.py`](scripts/test_readme_scope_truth.py),
which recomputes the counts and fails if this page stops naming forced
whole-space alternative C (`wholeSpaceBreakdown`) as the proved object, stops
stating that the Clay unforced Navier–Stokes Millennium problem is `OPEN`, or
drifts from the manifest. The `OPEN` rows are the two unforced Millennium
alternatives A and B, the vorticity-rate residual inside the forced
construction (`open_bkm_vorticity_integral_divergence_residual`), and the
mild-assembly time-leaf instantiation (`open_mild_assembly_leaves_instantiation`);
only the first two concern the Clay problem, and the conditional rows are
obligations inside the forced route, not the unforced statement.

## How to cite

If you use this repository, cite it as the project below; if you use a
specific result, cite that result's entry in
[docs/CITATIONS.md](docs/CITATIONS.md), which carries the exact Lean
declaration name, its quantifiers, and what it does and does not claim.
`CITATION.cff` is the machine-readable form of the project citation.

```bibtex
@software{navier2026,
  title  = {Navier: Lean formalization of forced Navier-Stokes breakdown,
            unforced regularity frontiers, and a Rust spectral fluid solver},
  author = {Jacoby, Tim and Awkronos},
  year   = {2026},
  license = {MIT},
  url    = {https://github.com/awkronos/navier}
}
```

**Upstream attribution.** The analytical construction is OpenAI's: the
adapted modules under `Navier/Construction` come from
[`openai/NavierStokesAndEuler`](https://github.com/openai/NavierStokesAndEuler)
at pinned revision `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` (Apache-2.0;
per-file upstream notices are preserved), released with the paper *Finite time
blowup for Navier–Stokes* (2026-09-08,
[cdn.openai.com](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)).
The count is stated twice rather than smoothed: this repository's provenance note
prints 577, while `git ls-tree` at the pinned trunk counts 579 tracked `.lean` files
under `Navier/Construction/`; `docs/CITATIONS.md` carries both measurements.
See [construction provenance](docs/OPENAI_CONSTRUCTION_PROVENANCE.md) for the
adaptation boundary. Awkronos contributes the transport into the original
native PDE carrier, the additional force-derivative comparisons, the solver
work, and the interactive explanation.

**Prior work, by identifier.** The full bibliography with DOIs and URLs is
[`references/manifest.json`](references/manifest.json) (17 sources). The
load-bearing ones: Fefferman, *Existence and Smoothness of the Navier-Stokes
Equation* (2000, [Clay](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf))
for alternatives A–D; Leray (1934, [doi:10.1007/BF02547354](https://doi.org/10.1007/BF02547354))
for the weak-solution boundary; Tao (2016, [doi:10.1090/jams/838](https://doi.org/10.1090/jams/838))
for the averaged-equation barrier that gates every positive route here;
Buckmaster–Vicol (2019, [doi:10.4007/annals.2019.189.1.3](https://doi.org/10.4007/annals.2019.189.1.3))
and Albritton–Brué–Colombo (2022, [doi:10.4007/annals.2022.196.1.3](https://doi.org/10.4007/annals.2022.196.1.3))
for non-uniqueness context. The hydrodynamic-comparison notes cite
Carles–Danchin–Saut (2012, [arXiv:1111.4670](https://arxiv.org/abs/1111.4670)),
Wallström (1994, [doi:10.1103/PhysRevA.49.1613](https://doi.org/10.1103/PhysRevA.49.1613)),
Meng–Yang (2024, [doi:10.1103/PhysRevResearch.6.043130](https://doi.org/10.1103/PhysRevResearch.6.043130)),
Khesin–Misiołek–Modin ([arXiv:1711.00321](https://arxiv.org/abs/1711.00321)),
and Ding–Chung–Illingworth ([doi:10.1017/jfm.2024.1193](https://doi.org/10.1017/jfm.2024.1193)).
Each of those identifiers is already present in the linked documents;
titles and full author lists are carried in the documents that cite them, and
`docs/CITATIONS.md` marks where the repository does not state them.
Its entry ids are the identifier itself, lower-cased because the carrier's
`citation_id` pattern requires lowercase (`doi:10.1103/physreva.49.1613`,
`arxiv:1711.00321`); works the repository's own bibliography carries are id'd by
that row instead (`navier.manifest.leray1934`, `navier.manifest.tao2016`,
`navier.manifest.buckmaster_vicol2019`). Each entry's `stable_link` keeps the
publisher's own capitalisation, so no identifier is rewritten to satisfy the id
pattern — the id is lowercased, the link is not.

**Toolchain.** Lean `leanprover/lean4:v4.35.0-rc4` with Mathlib at
`1f414401f69059aa7eead47b53ee40bd38455eeb` (both pinned in `lean-toolchain`
and `lake-manifest.json`); cite those pins, not a moving branch.

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
[CONTENT-STRATEGY.md](CONTENT-STRATEGY.md) maps this repository's two public
faces (the GitHub repo and the live companion), the link discipline for
`docs/`, and why the Polya relationship stays a Lean-identifier citation,
never a hyperlink.

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

The interactive companion is
[navier.awkronos.com](https://navier.awkronos.com/). It explains the construction
and runs the Rust solver; this repository supplies the exact
[results and open obligations](docs/RESULT_MAP.md),
[triad analysis](docs/TRIADS_AND_SYMMETRY.md), and
[reproducible experiments](solver/README.md).

The [Blender optical pipeline](tools/blender/README.md) imports the live
laboratory’s computed particle paths into an editable Cycles scene. The browser
traces refracted light through local cylindrical approximations of those same
paths; the glass geometry is a visualization of the velocity field.
