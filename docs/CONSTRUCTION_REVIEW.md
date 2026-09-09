# Carrier comparison for the constructed whole-space endpoint

The public theorem `Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown`
has the original type `Navier.ProblemStatements.WholeSpaceBreakdown`. The
construction, comparison argument, coordinate transport, and viscosity scaling
supply its proof without an additional analytic premise.

This review checks the connection between the formal carrier and the clauses
in [Fefferman’s official problem](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf).
It is an internal formalization review, not an external referee report or an
assessment of eligibility for a prize.

| Clause | Evidence in this repository |
| --- | --- |
| Every positive viscosity | `ViscosityEndpoints.wholeSpaceBreakdown_iff_atViscosityOne` and the explicit scaled construction in `ConstructedForceExtension` |
| Smooth divergence-free rapidly decaying initial data | The construction starts with the zero Schwartz velocity; its scaled datum remains admissible |
| Smooth force, including time zero | `ConstructedForceExtension.selected_compact_candidate_contDiff` extracts global smoothness from the actual selected construction, then proves localization, coordinate transport, and viscosity scaling preserve it |
| Smooth extension across the initial boundary | `constructedWholeSpaceBreakdownWithGloballySmoothForce` supplies the globally defined force itself as an explicit `HalfSpaceSmoothExtension`; it does not assume Seeley’s theorem |
| All weighted derivative bounds | Compact spatial and future-time support imply `ForcedDataRapidDecay`; `OfficialCDEncoding` transports the bounds to Euclidean coordinate weights |
| Successive mixed partials | `ForceRecursivePartials.successivePartialWithin_eq_iteratedFDerivWithin` proves that recursively differentiating the function agrees with multilinear-jet evaluation; the resulting estimates cover every ordered coordinate family |
| Original differential equation | `EuclideanPDETransport` proves the time derivative, spatial derivative, divergence, convection, Laplacian, and pressure-gradient identities on the faithful native and Euclidean carriers |
| Finite and uniformly bounded energy | Integrability is explicit, so Lean’s totalized integral cannot make this clause vacuous; the coordinate isometry and Euclidean energy comparison transport the original energy requirement |
| Every hypothetical global competitor | `R3FiniteEnergyComparison` derives agreement before the singular time without assuming compact support or pressure decay of the competitor |
| No globally smooth bounded-energy solution | Agreement contradicts the constructed unbounded velocity on a fixed compact region, where a global smooth competitor would be bounded |

## Boundary conventions

The native PDE uses the right-within derivative at `t = 0`. On positive time
this agrees with ordinary differentiation. For the selected force, the proved
global smooth extension also supplies the stronger two-sided interpretation at
the initial boundary.

The force estimates quantify over every ordered family of coordinate
directions. Consequently they bound any prescribed ordering of
`∂x^α ∂t^m`; they do not need a theorem that arbitrary multilinear maps are
symmetric. The earlier order-sensitive multilinear counterexample remains
valid, but does not obstruct these actual-derivative estimates.

For hypothetical solutions, an extension-based reading of smoothness on the
closed half-space implies the within-smooth predicate that the endpoint
excludes. The exclusion therefore does not require the converse general
half-space extension theorem.

## Trust and scope

Fresh source compilation and raw fully qualified `#print axioms` for the
selected candidate, comparison, global-force extension, recursive partials,
and original C endpoint report only `propext`, `Classical.choice`, and
`Quot.sound`. `scripts/verify_construction.py` rebuilds the source closure and
repeats the endpoint audit with fingerprinted receipts.

The analytical construction is adapted from OpenAI’s pinned source, with
license and modification notices retained. The result is forced whole-space
alternative C. This native endpoint does not establish periodic D, unforced
A/B, or uniqueness of a non-smooth continuation after the singular time.
