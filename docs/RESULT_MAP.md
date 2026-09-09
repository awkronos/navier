# Result and frontier map

This page maps each research claim to the declaration that actually carries
it. The theorem type fixes the scope. Compiler acceptance and the raw
transitive axiom list establish formal closure; neither can turn a forced
counterexample into an unforced all-data regularity theorem.

## The two endpoints

| Question | Exact Lean surface | Quantifiers and force | Status |
| --- | --- | --- | --- |
| Can one choose admissible data and forcing for which no global classical solution exists? | `Navier.ProblemStatements.WholeSpaceBreakdown` | For every `nu > 0`, there exist a divergence-free Schwartz datum and a rapidly decaying smooth force such that no global `IsClassicalSolution` exists | **THEOREM**, inhabited by `ConstructedBreakdown.wholeSpaceBreakdown` |
| Does every admissible datum produce a global classical solution with no force? | `Navier.ProblemStatements.WholeSpaceGlobalRegularity` | For every `nu > 0` and every divergence-free Schwartz datum, there exist global velocity and pressure fields satisfying `IsClassicalSolution nu zeroForce` | **OPEN** in this repository |

The completed endpoint is the whole-space forced alternative C in the official
problem statement. It is mathematically substantive: the proof constructs the
data and force, supplies a pre-singular classical candidate, and rules out every
hypothetical global smooth bounded-energy competitor. It does not select one
solution from several weak continuations, and it does not prove a global smooth
velocity.

## Completed forced path

| Claim | Proof-bearing declaration | Premise carried by its type | Fresh verification surface |
| --- | --- | --- | --- |
| A compact Euclidean candidate exists | `R3CompactCandidate.selected_compact_candidate` | None | `ConditionalAudit.lean`; raw axioms |
| Every admissible global competitor contradicts that candidate | `ComparatorBridge.compact_candidate_excludes_global_solution` | An actual candidate and an actual `GlobalSolutionRn` competitor | `ConditionalAudit.lean`; raw axioms |
| Euclidean construction data inhabit the native whole-space C carrier | `NativeConstructionEndpoint.wholeSpaceBreakdown_of_compactCandidate` | An actual compact candidate | `ConditionalAudit.lean`; raw axioms |
| The selected construction proves C for every positive viscosity | `ConstructedBreakdown.wholeSpaceBreakdown` | None | Direct single-file source compile plus raw axioms |
| The chosen force is smooth on all real spacetime and has an explicit half-space extension | `ConstructedForceExtension.constructedWholeSpaceBreakdownWithGloballySmoothForce` | None | `ConditionalAudit.lean`; raw axioms |
| Every ordered successive coordinate derivative of the chosen force obeys the required weighted bound | `ConstructedBreakdown.wholeSpaceBreakdown_with_successivePartials` | `nu > 0` | `ConditionalAudit.lean`; raw axioms |
| The formal Fréchet-bundle force condition is equivalent to smoothness plus decay of every genuine ordered coordinate partial | `ForceCoordinateEquivalence.forcedDataRapidDecay_iff_successivePartials` | A concrete force `f`; smoothness is explicit on the coordinate-partial side | Direct single-file compile plus raw axioms |
| The selected globally smooth force has compact support on physical spacetime and vanishes after a finite time | `ConstructedFiniteTimeObstruction.selected_force_has_compact_physical_support` | None; spatial support is asserted for `t ≥ 0`, with a finite future cutoff | Direct single-file source compile plus raw axioms |
| The selected force is nonzero somewhere strictly before the unit-viscosity deadline | `ConstructedFiniteTimeObstruction.selected_force_nonzero_before_one` | None; `∃ t ∈ (0,1), ∃ x, f(t,x) ≠ 0` | Direct single-file source compile plus raw axioms |
| The selected unit-viscosity candidate has uniformly finite energy before its deadline | `ConstructedBreakdown.selectedFiniteEnergyCandidate` | None; interval is `Set.Ico 0 1` | `ConditionalAudit.lean`; raw axioms |
| One selected witness simultaneously has a globally smooth force, pre-singular finite energy, compact spatial support, no continuous terminal extension on its support, and slab uniqueness | `ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile` | None | Dependency-ordered source rebuild plus raw axioms |
| Every compact candidate is unique against a smooth finite-energy competitor on a closed pre-singular slab | `ComparatorBridge.compact_candidate_unique_on_Icc` | Candidate properties and the competitor's local smoothness, energy, divergence, PDE and zero initial data on that slab | Dependency-ordered source rebuild plus raw axioms |
| Every same-force competitor smooth before time one and finite-energy on each closed earlier slab develops unbounded speed at that deadline | `ConstructedFiniteTimeObstruction.selected_candidate_forces_speed_blowup_in_every_smooth_competitor` | None for the selected witness; the competitor class is explicit and no terminal trace is assumed | Direct single-file source compile plus raw axioms |
| The selected witness excludes a same-force continuation smooth before the deadline and continuous through it, even when energy is assumed only separately on each closed pre-singular slab | `ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation` | None | Direct single-file source compile plus raw axioms |

All named completed declarations above currently report only `propext`,
`Classical.choice`, and `Quot.sound`. The source attribution and adaptation
boundary are recorded in
[OpenAI construction provenance](OPENAI_CONSTRUCTION_PROVENANCE.md).

The reverse force estimate is quantitative: if every ordered coordinate word
of length `n` is bounded by `C`, the full iterated Fréchet operator norm is
bounded by `4^n C`, expressed in Lean as the cardinality of the four-direction
word space. All orderings are already quantified. No extra claim that merely
smooth within-derivatives commute under arbitrary permutations is needed or
made.

## What “smooth” and “unique” mean here

There are four separate statements that should not be collapsed:

1. The selected **force** has a globally smooth spacetime extension.
2. The selected **velocity and pressure** solve the classical equation on each
   time slab strictly before the singular deadline and the velocity has one
   uniform finite-energy bound on the whole half-open interval `[0,1)`.
3. Slab uniqueness compares against any competitor that is smooth and
   finite-energy on that closed slab; it does not require the competitor to be
   global or spatially compact.
4. The selected velocity admits no continuous extension through time one even
   on its own fixed compact spatial support. In particular, a hypothetical
   global classical competitor cannot agree with it on all pre-singular times.

The positive speed-transfer theorem first forces every competitor in this class
to have arbitrarily large speed arbitrarily close to time one, without assuming
any terminal trace. The continuous-extension obstruction then excludes a regular
terminal velocity on the compact occupied region. See
[the exact force and regularity note](EXACT_FORCE_AND_REGULARITY.md) for the
cutoff formula, viscosity scaling, future-time support, and full quantifiers.

The strongest checked continuation obstruction does not assume one competitor
energy bound uniform all the way to time one. It assumes only a finite bound on
each fixed closed slab `[0,T]`, allows that bound to deteriorate as `T` tends to
one, and still derives a contradiction from pre-singular uniqueness and
terminal continuity.

The proof therefore establishes nonexistence of a global classical competitor
for the selected forced data. It does not establish uniqueness among all weak
solutions after the singular time.

## Sharp path toward unforced global regularity

The closest whole-space native consumer is
`CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_continuation_apriori`:

```text
LocalClassicalExistence
        +
NormalizedContinuationFromCriticalControl N
        +
APrioriCriticalControl N
        |
        v
WholeSpaceGlobalRegularity
```

The theorem glues pressure-normalized finite-energy classical pieces into the
exact unforced endpoint, but all three analytic inputs remain hypotheses. They
must be proved for one and the same physical critical quantity `N`.

The Fourier-lattice restart program isolates a more quantitative bottleneck.
`CriticalMildTerminalNormBound` asks for one horizon-independent terminal norm
bound for every finite original-data mild chart. The sharper
`LeiLinCoerciveTerminal.CriticalMildMixedTerminalBound` implies that bound by a
proved coercive estimate. What remains is to prove the mixed bound for arbitrary
large data and then transport the lattice mild object to the exact whole-space
velocity, pressure, smoothness, PDE and energy carrier. The existing scalar
heat/Duhamel majorant cannot supply a fixed positive invariant radius by itself;
`GlobalRegularityCrownCore.not_restart_scalar_budget_le_fixed_radius` proves
that obstruction at its exact type.

This frontier is useful because it identifies the nonlinear estimate that must
do new work. It is not a reformulation that assumes the desired global
solution.

## Numerical boundary

The Rust CPU/WASM/WebGPU solver evolves ordinary periodic spectral flows. Its
tests can validate implementation identities, convergence behavior and finite
resolution diagnostics. No finite grid establishes a universal regularity or
blowup theorem, and the solver is not an implementation of the full analytic
counterexample construction.

For the final dependency-ordered rebuild, compiled-object hashes and raw eleven-
endpoint audit, see
[`reports/receipts/2026-09-08-constructed-c-final/README.md`](../reports/receipts/2026-09-08-constructed-c-final/README.md).
The earlier [baseline receipt](../reports/receipts/2026-09-08-constructed-c-baseline/README.md)
preserves the pre-enhancement endpoint snapshot.

The [Madelung correspondence note](MADELUNG_CORRESPONDENCE.md) records the
scalar and spinor relationships, a conditional reconstruction obstruction, and
the exact additional inputs needed for a wavefunction lift. It is analytical
discussion, not an added Lean theorem or a proved quantum consequence.

[Breakdown, uniqueness, and concentration](DYNAMICS_AND_CONCENTRATION.md)
explains the exact comparison class, the finite-energy volume bound for fast
regions, and why concentration does not mean compression of fluid density.

The [2026-09-09 release recheck](../reports/receipts/2026-09-09-release-check/README.md)
binds all 615 current source/object hashes and repeats the eleven raw axiom
audits after the final artifact cleanup.
