# Result and frontier map

This page maps each research claim to the declaration that actually carries
it. The theorem type fixes the scope. Compiler acceptance and the raw
transitive axiom list establish formal closure; neither can turn a forced
counterexample into an unforced all-data regularity theorem.

The separate [quantization, regularity, and Wick-rotation note](QUANTIZATION_REGULARITY_WICK.md)
maps four native comparison modules to explicit examples: smooth wavefunctions
with singular decoded velocity, integer circulation and phase-lift obstruction,
smooth zero-set fold events, and loss of heat damping under imaginary time.
These comparisons do not inhabit A or B.

## Existence and breakdown endpoints

The active global-regularity construction targets are the exact A and B propositions.
Current open statuses report evidence and do not constrain future proofs.
The A route constructs native whole-space evolution; the B routes construct
physical Fourier reconstruction, positive-time regularity and global control;
The D construction now directly consumes the selected periodic candidate and
preserves every clause of the native periodic contract.

| Question | Exact Lean surface | Quantifiers and force | Status |
| --- | --- | --- | --- |
| Can one choose admissible data and forcing for which no global classical solution exists? | `Navier.ProblemStatements.WholeSpaceBreakdown` | For every `nu > 0`, there exist a divergence-free Schwartz datum and a rapidly decaying smooth force such that no global `IsClassicalSolution` exists | **THEOREM**, inhabited by `ConstructedBreakdown.wholeSpaceBreakdown` |
| Can admissible periodic forcing prevent every global smooth periodic solution? | `Navier.ProblemStatements.PeriodicBreakdown` | For every `nu > 0`, there exist an admissible periodic datum and smooth periodic time-decaying force excluding every global `IsPeriodicClassicalSolution` | **THEOREM**, inhabited by `PeriodicConstructedBreakdown.periodicBreakdown` |
| Does every admissible datum produce a global classical solution with no force? | `Navier.ProblemStatements.WholeSpaceGlobalRegularity` | For every `nu > 0` and every divergence-free Schwartz datum, there exist global velocity and pressure fields satisfying `IsClassicalSolution nu zeroForce` | **OPEN** in this repository |

The periodic unforced existence proposition
`Navier.ProblemStatements.PeriodicGlobalRegularity` (alternative B) also remains
open. A new [periodic classical uniqueness theorem](../Navier/Analysis/PeriodicClassicalUniqueness.lean)
proves equality of velocities at every positive viscosity under the native
classical contract, including **periodic velocity and periodic pressure**.
It consumes an assumed B witness to attach this proved uniqueness conclusion;
it does not discharge B's existence premise. No equality of pressures is
claimed, since a spatially constant pressure gauge remains free.

The checked [mean-drift algebra](../Navier/Analysis/CriticalMildMeanDriftRemoval.lean)
constructs the raw encoding `A=-2*pi*i*u_hat`, proves literal convolution phase
covariance, and identifies the constant-mean cross term and its cancellation
with the translation derivative. It preserves the off-zero amplitude, squared
energy and half-generator moment. The full time-integrated fixed-point
transport is a further construction; these coefficient identities do not
assume or establish arbitrary-data global control.

The completed forced endpoints are whole-space C and periodic D in the official
problem statement. The proof constructs the
data and force, supplies a pre-singular classical candidate, and rules out every
hypothetical global smooth bounded-energy competitor. It does not select one
solution from several weak continuations, and it does not prove a global smooth
velocity.

The [native D proof](../Navier/Analysis/PeriodicConstructedBreakdown.lean)
uses the selected unit-periodic candidate directly. Smooth forcing with a
uniform future cutoff has all required polynomially time-weighted derivative
bounds, by continuity on a compact time slab and fundamental spatial cell.
Every hypothetical native competitor transports to the construction's exact
same-force comparison class, including periodic pressure. The viscosity
equivalence supplies every positive viscosity. See the
[fresh D receipt](../reports/receipts/2026-09-09-periodic-constructed-breakdown/README.md).

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

## Periodic evolution: checked providers and the remaining consumer

**Normalization repair in progress.** The raw lattice interaction is a complex
bilinear dot-product convolution, and its mild equation adds that interaction.
The physical period-one Fourier equation instead requires `-2πi` times the
projected convolution and heat rate `ν(2π)²|k|²`. Consequently the unrotated
Fourier datum is not yet a valid physical evolution initializer. The active
repair is the explicit change `A=-2πi û`, `μ=(2π)²ν`, with inverse
`û=iA/(2π)`. Raw A then requires anti-Hermitian symmetry. The algebra and
time-dependent reconstruction are being proved, not assumed here. A bound for
every complex raw datum may be too strong; its exact quantifiers are under
counterexample audit. This does not affect the forced-C construction.

Fresh source compilers and raw axiom audits are in
[the periodic-evolution receipt](../reports/receipts/2026-09-09-periodic-evolution/README.md).
The [LSP endpoint examination](../reports/receipts/2026-09-09-regularity-status/README.md)
separately records A/B/C/D, construction constraints, and the exact remaining
terminal-bound quantifiers.

| Mathematical step | Native source | Exact scope |
| --- | --- | --- |
| Literal Fourier initialization | [PeriodicDatumFourierBridge](../Navier/Analysis/PeriodicDatumFourierBridge.lean), [PeriodicDatumFourierConstraints](../Navier/Analysis/PeriodicDatumFourierConstraints.lean) | Every native smooth periodic datum has summable weighted coefficients; divergence freedom and Hermitian reality hold for the canonical initialized carrier. |
| Exact initial reconstruction | [PeriodicNativeFourierInversion](../Navier/Analysis/PeriodicNativeFourierInversion.lean) | `nativeInitialReconstruction u₀ hu₀ = u₀`, with no inversion hypothesis. This closes the initial-data identity, not subsequent evolution. |
| Physical Fourier reconstruction | [PeriodicFourierReconstruction](../Navier/Analysis/PeriodicFourierReconstruction.lean) | A weighted carrier gives a continuous periodic field; Hermitian coefficients give a real field. Higher derivatives require additional moment control. |
| Pressure recovery | [PeriodicPressureRecovery](../Navier/Analysis/PeriodicPressureRecovery.lean) | Explicit pressure coefficients restore the unprojected mode equation from the projected one, with period-one `2π` factors. Time-dependent physical PDE realization remains to be consumed. |
| Native energy dissipation | [PeriodicNativeEnergyBalance](../Navier/Analysis/PeriodicNativeEnergyBalance.lean) | Every assumed native unforced periodic classical solution satisfies `K(T)+ν∫₀ᵀD=K(0)` and `∫₀ᵀD≤K(0)/ν`. It does not assert existence. |
| Native enstrophy evolution | [PeriodicEnstrophyControl](../Navier/Analysis/PeriodicEnstrophyControl.lean) | Derives `Z′=S−νDω` from the native physical PDE, with exact vortex stretching S. An actual cellwise gradient bound G gives `Z′+νDω≤2GZ`; control of G or depleted stretching remains required. |
| Moving-frame transport | [PeriodicGalileanReduction](../Navier/Analysis/PeriodicGalileanReduction.lean) | The actual velocity `u(t,x+tc)-c` and translated pressure preserve the complete native periodic classical contract; subtracting a constant datum changes neither existence nor viscosity. |
| Mean conservation and sharper terminal premise | [CriticalMildZeroMode](../Navier/Analysis/CriticalMildZeroMode.lean) | The original-data mild chart preserves its zero mode. A horizon-independent bound on only the nonzero modes feeds cofinal global mild continuation. The bound remains a hypothesis. |
| Lag-separated smoothing | [CriticalMildPositiveTimeSmoothing](../Navier/Analysis/CriticalMildPositiveTimeSmoothing.lean) | The resolved Duhamel history has half-generator moment control for positive lag. The unestimated terminal strip is explicit. |
| Dynamic endpoint cancellation | [PeriodicDynamicCriticalTail](../Navier/Analysis/PeriodicDynamicCriticalTail.lean) | The actual frozen nonlinear integral has moment at most `ν⁻¹‖u(T)‖²`; the evolving term has graph membership and a quantitative bound under an explicit Dini integral. |
| Interior time modulus | [CriticalMildInteriorTimeModulus](../Navier/Analysis/CriticalMildInteriorTimeModulus.lean) | The actual bounded mild equation derives a local quarter-Hölder modulus and terminal-window Dini integrability. Constants depend on observation time and chart radius. |
| Full positive-time raw smoothing | [CriticalMildFullPositiveTimeRegularity](../Navier/Analysis/CriticalMildFullPositiveTimeRegularity.lean) | Consumes the Dini window and frozen-source estimate to derive full half-generator membership, an explicit local bound and two-spatial-derivative coefficient summability. Higher moments/time jets and the physical decoder remain separate inputs. |
| Higher positive-time moments | [CriticalMildHigherMomentBootstrap](../Navier/Analysis/CriticalMildHigherMomentBootstrap.lean), [CriticalMildHigherUniformMoments](../Navier/Analysis/CriticalMildHigherUniformMoments.lean) | The actual bounded mild trajectory has uniform polynomial Fourier moments of every spatial order on each compact positive-time interval. Bounds depend on the interval and chart radius. All time jets and the full classical spacetime bridge remain to be constructed. |
| Evolving coefficient equation | [CriticalMildModeDifferentiation](../Navier/Analysis/CriticalMildModeDifferentiation.lean) | Differentiates the actual Duhamel equation and proves the normalized physical unprojected Fourier coefficient equation with recovered pressure. Passing the series to the full pointwise PDE remains separate. |
| Raw complex control obstruction | [PeriodicGlobalCriticalControl](../Navier/Analysis/PeriodicGlobalCriticalControl.lean) | An exact exponentially growing two-mode mild trajectory refutes unrestricted raw terminal bounds. Its nonzero real mean violates physical anti-Hermitian reality; physical periodic B remains open. |
| Reality of the constructed trajectory | [CriticalMildTrajectoryReality](../Navier/Analysis/CriticalMildTrajectoryReality.lean) | Constructs the contraction fixed point in a closed anti-Hermitian subspace, consumes Bochner reality preservation, and proves exact real physical Fourier reconstruction. |
| First joint evolving regularity | [CriticalMildSmoothBootstrap](../Navier/Analysis/CriticalMildSmoothBootstrap.lean) | The actual positive-time mild trajectory has decoded 2.25 spatial summability, summable mode time derivatives and pressure gradients, and the physical coefficient equation. Uniform all-order jets remain open. |
| Physical local evolution | [PhysicalLocalEvolution](../Navier/Analysis/PhysicalLocalEvolution.lean) | For every physical divergence-free weighted datum, constructs a positive local interval and the same real trajectory carrying the initial value, evolving summability, coefficient derivatives and physical mode equation. No evolving trajectory premise is assumed. |
| Official periodic initial data | [PeriodicInitialPhysicalEvolution](../Navier/Analysis/PeriodicInitialPhysicalEvolution.lean) | Every official smooth periodic datum has all polynomial Fourier moments and initializes the actual local physical trajectory through the exact raw encoding, with the original datum reconstructed at time zero. |
| Pointwise Fourier balance | [PeriodicNonlinearFourierReconstruction](../Navier/Analysis/PeriodicNonlinearFourierReconstruction.lean) | Reindexes the actual absolutely convergent nonlinear product, reconstructs pressure-gradient coefficients, and supplies pointwise Fourier balance for the constructed local trajectory. Global continuation and the full classical smoothness bridge remain open. |
| Uniform positive-interval estimates | [CriticalMildLocalUniformBootstrap](../Navier/Analysis/CriticalMildLocalUniformBootstrap.lean) | Derives one bound for second spatial moments and total coefficient time-derivative mass throughout each compact positive-time interval. Constants still depend on the local trajectory bound. |
| Polynomial nonlinear moments | [CriticalMildPolynomialMomentConvolution](../Navier/Analysis/CriticalMildPolynomialMomentConvolution.lean) | The literal projected convolution maps two order-s moments to an order-(s−1) bound for every real s ≥ 1. Propagation of all orders is a separate evolving-flow argument. |
| Countable energy differentiation | [RawHighEnergyDifferentiation](../Navier/Analysis/RawHighEnergyDifferentiation.lean), [CriticalMildEnergyEvolution](../Navier/Analysis/CriticalMildEnergyEvolution.lean) | Proves uniform convergence of finite energy-derivative sums using an inverse-frequency tail estimate, then differentiates the actual mild trajectory's countable high-frequency energy. No energy derivative is assumed. |
| Frequency-local energy transfer | [PhysicalPeriodicHighTailFlux](../Navier/Analysis/PhysicalPeriodicHighTailFlux.lean), [RawHighEnergyConvolutionIdentity](../Navier/Analysis/RawHighEnergyConvolutionIdentity.lean), [PhysicalPeriodicTailMomentControl](../Navier/Analysis/PhysicalPeriodicTailMomentControl.lean) | Identifies the actual nonlinear pairing sum with triad flux and bounds the damped generator by the evolving high-frequency tail. The affine comparison still requires bounds on the evolving critical norm and moment; it supplies no arbitrary-data global estimate. |
| Actual spectral energy balance | [RawHighEnergyRateIdentity](../Navier/Analysis/RawHighEnergyRateIdentity.lean), [PhysicalPeriodicEnergyBalance](../Navier/Analysis/PhysicalPeriodicEnergyBalance.lean) | Combines countable differentiation with the literal nonlinear identity to prove `dE_N/dt = 2 flux_N − 2μ D_N` along the actual mild trajectory on each positive local interval. |
| Actual finite-window high-energy estimate | [PhysicalPeriodicHighEnergyWindow](../Navier/Analysis/PhysicalPeriodicHighEnergyWindow.lean), [PhysicalPeriodicHighEnergyContinuity](../Navier/Analysis/PhysicalPeriodicHighEnergyContinuity.lean), [PhysicalPeriodicHighEnergyBootstrap](../Navier/Analysis/PhysicalPeriodicHighEnergyBootstrap.lean) | Derives the evolving energy continuity and moment budget internally, then proves exponential decay plus an explicit `4 R² H/(μ N³)` bound on positive time windows. The chart radius and budget are not controlled uniformly over all future horizons. |
| Weighted nonlinear cancellation | [PhysicalPeriodicWeightedFluxCommutator](../Navier/Analysis/PhysicalPeriodicWeightedFluxCommutator.lean) | Exact paired triad cancellation leaves an output-weight difference, bounded by the advecting frequency. The countable commutator is bounded by two carrier factors and a higher moment, without a proved coercive sign. |
| Whole-space heat test approximation | [WholeSpaceSolenoidalHeatApproximation](../Navier/Analysis/WholeSpaceSolenoidalHeatApproximation.lean), [WholeSpaceSolenoidalHeatDomination](../Navier/Analysis/WholeSpaceSolenoidalHeatDomination.lean) | Constructs compact divergence-free heat test approximants, proves cutoff derivative rates through order three, and derives a Gaussian convection-tail estimate from initial energy. Full derivative-envelope assembly, passage through time integrals, and Leray/Oseen representation remain open. |
| Physical energy cancellation | [PhysicalPeriodicGlobalControl](../Navier/Analysis/PhysicalPeriodicGlobalControl.lean), [PhysicalPeriodicEnergyEvolution](../Navier/Analysis/PhysicalPeriodicEnergyEvolution.lean) | Physical mean drift is skew; the absolutely summable countable projected triad energy series cancels exactly. This controls the energy-transfer algebra, not the global critical norm. |
| Energy versus fine-scale control | [PeriodicEnergyCriticalObstruction](../Navier/Analysis/PeriodicEnergyCriticalObstruction.lean) | Fixed-energy transverse mode examples have unbounded mixed critical quantity. This refutes a universal energy-only estimate over arbitrary fields, not a bound restricted to actual trajectories. |

The physical global-control target is:

```text
for every viscosity ν > 0 and physically initialized datum a,
there exists a finite K(ν,a), independent of horizon T and chart radius R,
such that every actual original-data mild chart satisfies
  offZeroMixedCriticalQty ν (u(T)) ≤ K(ν,a).
```

Local Hölder regularity and a finite Dini integral on each chart do not yield
this uniform K: their constants may grow with the chart radius. The active
proof lanes address the physically initialized class, nonlinear stretching, mean-drift removal,
and exact reconstruction of the evolving coefficients under the normalization
above. Bounds proved for the raw complex equation are not automatically
bounds for the native physical initialization.
Neither A nor B is counted as closed by these providers. The unrestricted raw
complex target is false; its checked counterexample and the evolving-flow
results are recorded in the [fresh verification receipt](../reports/receipts/2026-09-09-evolving-flow/README.md).

## Numerical boundary

The Rust crate has two separate numerical surfaces. `AxisConstruction`
evaluates a finite radial-series approximation to the analytic-axis profile,
reconstructs velocity and pressure in its bounded similarity chart, and
measures the profile-equation defects, divergence defect, and momentum
residual. The CPU/WASM/WebGPU spectral solver separately evolves ordinary
periodic flows. The [computed-construction note](COMPUTED_AXIS_CONSTRUCTION.md)
records the exact equations, defaults, sampled domain, and omitted correction
layers.

The axis evaluator does not implement the annular matching, Borel background,
covariance waves, correction cycles, or final spacetime localization that make
the selected force globally smooth. Its displayed momentum residual is the
force required by the finite reconstructed field, not the selected force of
`ConstructedBreakdown.wholeSpaceBreakdown`. Tests can validate implementation
identities and finite-resolution behavior. No finite grid, residual sample, or
visual trajectory establishes a continuum regularity or breakdown theorem.

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

The [physical local evolution receipt](../reports/receipts/2026-09-09-physical-local-evolution/README.md) records the subsequent native verification and numerical phase/energy regressions.
