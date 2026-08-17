# Open frontier map: checked leaves and exact open obligations

## Verdict

The formal support graph has advanced materially, but the three-dimensional
Navier--Stokes Navier--Stokes problem is not solved.  There is still no term
inhabiting `Navier.ProblemStatements.WholeSpaceGlobalRegularity`, `Navier.ProblemStatements.PeriodicGlobalRegularity`, `Navier.ProblemStatements.WholeSpaceBreakdown`, or
`Navier.ProblemStatements.PeriodicBreakdown`.  The repository therefore remains
`SCAFFOLDED / SCIENTIFIC_FRONTIER`.

At source commit `ca6d3b3d6954988541b45aef0bfb7ea2de1113e2`, the canonical command

```text
lake env lean Navier/AxiomAudit.lean
```

emits 448 raw declaration audits, each restricted to `propext`,
`Classical.choice`, and `Quot.sound`.  Later commits extend the tree and name
their own receipts.  The audits establish the named lower theorems only.  They
are not an endpoint certificate.

## Compiler-confirmed residual sorries (9) — triage 2026-08-15

`lake build` at `main@f1b496f` on a clean tree completes successfully (8729
jobs) and emits exactly nine `declaration uses 'sorry'` warnings.  This is the
whole compiler residual; it supersedes the stale `10` carried by the
`ba2995e1` proof-report row (`exists_subseq_windowCauchy` has since closed).

Triage verdict: **0 reachable, 9 blocked on absent infrastructure or a named
statement-level barrier.**  None is a tactic gap; each is a missing analytic
layer with a citation and a LOC estimate at its declaration.

| # | Declaration | File:line | Class | Exact missing layer |
|---|---|---|---|---|
| 1 | `exists_biotSavartLogTextbook` | `BKMLogBootstrap.lean:362` | infrastructure-blocked | Biot–Savart representation `∇u = PV(∇K ∗ ω)` for divergence-free Schwartz fields. The entire Calderón–Zygmund **size** layer (near field, log shell, far field) is already certified in-file; only the representation is Mathlib-absent |
| 2 | `exists_locallyUniformSliceDecay` | `BKMLogBootstrap.lean:1489` | infrastructure-blocked | Propagation of Schwartz seminorm bounds, locally uniform in time, along the flow — the genuinely PDE-dependent conjunct. In-file note proves no dominating function exists from `velocity_smooth` alone, so the NS clauses must be used |
| 3 | `exists_sobolevOrderEnergyEstimate` | `BKMLogBootstrap.lean:1561` | infrastructure-blocked | Kato–Ponce commutator bound `\|⟨D^n(u·∇u), D^n u⟩\| ≤ C‖∇u‖_∞‖u‖²_{H^n}` (CPAM 41 (1988) 891–907); Majda–Bertozzi Prop. 3.7; ~600 LOC. Order summation already certified (`BKMLogLeaves.exists_hasDerivAt_sum_range_le`) |
| 4 | `exists_galerkinModeData` | `LerayWeak.lean:1482` | infrastructure-blocked | `time_equicontinuous` + `weak_consistent` from the finite-mode energy identity and the `∂ₜu_m ∈ L²(0,T;H⁻¹)` bound (~100 LOC). Both Pattern-A fields from the Aubin–Lions repair are already discharged |
| 5 | `exists_lerayLimitData` | `LerayWeak.lean:5503` | **statement-level barrier** | Every domination-based route is closed off by the in-file unbounded-test-field construction (`sup_{t<T}‖φ(t)‖_{L²} = ∞`). Not a falsification; closing it needs a uniform-in-time seminorm field on the test class, an argument forming no `t`-majorant, or a compactly-supported-slice representative. The statement-level change is deliberately not taken |
| 6 | `prodiSerrin_layer_farField_bounded` | `ConditionalRegularity.lean:721` | infrastructure-blocked | Duhamel representation of an arbitrary `PartialClassicalSolution` + Leray projector as a pointwise bounded kernel. Kato, *Math. Z.* 187 (1984); Giga–Miyakawa, *ARMA* 89 (1985); ~300 LOC. Gaussian kernel, its `L^s` norms and the Young layer already land in `HeatSemigroupSmoothing` |
| 7 | `prodiSerrin_interior_outerRegion_bounded` | `ConditionalRegularity.lean:791` | infrastructure-blocked | Cutoff integration by parts against the local energy identity, plus an `L^r` pressure bound. Blocked in turn on the Calderón–Zygmund near-field cancellation, named residual in `SingularIntegralPrelims` |
| 8 | `constantinFefferman_layer_farField_bounded` | `ConditionalRegularity.lean:866` | infrastructure-blocked | Same layer as #6 with the uniform `L²` mass bracket replacing per-slice `L^p` |
| 9 | `constantinFefferman_interior_outerRegion_bounded` | `ConditionalRegularity.lean:951` | infrastructure-blocked | Integral enstrophy budget (pointwise stretching identity already lands as `Enstrophy.vorticityTransportEquation`), near-field cancellation as in #7, and `SobolevEmbedding`'s `H³ ↪ L^∞` which still carries a disclosed Plancherel `sorryAx` |

Three residuals (#1, #7, #9) route through one shared blocker — the
Calderón–Zygmund near-field cancellation in `SingularIntegralPrelims` — which
makes it the highest-fanout single target in the residual set.

## What the checked layer proves

### Official energy representation

The official Euclidean energy and the literal sum of the three coordinate
squares are related *exactly*: `kineticEnergy` is now defined by the Euclidean
density, so `officialKineticEnergy = kineticEnergy` is an identity
(`EnergyNormBridge.officialKineticEnergy_eq_kineticEnergy`).  Smooth classical
solution slices supply the measurability needed for the integral transports.

The inherited Pi-norm (supremum) energy is **not** related exactly: it is
two-sided but lossy, `supKineticEnergy ≤ kineticEnergy ≤ 3 * supKineticEnergy`,
and the constant three is attained pointwise
(`EnergyNormBridge.officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness`).  So
the whole-space kinetic-energy *integrand* mismatch is closed exactly, while
every other clause the former `currentSpaceNormEuclideanNormEquivalence`
residual named is closed only up to that attained constant.

Those other clauses are now all transported.  The `finite_energy` field goes
across with the uniform bound, using measurability derived from smoothness rather
than assumed; the Schwartz datum decay clause goes across in its weight, its
bundle value, and its argument slots; and the two force decay predicates of
`OfficialProblem.lean` go across in weight, bundle value, and spacetime argument
slots, which leaves Fefferman's alternatives C and D provably unchanged.  Since
Fefferman fixes no norm on spacetime derivative slots, the force transports
quantify over every slot measurement pinched between the inherited norm and `√3`
times it, and the resulting class is independent of that choice.

With every clause transported, that residual is now retired from
`Problem.lean`'s list, which is down to four encoding bridges.  The
identification available is class-level only: every transport moves an
existentially quantified constant through a power of `√3`, so the surface
matches Fefferman's clause *classes* without matching any of them
quantitatively.  None of this generates an energy estimate, an a priori bound,
or a solution.

Key files:

- [`EnergyNormBridge.lean`](../Navier/Analysis/EnergyNormBridge.lean)
- [`EnergyOfficialClause.lean`](../Navier/Analysis/EnergyOfficialClause.lean)
- [`ForceNormBridge.lean`](../Navier/Analysis/ForceNormBridge.lean)

### Frequencywise local-theory algebra

The real Leray projection has a genuine complex-linear extension.  Its
Hermitian contraction, transversality, idempotence, conjugation law, heat
decay, and semigroup law are checked at each frequency.  This is the correct
one-frequency symbol algebra, not an actual Fourier transform, Oseen kernel,
critical-space multiplier theorem, Duhamel contraction, or local solution.

Key files:

- [`ComplexLerayProjection.lean`](../Navier/Analysis/ComplexLerayProjection.lean)
- [`ComplexLerayNorm.lean`](../Navier/Analysis/ComplexLerayNorm.lean)
- [`ComplexFrequencyHeatLeray.lean`](../Navier/Analysis/ComplexFrequencyHeatLeray.lean)

### Conditional smooth energy chain

For a zero-force classical solution the exact pointwise local energy balance
is proved.  Under explicit spatial flux, flux-derivative, and dissipation
integrability guards, pressure and convection integrate to zero and viscous
work is the negative derivative-square integral.  The resulting instantaneous
integrated balance is proved.  At positive interior times, an explicit
dominated-Lipschitz hypothesis justifies moving the time derivative through
the spatial integral.

The following remain outside those theorems: deriving every guard from the
official solution class, the right endpoint `t = 0`, continuity of the total
energy derivative, and integration in time.  Consequently the full smooth
finite-interval energy identity is still open.

Key files:

- [`EnergyPointwiseBalance.lean`](../Navier/Analysis/EnergyPointwiseBalance.lean)
- [`EnergyInstantaneousIntegralBalance.lean`](../Navier/Analysis/EnergyInstantaneousIntegralBalance.lean)
- [`EnergyDerivativeUnderIntegral.lean`](../Navier/Analysis/EnergyDerivativeUnderIntegral.lean)

### Exact CKN scaling input

The parabolic determinant is `lambda^5`, product spacetime volume transports
with weight `lambda^-5`, the combined velocity/pressure density integral has
the expected weight, and the normalized backward-cylinder CKN functional is
scale invariant.  No suitable weak solution, local energy inequality,
pressure compactness theorem, epsilon-regularity theorem, or partial
regularity theorem is constructed.

Key file:

- [`CKNIntegralScaling.lean`](../Navier/Analysis/CKNIntegralScaling.lean)

### Generated Fourier support and finite instantaneous dynamics

Recursive supports are finite at each stage, centrally symmetric, and strictly
grow at every generation for nonzero scale.  No nontrivial finite support
containing zero can be closed under all pairwise sums.  The exact finite
viscous Leray-projected amplitude right-hand side has the expected support,
zero-mode, transversality, and conjugate-reality laws.

This does not prove that each newly generated frequency receives a nonzero
coefficient after cancellation.  It also supplies no infinite summable
amplitude flow, physical energy cascade, scale-uniform shell estimate, or
Navier--Stokes solution.

Key files:

- [`GeneratedSupport.lean`](../Navier/Routes/R7/GeneratedSupport.lean)
- [`FiniteAmplitudeDynamics.lean`](../Navier/Routes/R7/FiniteAmplitudeDynamics.lean)
- [`FiniteReality.lean`](../Navier/Routes/R7/FiniteReality.lean)
- [`FiniteSupportClosureObstruction.lean`](../Navier/Routes/R7/FiniteSupportClosureObstruction.lean)
- [`GeneratedSupportStrictGrowth.lean`](../Navier/Routes/R7/GeneratedSupportStrictGrowth.lean)

## Exact endpoint dependency picture

The positive branch still needs every stage in this chain:

```text
remaining official bridges
  -> local critical solution and uniqueness
  -> restart/maximal continuation
  -> one unconditional regularity producer
  -> endpoint composition
```

The energy identity is useful infrastructure, but its `L2` control is
supercritical in three dimensions and cannot itself supply the missing
unconditional producer.

The negative branch still needs every stage in this chain:

```text
admissible datum and force
  -> exact local/maximal solution
  -> agreement with every official global solution
  -> genuine finite-time nonextension mechanism
  -> exact C/D endpoint composition
```

Finite Fourier algebra, averaged-model blowup, weak nonuniqueness, or force
recovery without admissibility and agreement realizes none of these stages.

## Twelve-lane open-obligation map

| Lane | Checked boundary now | First genuinely open obligation | Best attack technique | Mandatory kill test |
|---|---|---|---|---|
| L01 official A/B representation | Euclidean/Pi datum norms and all whole-space energy clauses | Multi-index coordinate derivatives, half-space jets, coordinate PDE wording, periodic lift/quotient semantics | Expand iterated Frechet maps on the finite coordinate basis; prove operator-norm/basis-coefficient equivalence; treat boundary jets and periodic quotient as separate transports | Any changed datum, derivative, equation, energy, domain, or quotient quantifier rejects the bridge |
| L02 official C/D representation | One-way total-Frechet to coordinate force-decay control | Converse multilinear norm reconstruction, boundary convention, separate whole-space/periodic force semantics | Reconstruct finite-dimensional multilinear norms from basis coefficients and prove the within-derivative boundary law | A rough force, wrong spatial weight, or periodic/whole-space conflation rejects the bridge |
| L03 critical norms | Faithful cubic integrability, `MemLp`, and exact `L3` scaling | Nested time-space norms and any unconditional critical estimate | Build restricted-time Bochner `MemLp`/`eLpNorm`; use Tonelli and exact change of variables; keep the a priori estimate as an independent producer | A nonintegrable slice accepted as finite or a scale-dependent constant kills the interface |
| L04 local mild solution | Genuine complex heat--Leray one-frequency semigroup | Fourier/Helmholtz realization, Oseen and bilinear estimates, datum-dependent fixed point | Choose one critical Banach space, prove multiplier/kernel bounds, then run a quantitative short-time contraction | Hidden small-data/global assumptions or the wrong projection symbol kill the construction |
| L05 continuation | Restriction and agreement algebra | Time shift, overlap uniqueness, maximal gluing, restart blowup alternative | Define restart-compatible partial solutions; prove uniqueness in the same class; glue a directed family and derive a restart contradiction | Defining maximality with assumed global existence or switching solution classes is circular |
| L06 smooth energy | Pointwise balance, guarded spatial cancellation/dissipation, positive-time derivative interchange | Derive guards from official decay; handle `t = 0`; integrate in time | Prove quantitative cutoff estimates, dominate all fluxes from explicit decay, use a right-within DCT/extension theorem, then interval FTC | Any surviving boundary term, missing domination, or two-sided theorem misused at zero kills the identity |
| L07 weak/epsilon theory | Exact cylinders, Jacobian, density integrals, normalized CKN functional | Suitable weak solutions, distributional PDE, local energy inequality, pressure control, epsilon iteration | Formalize distributions and pressure-aware suitability first; then port one compactness/contradiction epsilon theorem | Omitting pressure or the local energy inequality produces the wrong solution class |
| L08 conditional critical regularity | Classical slice measurability and `L3` membership interface | Endpoint trace, suitable-weak compactness, ESS/backward uniqueness | State the critical bound explicitly as input; build rescaling, pressure bounds, endpoint trace, and backward uniqueness without producing the bound | Hiding `critical.unconditional_bound` inside the conditional theorem is circular |
| L09 compactness/rigidity | Scale-translation group laws and exact `L3` invariance | Profile extraction, orthogonality, remainder smallness, nonlinear stability, rigidity | Port a linear profile decomposition with explicit parameter orthogonality; prove perturbation separately; normalize one minimal ancient orbit | Failed decoupling or a non-small consumer-norm remainder kills the decomposition |
| L10 vorticity geometry | Curl scaling and unit direction away from zero | Vorticity PDE, Biot--Savart/strain representation, conditional stretching depletion | Derive vector-calculus identities and Riesz-transform recovery; isolate the singular high-vorticity stretching integral | Undefined direction at zero or omitted nonlocal velocity recovery kills the criterion |
| L11 frequency cascade | Exact finite RHS, reality, unavoidable strict support growth, no finite closure | Nonzero-amplitude persistence, infinite summability, shell identity, scale-uniform estimate | Work in weighted `l1` or Gevrey amplitudes; prove absolute convergence and local ODE flow; predeclare shell weights before estimating | Cancellation on new modes, nonsummable tails, or scale-growing constants kill the route |
| L12 exact breakdown | Force-recovery iff, restriction, nonextension consumer, zero-witness rejection | Admissible singular exact solution, agreement, blowup, official nonexistence | Construct `u,p` first; prove recovered-force admissibility and local uniqueness/agreement before applying nonextension | Averaged operators, rough force, weak nonuniqueness, or consumer-only witnesses are wrong objects |

## Highest-leverage next sequence

1. Finish the exact local critical solution and overlap uniqueness.  Every
   positive continuation route and every rigorous maximal-breakdown route
   needs this common infrastructure.
2. Close the smooth energy guards and time integration.  This removes a
   foundational formal gap, while explicitly retaining the supercritical
   barrier.
3. Build the suitable-weak/local-energy interface around the now-correct CKN
   functional.  This unlocks both epsilon regularity and conditional ESS work.
4. Choose exactly one unconditional producer: critical norm control,
   compactness-rigidity, vorticity depletion, epsilon singularity exclusion,
   or an infinite frequency estimate.  No endpoint proof exists until one of
   these is genuinely realized.
5. Treat the R7 route as an infinite weighted-system problem.  The finite
   closure strategy is formally refuted and should not receive more effort.
6. Attempt endpoint composition only after the producer and all exact
   representation dependencies carry native receipts.

## Scientific boundary

The checked layer proves substantial lower mathematics and sharply reduces
several formalization residuals.  It does not establish global regularity,
finite-time singularity, or either side of the problem alternative.  Any future
claim of closure must provide an actual A/B/C/D inhabitant, a fresh canonical
build, and a raw axiom audit restricted to the allowed foundational axioms.
