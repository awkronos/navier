# Resumed full-map attack: proved leaves and exact open frontier

## Verdict

This wave materially advances the formal support graph but does **not** solve
the three-dimensional Navier--Stokes Clay problem.  There is still no term
inhabiting `Navier.Clay.StatementA`, `StatementB`, `StatementC`, or
`StatementD`.  The repository therefore remains
`SCAFFOLDED / SCIENTIFIC_FRONTIER`.

At source commit `ca6d3b3d6954988541b45aef0bfb7ea2de1113e2`, the canonical command

```text
lake env lean Navier/AxiomAudit.lean
```

emits 448 raw declaration audits.  All 213 public theorems introduced by the
resumed wave are included directly in that canonical surface; every emitted
dependency is restricted to `propext`, `Classical.choice`, and `Quot.sound`.
This establishes the named lower theorems only.  It is not an endpoint
certificate.

## What the resumed wave actually proves

### Official energy representation

The inherited Pi-norm energy, official Euclidean energy, and literal sum of
the three coordinate squares are now related exactly.  Smooth classical
solution slices supply the measurability needed for those integral transports.
This closes the whole-space kinetic-energy representation mismatch; it does
not generate an energy estimate or a solution.

Key files:

- [`EnergyNormBridge.lean`](../Navier/Analysis/EnergyNormBridge.lean)
- [`EnergyOfficialClause.lean`](../Navier/Analysis/EnergyOfficialClause.lean)

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

The resumed wave proves substantial lower mathematics and sharply reduces
several formalization residuals.  It does not establish global regularity,
finite-time singularity, or either side of the Clay alternative.  Any future
claim of closure must provide an actual A/B/C/D inhabitant, a fresh canonical
build, and a raw axiom audit restricted to the allowed foundational axioms.
