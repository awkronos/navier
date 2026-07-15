# Twelve-lane scientific-frontier attack

Starting point: `dbb8e6111684d276c60dad1d630ce07d56b0bc90` on
`codex/navier-six-lane-20260714`.

This campaign attacks every producer class in the canonical registry.  Its
global status is `SCAFFOLDED / SCIENTIFIC_FRONTIER`: neither an official
positive endpoint nor an official breakdown endpoint has an inhabitant.  A
compiled surface, conditional consumer, experiment, or representation bridge
is not an endpoint proof.

The later resumed wave is recorded in
[`FULL_MAP_RESUMED_ATTACK.md`](FULL_MAP_RESUMED_ATTACK.md).  Its updated L01,
L04, L06, L07, and L11 residuals supersede the corresponding rows below; the
endpoint verdict remains unchanged.

The runtime permits three workers plus the integrating agent.  The twelve
logical lanes therefore execute in four fold-and-refill waves.  Each lane must
return one of:

- a checked nontrivial Lean theorem with an allowed raw axiom audit;
- a checked counterexample or exact replayable falsification witness; or
- a strictly smaller reference-grounded residual with an exact declaration
  signature and consumer.

## Lane matrix

| Lane | Pattern family | Canonical obligations | Required artifact | Residual guarded against |
|---|---|---|---|---|
| L01 | representation transport | `semantics.encoding_bridges`, `semantics.exact_a_surface` | A/B datum, norm, smoothness, PDE, energy, or periodic bridge | treating the current Lean encoding as definitionally identical to Fefferman's coordinates |
| L02 | representation transport | `breakdown.c_encoding_bridges`, `breakdown.exact_c_surface` | C/D force, derivative, point-norm, PDE, energy, or quotient bridge | importing periodic semantics into C or weakening force admissibility |
| L03 | data contract | `scaling.algebraic_critical_line` | faithful `MemLp`/norm and mixed-norm infrastructure with genuine measure semantics | raw integrals that silently become zero on nonintegrable functions |
| L04 | payload realization | `local.mild_solution` | heat/Leray/Duhamel infrastructure and a datum-dependent contraction leaf | assuming local existence or using the wrong projected operator |
| L05 | bridge contract | `local.continuation_alternative` | restriction, restart-compatible uniqueness, maximal gluing, or critical blowup alternative | assuming global smoothness in a continuation proof |
| L06 | kernel certificate | `energy.smooth_identity` | compact-support pressure/convection cancellation and a justified decay limit | discarding a boundary, pressure, or integrability term |
| L07 | data contract + bridge | `energy.global_weak_solution`, `epsilon.local_regular_criterion` | weak/suitable solution, local energy, pressure, and cylinder interface | calling a distributional solution suitable without the local energy inequality |
| L08 | bridge contract | `critical.global_regularity_bridge` | conditional endpoint regularity theorem with exact solution and pressure hypotheses | hiding the unconditional critical bound inside the conditional theorem |
| L09 | decomposition tree + payload | `compact.profile_decomposition`, `compact.rigidity_exclusion` | orthogonality/remainder leaf or a precise ancient-profile rigidity statement | an untracked translation, scale, or frequency defect |
| L10 | bridge contract + payload | `vorticity.alignment_criterion`, `vorticity.unconditional_depletion` | curl/Biot--Savart/direction infrastructure and one checked stretching estimate | defining direction at zero vorticity or dropping nonlocal recovery |
| L11 | falsification ledger + payload | `frequency.cascade_exclusion`, `critical.unconditional_bound` | complete generated convolution network, exact shell balance, and predeclared collective weight | promoting one selected output or a finite table to a PDE shell estimate |
| L12 | payload realization + verifier interface | `breakdown.forced_c_payload`, `breakdown.zero_force_blowup_payload`, `breakdown.any_exact_realization` | an admissible partial solution plus agreement and blowup, or a checked obstruction that lowers the construction target | averaged operators, weak nonuniqueness, rough force, or consumer-only witnesses |

## Consumer graph

The positive endpoint requires all of the following layers:

1. official representation bridges;
2. a local solution with restart-compatible uniqueness;
3. a conditional continuation theorem;
4. at least one unconditional analytic producer;
5. the smooth energy clause and final viscosity-one composition.

The critical route must keep `critical.unconditional_bound` independent from
`critical.global_regularity_bridge`.  A separate `ALL` composition joins the
payload and conditional theorem before `regularity.any_positive_route`.

The negative endpoint requires:

1. exact force/datum representation bridges;
2. an admissible viscosity-one datum and force;
3. an exact classical solution on a genuine half-open interval;
4. local uniqueness or agreement with every official global pair;
5. point-norm blowup or another exact nonextension mechanism;
6. the already checked conditional nonextension consumer.

## Verification gates

- Lean LSP diagnostics and exact declaration signatures are the preflight
  evidence for each new file.
- A targeted `lake env lean <file>` is required before folding a Lean file.
- Public lower-theorem claims require raw `#print axioms` contained in
  `{propext, Classical.choice, Quot.sound}`, with `native_decide` explicitly
  identified if used.
- Experiments retain `closes_clay_endpoint=false` and never provide realization
  evidence.
- One serialized aggregate verifier runs only after all writers have folded.
- `StatementA`, `StatementB`, `StatementC`, or `StatementD` may be called proved
  only if an actual native inhabitant passes the same axiom audit.

## Current verifier caveat

The Kimina configuration file contains a `navier` project entry, but the live
Kimina server's project map did not expose it at campaign start.  Local Lean
LSP remains available.  This is recorded as stale live verifier state; it is
not permission to restart a service or modify shared verifier infrastructure.

## Fold log

### Wave 1

- L01 (`representationTransport`) proved the finite-dimensional norm bounds
  `‖x‖∞ ≤ ‖x‖₂ ≤ √3‖x‖∞`, transported the existing rapid-decay predicate to
  Euclidean spatial weights, and supplied the Schwartz-map consumer.  The
  literal multi-index derivative and energy clauses remain open.
- L02 (`representationTransport`) proved that the current total Fréchet force
  bound controls every mixed unit time/space coordinate direction and output
  component, with the correct Euclidean whole-space weight and no spurious
  periodic spatial weight.  The converse and derivative-convention identity
  remain open.
- L03 (`dataContract`) proved genuine `MemLp` membership transport and exact
  `eLpNorm`/`lpNorm` invariance under positive critical scaling, plus faithful
  finite-time bound covariance.  Outer mixed norms and the unconditional
  Navier--Stokes bound remain open.

All three files passed targeted Lean compilation, empty LSP diagnostics, and
per-theorem allowed-axiom audits before their path-scoped commits.

### Wave 2

- L04 (`payloadRealization`) constructed the Euclidean frequency plane and
  orthogonal Leray projector, proved transversality, norm contraction and
  idempotence, and transported the exact projector formula and contraction
  bound to `normalizedLeraySymbol` in `Navier/Analysis/LerayProjection.lean`
  (`662416f`).  This is the finite-dimensional multiplier at one real
  frequency.  It is not a bounded complex Fourier multiplier, a heat
  semigroup, a Duhamel map, a contraction argument, or a local mild solution.
- L05 (`bridgeContract`) defined restriction of an exact
  `PartialClassicalSolution`, proved restriction transitivity, and established
  reflexivity, symmetry, transitivity, and time monotonicity for
  `VelocityAgreesBefore` in `Navier/Breakdown/Restriction.lean` (`7f20dbe`).
  No time-shift/restart operator, restart-compatible uniqueness theorem,
  maximal gluing construction, or continuation alternative was derived.
- L06 (`kernelCertificate`) identified pointwise pressure work with the
  divergence of the pressure flux under explicit smoothness and
  incompressibility hypotheses in
  `Navier/Analysis/EnergyPressureCancellation.lean` (`503d43a`).  It then
  proved the whole-space integral of a divergence, and hence total pressure
  work, is zero when every flux component and its coordinate derivative is
  integrable in `Navier/Analysis/EnergyPressureIntegral.lean` (`16698bf`).
  The official solution record does not yet imply those flux hypotheses, and
  the time, convection, and viscosity terms of the energy identity remain
  open.

The initial L05/L06 leaves were folded into the aggregate import and raw axiom
audit at `3fafab8`; the pressure-integral leaf and all three L11 modules were
folded at `0410bcb`.

### Wave 3

- L07 (`dataContract` + `bridgeContract`) defined literal backward CKN
  cylinders with the official Euclidean spatial norm and proved their exact
  image/preimage laws under positive parabolic dilation in
  `Navier/Analysis/CKNCylinderGeometry.lean` (`17a8d4c`).  It then defined
  product spacetime Haar measure and proved that composition with dilation,
  with an optional nonzero amplitude, preserves and reflects `IntegrableOn`
  over corresponding cylinders in `Navier/Analysis/CKNMeasureTransport.lean`
  (`8e564c4`).  Finally it defined the velocity-cubic, pressure-three-halves,
  and combined unnormalized CKN densities, proved their exact weight-three
  scaling, and transported their cylinder integrability in
  `Navier/Analysis/CKNDensity.lean` (`6e0ee07`).  There is no exact
  cylinder-volume/Jacobian formula, integral scaling value, normalized CKN
  functional, or boundary-variant equivalence.  A suitable weak-solution
  record, distributional Navier--Stokes, local energy inequality, pressure
  control, epsilon-regularity theorem, and singular-set or partial-regularity
  conclusion all remain open.
- L08 (`bridgeContract`) proved that velocity and pressure spatial slices of a
  genuine `PartialClassicalSolution` are continuous and almost-everywhere
  strongly measurable.  It also proved that the velocity slice is in
  `L^3(R^3)` exactly when its cubic norm is integrable, in
  `Navier/Analysis/ESSInputs.lean` (`59def54`).  There is no endpoint-time
  trace, suitable weak limit, local energy inequality, ESS endpoint theorem,
  or backward-uniqueness bridge, and no unconditional critical bound is
  supplied.
- L09 (`decompositionTree` + `payloadRealization`) defined the affine critical
  scale/translation action and proved identity, composition, inverse, and
  relative-parameter laws in
  `Navier/Analysis/CriticalProfileAction.lean` (`472489a`).  Translation and
  the full action were then proved to preserve `MemLp` and the exact `L^3`
  `eLpNorm` (`1c0cc85`).  No profile extraction, parameter orthogonality,
  remainder smallness, norm decoupling, nonlinear perturbation theorem,
  ancient minimal element, or rigidity exclusion was proved.

The checked L08/L09 leaves were folded into the aggregate import and raw axiom
audit at `f726979`, together with the L10 leaf below.  The three declaration-
local L07 commits passed targeted compilation, empty LSP diagnostics, and
allowed-axiom audits before their aggregate fold at `84fb8c1`.  The conditional
ESS bridge and the independent unconditional bound remain separate registry
producers; neither may be hidden inside the other.

### Wave 4

- L10 (`bridgeContract` + `payloadRealization`) defined coordinate curl and
  vorticity, proved their critical scaling laws, related zero and scalar
  multiplication to the official Euclidean norm, and defined vorticity
  direction only on the nonzero-vorticity subtype with unit norm in
  `Navier/Analysis/Vorticity.lean` (`89e727e`).  Curl-gradient/divergence-curl
  identities, the vorticity equation, Biot--Savart recovery, the singular
  strain estimate, a conditional alignment criterion, and unconditional
  dynamical depletion remain open.
- L11 (`falsificationLedger` + `payloadRealization`) exhausted every ordered
  input pair for each occupied receiver of the symmetric six-mode witness.
  `FullSixModePairClassification.lean` (`9785dde`) proves the unique producing
  pair up to order; `FullSixModeReceiverRates.lean` (`42bf9d6`) proves the
  exact occupied rate table `(0,-s,s,0,-s,s)` for `s != 0`; and
  `FullSixModeBalance.lean` (`9516bd1`) proves constant-weight sum zero,
  squared-frequency rate `2*s^3` (strictly positive for `s > 0`), and the
  simultaneous off-support projected leakage coefficient `s`.  Thus the
  finite occupied table is not invariant when `s != 0`.  There is no recursive
  convolution closure, amplitude evolution, viscous dynamics, infinite-shell
  summability, scale-uniform PDE estimate, or Navier--Stokes solution.
- L12 (`payloadRealization` + `verifierInterface`) defined the force recovered
  from an arbitrary velocity-pressure pair and proved exact iff theorems for
  the global and partial Navier--Stokes equations.  It also restricted a
  global official solution to a partial one and constructed the zero partial
  solution, proving that zero is not point-norm unbounded, in
  `Navier/Breakdown/ForceRecovery.lean` (`c064afc`).  No admissible recovered
  force, singular partial solution, local/global agreement theorem,
  point-norm blowup witness, or exact C/D nonexistence payload was produced.

## Current frontier and optimal next attacks

The table distinguishes a checked leaf from the first bridge that would make
it useful to an endpoint.  “Next attack” names a proof technique, not an
assumption that may be inserted into a payload.

| Lane | Checked gain | Still open | Optimal next attack / technique |
|---|---|---|---|
| L01 | Euclidean/Pi norm comparison and one-way Schwartz decay transport | Literal multi-index Schwartz equivalence; half-space smoothness; coordinate PDE and energy wording; periodic quotient semantics | Expand iterated Frechet maps on the finite coordinate basis and prove both operator-norm/coordinate-seminorm bounds.  Close boundary-jet, PDE, energy, and periodic lift/quotient equivalences as independent transports. |
| L02 | Total Frechet force decay implies every mixed coordinate-direction/component bound | Converse norm reconstruction; datum and boundary-jet conventions; coordinate PDE and energy clauses; separate periodic force quotient | Reconstruct the finite-dimensional multilinear operator norm from basis coefficients, then prove the within-derivative boundary convention.  Keep whole-space C and periodic D transports separate. |
| L03 | Genuine `MemLp` and exact critical `L^3` scaling | Nested time-space norms and every unconditional critical estimate | Define Bochner/mixed norms over restricted time measure, prove scaling with change of variables and Tonelli, and test any proposed nonlinear bound on rescaled divergence-free packets before promoting it. |
| L04 | Exact Euclidean Leray symbol and contraction | Complex Fourier multiplier, heat flow, Duhamel bilinear estimate, datum-dependent local solution | Build the heat semigroup and Leray multiplier on the selected critical Banach space; prove Oseen/heat kernel estimates and a short-time contraction with explicit datum and interval dependence. |
| L05 | Exact restriction and agreement algebra | Time shift, restart uniqueness, maximal gluing, continuation alternative | Prove a restart map compatible with right-time derivatives, obtain uniqueness in the same mild/classical class, then glue the directed family of restrictions into a maximal interval and prove the restart contradiction. |
| L06 | Pointwise pressure-flux identity and global cancellation under explicit integrability | Derivation of flux hypotheses; convection, viscosity, time-integral interchange; full energy identity | First prove a compactly supported cutoff energy identity.  Pass to infinity with quantified decay/integrability, integration by parts, and dominated convergence; derive every pressure-flux hypothesis from the actual solution class. |
| L07 | Exact backward-cylinder scaling; cylinder-integrability transport; critical-density scaling and integrability | Exact Jacobian/integral scaling and normalized functional; suitable weak solution; pressure control; distributional PDE; local energy; epsilon/partial regularity | Compute the parabolic determinant and normalized functional first.  Then formalize spacetime distributions and a non-vacuous suitable-solution record, and port one epsilon-regularity implication with every pressure and defect term explicit. |
| L08 | Classical spatial slices are measurable; exact `L^3` membership/cubic-integrability equivalence | Endpoint trace, suitable weak compactness, ESS and backward uniqueness; independent unconditional bound | Port ESS only as a conditional bridge: construct the endpoint rescaling/weak limit, pressure bounds and backward-uniqueness chain while taking the faithful `L∞_t L^3_x` bound as an explicit input. |
| L09 | Critical scale/translation group laws and exact `L^3` invariance | Profile extraction, orthogonality, decoupling, perturbation, ancient element, rigidity | Prove a linear profile decomposition with explicit scale/translation orthogonality and remainder topology, then a separate nonlinear stability theorem.  Normalize one minimal orbit before attempting backward uniqueness or a rigidity identity. |
| L10 | Curl/vorticity scaling and unit direction away from zeros | Vector-calculus identities, vorticity PDE, Biot--Savart/strain, conditional alignment, unconditional coherence | Derive the exact curl equation and formalize Biot--Savart/Riesz-transform recovery.  Prove the singular-integral stretching estimate on the high-vorticity set before stating a scale-correct direction-coherence criterion. |
| L11 | Exhaustive occupied rates, constant-weight cancellation, squared-frequency rate, and nonzero off-support leakage | Recursive generated support, amplitude ODE, viscosity, summability, collective critical estimate, PDE realization | Enumerate the convolution closure rather than truncating it, derive the full coefficient ODE including dissipation, and predeclare a collective shell weight.  Prove absolute summability and scale-uniformity or preserve the resulting counterexample as a route falsification. |
| L12 | Exact force recovery iff equations and zero-solution non-blowup obstruction | Admissible Schwartz datum/rapidly decaying force, singular partial solution, agreement, finite-time nonextension, exact C/D witness | Use force recovery only as a search parameterization: construct `u,p` first, then prove the recovered force satisfies every official clause.  Establish local uniqueness/agreement before applying the existing blowup-to-nonextension consumer. |

## Endpoint verdict

At the end of the four attack waves there is no assumption-free inhabitant of
`Navier.Clay.StatementA`, `StatementB`, `StatementC`, or `StatementD`.  The
positive graph still lacks an exact local/restart construction, a conditional
continuation bridge, an independent unconditional regularity producer, and the
full smooth energy conclusion.  The negative graph still lacks admissible
data/force, a genuine singular exact solution, official-class agreement, and
finite-time nonextension.  The representation equivalences for the official
wording also remain incomplete on both graphs.

Accordingly the endpoint verdict is **`SCAFFOLDED / SCIENTIFIC_FRONTIER`**.
The campaign has produced reusable kernel-checked leaves and a sharper set of
falsifiable residuals; it has not proved a Clay Navier--Stokes alternative and
does not constitute a Clay Prize solution.
