# Mathematical obligation navigation

Use current theorem types and compiler evidence to select work. This file
does not assign fixed outcomes or prescribe a proof route.

## Current boundary

| Surface | Current status | Live edge |
| --- | --- | --- |
| Forced whole-space alternative C | **THEOREM**: `ConstructedBreakdown.wholeSpaceBreakdown` | Optional follow-ups: sharper mechanism, force semantics, finite-time localization; C itself has no remaining premise |
| Deadline-parameterized forced alternative C | **THEOREM**: `DeadlineParameterizedWholeSpaceBreakdown.wholeSpaceBreakdown_deadlineT` | Proved for every `ν > 0` and every prescribed `T > 0`; the force-support endpoint is the proved law `T₀·T` with `T₀` the existential raw-candidate endpoint, and the rescaled velocity and native force carriers are parallel, related by `nativeForce` transport |
| BKM criterion at the constructed breakdown | **THEOREM**: `BKMForcedBreakdownNecessity.selected_candidate_forces_no_BKM_control_in_every_smooth_competitor` | The criterion's hypothesis is refuted for every admissible profile of the proved blow-up mechanism, so it cannot be weakened and remain consumable at this endpoint; the vorticity-integral divergence of the constructed field is a named OPEN residual |
| Unforced whole-space alternative A | **OPEN**: `ProblemStatements.WholeSpaceGlobalRegularity` | Local existence, normalized continuation and arbitrary-large-data critical control must meet in one faithful whole-space consumer |
| Unforced periodic alternative B | **OPEN (arbitrary data)**: `ProblemStatements.PeriodicGlobalRegularity` | Constructed physical local evolution and all spatial moments must feed joint classical reconstruction and arbitrary-data, horizon-uniform continuation control. The small-data case is settled on the lattice carrier: `CriticalMildSmallDataGlobal.smallDataGlobalMild`, unconditional `ε(ν) = ν/16` (2026-09-11); and its official-carrier momentum identity is unconditional for anti-Hermitian data (reality transport closed in `CriticalMildGlobalTrajectoryReality`, 2026-09-11) |
| Fourier-lattice continuation | **CONDITIONAL THEOREM** | `CriticalMildMixedTerminalBound` is a sufficient uniform nonlinear estimate to construct; its optimality is not established. The linear transport half is proved on the whole-space carrier: `Analysis.ContinuousLeiLinDissipation` supplies the `ν⁻¹` dissipation budget (`integral_normX1_heatMode_le`), the honest no-spectral-gap free-term decay (`tendsto_normXm1_heatMode`), the coordinate-aggregated budgets, and the Duhamel `X⁻¹` bound (`normXm1_continuousDuhamel_le`) with strict axioms. The mild fixed-point assembly landed 2026-09-13: `ContinuousLeiLinMildFixedPoint.actual_existsUnique_mildFixedPoint` derives existence, uniqueness, and the `3/4` slot contraction of the actual mild self-map on the completed linked box `ActualLinkedBox ν T (2R) (2R)` at the consumed threshold `R ≤ ν/16` — box-valuedness and contraction are derived (`mildLift_mem`, `mildLift_contraction`), never assumed; strict axioms. The travelling premise is the `MildAssemblyLeaves` record: joint `(ξ,t)` a.e. strong measurability of the diagonal and both ordered mixed Navier sources, the six mild-image lift measurability/integrability fields, and the two bare polarization identities — each produced nowhere in the repo for general box elements (existing suppliers `RecentTailInputs` / `actualLinkedContinuousMildImage_of_continuous` require joint continuity), so the named construction is their instantiation for quotient representatives. The other separately named object, the continuous-carrier pressure-reconstruction primitive, landed 2026-09-13: `Analysis.ContinuousLeiLinPressureReconstruction` constructs the Riesz-symbol Fourier pressure `p̂ = -Σᵢⱼ(ξᵢξⱼ/‖ξ‖²)(ûᵢ ⋆ ûⱼ)` mean-zero normalized (`p̂(0) = 0`, no Dirac component), with `∫‖p̂‖ ≤ X⁰²`, `normX1 p̂ ≤ 2·X⁰·X¹`, the honest `X⁻¹` statement on the gradient (the naive `X⁻¹`-mass-of-`p` bound is false in general by concentration at `ξ = 0` — replaced, not repaired), pointwise and Schwartz-pairing Poisson identities `‖ξ‖²·p̂ = -Σᵢⱼ ξᵢξⱼ·(uᵢ⋆uⱼ)`, and two Duhamel-shaped `X⁻¹` feeds; its premises are exactly the measurability/integrability data the box elements carry; no consumer has invoked it yet — the connection is stated at the signature level, not claimed as consumption. The physical-space inversion landed 2026-09-13: `Analysis.ContinuousLeiLinPressurePhysical`
inverts the primitive to `p = 𝓕⁻ p̂` with `‖p(x)‖ ≤ X⁰` mass budget, continuity, and
the distributional Poisson identity in transported-pairing form
`∫ p·Δψ = (2π)² ∫ (Σᵢⱼ ξᵢξⱼ·(ûᵢ⋆ûⱼ))·𝓕⁻ψ` for Schwartz tests, same carrier
premises, strict axioms on all 14 declarations. Its named residual is the
fully-physical stress-tensor rewrite of the frequency side — the pointwise
`𝓕⁻(ûᵢ⋆ûⱼ) = vᵢ·vⱼ` product-to-convolution bridge for merely-`L¹` frequency data
(pinned Mathlib carries only the converse), closing under a Schwartz-`u`
specialization. The primitive's other live obligation is fixed-point
consumption by `actual_existsUnique_mildFixedPoint`. `Φ x = x` remains carrier equality (both slot distances zero), not the pointwise PDE |
| Scalar Madelung route for the lift | **FALSIFIED (kernel, decoder level)**: `Analysis.MadelungDecoderCurlObstruction.no_scalar_madelung_initial_lift_of_rotational_data` | No `C^∞` scalar wavefunction nonzero at the origin decodes any rotational datum `λ > 0` — including the compactly supported, divergence-free `rotationalDatum λ` with `|u| ≤ λ < ν₀/16` (2026-09-11). The `{phase topology, zeros}` obligations are discharged by this counterexample; the transport obligations `{PDE, forcing, energy class}` move to the whole-space ScaledCutoff family |
| Periodic breakdown D | **THEOREM**: `PeriodicConstructedBreakdown.periodicBreakdown` | The native periodic forced endpoint has no remaining premise; it does not settle unforced periodic evolution |
| Unforced 3-D Euler blowup (upstream, not adapted here) | **THEOREM (upstream)**: `Euler.euler_breakdown_R3`, `Euler.exists_compact_smooth_euler_singularity` [OPENAI2026_EULER]; this repository re-verified the upstream build clean on 2026-09-13 | Different carrier: the Euler model is quarantined for A/B (`BARRIERS.md` §5) and no transfer theorem exists. Upstream's Euler vorticity divergence does **not** discharge this repository's NS residual — the line-12 OPEN obligation concerns the divergence of the vorticity integral of the *constructed forced Navier–Stokes field*, a different object on a different equation |

The globally smooth object in the completed strengthened C result is the
force. The selected velocity is classical before its singular deadline and
cannot be continued as a global smooth bounded-energy solution. “Global smooth
velocity” would describe A or B and must not be inferred from C.

## Structural certification (measured 2026-09-13)

`scripts/proof_graph.py` over this tree: 966 modules, 2,665 local
import edges, **0 cycles**, longest path 65, crown import closures 616 (C) /
538 (D) / 611 (deadline-C); umbrella coverage excludes only `Main` (the mild
fixed-point assembly and the pressure-reconstruction primitive are wired into
the build-time receipt pipeline through `Navier/ConditionalAudit.lean`). 619
modules are consumed by at least one crown; 346 are intermediate-unconsumed
research infrastructure feeding future endpoints.
`formalization.yaml` is the machine-readable mirror of the table above;
`scripts/check_formalization.py --check` validates it fail-closed and
`--probe` prints the raw-axiom command sequence without asserting results.
Every `lake build` now emits raw `#print axioms` receipts for all four crowns
from `Navier/ConditionalAudit.lean` (build log = receipt pipeline), and
`scripts/check_construction_drift.py` pins the vendored slice to upstream
`8937a8f` — the precondition for the pending appendix port.

The exact original target and a conditional construction are described in
[`DECOMPOSITION.md`](DECOMPOSITION.md). The encoding comparison theorems and
checked energy/pressure counterexamples are listed in
[`FORMALIZATION.md`](FORMALIZATION.md).

The soundness cleanup removed admitted proof claims from:

- `BKMLogBootstrap.lean`: weighted-energy propagation and Sobolev-order
  energy estimates, together with claims that consumed them. The log-Grönwall,
  Fourier, Biot–Savart, and conditional transfer results remain.
- `ConditionalRegularity.lean`: the general Duhamel representation, source
  bounds, and resulting Prodi–Serrin/Constantin–Fefferman bridge claims.
  Compact-region, Gaussian convolution, integrability, and explicit strain
  counterexample results remain.
- `GalerkinModeData.lean`: general stable-basis and mode-data existence
  claims. The proved projection and coefficient-flow support remains.
- `LerayWeakExistence.lean`: all three existence wrappers depended on the
  admitted mode-data construction, so the file was removed. The proved
  conditional compactness and limit passage in `LerayWeak.lean` remain.

Removing an admission neither proves nor refutes its mathematical statement.
The surviving source supplies the smaller proved inputs for further work.
The general analytic estimates and the original unforced global target
require proofs or exact counterexamples. The completed forced construction is
documented separately in the [result map](RESULT_MAP.md).

`scripts/AuditAllAxioms.lean` checks every declaration imported from a Navier
module, including private helpers and declarations in other namespaces, for
disallowed transitive axioms. Refresh changed modules before running it.
This detects admitted dependencies omitted by a handpicked public audit.
It does not decide whether the definitions faithfully encode a scientific
claim, or whether the hypotheses of a conditional theorem can be proved.

The dated residual ledger and research blueprint are historical records.
Their counts, line numbers, and proposed routes are not current verification
evidence or constraints on new proofs.
