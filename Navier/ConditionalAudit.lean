import Navier.Analysis.CriticalControlDecomposition
import Navier.Analysis.CriticalMildRestartFixedPoint
import Navier.Analysis.CriticalMildBoundedContinuation
import Navier.Analysis.LeiLinCoerciveTerminal
import Navier.Analysis.LerayWeak
import Navier.Analysis.HeatSemigroupSmoothing
import Navier.Analysis.BKMLogBootstrap
import Navier.Analysis.ViscosityEndpoints
import Navier.Breakdown.MaximalNonextension
import Navier.Breakdown.CompactPathBreakdown
import Navier.Breakdown.ConstructedBreakdown
import Navier.Analysis.ForcedEnergyBalance
import Navier.Breakdown.DeadlineParameterizedWholeSpaceBreakdown
import Navier.Analysis.PeriodicConstructedBreakdown
import Navier.Analysis.ContinuousLeiLinMildFixedPoint
import Navier.Analysis.ContinuousLeiLinPressureReconstruction
import Navier.Analysis.ContinuousLeiLinPressurePhysical
import Navier.Analysis.PressureStressTensor
import Navier.Analysis.BKMVorticityIntegralDivergence
import Navier.Analysis.BKMProfileGronwallPair
import Navier.Analysis.BKMProfileRateBound
import Navier.Analysis.BKMProfileEnvelope
import Navier.Analysis.BKMProfileSelectedEnvelope
import Navier.Construction.BaseVorticityAxis
import Navier.Construction.CorrectionStep
import Navier.Construction.CorrectionInitialization
import Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
import Navier.Analysis.ContinuousLeiLinMildFixedPointPressure
import Navier.Analysis.SourceL1X1BoxFalsification
import Navier.Analysis.LinkedBoxX2Carrier
import Navier.Analysis.ContRepPinProdAe
import Navier.Analysis.EnvelopeDatumSeed
import Navier.Analysis.HorizonFreeBudgetRestart

/-! Selected consumer-facing conditions and the constructed alternative-C
endpoint; not a project-wide census.
Checks inspect existing imported objects. Rebuild changed providers before
using axiom output as current-source evidence. Audit commands inspect proofs;
they do not manufacture them. -/

#check Navier.Construction.R3CompactCandidate.selected_compact_candidate
#print axioms Navier.Construction.R3CompactCandidate.selected_compact_candidate

#check Navier.Construction.ComparatorBridge.compact_candidate_excludes_global_solution
#print axioms Navier.Construction.ComparatorBridge.compact_candidate_excludes_global_solution

#check Navier.Breakdown.NativeConstructionEndpoint.wholeSpaceBreakdown_of_compactCandidate
#print axioms Navier.Breakdown.NativeConstructionEndpoint.wholeSpaceBreakdown_of_compactCandidate

#check Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown
#print axioms Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown
#check Navier.Analysis.ForceCoordinateEquivalence.forcedDataRapidDecay_iff_successivePartials
#print axioms Navier.Analysis.ForceCoordinateEquivalence.forcedDataRapidDecay_iff_successivePartials
#check Navier.Analysis.ForceCoordinateEquivalence.periodicForcedDataRapidDecay_iff_successivePartials
#print axioms Navier.Analysis.ForceCoordinateEquivalence.periodicForcedDataRapidDecay_iff_successivePartials
#check Navier.Construction.ComparatorBridge.compact_candidate_unique_on_Icc
#print axioms Navier.Construction.ComparatorBridge.compact_candidate_unique_on_Icc
#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile
#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_no_continuous_extension
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_no_continuous_extension
#check Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation
#print axioms Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation
#check Navier.Analysis.ConstructedForceExtension.constructedWholeSpaceBreakdownWithGloballySmoothForce
#print axioms Navier.Analysis.ConstructedForceExtension.constructedWholeSpaceBreakdownWithGloballySmoothForce
#check Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown_with_successivePartials
#print axioms Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown_with_successivePartials
#check Navier.Breakdown.ConstructedBreakdown.selectedFiniteEnergyCandidate
#print axioms Navier.Breakdown.ConstructedBreakdown.selectedFiniteEnergyCandidate

#check Navier.Analysis.CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_continuation_apriori
#print axioms Navier.Analysis.CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_continuation_apriori

#check Navier.Analysis.CriticalMildRestartFixedPoint.existsUnique_criticalMildTerminalRestart_fixedPoint
#print axioms Navier.Analysis.CriticalMildRestartFixedPoint.existsUnique_criticalMildTerminalRestart_fixedPoint

#check Navier.Analysis.CriticalMildBoundedContinuation.bounded_global_mild_of_terminalNormBound
#print axioms Navier.Analysis.CriticalMildBoundedContinuation.bounded_global_mild_of_terminalNormBound

#check Navier.Analysis.LeiLinCoerciveTerminal.criticalMildTerminalNormBound_of_mixed
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.criticalMildTerminalNormBound_of_mixed

#check Navier.Analysis.LeiLinCoerciveTerminal.terminal_X1_le_of_trailingMass_and_X2Mass
#print axioms Navier.Analysis.LeiLinCoerciveTerminal.terminal_X1_le_of_trailingMass_and_X2Mass

#check Navier.Analysis.LerayWeak.exists_galerkinLimit_energy_le
#print axioms Navier.Analysis.LerayWeak.exists_galerkinLimit_energy_le

#check Navier.Analysis.LerayWeak.exists_lerayLimitData_of_weakClauses
#print axioms Navier.Analysis.LerayWeak.exists_lerayLimitData_of_weakClauses

#check Navier.Analysis.HeatSemigroupSmoothing.heatKernel_convolution_smoothing_le
#print axioms Navier.Analysis.HeatSemigroupSmoothing.heatKernel_convolution_smoothing_le

#check Navier.Analysis.BealeKatoMajda.exists_fderivSupBound_of_sobolevH3
#print axioms Navier.Analysis.BealeKatoMajda.exists_fderivSupBound_of_sobolevH3

#check Navier.Analysis.ViscosityEndpoints.wholeSpaceBreakdown_iff_atViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.wholeSpaceBreakdown_iff_atViscosityOne

#check Navier.Breakdown.noWholeSpaceGlobal_of_pointEvaluationBreakdown
#print axioms Navier.Breakdown.noWholeSpaceGlobal_of_pointEvaluationBreakdown

#check Navier.Breakdown.wholeSpaceBreakdown_of_compactSmooth_negativePowerProfile
#print axioms Navier.Breakdown.wholeSpaceBreakdown_of_compactSmooth_negativePowerProfile

#check Navier.Analysis.ForcedEnergyBalance.forced_pointwise_energy_balance_of_partialSolution
#print axioms Navier.Analysis.ForcedEnergyBalance.forced_pointwise_energy_balance_of_partialSolution

/-! Crown receipts: the deadline-parameterized and periodic crowns (the
successive-partials strengthening is emitted above with the C chain). -/
#check Navier.Breakdown.DeadlineParameterizedWholeSpaceBreakdown.wholeSpaceBreakdown_deadlineT
#print axioms Navier.Breakdown.DeadlineParameterizedWholeSpaceBreakdown.wholeSpaceBreakdown_deadlineT
#check Navier.Analysis.PeriodicConstructedBreakdown.periodicBreakdown
#print axioms Navier.Analysis.PeriodicConstructedBreakdown.periodicBreakdown

/-! Assembly receipts: the conditional mild fixed point (landed 2026-09-13,
strict under the MildAssemblyLeaves travelling premise) and the right-ordered
mixed spacetime supplier it consumes. -/
#check Navier.Analysis.ContinuousLeiLinMildFixedPoint.selfMapEstimate
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.selfMapEstimate
#check Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildLift_mem
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildLift_mem
#check Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildLift_contraction
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildLift_contraction
#check Navier.Analysis.ContinuousLeiLinMildFixedPoint.actual_existsUnique_mildFixedPoint
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.actual_existsUnique_mildFixedPoint
#check Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right.integral_coordinateX1Mass_continuousDuhamel_right_sub_le_linked_distance_of_jointSource
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right.integral_coordinateX1Mass_continuousDuhamel_right_sub_le_linked_distance_of_jointSource

/-! Pressure receipts: the continuous-carrier pressure-reconstruction
primitive (landed 2026-09-13) — Poisson pairing, the X¹ budget, the honest
X⁻¹ gradient bound, and the Duhamel-shaped feed its pointwise-PDE consumer
will use. -/
#check Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressurePoisson_pairing
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.continuousPressurePoisson_pairing
#check Navier.Analysis.ContinuousLeiLinPressureReconstruction.normX1_continuousPressureFourier_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.normX1_continuousPressureFourier_le
#check Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureGrad_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureGrad_le
#check Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureDuhamel_grad_le
#print axioms Navier.Analysis.ContinuousLeiLinPressureReconstruction.normXm1_continuousPressureDuhamel_grad_le

/-! Physical-space pressure receipts (landed 2026-09-13): the inverted
pressure p = 𝓕⁻ p̂ with its pointwise budget, and the ∫ p Δφ identity in
transported-pairing form — the primitive's first named residual, now a
theorem.  The `L¹` product→convolution bridge `𝓕⁻(a ⋆ b) = 𝓕⁻a · 𝓕⁻b`
is proved (`PressureStressTensor.fourierInv_bilin_convolution`, bare `L¹`
hypotheses), and the fully-physical stress-tensor rewrite
`∫ p Δψ = -∑ᵢⱼ ∫ ∂ᵢ∂ⱼ(vᵢvⱼ) ψ` is proved for Schwartz data
(`continuousPressurePhysical_pairing_stressTensor`); the open part is the
stress-pairing transport for general box elements, whose bounded continuous
`vᵢ` need not be integrable (header of `PressureStressTensor`). -/
#check Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_pairing_physicalLaplacian
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_pairing_physicalLaplacian
#check Navier.Analysis.ContinuousLeiLinPressurePhysical.norm_continuousPressurePhysical_le
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.norm_continuousPressurePhysical_le
#check Navier.Analysis.ContinuousLeiLinPressurePhysical.integral_fourierInv_pairing
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.integral_fourierInv_pairing
#check Navier.Analysis.PressureStressTensor.fourierInv_bilin_convolution
#print axioms Navier.Analysis.PressureStressTensor.fourierInv_bilin_convolution
#check Navier.Analysis.PressureStressTensor.continuousPressurePhysical_pairing_stressTensor
#print axioms Navier.Analysis.PressureStressTensor.continuousPressurePhysical_pairing_stressTensor

/-! BKM vorticity-divergence receipts (landed 2026-09-13, DECOMPOSED): the
vorticity rate V, its continuity, the conditional divergence chain and the
top-valued vorticity control. The named residual — the positive Grönwall pair
Y, Y' with Y' ≤ V·Y and ‖u‖ ≤ Y for the selected profile — is constructed
nowhere; these receipts prove everything downstream of such a pair. -/
#check Navier.Analysis.BKMVorticityIntegralDivergence.V_continuousOn
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.V_continuousOn
#check Navier.Analysis.BKMVorticityIntegralDivergence.lintegral_vorticity_integral_divergence
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.lintegral_vorticity_integral_divergence
#check Navier.Analysis.BKMVorticityIntegralDivergence.bkmVorticityControl_eq_top
#print axioms Navier.Analysis.BKMVorticityIntegralDivergence.bkmVorticityControl_eq_top

/-! Mild-assembly leaves receipts (landed 2026-09-13, DECOMPOSED): the
joint-source measurability primitive and its three consumer leaves are closed
for general box elements; the remaining record content is the two named
sub-records, and the ∀t heat-explosion obstruction (t < 0) is recorded where
it is packaged; the restricted-domain repair landed in lane L6c (below). -/
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.continuousNavierSource_joint_aestronglyMeasurable_of_jointProxies
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.continuousNavierSource_joint_aestronglyMeasurable_of_jointProxies
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildLeafHjointDiag
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildLeafHjointDiag
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildAssemblyLeaves_of_namedLeaves
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildAssemblyLeaves_of_namedLeaves

/-! Fixed-point pressure consumption receipts (landed 2026-09-13, lane P2):
the assembly premise is WITNESSED INHABITED — `record_zeroBox` constructs a
full `MildAssemblyLeaves` instance (a = 0, R = 0) and
`existsUnique_mildFixedPoint_zeroBox` applies the conditional assembly to it,
so `actual_existsUnique_mildFixedPoint` is not a vacuous conditional; the
non-degenerate discharge of the every-time `X¹` time leaves is the named
open construction (time-leaf block below). `fixedPoint_pressureEq` consumes the physical inversion AT a
fixed point; the conditional feed bound carries its feeds visible. -/
#check Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.record_zeroBox
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.record_zeroBox
#check Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.existsUnique_mildFixedPoint_zeroBox
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.existsUnique_mildFixedPoint_zeroBox
#check Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.fixedPoint_pressureEq
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.fixedPoint_pressureEq
#check Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.pressureDuhamel_grad_normXm1_le_of_feed
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPressure.pressureDuhamel_grad_normXm1_le_of_feed

/-! Time-leaf receipts (landed 2026-09-13, lane L6c): the record's pointwise
fields are restated over the horizon `t ∈ Icc 0 T` via the zero extension
`mildImageIcc` (equal to the mild image on the horizon and zero off it — the
unrestricted `∀ t` reading is FALSE at `t < 0`, where the heat multiplier
`exp(ν‖ξ‖²|t|)` explodes the moments), with the constructor obligation
supplied by `mildImageIcc_aestronglyMeasurable` /
`mildImageIcc_integrableXm1` / `mildImageIcc_integrableX1`.  Four of the
six time leaves are CLOSED for general box elements at every horizon time —
spatial measurability `hmM` (2a), `X⁻¹` integrability `hmXm1` (2b), the
`X⁻¹` section measurability `hmXm1Time` (2d,
`mildTimeLeaf_hmXm1Time_actualBox`, lane L6d2) and the spacetime `X¹`
budget `hmX1Int` (2f) — with the `a.e.`-time `X¹` reading
`mildTimeLeaf_hmX1_ae` as the maximal honest unconditional supplier behind
the every-time field.  Both polarization leaves are CLOSED for every actual
box element (`mildPolarizationLeaves_actualBox`, lane L6d4).  The every-time
`hmX1` (2c) and `hmX1Time` (2e) are proved under the named input
`SourceL1X1` (`mildAssemblyTimeLeaves_of_sourceL1X1`) and are the exact open
propositions unconditionally.  The general-box universal supplier is now
kernel-refuted at `(ν,T)=(1,1)` for every positive radius by
`not_forall_actualLinkedBox_sourceL1X1`.  The proved scoped supplier is
`LinkedBoxX2Carrier.boxX2_sourceL1X1_of_hv`, which uses the extended record's
integrated `X²` budget and still requires continuity of its gated
representative.  `ContRepPinProdAe` closes the product-a.e. pin for the zero
and constant `ActualLinkedBoxX2ContRep` suppliers, while its own honest-scope
note retains source-bound transport as a separate residual. -/
#check Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_aestronglyMeasurable
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_aestronglyMeasurable
#check Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_integrableXm1
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_integrableXm1
#check Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_integrableX1
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_integrableX1
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmM
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmM
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmXm1
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmXm1
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmX1_ae
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmX1_ae
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmX1Int
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmX1Int
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmXm1Time_actualBox
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildTimeLeaf_hmXm1Time_actualBox
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildPolarizationLeaves_actualBox
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildPolarizationLeaves_actualBox
#check Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildAssemblyTimeLeaves_of_sourceL1X1
#print axioms Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves.mildAssemblyTimeLeaves_of_sourceL1X1
#check Navier.Analysis.SourceL1X1BoxFalsification.not_forall_actualLinkedBox_sourceL1X1
#print axioms Navier.Analysis.SourceL1X1BoxFalsification.not_forall_actualLinkedBox_sourceL1X1
#check Navier.Analysis.LinkedBoxX2Carrier.boxX2_sourceL1X1_of_hv
#print axioms Navier.Analysis.LinkedBoxX2Carrier.boxX2_sourceL1X1_of_hv
#check Navier.Analysis.ContRepPinProdAe.boxX2ZeroContRep_pinProdAe
#print axioms Navier.Analysis.ContRepPinProdAe.boxX2ZeroContRep_pinProdAe
#check Navier.Analysis.ContRepPinProdAe.boxX2ConstantContRep_pinProdAe
#print axioms Navier.Analysis.ContRepPinProdAe.boxX2ConstantContRep_pinProdAe

/-! Grönwall-pair decomposition receipts (landed 2026-09-14, lane L6b2,
DECOMPOSED): for the constructed forced alternative-C profile the Grönwall
control pair of the BKM vorticity-divergence decomposition is equivalent to
the single scalar velocity estimate `(†)`, the uniform-sup shortcut is
kernel-falsified (`no_uniform_sup_bound`), the Biot–Savart route supplies the
velocity-to-vorticity-majorant bridge `velocity_le_V`, and the exact remaining
dependency is the named scalar vorticity-rate estimate `VorticityRateBound` —
one inequality from the pair and from the two crown divergence corollaries.
All six receipts print the strict axiom set. -/
#check Navier.Analysis.BKMProfileGronwallPair.gronwall_pair_iff_velocity_bound
#print axioms Navier.Analysis.BKMProfileGronwallPair.gronwall_pair_iff_velocity_bound
#check Navier.Analysis.BKMProfileGronwallPair.no_uniform_sup_bound
#print axioms Navier.Analysis.BKMProfileGronwallPair.no_uniform_sup_bound
#check Navier.Analysis.BKMProfileGronwallPair.velocity_le_V
#print axioms Navier.Analysis.BKMProfileGronwallPair.velocity_le_V
#check Navier.Analysis.BKMProfileGronwallPair.gronwall_pair_of_rate_bound
#print axioms Navier.Analysis.BKMProfileGronwallPair.gronwall_pair_of_rate_bound
#check Navier.Analysis.BKMProfileGronwallPair.vorticity_integral_divergence_of_gronwall_pair
#print axioms Navier.Analysis.BKMProfileGronwallPair.vorticity_integral_divergence_of_gronwall_pair
#check Navier.Analysis.BKMProfileGronwallPair.lintegral_vorticity_integral_divergence_of_rate_bound
#print axioms Navier.Analysis.BKMProfileGronwallPair.lintegral_vorticity_integral_divergence_of_rate_bound

/-! Lane L6b3 (2026-09-14): the named `VorticityRateBound` leaf is reduced to one of two
quantitative envelopes for the selected profile — a two-sided power-law sandwich
(`α > 1` exact, consumed through the convergent antiderivative) or a monotone
self-referential lag bound on geometric windows — and each envelope is wired through
the L6b2 consumers to the Grönwall pair and both crown divergence corollaries.
Soundness content fixed here: an UPPER envelope alone never suffices (a monotonicity or
lower envelope is consumed too), and ODE majorization with constant C ≠ 1 does not imply
the leaf. All fourteen receipts print the strict axiom set. -/
#check Navier.Analysis.BKMProfileRateBound.pow_le_C_exp
#print axioms Navier.Analysis.BKMProfileRateBound.pow_le_C_exp
#check Navier.Analysis.BKMProfileRateBound.rpow_le_C_exp
#print axioms Navier.Analysis.BKMProfileRateBound.rpow_le_C_exp
#check Navier.Analysis.BKMProfileRateBound.one_add_rpow_le_C_exp
#print axioms Navier.Analysis.BKMProfileRateBound.one_add_rpow_le_C_exp
#check Navier.Analysis.BKMProfileRateBound.lag_pow_le_exp
#print axioms Navier.Analysis.BKMProfileRateBound.lag_pow_le_exp
#check Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_sandwich
#print axioms Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_sandwich
#check Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_monotoneLag
#print axioms Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_monotoneLag
#check Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_sandwich_for
#print axioms Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_sandwich_for
#check Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_monotoneLag_for
#print axioms Navier.Analysis.BKMProfileRateBound.vorticityRateBound_of_monotoneLag_for
#check Navier.Analysis.BKMProfileRateBound.gronwall_pair_of_sandwich_for
#print axioms Navier.Analysis.BKMProfileRateBound.gronwall_pair_of_sandwich_for
#check Navier.Analysis.BKMProfileRateBound.vorticity_integral_divergence_of_sandwich_for
#print axioms Navier.Analysis.BKMProfileRateBound.vorticity_integral_divergence_of_sandwich_for
#check Navier.Analysis.BKMProfileRateBound.lintegral_vorticity_integral_divergence_of_sandwich_for
#print axioms Navier.Analysis.BKMProfileRateBound.lintegral_vorticity_integral_divergence_of_sandwich_for
#check Navier.Analysis.BKMProfileRateBound.gronwall_pair_of_monotoneLag_for
#print axioms Navier.Analysis.BKMProfileRateBound.gronwall_pair_of_monotoneLag_for
#check Navier.Analysis.BKMProfileRateBound.vorticity_integral_divergence_of_monotoneLag_for
#print axioms Navier.Analysis.BKMProfileRateBound.vorticity_integral_divergence_of_monotoneLag_for
#check Navier.Analysis.BKMProfileRateBound.lintegral_vorticity_integral_divergence_of_monotoneLag_for
#print axioms Navier.Analysis.BKMProfileRateBound.lintegral_vorticity_integral_divergence_of_monotoneLag_for

/-! ## Lane L6b5 (2026-09-14): q-envelope bridge `BKMProfileEnvelope`. -/
#check Navier.Analysis.BKMProfileEnvelope.forwardScalar_le_self
#print axioms Navier.Analysis.BKMProfileEnvelope.forwardScalar_le_self
#check Navier.Analysis.BKMProfileEnvelope.one_sub_le_physicalQ
#print axioms Navier.Analysis.BKMProfileEnvelope.one_sub_le_physicalQ
#check Navier.Analysis.BKMProfileEnvelope.physicalQ_axis
#print axioms Navier.Analysis.BKMProfileEnvelope.physicalQ_axis
#check Navier.Analysis.BKMProfileEnvelope.vorticityRateBound_of_q_curlBound
#print axioms Navier.Analysis.BKMProfileEnvelope.vorticityRateBound_of_q_curlBound
#check Navier.Analysis.BKMProfileEnvelope.gronwall_pair_of_q_curlBound
#print axioms Navier.Analysis.BKMProfileEnvelope.gronwall_pair_of_q_curlBound
#check Navier.Analysis.BKMProfileEnvelope.vorticity_integral_divergence_of_q_curlBound
#print axioms Navier.Analysis.BKMProfileEnvelope.vorticity_integral_divergence_of_q_curlBound
#check Navier.Analysis.BKMProfileEnvelope.lintegral_vorticity_integral_divergence_of_q_curlBound
#print axioms Navier.Analysis.BKMProfileEnvelope.lintegral_vorticity_integral_divergence_of_q_curlBound

/-! ## Lane L6b6 (2026-09-14): polynomial-upper / axis-lower third bridge `BKMProfileSelectedEnvelope`. -/
#check Navier.Analysis.BKMProfileSelectedEnvelope.vorticityRateBound_of_polyUpper_axisLower
#print axioms Navier.Analysis.BKMProfileSelectedEnvelope.vorticityRateBound_of_polyUpper_axisLower

/-! ## Lane L6b4 (2026-09-14): exact-constant axis vorticity blow-up `BaseVorticityAxis`. -/
#check Navier.Construction.BaseVorticityAxis.baseVorticity_axis
#print axioms Navier.Construction.BaseVorticityAxis.baseVorticity_axis
#check Navier.Construction.BaseVorticityAxis.baseVorticity_norm_at_origin
#print axioms Navier.Construction.BaseVorticityAxis.baseVorticity_norm_at_origin
#check Navier.Construction.BaseVorticityAxis.baseVorticity_axis_tendsto_atTop
#print axioms Navier.Construction.BaseVorticityAxis.baseVorticity_axis_tendsto_atTop
#check Navier.Construction.FinalSlowBase.inv_phi_axis
#print axioms Navier.Construction.FinalSlowBase.inv_phi_axis
#check Navier.Construction.FinalSlowBase.f_axis_positive
#print axioms Navier.Construction.FinalSlowBase.f_axis_positive
#check Navier.Construction.FinalSlowBase.axis_vorticity_origin
#print axioms Navier.Construction.FinalSlowBase.axis_vorticity_origin
#check Navier.Construction.FinalSlowBase.axis_vorticity_tendsto
#print axioms Navier.Construction.FinalSlowBase.axis_vorticity_tendsto

/-! ## Stable API — correction-step interface (lane rsi-pv-navier, 2026-10-01)

`Navier/Construction/CorrectionStep.lean` and
`Navier/Construction/CorrectionInitialization.lean` are load-bearing providers
(top of the priority stratum; public exports: CorrectionStep 556 named + 233
field projections, CorrectionInitialization 394 named + 76). The names below are
the stable API of the correction-step interface: every public name either file
currently exports that a direct importer references (144 from CorrectionStep
across 11 direct importers; 138 from CorrectionInitialization across 9).

Deleting, renaming, or relocating a pinned name fails this audit (and every
`lake env lean Navier.lean` closure) before downstream consumers break; the
printed types record the pinned signature surface in the build log. Future
lanes must validate `make conditional-audit` before refactoring either file.

Method note: consumer references were computed by a comment-stripped static
scan of the direct importers; each pinned name itself resolves from the module
sources, which the compiler checks here. -/
/-! ### Navier.Construction.CorrectionStep — 144 names consumed by direct importers -/
#check Navier.Construction.CorrectionStep.ScalarField
#print axioms Navier.Construction.CorrectionStep.ScalarField
#check Navier.Construction.CorrectionStep.Tensor
#print axioms Navier.Construction.CorrectionStep.Tensor
#check Navier.Construction.CorrectionStep.axialCovarianceChange
#print axioms Navier.Construction.CorrectionStep.axialCovarianceChange
#check Navier.Construction.CorrectionStep.TensorClass
#print axioms Navier.Construction.CorrectionStep.TensorClass
#check Navier.Construction.CorrectionStep.thetaCovarianceChange_mem
#print axioms Navier.Construction.CorrectionStep.thetaCovarianceChange_mem
#check Navier.Construction.CorrectionStep.axialCovarianceChange_mem
#print axioms Navier.Construction.CorrectionStep.axialCovarianceChange_mem
#check Navier.Construction.CorrectionStep.fullGoodResidual
#print axioms Navier.Construction.CorrectionStep.fullGoodResidual
#check Navier.Construction.CorrectionStep.angularMeanVector
#print axioms Navier.Construction.CorrectionStep.angularMeanVector
#check Navier.Construction.CorrectionStep.AngularContinuous
#print axioms Navier.Construction.CorrectionStep.AngularContinuous
#check Navier.Construction.CorrectionStep.covarianceIncrement
#print axioms Navier.Construction.CorrectionStep.covarianceIncrement
#check Navier.Construction.CorrectionStep.meanBar
#print axioms Navier.Construction.CorrectionStep.meanBar
#check Navier.Construction.CorrectionStep.meanLift
#print axioms Navier.Construction.CorrectionStep.meanLift
#check Navier.Construction.CorrectionStep.fullDivergence
#print axioms Navier.Construction.CorrectionStep.fullDivergence
#check Navier.Construction.CorrectionStep.fullDivergence_actual_update
#print axioms Navier.Construction.CorrectionStep.fullDivergence_actual_update
#check Navier.Construction.CorrectionStep.SameCarrier
#print axioms Navier.Construction.CorrectionStep.SameCarrier
#check Navier.Construction.CorrectionStep.SameCarrier.frequency
#print axioms Navier.Construction.CorrectionStep.SameCarrier.frequency
#check Navier.Construction.CorrectionStep.SameCarrier.angular
#print axioms Navier.Construction.CorrectionStep.SameCarrier.angular
#check Navier.Construction.CorrectionStep.gaugeRefreshPressureAlias
#print axioms Navier.Construction.CorrectionStep.gaugeRefreshPressureAlias
#check Navier.Construction.CorrectionStep.zeroTriple
#print axioms Navier.Construction.CorrectionStep.zeroTriple
#check Navier.Construction.CorrectionStep.updated_zeroTriple
#print axioms Navier.Construction.CorrectionStep.updated_zeroTriple
#check Navier.Construction.CorrectionStep.gaugeWaveStage
#print axioms Navier.Construction.CorrectionStep.gaugeWaveStage
#check Navier.Construction.CorrectionStep.gaugeWaveStage_cumulative
#print axioms Navier.Construction.CorrectionStep.gaugeWaveStage_cumulative
#check Navier.Construction.CorrectionStep.SignedParameters.Control.covariance
#print axioms Navier.Construction.CorrectionStep.SignedParameters.Control.covariance
#check Navier.Construction.CorrectionStep.SignedParameters.Control.normal
#print axioms Navier.Construction.CorrectionStep.SignedParameters.Control.normal
#check Navier.Construction.CorrectionStep.SignedParameters.Control.normalMotion
#print axioms Navier.Construction.CorrectionStep.SignedParameters.Control.normalMotion
#check Navier.Construction.CorrectionStep.SignedParameters.Control.radius
#print axioms Navier.Construction.CorrectionStep.SignedParameters.Control.radius
#check Navier.Construction.CorrectionStep.SignedParameters.Control.cutoff
#print axioms Navier.Construction.CorrectionStep.SignedParameters.Control.cutoff
#check Navier.Construction.CorrectionStep.GaugeSupported.zero
#print axioms Navier.Construction.CorrectionStep.GaugeSupported.zero
#check Navier.Construction.CorrectionStep.PeriodizedSignedParameters
#print axioms Navier.Construction.CorrectionStep.PeriodizedSignedParameters
#check Navier.Construction.CorrectionStep.PeriodizedSignedParameters.directions
#print axioms Navier.Construction.CorrectionStep.PeriodizedSignedParameters.directions
#check Navier.Construction.CorrectionStep.PeriodizedSignedParameters.matrix
#print axioms Navier.Construction.CorrectionStep.PeriodizedSignedParameters.matrix
#check Navier.Construction.CorrectionStep.PeriodizedSignedParameters.fundamental
#print axioms Navier.Construction.CorrectionStep.PeriodizedSignedParameters.fundamental
#check Navier.Construction.CorrectionStep.PeriodizedSignedParameters.cutoff
#print axioms Navier.Construction.CorrectionStep.PeriodizedSignedParameters.cutoff
#check Navier.Construction.CorrectionStep.PeriodizedSignedParameters.angularFrequency
#print axioms Navier.Construction.CorrectionStep.PeriodizedSignedParameters.angularFrequency
#check Navier.Construction.CorrectionStep.PeriodizedSignedParameters.copyData
#print axioms Navier.Construction.CorrectionStep.PeriodizedSignedParameters.copyData
#check Navier.Construction.CorrectionStep.PeriodizedSignedParameters.exactBlock
#print axioms Navier.Construction.CorrectionStep.PeriodizedSignedParameters.exactBlock
#check Navier.Construction.CorrectionStep.ParticularParameters
#print axioms Navier.Construction.CorrectionStep.ParticularParameters
#check Navier.Construction.CorrectionStep.ParticularParameters.geometry
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.geometry
#check Navier.Construction.CorrectionStep.ParticularParameters.length_pos
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.length_pos
#check Navier.Construction.CorrectionStep.ParticularParameters.cutoff
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.cutoff
#check Navier.Construction.CorrectionStep.ParticularParameters.background
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.background
#check Navier.Construction.CorrectionStep.ParticularParameters.directions
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.directions
#check Navier.Construction.CorrectionStep.ParticularParameters.copyData
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.copyData
#check Navier.Construction.CorrectionStep.ParticularParameters.nativeStrip
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.nativeStrip
#check Navier.Construction.CorrectionStep.ParticularParameters.updateBlock
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.updateBlock
#check Navier.Construction.CorrectionStep.ParticularParameters.gaussianBlock
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.gaussianBlock
#check Navier.Construction.CorrectionStep.CyclePoint
#print axioms Navier.Construction.CorrectionStep.CyclePoint
#check Navier.Construction.CorrectionStep.CycleSlow
#print axioms Navier.Construction.CorrectionStep.CycleSlow
#check Navier.Construction.CorrectionStep.cycleAssoc
#print axioms Navier.Construction.CorrectionStep.cycleAssoc
#check Navier.Construction.CorrectionStep.CycleCoefficients
#print axioms Navier.Construction.CorrectionStep.CycleCoefficients
#check Navier.Construction.CorrectionStep.CycleCoefficients.labels
#print axioms Navier.Construction.CorrectionStep.CycleCoefficients.labels
#check Navier.Construction.CorrectionStep.CycleCoefficients.blocks
#print axioms Navier.Construction.CorrectionStep.CycleCoefficients.blocks
#check Navier.Construction.CorrectionStep.CycleCoefficients.gaussian
#print axioms Navier.Construction.CorrectionStep.CycleCoefficients.gaussian
#check Navier.Construction.CorrectionStep.CycleCoefficients.aliasCoefficients
#print axioms Navier.Construction.CorrectionStep.CycleCoefficients.aliasCoefficients
#check Navier.Construction.CorrectionStep.CycleCoefficients.residualBand
#print axioms Navier.Construction.CorrectionStep.CycleCoefficients.residualBand
#check Navier.Construction.CorrectionStep.CycleParameters
#print axioms Navier.Construction.CorrectionStep.CycleParameters
#check Navier.Construction.CorrectionStep.CycleParameters.timeExponent
#print axioms Navier.Construction.CorrectionStep.CycleParameters.timeExponent
#check Navier.Construction.CorrectionStep.CycleParameters.commonIndex
#print axioms Navier.Construction.CorrectionStep.CycleParameters.commonIndex
#check Navier.Construction.CorrectionStep.CycleParameters.particularBlock
#print axioms Navier.Construction.CorrectionStep.CycleParameters.particularBlock
#check Navier.Construction.CorrectionStep.CycleParameters.particularGaussianBlock
#print axioms Navier.Construction.CorrectionStep.CycleParameters.particularGaussianBlock
#check Navier.Construction.CorrectionStep.CycleParameters.particularVelocity
#print axioms Navier.Construction.CorrectionStep.CycleParameters.particularVelocity
#check Navier.Construction.CorrectionStep.CycleParameters.particularPressure
#print axioms Navier.Construction.CorrectionStep.CycleParameters.particularPressure
#check Navier.Construction.CorrectionStep.CycleParameters.particularGaussian
#print axioms Navier.Construction.CorrectionStep.CycleParameters.particularGaussian
#check Navier.Construction.CorrectionStep.CycleParameters.afterParticular
#print axioms Navier.Construction.CorrectionStep.CycleParameters.afterParticular
#check Navier.Construction.CorrectionStep.CycleParameters.signedBlock
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedBlock
#check Navier.Construction.CorrectionStep.CycleParameters.signedGaussianBlock
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedGaussianBlock
#check Navier.Construction.CorrectionStep.CycleParameters.signedVelocity
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedVelocity
#check Navier.Construction.CorrectionStep.CycleParameters.signedPressure
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedPressure
#check Navier.Construction.CorrectionStep.CycleParameters.signedGaussian
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedGaussian
#check Navier.Construction.CorrectionStep.CycleParameters.afterSigned
#print axioms Navier.Construction.CorrectionStep.CycleParameters.afterSigned
#check Navier.Construction.CorrectionStep.CycleParameters.temporalIncrement
#print axioms Navier.Construction.CorrectionStep.CycleParameters.temporalIncrement
#check Navier.Construction.CorrectionStep.CycleParameters.afterTemporal
#print axioms Navier.Construction.CorrectionStep.CycleParameters.afterTemporal
#check Navier.Construction.CorrectionStep.CycleParameters.rankIncrement
#print axioms Navier.Construction.CorrectionStep.CycleParameters.rankIncrement
#check Navier.Construction.CorrectionStep.CycleParameters.finalBlock
#print axioms Navier.Construction.CorrectionStep.CycleParameters.finalBlock
#check Navier.Construction.CorrectionStep.CycleParameters.particularBlock_band
#print axioms Navier.Construction.CorrectionStep.CycleParameters.particularBlock_band
#check Navier.Construction.CorrectionStep.CycleParameters.next_oscillatoryPressure
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_oscillatoryPressure
#check Navier.Construction.CorrectionStep.CycleParameters.next_base_error
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_base_error
#check Navier.Construction.CorrectionStep.CycleParameters.next_alias_error
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_alias_error
#check Navier.Construction.CorrectionStep.ParticularParameters.angleStrip_nativeStrip
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.angleStrip_nativeStrip
#check Navier.Construction.CorrectionStep.AxisymmetricAlias
#print axioms Navier.Construction.CorrectionStep.AxisymmetricAlias
#check Navier.Construction.CorrectionStep.coefficientField
#print axioms Navier.Construction.CorrectionStep.coefficientField
#check Navier.Construction.CorrectionStep.CycleRepresentation
#print axioms Navier.Construction.CorrectionStep.CycleRepresentation
#check Navier.Construction.CorrectionStep.CycleRepresentation.velocity
#print axioms Navier.Construction.CorrectionStep.CycleRepresentation.velocity
#check Navier.Construction.CorrectionStep.CycleRepresentation.pressure
#print axioms Navier.Construction.CorrectionStep.CycleRepresentation.pressure
#check Navier.Construction.CorrectionStep.CoefficientBands
#print axioms Navier.Construction.CorrectionStep.CoefficientBands
#check Navier.Construction.CorrectionStep.CycleParameters.nextAxisymmetricAlias
#print axioms Navier.Construction.CorrectionStep.CycleParameters.nextAxisymmetricAlias
#check Navier.Construction.CorrectionStep.CycleParameters.next_representation
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_representation
#check Navier.Construction.CorrectionStep.CycleParameters.next_coefficient_bands
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_coefficient_bands
#check Navier.Construction.CorrectionStep.CycleParameters.next_residual_band
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_residual_band
#check Navier.Construction.CorrectionStep.CycleState
#print axioms Navier.Construction.CorrectionStep.CycleState
#check Navier.Construction.CorrectionStep.CycleState.coefficients
#print axioms Navier.Construction.CorrectionStep.CycleState.coefficients
#check Navier.Construction.CorrectionStep.CycleState.axisymmetricAlias
#print axioms Navier.Construction.CorrectionStep.CycleState.axisymmetricAlias
#check Navier.Construction.CorrectionStep.CycleState.step
#print axioms Navier.Construction.CorrectionStep.CycleState.step
#check Navier.Construction.CorrectionStep.CycleState.iterate
#print axioms Navier.Construction.CorrectionStep.CycleState.iterate
#check Navier.Construction.CorrectionStep.CycleState.iterate_zero
#print axioms Navier.Construction.CorrectionStep.CycleState.iterate_zero
#check Navier.Construction.CorrectionStep.CycleState.iterate_succ
#print axioms Navier.Construction.CorrectionStep.CycleState.iterate_succ
#check Navier.Construction.CorrectionStep.assembledCovarianceIncrement_mem
#print axioms Navier.Construction.CorrectionStep.assembledCovarianceIncrement_mem
#check Navier.Construction.CorrectionStep.gaugeWaveStage_mean_from_covariance
#print axioms Navier.Construction.CorrectionStep.gaugeWaveStage_mean_from_covariance
#check Navier.Construction.CorrectionStep.CycleParameters.beforeSignedBlock
#print axioms Navier.Construction.CorrectionStep.CycleParameters.beforeSignedBlock
#check Navier.Construction.CorrectionStep.CycleParameters.signedTangent
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedTangent
#check Navier.Construction.CorrectionStep.CycleParameters.signedCurl
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedCurl
#check Navier.Construction.CorrectionStep.CycleParameters.beforeSignedBlock_represents
#print axioms Navier.Construction.CorrectionStep.CycleParameters.beforeSignedBlock_represents
#check Navier.Construction.CorrectionStep.CycleParameters.signedVelocity_split
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedVelocity_split
#check Navier.Construction.CorrectionStep.CycleParameters.signedFamily
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedFamily
#check Navier.Construction.CorrectionStep.ParticularParameters.common_amplitude
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.common_amplitude
#check Navier.Construction.CorrectionStep.ParticularParameters.common_pressure
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.common_pressure
#check Navier.Construction.CorrectionStep.ParticularParameters.fromReference
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.fromReference
#check Navier.Construction.CorrectionStep.ParticularParameters.fromReference_coherent_amplitude
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.fromReference_coherent_amplitude
#check Navier.Construction.CorrectionStep.ParticularParameters.fromReference_coherent_pressure
#print axioms Navier.Construction.CorrectionStep.ParticularParameters.fromReference_coherent_pressure
#check Navier.Construction.CorrectionStep.meanStages_constructed
#print axioms Navier.Construction.CorrectionStep.meanStages_constructed
#check Navier.Construction.CorrectionStep.CycleParameters.finalBlock_uniform_cumulative
#print axioms Navier.Construction.CorrectionStep.CycleParameters.finalBlock_uniform_cumulative
#check Navier.Construction.CorrectionStep.CycleParameters.finalBlock_increment_bounds
#print axioms Navier.Construction.CorrectionStep.CycleParameters.finalBlock_increment_bounds
#check Navier.Construction.CorrectionStep.CycleParameters.meanStages_residual_gain
#print axioms Navier.Construction.CorrectionStep.CycleParameters.meanStages_residual_gain
#check Navier.Construction.CorrectionStep.OscillationPeriodic
#print axioms Navier.Construction.CorrectionStep.OscillationPeriodic
#check Navier.Construction.CorrectionStep.covarianceIncrement_moving
#print axioms Navier.Construction.CorrectionStep.covarianceIncrement_moving
#check Navier.Construction.CorrectionStep.symmetricCovariance_moving
#print axioms Navier.Construction.CorrectionStep.symmetricCovariance_moving
#check Navier.Construction.CorrectionStep.fieldSum_angularMean_zero
#print axioms Navier.Construction.CorrectionStep.fieldSum_angularMean_zero
#check Navier.Construction.CorrectionStep.CycleParameters.particularBlock_zero
#print axioms Navier.Construction.CorrectionStep.CycleParameters.particularBlock_zero
#check Navier.Construction.CorrectionStep.CycleParameters.next_gaussian_angularMean
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_gaussian_angularMean
#check Navier.Construction.CorrectionStep.CycleParameters.next_meanResidualBounds
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_meanResidualBounds
#check Navier.Construction.CorrectionStep.CycleParameters.ofGeometry
#print axioms Navier.Construction.CorrectionStep.CycleParameters.ofGeometry
#check Navier.Construction.CorrectionStep.CycleParameters.next_primitive
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_primitive
#check Navier.Construction.CorrectionStep.CycleParameters.next_zeroMassesOn
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_zeroMassesOn
#check Navier.Construction.CorrectionStep.CycleParameters.particularBlock_real
#print axioms Navier.Construction.CorrectionStep.CycleParameters.particularBlock_real
#check Navier.Construction.CorrectionStep.CycleParameters.signedBlock_real
#print axioms Navier.Construction.CorrectionStep.CycleParameters.signedBlock_real
#check Navier.Construction.CorrectionStep.CycleParameters.next_realCoefficients
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_realCoefficients
#check Navier.Construction.CorrectionStep.block_velocity_zero_germ_of_inputSupport
#print axioms Navier.Construction.CorrectionStep.block_velocity_zero_germ_of_inputSupport
#check Navier.Construction.CorrectionStep.velocity_zero_germ_of_inputSupport
#print axioms Navier.Construction.CorrectionStep.velocity_zero_germ_of_inputSupport
#check Navier.Construction.CorrectionStep.CycleAnalyticInvariant
#print axioms Navier.Construction.CorrectionStep.CycleAnalyticInvariant
#check Navier.Construction.CorrectionStep.CycleAnalyticInvariant.frequency
#print axioms Navier.Construction.CorrectionStep.CycleAnalyticInvariant.frequency
#check Navier.Construction.CorrectionStep.CycleAnalyticInvariant.angular
#print axioms Navier.Construction.CorrectionStep.CycleAnalyticInvariant.angular
#check Navier.Construction.CorrectionStep.CycleAnalyticInvariant.pressure
#print axioms Navier.Construction.CorrectionStep.CycleAnalyticInvariant.pressure
#check Navier.Construction.CorrectionStep.CycleAnalyticInvariant.aliasCoefficients
#print axioms Navier.Construction.CorrectionStep.CycleAnalyticInvariant.aliasCoefficients
#check Navier.Construction.CorrectionStep.CycleParameters.waveStages_residual_gain
#print axioms Navier.Construction.CorrectionStep.CycleParameters.waveStages_residual_gain
#check Navier.Construction.CorrectionStep.waveStage_mean_gain
#print axioms Navier.Construction.CorrectionStep.waveStage_mean_gain
#check Navier.Construction.CorrectionStep.CycleParameters.next_covariance_mem
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_covariance_mem
#check Navier.Construction.CorrectionStep.CycleParameters.next_gaussian_mem
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_gaussian_mem
#check Navier.Construction.CorrectionStep.CycleParameters.next_inputSupport
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_inputSupport
#check Navier.Construction.CorrectionStep.CycleParameters.next_oscillation_smooth
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_oscillation_smooth
#check Navier.Construction.CorrectionStep.CycleParameters.next_oscillation_periodic
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_oscillation_periodic
#check Navier.Construction.CorrectionStep.CycleParameters.next_oscillation_support
#print axioms Navier.Construction.CorrectionStep.CycleParameters.next_oscillation_support
#check Navier.Construction.CorrectionStep.CycleParameters.finalBlock_zero
#print axioms Navier.Construction.CorrectionStep.CycleParameters.finalBlock_zero
#check Navier.Construction.CorrectionStep.CycleParameters.finalBlock_pressure_zero
#print axioms Navier.Construction.CorrectionStep.CycleParameters.finalBlock_pressure_zero
#check Navier.Construction.CorrectionStep.CycleParameters.finalBlock_pressure_cumulative
#print axioms Navier.Construction.CorrectionStep.CycleParameters.finalBlock_pressure_cumulative

/-! ### Navier.Construction.CorrectionInitialization — 138 names consumed by direct importers -/
#check Navier.Construction.CorrectionInitialization.PrimaryPiece
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.directions
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.directions
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.coefficients
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.coefficients
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.cutoff
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.cutoff
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.exactCoefficients
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.exactCoefficients
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.velocity
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.velocity
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentVelocity
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentVelocity
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.pressure
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.pressure
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.excluded
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.excluded
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.linearGood
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.linearGood
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.linearGoodField
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.linearGoodField
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.linearResidual
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.linearResidual
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.velocity_tsupport_subset_tangent
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.velocity_tsupport_subset_tangent
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock_frequency
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock_frequency
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock_phase
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock_phase
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock_angularFrequency
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock_angularFrequency
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock_represents
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.excludedBlock_represents
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.excluded_angularContinuous
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.excluded_angularContinuous
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.excluded_mean_zero
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.excluded_mean_zero
#check Navier.Construction.CorrectionInitialization.seed
#print axioms Navier.Construction.CorrectionInitialization.seed
#check Navier.Construction.CorrectionInitialization.bandSeed
#print axioms Navier.Construction.CorrectionInitialization.bandSeed
#check Navier.Construction.CorrectionInitialization.GaugeInitialization.retainPressureAlias
#print axioms Navier.Construction.CorrectionInitialization.GaugeInitialization.retainPressureAlias
#check Navier.Construction.CorrectionInitialization.GaugeInitialization.initializedBands
#print axioms Navier.Construction.CorrectionInitialization.GaugeInitialization.initializedBands
#check Navier.Construction.CorrectionInitialization.GaugeInitialization.initializedBands_oscillation
#print axioms Navier.Construction.CorrectionInitialization.GaugeInitialization.initializedBands_oscillation
#check Navier.Construction.CorrectionInitialization.GaugeInitialization.initializedBands_error_components
#print axioms Navier.Construction.CorrectionInitialization.GaugeInitialization.initializedBands_error_components
#check Navier.Construction.CorrectionInitialization.angularMeanVector_fieldSum
#print axioms Navier.Construction.CorrectionInitialization.angularMeanVector_fieldSum
#check Navier.Construction.CorrectionInitialization.PrimaryHarmonics.block_band
#print axioms Navier.Construction.CorrectionInitialization.PrimaryHarmonics.block_band
#check Navier.Construction.CorrectionInitialization.PrimaryHarmonics.block_velocity_represents
#print axioms Navier.Construction.CorrectionInitialization.PrimaryHarmonics.block_velocity_represents
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentBlock
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentBlock
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceCoefficients
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceCoefficients
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock_frequency
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock_frequency
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock_phase
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock_phase
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock_angularFrequency
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock_angularFrequency
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentBlock_frequency
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentBlock_frequency
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentBlock_phase
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentBlock_phase
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentBlock_angularFrequency
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.tangentBlock_angularFrequency
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock_frequency
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock_frequency
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock_phase
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock_phase
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock_angularFrequency
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock_angularFrequency
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock_represents
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.harmonicBlock_represents
#check Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock_represents
#print axioms Navier.Construction.CorrectionInitialization.PrimaryPiece.differenceBlock_represents
#check Navier.Construction.CorrectionInitialization.MovingInitialization.zeroMean_reconstructed_bounds
#print axioms Navier.Construction.CorrectionInitialization.MovingInitialization.zeroMean_reconstructed_bounds
#check Navier.Construction.CorrectionInitialization.AssembledPrimary.covariance_bounds
#print axioms Navier.Construction.CorrectionInitialization.AssembledPrimary.covariance_bounds
#check Navier.Construction.CorrectionInitialization.MovingInitialization.PrimaryMeanData
#print axioms Navier.Construction.CorrectionInitialization.MovingInitialization.PrimaryMeanData
#check Navier.Construction.CorrectionInitialization.MovingInitialization.TemporalStateBounds
#print axioms Navier.Construction.CorrectionInitialization.MovingInitialization.TemporalStateBounds
#check Navier.Construction.CorrectionInitialization.MovingInitialization.InitialRankBounds
#print axioms Navier.Construction.CorrectionInitialization.MovingInitialization.InitialRankBounds
#check Navier.Construction.CorrectionInitialization.CommonWindow.levels
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.levels
#check Navier.Construction.CorrectionInitialization.CommonWindow.distance
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.distance
#check Navier.Construction.CorrectionInitialization.CommonWindow.index
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.index
#check Navier.Construction.CorrectionInitialization.CommonWindow.index_le
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.index_le
#check Navier.Construction.CorrectionInitialization.CommonWindow.index_le_native
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.index_le_native
#check Navier.Construction.CorrectionInitialization.CommonWindow.gap
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.gap
#check Navier.Construction.CorrectionInitialization.CommonWindow.native_le_index_add
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.native_le_index_add
#check Navier.Construction.CorrectionInitialization.CommonWindow.labels
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.labels
#check Navier.Construction.CorrectionInitialization.CommonWindow.indexBounds
#print axioms Navier.Construction.CorrectionInitialization.CommonWindow.indexBounds
#check Navier.Construction.CorrectionInitialization.ActualPrimary.profile
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.profile
#check Navier.Construction.CorrectionInitialization.ActualPrimary.outgoing
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.outgoing
#check Navier.Construction.CorrectionInitialization.ActualPrimary.nominal
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.nominal
#check Navier.Construction.CorrectionInitialization.ActualPrimary.h
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.h
#check Navier.Construction.CorrectionInitialization.ActualPrimary.certificate
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.certificate
#check Navier.Construction.CorrectionInitialization.ActualPrimary.modulation
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.modulation
#check Navier.Construction.CorrectionInitialization.ActualPrimary.radialVector
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.radialVector
#check Navier.Construction.CorrectionInitialization.ActualPrimary.temporalVector
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.temporalVector
#check Navier.Construction.CorrectionInitialization.ActualPrimary.vectors_det
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.vectors_det
#check Navier.Construction.CorrectionInitialization.ActualPrimary.slots
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.slots
#check Navier.Construction.CorrectionInitialization.ActualPrimary.upper
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.upper
#check Navier.Construction.CorrectionInitialization.ActualPrimary.choice
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.choice
#check Navier.Construction.CorrectionInitialization.ActualPrimary.Label
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.Label
#check Navier.Construction.CorrectionInitialization.ActualPrimary.phases
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.phases
#check Navier.Construction.CorrectionInitialization.ActualPrimary.covariance
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.covariance
#check Navier.Construction.CorrectionInitialization.ActualPrimary.prefactor
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.prefactor
#check Navier.Construction.CorrectionInitialization.ActualPrimary.covariance_eq_integral
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.covariance_eq_integral
#check Navier.Construction.CorrectionInitialization.ActualPrimary.covariance_bounds
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.covariance_bounds
#check Navier.Construction.CorrectionInitialization.ActualPrimary.spatialMask
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.spatialMask
#check Navier.Construction.CorrectionInitialization.ActualPrimary.pulseCoordinates
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.pulseCoordinates
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rawVelocity
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rawVelocity
#check Navier.Construction.CorrectionInitialization.ActualPrimary.gaussian
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.gaussian
#check Navier.Construction.CorrectionInitialization.ActualPrimary.phasePoint
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.phasePoint
#check Navier.Construction.CorrectionInitialization.ActualPrimary.geometry
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.geometry
#check Navier.Construction.CorrectionInitialization.ActualPrimary.clockWindow
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.clockWindow
#check Navier.Construction.CorrectionInitialization.ActualPrimary.length_sign
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.length_sign
#check Navier.Construction.CorrectionInitialization.ActualPrimary.commonContext
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.commonContext
#check Navier.Construction.CorrectionInitialization.ActualPrimary.commonGauge
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.commonGauge
#check Navier.Construction.CorrectionInitialization.ActualPrimary.spatialMask_eq
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.spatialMask_eq
#check Navier.Construction.CorrectionInitialization.ActualPrimary.spatialMask_native_support
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.spatialMask_native_support
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rankInner
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rankInner
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rankOuter
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rankOuter
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rankData
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rankData
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rank_radii_ordered
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rank_radii_ordered
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rankAmplitude_pos
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rankAmplitude_pos
#check Navier.Construction.CorrectionInitialization.ActualPrimary.active_left_before_rank
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.active_left_before_rank
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rank_before_active_right
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rank_before_active_right
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rankData_parameters
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rankData_parameters
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rank_geometry
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rank_geometry
#check Navier.Construction.CorrectionInitialization.ActualPrimary.nativeReferenceBounds
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.nativeReferenceBounds
#check Navier.Construction.CorrectionInitialization.ActualPrimary.toAbsolute
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.toAbsolute
#check Navier.Construction.CorrectionInitialization.ActualPrimary.toAbsolute_smooth
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.toAbsolute_smooth
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartGeometry
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartGeometry
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartGeometry_coordinates_active
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartGeometry_coordinates_active
#check Navier.Construction.CorrectionInitialization.ActualPrimary.outerRawVelocity
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.outerRawVelocity
#check Navier.Construction.CorrectionInitialization.ActualPrimary.attachedRawVelocity
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.attachedRawVelocity
#check Navier.Construction.CorrectionInitialization.ActualPrimary.uncutAmplitude
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.uncutAmplitude
#check Navier.Construction.CorrectionInitialization.ActualPrimary.periodicGaussian_smooth
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.periodicGaussian_smooth
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rawVelocity_transverse
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rawVelocity_transverse
#check Navier.Construction.CorrectionInitialization.ActualPrimary.periodicGaussian_eq_on_core
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.periodicGaussian_eq_on_core
#check Navier.Construction.CorrectionInitialization.ActualPrimary.outerRawPressure
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.outerRawPressure
#check Navier.Construction.CorrectionInitialization.ActualPrimary.attachedRawPressure
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.attachedRawPressure
#check Navier.Construction.CorrectionInitialization.ActualPrimary.uncutPressure
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.uncutPressure
#check Navier.Construction.CorrectionInitialization.ActualPrimary.rawPressure_zero_of_velocity_zero
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.rawPressure_zero_of_velocity_zero
#check Navier.Construction.CorrectionInitialization.ActualPrimary.closedMargins
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.closedMargins
#check Navier.Construction.CorrectionInitialization.ActualPrimary.bandVelocity_eq
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.bandVelocity_eq
#check Navier.Construction.CorrectionInitialization.ActualPrimary.bandPressure_eq
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.bandPressure_eq
#check Navier.Construction.CorrectionInitialization.ActualPrimary.preOuterVelocity_jets
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.preOuterVelocity_jets
#check Navier.Construction.CorrectionInitialization.ActualPrimary.preOuterPressure_jets
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.preOuterPressure_jets
#check Navier.Construction.CorrectionInitialization.ActualPrimary.attachedRawVelocity_core
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.attachedRawVelocity_core
#check Navier.Construction.CorrectionInitialization.ActualPrimary.attachedRawPressure_core
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.attachedRawPressure_core
#check Navier.Construction.CorrectionInitialization.ActualPrimary.standardRegion
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.standardRegion
#check Navier.Construction.CorrectionInitialization.ActualPrimary.activeLabels
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.activeLabels
#check Navier.Construction.CorrectionInitialization.ActualPrimary.FullPoint
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.FullPoint
#check Navier.Construction.CorrectionInitialization.ActualPrimary.nativeSlow
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.nativeSlow
#check Navier.Construction.CorrectionInitialization.ActualPrimary.nativeSlow_smooth
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.nativeSlow_smooth
#check Navier.Construction.CorrectionInitialization.ActualPrimary.absoluteAmplitude
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.absoluteAmplitude
#check Navier.Construction.CorrectionInitialization.ActualPrimary.absolutePressure
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.absolutePressure
#check Navier.Construction.CorrectionInitialization.ActualPrimary.absolutePhase
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.absolutePhase
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartCutoff
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartCutoff
#check Navier.Construction.CorrectionInitialization.ActualPrimary.piece
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.piece
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_frequency_pos
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_frequency_pos
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_phase
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_phase
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_angular
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_angular
#check Navier.Construction.CorrectionInitialization.ActualPrimary.nativeSlow_toAbsolute_eq_slowChange
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.nativeSlow_toAbsolute_eq_slowChange
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_phase_view
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_phase_view
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chart_nativePoint
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chart_nativePoint
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_amplitude_copies
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_amplitude_copies
#check Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_pressure_copies
#print axioms Navier.Construction.CorrectionInitialization.ActualPrimary.chartCoefficients_pressure_copies

/-! Envelope-crown receipts (card DC-6).  The curated consumer-facing audit
emitted BKM-envelope receipts but not the envelope crown: today the single
live-premise reduction of statement A,
`HorizonFreeBudgetRestart.crown_from_envelopeApriori`
(HorizonFreeBudgetRestart.lean:250 — its only carried premise is
`APrioriIn RegularOnCompacts h3EnvelopeControl`, the F-026 propagation rung),
and its landed base-case seeds `EnvelopeDatumSeed.h3F_lt_top_of_schwartz`
(EnvelopeDatumSeed.lean:80) and `EnvelopeDatumSeed.envelopeBudget_datumSeed`
(:138). -/
#check Navier.Analysis.HorizonFreeBudgetRestart.crown_from_envelopeApriori
#print axioms Navier.Analysis.HorizonFreeBudgetRestart.crown_from_envelopeApriori
#check @Navier.Analysis.EnvelopeDatumSeed.h3F_lt_top_of_schwartz
#print axioms Navier.Analysis.EnvelopeDatumSeed.h3F_lt_top_of_schwartz
#check @Navier.Analysis.EnvelopeDatumSeed.envelopeBudget_datumSeed
#print axioms Navier.Analysis.EnvelopeDatumSeed.envelopeBudget_datumSeed
