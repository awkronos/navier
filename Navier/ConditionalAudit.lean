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
import Navier.Analysis.BKMVorticityIntegralDivergence
import Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
import Navier.Analysis.ContinuousLeiLinMildFixedPointPressure

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
theorem; the fully-physical stress-tensor rewrite of the frequency side
remains named where the L¹ product→convolution bridge is missing. -/
#check Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_pairing_physicalLaplacian
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_pairing_physicalLaplacian
#check Navier.Analysis.ContinuousLeiLinPressurePhysical.norm_continuousPressurePhysical_le
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.norm_continuousPressurePhysical_le
#check Navier.Analysis.ContinuousLeiLinPressurePhysical.integral_fourierInv_pairing
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.integral_fourierInv_pairing

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
it is packaged — the restricted-domain repair is the named next construction. -/
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
non-degenerate discharge and the restricted-domain time leaves remain named
constructions. `fixedPoint_pressureEq` consumes the physical inversion AT a
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
`mildImageIcc_integrableXm1` / `mildImageIcc_integrableX1`.  Three of the
six time leaves are now CLOSED for general box elements at every horizon
time — spatial measurability `hmM` (2a), `X⁻¹` integrability `hmXm1` (2b),
and the spacetime `X¹` budget `hmX1Int` (2f) — with the `a.e.`-time `X¹`
reading `mildTimeLeaf_hmX1_ae` as the maximal honest supplier behind the
still-open every-time field.  Named residuals: the every-time `hmX1` (2c),
the `Lp`-valued section measurabilities `hmXm1Time` (2d) / `hmX1Time` (2e),
and the polarization leaves' all-`ξ` pointwise convolution integrabilities. -/
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
