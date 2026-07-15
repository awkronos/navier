import Navier.ClayFrontier
import Navier.OfficialProblem
import Navier.OfficialSurfaceSignatures
import Navier.Analysis.Covariance
import Navier.Analysis.CriticalL3
import Navier.Analysis.CriticalL3Integrable
import Navier.Analysis.CriticalLp
import Navier.Analysis.CriticalProfileAction
import Navier.Analysis.OfficialABEncoding
import Navier.Analysis.LerayProjection
import Navier.Analysis.VectorCalculus
import Navier.Analysis.EnergyPressureCancellation
import Navier.Analysis.ViscosityTransport
import Navier.Analysis.ViscosityAdmissibility
import Navier.Analysis.ViscosityForceDecay
import Navier.Analysis.ViscosityEndpoints
import Navier.EnergyObstruction
import Navier.ConventionBridges
import Navier.Breakdown.MaximalNonextension
import Navier.Breakdown.Restriction
import Navier.Breakdown.ForceRecovery
import Navier.Breakdown.OfficialCDEncoding
import Navier.Routes.R7.ExactSymbol
import Navier.Routes.R7.Triad
import Navier.Routes.R7.ScaledTriad
import Navier.Routes.R7.PhaseSymbol
import Navier.Routes.R7.SymmetrizedPhase
import Navier.Routes.R7.SymmetrizedWitness
import Navier.Routes.R7.WeightedShellTransfer
import Navier.Routes.R7.FieldLeakage
import Navier.Routes.R7.FullFieldLeakage

/-!
# Raw axiom audit for the public formal infrastructure

Each command below asks Lean for the transitive axioms of a named declaration.
The audit of `Clay.StatementA` concerns only the canonical proposition's
definition and its imported foundations; it does not construct an inhabitant
and is not evidence that the conjectural endpoint is proved.  The proved
declarations audited below are scaling arithmetic, disposition guards, and
finite-frontier facts.
-/

#print axioms Navier.Clay.StatementA
#print axioms Navier.Clay.StatementB
#print axioms Navier.Clay.StatementC
#print axioms Navier.Clay.StatementD
#print axioms Navier.problemEncodingResiduals_card
#print axioms Navier.OfficialSurfaceSignatures.classicalSolution_signature
#print axioms Navier.OfficialSurfaceSignatures.periodicClassicalSolution_signature
#print axioms Navier.OfficialSurfaceSignatures.statementA_signature
#print axioms Navier.OfficialSurfaceSignatures.statementB_signature
#print axioms Navier.OfficialSurfaceSignatures.statementC_signature
#print axioms Navier.OfficialSurfaceSignatures.statementD_signature

#print axioms Navier.Scaling.mixedNormExponent_eq_zero_iff
#print axioms Navier.Scaling.criticalLine_six_four
#print axioms Navier.Scaling.criticalLine_nine_three
#print axioms Navier.Scaling.reciprocalMixedNormExponent_eq_zero_iff
#print axioms Navier.Scaling.reciprocalCriticalLine_three_infinity
#print axioms Navier.Scaling.reciprocalCriticalLine_infinity_two

#print axioms Navier.EnergyObstruction.space_finrank
#print axioms Navier.EnergyObstruction.l2_energy_dilation
#print axioms Navier.EnergyObstruction.l3_critical_dilation
#print axioms Navier.EnergyObstruction.energy_not_scale_coercive
#print axioms Navier.EnergyObstruction.lp_dilation_scaling
#print axioms Navier.EnergyObstruction.time_dilation_scaling

#print axioms Navier.ConventionBridges.schwartzmap_satisfies_fefferman_rapid_decay
#print axioms Navier.ConventionBridges.schwartzmap_satisfies_fefferman_smoothness

#print axioms Navier.staticDivergence_smul
#print axioms Navier.staticDivergence_const_smul
#print axioms Navier.convection_eq_sum_coordinate_derivatives
#print axioms Navier.pressure_work_eq_staticDivergence

#print axioms Navier.Analysis.Covariance.fderiv_velocity_dilation
#print axioms Navier.Analysis.Covariance.staticDivergence_dilation
#print axioms Navier.Analysis.Covariance.zero_dilation_truth_check
#print axioms Navier.Analysis.Covariance.scaledSchwartzVelocity_apply
#print axioms Navier.Analysis.Covariance.divergenceFreeInitial_scaled
#print axioms Navier.Analysis.Covariance.fderiv_amplitude_dilation
#print axioms Navier.Analysis.Covariance.spatialDerivative_scaled
#print axioms Navier.Analysis.Covariance.divergence_scaled
#print axioms Navier.Analysis.Covariance.convection_scaled
#print axioms Navier.Analysis.Covariance.pressureGradient_scaled
#print axioms Navier.Analysis.Covariance.secondDirectionalDerivative_scaled
#print axioms Navier.Analysis.Covariance.laplacian_scaled
#print axioms Navier.Analysis.Covariance.timeDerivative_scaled
#print axioms Navier.Analysis.Covariance.satisfiesNavierStokes_scaled
#print axioms Navier.Analysis.Covariance.zero_scale_fields
#print axioms Navier.Analysis.Covariance.one_scale_fields

#print axioms Navier.Analysis.CriticalL3.criticalL3Mass_parabolicScaled
#print axioms Navier.Analysis.CriticalL3.criticalL3BoundOn_parabolicScaled_iff
#print axioms Navier.Analysis.CriticalL3.criticalL3BoundBefore_parabolicScaled_iff

#print axioms Navier.Analysis.CriticalL3Integrable.integrableCriticalL3BoundOn_to_raw
#print axioms Navier.Analysis.CriticalL3Integrable.l3SliceIntegrable_parabolicScaled_iff
#print axioms Navier.Analysis.CriticalL3Integrable.integrableCriticalL3BoundOn_parabolicScaled_iff
#print axioms Navier.Analysis.CriticalL3Integrable.integrableCriticalL3BoundBefore_parabolicScaled_iff

#print axioms Navier.Analysis.CriticalLp.memLp_three_iff_integrable_norm_cube
#print axioms Navier.Analysis.CriticalLp.aestronglyMeasurable_criticalL3SpatialScale_iff
#print axioms Navier.Analysis.CriticalLp.integrable_norm_cube_criticalL3SpatialScale_iff
#print axioms Navier.Analysis.CriticalLp.memLp_three_criticalL3SpatialScale_iff
#print axioms Navier.Analysis.CriticalLp.eLpNorm_three_criticalL3SpatialScale
#print axioms Navier.Analysis.CriticalLp.lpNorm_three_criticalL3SpatialScale
#print axioms Navier.Analysis.CriticalLp.memLp_three_iff_l3SliceIntegrable
#print axioms Navier.Analysis.CriticalLp.memLp_three_parabolicScaled_iff
#print axioms Navier.Analysis.CriticalLp.eLpNorm_three_parabolicScaled
#print axioms Navier.Analysis.CriticalLp.lpNorm_three_parabolicScaled
#print axioms Navier.Analysis.CriticalLp.criticalL3MemLpBoundOn_parabolicScaled_iff
#print axioms Navier.Analysis.CriticalLp.criticalL3MemLpBoundBefore_parabolicScaled_iff

#print axioms Navier.Analysis.CriticalProfileAction.criticalProfileAction_one_zero
#print axioms Navier.Analysis.CriticalProfileAction.criticalProfileAction_comp
#print axioms Navier.Analysis.CriticalProfileAction.criticalProfileAction_inverse_left
#print axioms Navier.Analysis.CriticalProfileAction.criticalProfileAction_inverse_right
#print axioms Navier.Analysis.CriticalProfileAction.criticalProfileAction_relative

#print axioms Navier.Analysis.OfficialABEncoding.officialEuclideanPoint_apply
#print axioms Navier.Analysis.OfficialABEncoding.officialEuclideanNorm_nonneg
#print axioms Navier.Analysis.OfficialABEncoding.officialEuclideanNorm_eq_sqrt_sum_sq
#print axioms Navier.Analysis.OfficialABEncoding.norm_le_officialEuclideanNorm
#print axioms Navier.Analysis.OfficialABEncoding.officialEuclideanNorm_le
#print axioms Navier.Analysis.OfficialABEncoding.feffermanRapidDecayBound_iff_euclideanWeight
#print axioms Navier.Analysis.OfficialABEncoding.schwartzmap_satisfies_fefferman_euclidean_weight_rapid_decay

#print axioms Navier.Analysis.LerayProjection.euclideanLeray_mem
#print axioms Navier.Analysis.LerayProjection.inner_euclideanLeray
#print axioms Navier.Analysis.LerayProjection.euclideanLeray_norm_le
#print axioms Navier.Analysis.LerayProjection.euclideanLeray_idempotent
#print axioms Navier.Analysis.LerayProjection.euclideanLeray_formula
#print axioms Navier.Analysis.LerayProjection.officialPoint_inner_eq_dotProduct
#print axioms Navier.Analysis.LerayProjection.officialPoint_norm_sq_eq_dotProduct
#print axioms Navier.Analysis.LerayProjection.officialPoint_normalizedLeray
#print axioms Navier.Analysis.LerayProjection.officialEuclideanNorm_normalizedLeray_le

#print axioms Navier.Analysis.ViscosityTransport.satisfiesNavierStokes_viscosityScaled_mul
#print axioms Navier.Analysis.ViscosityTransport.satisfiesNavierStokes_one_to_viscosity
#print axioms Navier.Analysis.ViscosityTransport.satisfiesNavierStokes_viscosity_to_one
#print axioms Navier.Analysis.ViscosityTransport.viscosityScaledForce_zero
#print axioms Navier.Analysis.ViscosityTransport.viscosityScaledVelocity_inv
#print axioms Navier.Analysis.ViscosityTransport.viscosityScaledForce_inv

#print axioms Navier.Analysis.ViscosityAdmissibility.isPeriodicClassicalSolution_viscosityScaled_mul
#print axioms Navier.Analysis.ViscosityAdmissibility.isClassicalSolution_viscosityScaled_mul
#print axioms Navier.Analysis.ViscosityAdmissibility.kineticEnergy_viscosityScaled
#print axioms Navier.Analysis.ViscosityAdmissibility.forcedDataRapidDecay_zeroForce
#print axioms Navier.Analysis.ViscosityAdmissibility.periodicForcedDataRapidDecay_zeroForce

#print axioms Navier.Analysis.ViscosityForceDecay.iteratedFDerivWithin_viscosityScaledForce
#print axioms Navier.Analysis.ViscosityForceDecay.forcedDataRapidDecay_viscosityScaled
#print axioms Navier.Analysis.ViscosityForceDecay.periodicForcedDataRapidDecay_viscosityScaled

#print axioms Navier.Analysis.ViscosityEndpoints.statementA_iff_atViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.statementB_iff_atViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.statementC_iff_atViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.statementD_iff_atViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.statementC_of_zeroForceAtViscosityOne
#print axioms Navier.Analysis.ViscosityEndpoints.statementD_of_zeroForceAtViscosityOne

#print axioms Navier.Breakdown.bounded_pointEvaluation_of_smooth
#print axioms Navier.Breakdown.noGlobal_of_pointEvaluationBreakdown
#print axioms Navier.Breakdown.noWholeSpaceGlobal_of_pointEvaluationBreakdown
#print axioms Navier.Breakdown.noPeriodicGlobal_of_pointEvaluationBreakdown

#print axioms Navier.Breakdown.spacetimeBefore_mono
#print axioms Navier.Breakdown.PartialClassicalSolution.restrict
#print axioms Navier.Breakdown.PartialClassicalSolution.restrict_velocity
#print axioms Navier.Breakdown.PartialClassicalSolution.restrict_pressure
#print axioms Navier.Breakdown.PartialClassicalSolution.restrict_restrict
#print axioms Navier.Breakdown.velocityAgreesBefore_refl
#print axioms Navier.Breakdown.velocityAgreesBefore_symm
#print axioms Navier.Breakdown.velocityAgreesBefore_trans
#print axioms Navier.Breakdown.velocityAgreesBefore_mono

#print axioms Navier.Breakdown.ForceRecovery.recoveredForce
#print axioms Navier.Breakdown.ForceRecovery.satisfiesNavierStokes_iff_force_eq_recoveredForce
#print axioms Navier.Breakdown.ForceRecovery.satisfiesNavierStokesBefore_iff_force_eq_recoveredForce
#print axioms Navier.Breakdown.PartialClassicalSolution.ofClassical
#print axioms Navier.Breakdown.zeroPartialClassicalSolution
#print axioms Navier.Breakdown.zeroPartial_not_pointNormUnbounded

#print axioms Navier.Breakdown.OfficialCDEncoding.norm_le_euclideanNorm
#print axioms Navier.Breakdown.OfficialCDEncoding.euclideanNorm_le_sqrt_three_mul_norm
#print axioms Navier.Breakdown.OfficialCDEncoding.abs_coordinateForceDerivativeWithin_le
#print axioms Navier.Breakdown.OfficialCDEncoding.forcedDataRapidDecay_implies_coordinatewise
#print axioms Navier.Breakdown.OfficialCDEncoding.periodicForcedDataRapidDecay_implies_coordinatewise

#print axioms Navier.Routes.R7.dot_lerayNumerator
#print axioms Navier.Routes.R7.divergenceFree_singleMode_selfInteraction_zero
#print axioms Navier.Routes.R7.countermodel_energyCancellation
#print axioms Navier.Routes.R7.countermodel_witness_value
#print axioms Navier.Routes.R7.countermodel_selfInteraction_ne_zero

#print axioms Navier.Routes.R7.receiver_dot_lerayNumerator
#print axioms Navier.Routes.R7.advector_pair_cancels
#print axioms Navier.Routes.R7.grouped_six_transfer_cancellation
#print axioms Navier.Routes.R7.six_transfer_sum_zero
#print axioms Navier.Routes.R7.witness_admissible
#print axioms Navier.Routes.R7.witness_nontermwise_cancellation

#print axioms Navier.Routes.R7.scaled_witness_admissible
#print axioms Navier.Routes.R7.scaled_witness_orderedTransfer
#print axioms Navier.Routes.R7.scaled_witness_sixTransferSum
#print axioms Navier.Routes.R7.orderedTransfer_unbounded_across_scale

#print axioms Navier.Routes.R7.normalizedLeraySymbol_zero
#print axioms Navier.Routes.R7.receiver_dot_normalizedLeraySymbol
#print axioms Navier.Routes.R7.normalizedProjectedOrderedCoefficient_eq_orderedTransfer
#print axioms Navier.Routes.R7.receiver_orthogonal_output_of_triad
#print axioms Navier.Routes.R7.phasedNormalizedProjectedCoefficient_eq_ordered
#print axioms Navier.Routes.R7.unphased_witness_real_part_zero
#print axioms Navier.Routes.R7.phased_witness_orderedCoefficient
#print axioms Navier.Routes.R7.witness_phase_factors_have_unit_norm
#print axioms Navier.Routes.R7.witness_receiver_orthogonal_output
#print axioms Navier.Routes.R7.phased_normalized_witness_coefficient
#print axioms Navier.Routes.R7.witness_opposite_orderedCoefficient
#print axioms Navier.Routes.R7.scaled_witness_receiver_orthogonal_output
#print axioms Navier.Routes.R7.phased_scaled_normalized_coefficient
#print axioms Navier.Routes.R7.phased_normalized_coefficient_unbounded_across_positive_scale

#print axioms Navier.Routes.R7.phased_symmetrized_scaled_witness_cancels
#print axioms Navier.Routes.R7.no_scaled_witness_nonzero_symmetrized_output

#print axioms Navier.Routes.R7.sym_scaled_witness_admissible
#print axioms Navier.Routes.R7.phased_symmetrized_scaled_witness_coefficient
#print axioms Navier.Routes.R7.phased_symmetrized_coefficient_unbounded_across_positive_scale
#print axioms Navier.Routes.R7.symWitnessModeCoefficient_conjugate
#print axioms Navier.Routes.R7.symWitnessMode_divergence_free

#print axioms Navier.Routes.R7.symWitnessRateK_eq_zero
#print axioms Navier.Routes.R7.symWitnessRateL_eq_neg
#print axioms Navier.Routes.R7.symWitnessRateM_eq
#print axioms Navier.Routes.R7.symWitness_constantWeight_cancels
#print axioms Navier.Routes.R7.symWitnessSquaredFrequencyRate_eq_cube
#print axioms Navier.Routes.R7.symWitnessSquaredFrequencyRate_pos

#print axioms Navier.Routes.R7.phased_symmetrized_scaled_leak_coefficient
#print axioms Navier.Routes.R7.leakOutputWave_not_in_six_mode_support
#print axioms Navier.Routes.R7.six_mode_support_has_nonzero_off_support_interaction

#print axioms Navier.Routes.R7.pairProducesLeakOutput_iff
#print axioms Navier.Routes.R7.fullSixModeProjectedLeakCoefficient_eq_scale
#print axioms Navier.Routes.R7.fullSixMode_has_nonzero_off_support_coefficient

#print axioms Navier.ScientificDisposition.readiness_realized
#print axioms Navier.ScientificDisposition.readiness_falsified
#print axioms Navier.ScientificDisposition.readiness_conditional
#print axioms Navier.ScientificDisposition.readiness_conjectural
#print axioms Navier.ScientificDisposition.readiness_quarantined
#print axioms Navier.ScientificDisposition.readiness_eq_true_iff_status_eq_realized
#print axioms Navier.ScientificDisposition.readiness_eq_false_iff_status_ne_realized
#print axioms Navier.ScientificDisposition.proof_of_readiness
#print axioms Navier.ScientificDisposition.nonrealized_cannot_be_ready
#print axioms Navier.scientificStatus_card

#print axioms Navier.Frontier.dependency_rank_decreases
#print axioms Navier.Frontier.not_mem_own_dependencies
#print axioms Navier.Frontier.nodes_card
#print axioms Navier.Frontier.encodingResidual_is_tracked
#print axioms Navier.Frontier.statementA_dependencies

#print axioms Navier.Clay.statementADisposition_status
#print axioms Navier.Clay.statementADisposition_not_ready
#print axioms Navier.Clay.statementAFrontier_eq
#print axioms Navier.Clay.statementA_not_self_dependent
