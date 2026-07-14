import Navier.ClayFrontier
import Navier.EnergyObstruction
import Navier.ConventionBridges

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

#print axioms Navier.ConventionBridges.schwartzmap_satisfies_fefferman_rapid_decay

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
