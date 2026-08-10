import Navier.Disposition
import Navier.Problem
import Navier.Scaling

/-!
# Finite scientific frontier map

This module records a finite, ranked dependency map for the present attack
surface.  The map is planning data: it does not assert that arbitrary proofs of
the listed nodes compose to `ProblemStatements.WholeSpaceGlobalRegularity`, and it intentionally defines no
proof-program argument whose result is the problem endpoint.

The five statement-A representation residuals from `Problem.lean` occur as
explicit frontier nodes.  The global analytic obstruction remains the
critical-control/global-continuation branch.

Node count is unchanged by the successive discharges of `currentSpaceNormBridge`
clauses — the Euclidean energy density, the energy transport, the decay weight,
and now the decay derivative bundle.  Partially discharged bridges stay in
`dependencies .statementA`, so this map never reports a bridge as closed while
any of its clauses is open; what `currentSpaceNormBridge` still has open is the
*force* side of the decay clauses, not the whole-space data side.
-/

set_option autoImplicit false

namespace Navier.Frontier

/-- Finite nodes in the whole-space statement-A dependency overview. -/
inductive FrontierNode where
  | schwartzConventionBridge
  | halfSpaceSmoothnessBridge
  /-- The sup-norm/Euclidean-norm bridge.  Still a leaf, but the clauses this
  node named for the whole-space *data* are now all transported: the energy
  integrand is Euclidean (`Navier.kineticEnergy`), the
  `IsClassicalSolution.finite_energy` integrability and the uniform bound
  transport by
  `Analysis.EnergyOfficialClause.IsClassicalSolution.officialWholeSpaceEnergyClause`
  and `Analysis.EnergyNormBridge.uniformlyBoundedEnergy_iff_sup`, the decay
  clause's spatial weight by
  `Analysis.OfficialABEncoding.feffermanRapidDecayBound_iff_euclideanWeight`, and
  its derivative bundle by
  `Analysis.EnergyNormBridge.feffermanRapidDecayBound_iff_fullyEuclidean`.

  What keeps the node open is the *force* decay clauses of
  `Navier.OfficialProblem`.  Their `iteratedFDerivWithin` bundles differentiate
  on `ℝ × Space`, so both their spacetime weight `(1 + ‖x‖ + t) ^ K` and their
  argument slots are still in the inherited product norm; only the bundle value
  is covered
  (`Analysis.EnergyNormBridge.officialEuclideanNorm_apply_le_sqrt_three_mul_opNorm`),
  and no consumer there is rewired.  The two norms still provably differ, so none
  of the transport constants is slack.  See
  `ProblemEncodingResidual.currentSpaceNormEuclideanNormEquivalence`. -/
  | currentSpaceNormBridge
  | frechetCoordinatePDEBridge
  | wholeSpaceEnergyBridge
  | localClassicalExistence
  | continuationCriterion
  | aPrioriCriticalControl
  | globalContinuation
  | statementA
  deriving DecidableEq, Repr, Fintype

/-- Immediate planning dependencies.  Empty dependency sets are frontier
leaves at this level of resolution, not declarations that those leaves have
been proved. -/
def dependencies : FrontierNode → Finset FrontierNode
  | .schwartzConventionBridge => ∅
  | .halfSpaceSmoothnessBridge => ∅
  | .currentSpaceNormBridge => ∅
  | .frechetCoordinatePDEBridge => ∅
  | .wholeSpaceEnergyBridge => ∅
  | .localClassicalExistence => ∅
  | .continuationCriterion => ∅
  | .aPrioriCriticalControl => ∅
  | .globalContinuation =>
      { .localClassicalExistence, .continuationCriterion,
        .aPrioriCriticalControl }
  | .statementA =>
      { .schwartzConventionBridge, .halfSpaceSmoothnessBridge,
        .currentSpaceNormBridge, .frechetCoordinatePDEBridge,
        .wholeSpaceEnergyBridge, .globalContinuation }

/-- A rank used only to certify that the finite dependency graph points
strictly downward. -/
def rank : FrontierNode → Nat
  | .schwartzConventionBridge => 0
  | .halfSpaceSmoothnessBridge => 0
  | .currentSpaceNormBridge => 0
  | .frechetCoordinatePDEBridge => 0
  | .wholeSpaceEnergyBridge => 0
  | .localClassicalExistence => 0
  | .continuationCriterion => 0
  | .aPrioriCriticalControl => 0
  | .globalContinuation => 1
  | .statementA => 2

/-- Every dependency edge strictly decreases the declared finite rank. -/
theorem dependency_rank_decreases {parent child : FrontierNode}
    (h : child ∈ dependencies parent) : rank child < rank parent := by
  cases parent <;> simp [dependencies, rank] at h ⊢
  · rcases h with h | h | h
    · subst child
      decide
    · subst child
      decide
    · subst child
      decide
  · rcases h with h | h | h | h | h | h
    · subst child
      decide
    · subst child
      decide
    · subst child
      decide
    · subst child
      decide
    · subst child
      decide
    · subst child
      decide

/-- The dependency map has no self-edge. -/
theorem not_mem_own_dependencies (node : FrontierNode) :
    node ∉ dependencies node := by
  intro h
  exact (Nat.lt_irrefl (rank node)) (dependency_rank_decreases h)

/-- The complete finite node set. -/
def nodes : Finset FrontierNode := Finset.univ

/-- This overview currently has ten explicitly named nodes. -/
theorem nodes_card : nodes.card = 10 := by
  decide

/-- Embed each problem-encoding residual into the finite frontier. -/
def nodeForEncodingResidual : ProblemEncodingResidual → FrontierNode
  | .schwartzConventionEquivalence => .schwartzConventionBridge
  | .halfSpaceSmoothnessEquivalence => .halfSpaceSmoothnessBridge
  | .currentSpaceNormEuclideanNormEquivalence => .currentSpaceNormBridge
  | .problemFrechetCoordinatePDEEquivalence => .frechetCoordinatePDEBridge
  | .wholeSpaceEnergyClauseEquivalence => .wholeSpaceEnergyBridge

/-- Every named problem-encoding residual is represented by a frontier node. -/
theorem encodingResidual_is_tracked (residual : ProblemEncodingResidual) :
    nodeForEncodingResidual residual ∈ nodes := by
  simp [nodes]

/-- The immediate dependency view attached to the formal statement-A surface. -/
theorem wholeSpaceGlobalRegularity_dependencies :
    dependencies .statementA =
      { .schwartzConventionBridge, .halfSpaceSmoothnessBridge,
        .currentSpaceNormBridge, .frechetCoordinatePDEBridge,
        .wholeSpaceEnergyBridge, .globalContinuation } := rfl

end Navier.Frontier
