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
-/

set_option autoImplicit false

namespace Navier.Frontier

/-- Finite nodes in the whole-space statement-A dependency overview. -/
inductive FrontierNode where
  | schwartzConventionBridge
  | halfSpaceSmoothnessBridge
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
