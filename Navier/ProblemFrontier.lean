import Navier.Frontier

/-!
# Current disposition of the formal statement-A surface

The canonical proposition `ProblemStatements.WholeSpaceGlobalRegularity` is kept conjectural.  Its readiness
bit is therefore false.  The finite dependency view is exposed for navigation,
but there is no theorem accepting a proof program, dependency bundle, or
endpoint hypothesis and returning statement A.  Open convention bridges mean
this formal surface is not described as definitionally identical to
Fefferman's official prose.
-/

set_option autoImplicit false

namespace Navier.ProblemStatements

/-- The present proof-bearing disposition of the formal statement-A surface.

This value contains no proof of `WholeSpaceGlobalRegularity`; it records the honest
scientific-frontier status. -/
def wholeSpaceGlobalRegularityDisposition : ScientificDisposition WholeSpaceGlobalRegularity :=
  .conjectural

/-- The current proof-erased status is conjectural. -/
@[simp] theorem wholeSpaceGlobalRegularityDisposition_status :
    ScientificDisposition.status wholeSpaceGlobalRegularityDisposition =
      ScientificStatus.conjectural := rfl

/-- The statement-A surface is not theorem-ready in the current frontier. -/
@[simp] theorem wholeSpaceGlobalRegularityDisposition_not_ready :
    ScientificDisposition.readiness wholeSpaceGlobalRegularityDisposition = false := rfl

/-- Immediate planning dependencies associated with the statement-A surface. -/
def wholeSpaceGlobalRegularityFrontier : Finset Frontier.FrontierNode :=
  Frontier.dependencies .statementA

/-- The frontier keeps all five statement-A encoding comparisons and the
analytic global-continuation branch visible. -/
theorem wholeSpaceGlobalRegularityFrontier_eq :
    wholeSpaceGlobalRegularityFrontier =
      { .schwartzConventionBridge, .halfSpaceSmoothnessBridge,
        .currentSpaceNormBridge, .frechetCoordinatePDEBridge,
        .wholeSpaceEnergyBridge, .globalContinuation } :=
  Frontier.wholeSpaceGlobalRegularity_dependencies

/-- Statement A itself is not listed as its own immediate dependency. -/
theorem wholeSpaceGlobalRegularity_not_self_dependent :
    Frontier.FrontierNode.statementA ∉ wholeSpaceGlobalRegularityFrontier := by
  exact Frontier.not_mem_own_dependencies .statementA

end Navier.ProblemStatements
