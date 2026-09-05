import Navier.Frontier

/-!
# Current disposition of the formal statement-A surface

The canonical proposition `ProblemStatements.WholeSpaceGlobalRegularity` is
kept visible without a hand-maintained status value.  The finite dependency
view is for navigation; it does not prove statement A.  Open convention bridges
mean this formal surface is not described as definitionally identical to
Fefferman's official prose.
-/

set_option autoImplicit false

namespace Navier.ProblemStatements

/-- Immediate planning dependencies associated with the statement-A surface. -/
def wholeSpaceGlobalRegularityFrontier : Finset Frontier.FrontierNode :=
  Frontier.dependencies .statementA

/-- The frontier keeps the four remaining statement-A encoding comparisons and the
analytic global-continuation branch visible. -/
theorem wholeSpaceGlobalRegularityFrontier_eq :
    wholeSpaceGlobalRegularityFrontier =
      { .schwartzConventionBridge, .halfSpaceSmoothnessBridge,
        .frechetCoordinatePDEBridge,
        .wholeSpaceEnergyBridge, .globalContinuation } :=
  Frontier.wholeSpaceGlobalRegularity_dependencies

/-- Statement A itself is not listed as its own immediate dependency. -/
theorem wholeSpaceGlobalRegularity_not_self_dependent :
    Frontier.FrontierNode.statementA ∉ wholeSpaceGlobalRegularityFrontier := by
  exact Frontier.not_mem_own_dependencies .statementA

end Navier.ProblemStatements
