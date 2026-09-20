import Navier.Analysis.AprioriCriticalControlQuantifiers
import Navier.Analysis.RestartPaste

/-!
# BKM control consumed by the whole-space restart paste

This module connects the repository's explicit nondegenerate BKM quantity to
the actual whole-space consumer.  The quantity is
`AprioriCriticalControlQuantifiers.bkmVorticityControl`; its nondegeneracy is
proved in that module, and its exact solution-uniform, horizon-uniform budget
is named `NSBKMUniformVorticityApriori`.

The theorem below consumes that budget and a horizon-independent restart for
the *same* quantity.  `normalizedContinuation_of_horizonIndependentRestart`
performs the shifted-strip paste, so the result reaches the canonical
`ProblemStatements.WholeSpaceGlobalRegularity` proposition rather than a new
surrogate endpoint.

No analytic leaf is hidden here: local classical existence, the uniform BKM
budget on every `SolvesBefore` member, and the horizon-independent restart
remain explicit hypotheses.
-/

set_option autoImplicit false

namespace Navier.Analysis.RestartBKMConsumer

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Analysis.RestartPaste

/-- Local existence, a solution-uniform BKM vorticity-integral budget, and a
horizon-independent restart controlled by that same nondegenerate quantity
imply the canonical whole-space global-regularity proposition. -/
theorem wholeSpaceGlobalRegularity_of_local_bkmRestart
    (hlocal : LocalClassicalExistence)
    (hbkm : NSBKMUniformVorticityApriori)
    (hrestart : HorizonIndependentRestart bkmVorticityControl) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  exact wholeSpaceGlobalRegularity_of_local_continuation_apriori
    bkmVorticityControl hlocal
    (normalizedContinuation_of_horizonIndependentRestart hrestart) hbkm

end Navier.Analysis.RestartBKMConsumer

#check @Navier.Analysis.RestartBKMConsumer.wholeSpaceGlobalRegularity_of_local_bkmRestart
#check @Navier.Analysis.AprioriCriticalControlQuantifiers.bkmVorticityControl_nondegenerate
#print axioms Navier.Analysis.RestartBKMConsumer.wholeSpaceGlobalRegularity_of_local_bkmRestart
#print axioms Navier.Analysis.AprioriCriticalControlQuantifiers.bkmVorticityControl_nondegenerate
