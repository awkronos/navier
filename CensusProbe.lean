/-
PROBE (lane NAVIER-RSI-f99687-RETRY): enumerate, from the compiler's own
declaration environment, every public declaration whose module is
Navier.Analysis.ContinuousLeiLinSpace. This is the measurement that closes the
named follow-up in Navier/APIPin.lean ("a name-by-name comparison against the
compiler's own declaration environment"). Not committed; used to generate the
expected-surface list for the real census guard.
-/
import Navier.Analysis.ContinuousLeiLinSpace
set_option autoImplicit false

open Lean Elab Command in

run_cmd do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `Navier.Analysis.ContinuousLeiLinSpace
    | throwError "PROBE-CENSUS-FAULT: module not present in environment"
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if env.getModuleIdxFor? n == some modIdx then
      names := names.push n
  logInfo m!"PROBE-CENSUS-SIZE {names.size}\n{names.qsort Name.lt |>.map (fun n => toString n)}"
