/-
# ApiEnvCensus — the compiler's own declaration environment for the two T0 modules

Emits one fully qualified name per line for every *non-internal* declaration in
the deserialized environment whose name starts with one of the two T0 module
prefixes pinned by `Navier/APIPin.lean`. This is the denominator for the pin
census: it comes from the compiler environment, never from a grep over `.lean`
text, so it sees every exported name regardless of the modifiers written on the
declaring line (`noncomputable def …`, `protected def …`, …) that the anchored
grep pattern in the old coverage guard could not match.

Run (repository root, built artifacts present):
  lake env lean scripts/ApiEnvCensus.lean
The consumer contract lives in `scripts/api_pin_census.py`, which diffs this
output against the `#check` pins in `Navier/APIPin.lean`.
-/
import Navier.Analysis.ContinuousLeiLinSpace
import Navier.Construction.PeriodizedWaveBounds

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut n := 0
  for (name, _) in env.constants.toList do
    if !name.isInternal &&
        ((`Navier.Analysis.ContinuousLeiLinSpace).isPrefixOf name
          || (`Navier.Construction.PeriodizedWaveBounds).isPrefixOf name) then
      n := n + 1
      IO.println name
  IO.println s!"TOTAL:{n}"
