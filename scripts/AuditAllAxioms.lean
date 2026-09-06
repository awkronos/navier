import Navier
import Lean.Util.CollectAxioms

/-!
Check transitive axiom dependencies for every declaration imported from a
Navier module, including private helpers and declarations in other namespaces.
The named raw `#print axioms` traces remain in `Navier/AxiomAudit.lean`.
This check concerns the imported environment; changed sources must be compiled
and their dependency artifacts refreshed before it is evidence about them.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut failed := false
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.modules[idx.toNat]!.module
    if !(`Navier).isPrefixOf owner then continue
    let axioms ← liftCoreM (collectAxioms name)
    let unexpected := axioms.filter fun ax =>
      ax != `propext && ax != `Classical.choice && ax != `Quot.sound
    if !unexpected.isEmpty then
      logError m!"{name} (from {owner}) depends on disallowed axioms: {unexpected}"
      failed := true
  if failed then
    throwError "Imported project axiom audit failed."
  logInfo "All imported Navier declarations use only the permitted axioms."
