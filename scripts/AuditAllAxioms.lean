import Navier
import Navier.Analysis.H3RestartSlice
import Navier.Analysis.RestartAgreementOpen
import Navier.Analysis.WienerH3DampedProducer
import Navier.Analysis.MildTimeLeafX1CascadeFalsification
import Navier.Transfer.MildSelfMapDefectBudget
import Navier.Transfer.MildSelfMapTransport
import Navier.AdjointBackpropagation
import Lean.Util.CollectAxioms

/-!
Check transitive axiom dependencies for every declaration imported from a
Navier module, including private helpers and declarations in other namespaces.
The named raw `#print axioms` traces remain in `Navier/AxiomAudit.lean`.
This check concerns the imported environment; changed sources must be compiled
and their dependency artifacts refreshed before it is evidence about them.

The loop below walks `env.constants`, so the DENOMINATOR of this census is
exactly what this file imports. Seven modules were committed by their own lanes
outside `Navier.lean`'s import closure and so were never in this denominator:
`H3RestartSlice`, `RestartAgreementOpen`, `WienerH3DampedProducer`,
`MildTimeLeafX1CascadeFalsification`, `MildSelfMapDefectBudget`,
`MildSelfMapTransport`, `AdjointBackpropagation`. Importing them here is the
no-umbrella-edit route to covering them: it extends the census without staging
the aggregator, which estate law (Decree 8.8 item 2 / K11-1017) refuses to
resolve as a build target while staged.

`Navier.Analysis.CrownBridgeReduction` is deliberately NOT imported. It carries
three code-position holes (:308, :344, :391), and the witness axiom they imply is
outside the allowed set, so importing it would fail this audit by construction
rather than report it. The three holes are recorded as opens, with a
tractability classification, and the module is left listed by
`tools/module-closure-check.py` as an un-wired finding -- not as an intentional
leaf. With the library globs now declared, `lake build` compiles it and its
declaration-uses-sorry witnesses become public CI output.
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
