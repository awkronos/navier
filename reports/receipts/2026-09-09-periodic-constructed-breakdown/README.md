# Native periodic breakdown D — independent verification

`Navier.Analysis.PeriodicConstructedBreakdown.periodicBreakdown` inhabits
`Navier.ProblemStatements.PeriodicBreakdown` with no additional premises.
For every positive viscosity it selects periodic zero initial velocity and
admissible smooth periodic time-decaying forcing excluding every global smooth
periodic velocity-pressure pair.

The root independently compiled the frozen source, checked the exact original
consumer, and inspected raw transitive axioms: only `propext`,
`Classical.choice`, and `Quot.sound`. LSP diagnostics are empty. All 538 local
dependency receipts are current. `verification.json` binds source and outputs.

The proof consumes the selected periodic candidate directly. It proves native
force-jet decay from smoothness, periodicity and a uniform future time cutoff;
transports the hypothetical native competitor, including periodic pressure,
into the exact same-force comparison class; and applies the existing
all-positive-viscosity equivalence.

Reproduce with `python3 scripts/verify_construction.py --audit-regularity-endpoints`.
For a changed import, first refresh only its dependency closure using
`--root-module Navier.Analysis.PeriodicConstructedBreakdown --materialize-only`.
Materialization alone makes no endpoint proof claim.

This updates the earlier regularity-status audit, whose D row had no registered
witness. A and B remain construction targets; D is the forced periodic endpoint.
