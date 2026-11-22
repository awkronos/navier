# Measurement snapshot, 2026-11-13 (historical record)

Historical record; not maintained as current claims.

## Source census and sorry audit

Verified against `f521f79` on 2026-11-13 (source census: rg over `.lean`
outside `.lake`; the central `navier` row is UNMEASURED — no compiler run at
report time): 30002 theorem/lemma declarations, 120 `sorry` token
occurrences and 0 sorry sites in tactic/term position across the library;
the two headline files (`Navier/Breakdown/ConstructedBreakdown.lean`,
`Navier/Analysis/PeriodicConstructedBreakdown.lean`) carry no `sorry`.

## Axiom receipts at that date

The exact-axioms statements carried by the position README are carried
compiler receipts: a fresh `#print axioms` probe on 2026-11-13 could not run
against that checkout (module olean absent; full `lake build` required), so
as of that date the axiom sets of `wholeSpaceBreakdown` and
`periodicBreakdown` were UNCHECKED-at-date — carried, not contradicted.
Unforced global regularity (A, B) remains open, as the position page states.

## Construction file-count erratum

The count is stated twice rather than smoothed: this repository's provenance
note prints 577, while `git ls-tree` at the pinned trunk counts 579 tracked
`.lean` files under `Navier/Construction/`; `docs/CITATIONS.md` carries both
measurements.
