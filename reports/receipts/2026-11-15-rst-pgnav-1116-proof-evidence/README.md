# Proof-report evidence restoration: `(proof:navier)` — MEASURED

**Row restored from UNKNOWN to measured.** The RSI T0 `proof_gap` row on
`(proof:navier)` (generation `999c6764f2ca4d749cc113fe4929aea9`) carried
`status: unknown` / `claim_status: VERIFIER-UNKNOWN`: the code map could not see
the compiler for this project. This receipt files the missing measurement —
a complete transitive axiom census of the declared Navier surface at
`origin/main` — as raw compiler output, produced in **20.7 s** on the warm
cache.

Lane `RST-PGNAV-1116`, band `omni1116`, filed 2026-11-15. No math, axiom, pin
or API was changed; nothing here is a proof attempt.

## The measured row

Revision measured: `49abd6511a6d96101f1633d81ab504e39d57bfe3` (`origin/main`,
clean tree). Toolchain `leanprover/lean4:v4.35.0-rc4`, mathlib
`1f414401f69059aa7eead47b53ee40bd38455eeb`.

| Leg | Command | rc | wall | Raw output |
|---|---|---|---|---|
| A — repo-named census (`make axioms`, CI step 5) | `lake env lean scripts/AuditAllAxioms.lean` | **0** | 19.3 s | `All imported Navier declarations use only the permitted axioms.` |
| B — full declared surface (A + the 8 modules outside the aggregator closure) | `lake env lean FullClosureAxiomCensus.lean` | **0** | 20.7 s | `DECLARATIONS_AUDITED: 66234` / `CENSUS_COMPLETE: all Navier-owned declarations use only {propext, Classical.choice, Quot.sound}` |

Leg B raw stdout, verbatim (`full-closure-census-leg.txt`):

```
DECLARATIONS_AUDITED: 66234
CENSUS_COMPLETE: all Navier-owned declarations use only {propext, Classical.choice, Quot.sound}
```

Leg A raw stdout, verbatim (`audit-all-axioms-leg.txt`):

```
=== rc=0 wall=19.3s started=Sun Nov 15 12:41:13 2026 ===
All imported Navier declarations use only the permitted axioms.
```

Zero `depends on disallowed axioms` lines were emitted by either leg, so the
transitive axiom set of every Navier-owned declaration is inside
`{propext, Classical.choice, Quot.sound}`. `sorryAx` is outside that permitted
set, so this census also witnesses zero sorry-bearing transitive dependencies
over the same population — matching the report row's own
`sorry_count: 0` / `coverage_complete: true`.

### What leg B adds over leg A

`scripts/AuditAllAxioms.lean` imports `Navier` only, which reaches the
aggregator's import closure. `tools/module-closure-check.py`, run in the seat,
names the modules built by the `lakefile.toml` `globs = ["Navier", "Navier.**"]`
entry but sitting outside that closure — 8 of them:

```
Navier.AdjointBackpropagation
Navier.Analysis.CrownBridgeReduction
Navier.Analysis.H3RestartSlice
Navier.Analysis.MildTimeLeafX1CascadeFalsification
Navier.Analysis.RestartAgreementOpen
Navier.Analysis.WienerH3DampedProducer
Navier.Transfer.MildSelfMapDefectBudget
Navier.Transfer.MildSelfMapTransport
```

Leg B imports those 8 explicitly on top of `Navier`, so its population is the
whole declared library surface. `FullClosureAxiomCensus.lean.txt` is kept here as
the exact command that produced the number; it is the same predicate as leg A
and `Navier/AxiomAudit.lean`, not a second standard.

## Why the code map read UNKNOWN, measured

The producer's own row for navier in `/tmp/proof-report.json` (envelope
generated 2026-11-15 12:18:58; navier row generated 05:12:38) carries:

```
claim_status                       VERIFIER-UNKNOWN
soundness_complete                 false
kernel_axiom_check_exit            124
kernel_axiom_check_timeout_s       1800      # PER SHARD
kernel_axiom_check_elapsed_s       7261.3
kernel_axiom_modules_total         1069
kernel_axiom_unattempted_module    900
kernel_axiom_attempted_unaudited   100       # => 69 modules audited
mode / compiler_run / build_status disk-floor-skipped / false / SKIPPED
```

and `soundness_partial_reasons` (17 entries), whose first six are footprint
kills, not slow-compiles:

```
kernel_axiom_owned_child_footprint_exceeded: phys_footprint_peak=8.35GiB  exceeds the 8 GiB cap
kernel_axiom_owned_child_footprint_exceeded: phys_footprint_peak=7.64GiB  crossed the 7.20 GiB guard band
kernel_axiom_owned_child_footprint_exceeded: phys_footprint_peak=7.47GiB  crossed the 7.20 GiB guard band
kernel_axiom_owned_child_footprint_exceeded: phys_footprint_peak=10.00GiB exceeds the 8 GiB cap
kernel_axiom_owned_child_footprint_exceeded: phys_footprint_peak=8.03GiB  exceeds the 8 GiB cap
kernel_axiom_owned_child_footprint_exceeded: phys_footprint_peak=8.31GiB  exceeds the 8 GiB cap
```

The gate that turns this into UNKNOWN is
`packages/kagami/core/proof/proof_report_validation.py:906`: a row is not
decision-grade unless
`soundness_complete is True AND kernel_axiom_check_exit == 0`, so it appends
`kernel_axiom_audit_incomplete`; the open-math projection then writes
`status: unknown` and `kernel_axiom_audit_incomplete` becomes the carrier's
dominant leg, which `packages/kagami/core/proof/proof_quality.py:1325` answers
as "run the transitive axiom audit leg". The RSI consumer
(`packages/kagami/core/code_intel/rsi.py`, the `context-unknown` arm) mints the
row as `measurement_class: unverifiability-floor` — a floor, not a size — with
the standing instruction that unknown is not closed. **This receipt restores the
measurement; it does not close the obligation the census is a floor over.**

The cost difference is structural, not tuning: the producer partitions 1069
modules into shards of 200 (`PROOF_REPORT_SOUNDNESS_SHARD_SIZE` default,
`.claude/scripts/proof_report.py:16263`) and each shard re-imports its own
environment, paying the import and `collectAxioms` work from zero, so a shard
peaks above the 8 GiB per-child footprint law and is killed at 124 before
finishing. One warm `lake env lean` process imports the environment once and
`Lean.Util.CollectAxioms` memoizes over it, measuring 66 234 declarations in
20.7 s. The footprint law is not the defect and must not be raised — the shard
size is what does not fit navier.

## Typed absences (what this receipt does NOT measure)

- **`build_exit` / `error_count` at `49abd651`** — ABSENT here, reason
  `budget_exceeded`, and now measured as such: `lake build Navier` launched
  warm in the seat hit this lane's own 600 s bound at
  `rc=TIMEOUT wall=600.1s`, still elaborating
  `Navier/Analysis/ContinuousLeiLinActualSlots.lean`. The cause is a
  provisioning gap, not a repo defect: the seat's `.lake` clone, copied at
  lane start, is missing the 5 oleans added by the three most recent commits
  (`ContinuousLeiLinAdmissibleContraction`,
  `ContinuousLeiLinPhysicalRegularity`, `CorrectionStep`,
  `GermCandidateAssembly`, `InitializedPhysicalBackground`), so that leg is a
  5-module cold rebuild under host load (`loadavg1` was 66 when the build
  watchdog recorded it) rather than a warm cache check. The attempt against the
  incomplete cache is kept verbatim in
  `seat-census-incomplete-cache-diagnostic.txt`:
  `object file '...Navier/Construction/ActualSignedGeometry.olean' of module
  Navier.Construction.ActualSignedGeometry does not exist`. Worth noting from
  the build's own partial output: the declarations it did reach printed
  `'Navier.Analysis.ContinuousLeiLinActualSlots.commonFrequencyMeasure_le_xm1'
  depends on axioms: [propext, Classical.choice, Quot.sound]` — the same
  permitted set leg B certifies over all 66 234. Leg B was therefore run in
  `/Users/schizodactyl/navier`, a clean checkout at the same
  `49abd6511a6d96101f1633d81ab504e39d57bfe3` with a complete 1075-olean cache;
  the census measures that revision, and the compiler evidence for it is the
  cached oleans plus the zero-error census run.
- **Freshness of the census against a *future* head** — this measures
  `49abd651` only. The report row is stamped at the older `82f4e7f1380…`
  (`canonicality_reasons: head_not_origin/main:82f4e7f1380!=5109087051f`,
  `head_pin_diverged:carried_head_drift`), and navier has advanced three
  commits since; a sweep that re-measures at a head that has already moved on
  reproduces the drift regardless of shard size.
- **The `/tmp/proof-report.json` row itself** — NOT rewritten by this lane.
  The producer rewrites that host-global artifact on its own sweep behind a
  singleton lock; `~/.claude/scripts/open-math.py verify --project navier`, the
  command `make proof` names, waits up to `DEFAULT_QUEUED_WAIT_S = 21900` s for
  that lock, far outside this lane's 1200 s budget, and `RST-PGHON-1116`
  measured exactly that queueing (`rc 75 native_compiler_refresh_queued`) in
  the same hour. So the code map will keep reading `unknown` for navier until
  the producer's axiom leg is wired to a shard size that fits; the repair is
  named in the recommendation, and only a producer sweep can put a measured
  value into the report.

## Producer inventory (finding 1)

Everything this repo names as a proof-evidence producer, and what each is
worth for the missing measurement:

| Where | Producer | Status for this lane |
|---|---|---|
| `Makefile` `proof` | `~/.claude/scripts/open-math.py verify --project navier --report /tmp/proof-report.json --sidecar /tmp/open_math.json` | exists; out of budget (21900 s lock wait, rc 75) |
| `Makefile` `axioms` | `lake env lean Navier/AxiomAudit.lean`, `lake env lean scripts/AuditAllAxioms.lean` | **run warm, rc 0** (leg A) |
| `Makefile` `lean` | `lake env lean Navier.lean` | not run; subsumed for the axiom question by legs A/B |
| `Makefile` `closure` | `tools/module-closure-check.py` | **run**, rc 0, names the 8 modules |
| `.github/workflows/ci.yml` lean job | `lake build`, `lake env lean Navier/AxiomAudit.lean`, `lake env lean scripts/AuditAllAxioms.lean`, reality-sourced `native_decide_census.py --ratchet` | self-hosted `[self-hosted, lean]` runner, 180 min budget |
| `Makefile` `conditional-audit` | `lake env lean Navier/ConditionalAudit.lean` | not run (conditional-axiom surface, not the census) |
| `scripts/verify_construction.py`, `scripts/check_formalization.py`, `scripts/proof_graph.py`, `tools/module-closure-check.py` | repo-resident verifiers | only the closure checker was needed |

No new census, tracker or auditor was written: legs A and B are the repo's own
`make axioms` predicate, and leg B differs only by importing the 8 modules the
aggregator does not reach.

## PRIOR ART consumed

Before writing anything I read, in this repo and the estate, and reused rather
than re-derived:

- `reports/receipts/DUPLICATE_GROUP_AXIOMS_2026-11-15.md` — lane
  `RST-NAVAXD-1116` filed today on the same generation; it established the
  receipt shape this file follows (`reports/receipts/<date>-<slug>/`) and the
  blob-hash discipline. No overlap with this row: that lane dispositioned the
  `duplicate_group` risk row, this one restores the `proof_gap` measurement.
- `scripts/AuditAllAxioms.lean` (28 lines) — the repo's own strict transitive
  census and CI's authority. Leg B extends its import list only.
- `Navier/AxiomAudit.lean` (755 lines of named `#print axioms` traces) — the
  permitted-axiom vocabulary and the disclosure precedent.
- `lakefile.toml` `globs` comment — names the 8-outside-closure defect and the
  Decree 8.8 / K11-1017 rule that forbids reaching them by staging the
  aggregator; that is why leg B imports them explicitly instead of editing
  `Navier.lean`.
- `tools/module-closure-check.py` — run, not reimplemented.
- `.github/workflows/ci.yml` — the trigger-scope and runner history explaining
  why the full build is not the cheap leg.
- `Makefile` `proof` target and `~/.claude/scripts/open-math.py` — the
  refresh-taxonomy comments (rc 75 / 124 / other) and `DEFAULT_QUEUED_WAIT_S`,
  which set this lane's route choice.
- Estate: `proof_report_validation.py:906` (the gate), `proof_quality.py:1325`
  (the named remedy), `code_intel/rsi.py` (`context-unknown` arm),
  `proof_report.py:11433` / `:16247-16280` (the shard-size table and env
  overrides), and the live `/tmp/proof-report.json` navier row.
