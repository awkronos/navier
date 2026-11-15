# Receipt duplicate group: `axioms.txt` — disposition (retained, indexed)

**Row dispositioned.** RSI `duplicate_group` T0 risk row (score 12.66), carrier
`reports/receipts/2026-09-08-constructed-c-final/axioms.txt`, generation
`93fa7be454194153a23d95d38f5a69cf`. Filed by lane `RST-NAVAXD-1116` on 2026-11-15.

**Disposition type: `retained_with_reason`.** Every member is kept byte-for-byte.
Nothing here was rewritten, truncated, deleted, or replaced by a pointer, because
each file is a historical compiler receipt and the duplication is the evidence,
not an accident. The pointers that make this discoverable were appended to the
three owning READMEs; the appends are the only change to existing files.

## Members and measured relation to the carrier

Blob hashes are `git hash-object` output, so content identity is checked the way
Git checks it. Line/byte counts are over the files as committed.

| # | path | blob (12) | bytes | lines | relation to carrier | owner |
|---|---|---|---|---|---|---|
| M1 | `2026-09-08-constructed-c-final/axioms.txt` | `54872b8fe043` | 30530 | 482 | carrier: 11 endpoints, 11 `depends on axioms` lines, 11 proof-term dumps, 402 distinct lines | the 2026-09-08 constructed-C **final** verification receipt (`3399f9f`) |
| M2 | `2026-09-09-release-check/axioms.txt` | `54872b8fe043` | 30530 | 482 | **byte-identical** to M1 | the 2026-09-09 **release recheck** receipt (`9d00376`) |
| M3 | `2026-09-08-constructed-c-final/verifier.txt` | `a51d8a109060` | 32350 | 498 | **strict superset**: contains all of M1 verbatim as one contiguous block at byte offset 315, plus 5 framing lines before and 11 `VERIFIED …` summary lines after | same final receipt |
| M4 | `2026-09-08-constructed-c-baseline/axioms.txt` | `9a21918b708b` | 2697 | 43 | 30 of its 37 distinct non-blank lines appear verbatim in M1; 5 endpoints | the 2026-09-08 constructed-C **baseline** freeze receipt |
| M5 | `2026-09-08-constructed-c-final/baseline-audit-recheck.txt` | `9a21918b708b` | 2697 | 43 | **byte-identical** to M4 | filed inside the final receipt as the recompile-after-imports-change record |
| M6 | `2026-09-08-constructed-c-final/full-rebuild.txt` | `b9e29adf94f2` | 59457 | 997 | partial only: 358 of M1's 402 distinct lines, no contiguous block — this is the build log, not a copy | same final receipt |

## Why each duplicate exists (the distinguishing reason, per pair)

**M1 / M2 — two independent compiler runs that agree exactly.** They are not one
run recorded twice; they are the *same audit produced at two different revisions
under two different rebuild profiles*, and the byte-identity is the reproduction
result the second run was filed to obtain:

- M1 came from `python3 -u scripts/verify_construction.py --jobs 8` against
  snapshot `e7aba55ff119deb7de47819ca4b33e4d1c7b5d5c`, whose own framing is
  `local_closure=615 fresh=613 rebuild=2`.
- M2 came from a separate `--jobs 2` invocation on 2026-09-09, on top of native
  main `4e4aab7`, where the verifier accepted 332 current receipts and rebuilt
  283 invalidated objects, with no Lean source changed.
- The identical 30530-byte block is embedded in **both** runs' full logs: M3 at
  byte offset 315, and `2026-09-09-release-check/construction.txt`
  (`faa4764ec050`, 48629 bytes) at byte offset 16594, under different framing.
  So each directory's `axioms.txt` is the extracted audit section of *that
  directory's own* run log, and each README cites it as that run's evidence.

Collapsing M2 into a pointer to M1 would erase the only record that the axiom
audit reproduced across a revision change and a different rebuild profile — the
reproduction is a two-member fact by construction.

**M1 / M3 — extraction, not copy.** M3 is the complete closing verifier output;
M1 is the raw exact-type, proof-term and transitive-axiom section of it, which
the final README names and counts endpoint by endpoint. Deleting M1 would break
that README's reference; deleting M3 would lose the `CHECKED` progress and the
11 `VERIFIED axioms=…` summary lines. Both are load-bearing at different
granularity.

**M4 / M5 — before and after an import change.** M4 is the baseline freeze at
`e7aba55f`; M5 is the same audit recompiled after the final imports changed,
filed by the final README as `baseline-audit-recheck.txt`. Their byte-identity
records that the import change moved no axiom trace.

**M4's 7 non-carrier lines are not unique evidence — checked, not assumed.**
They are the audit block for
`Navier.Analysis.CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_continuation_apriori`,
a conditional bridge (it consumes `LocalClassicalExistence`,
`NormalizedContinuationFromCriticalControl` and `APrioriCriticalControl`) that
M1's 11-endpoint list does not cover. That conditional theorem's raw axiom line
is nevertheless recorded elsewhere in the repo, so M4/M5 are not the sole
carriers of it: the same line appears at
`2026-09-08-constructed-c-final/conditional-audit.txt:160` and at
`2026-09-09-regularity-status/frontier-compiler.txt:10` and `:25`. M4/M5 are
retained for the run-reproduction reason above, not for content found nowhere
else.

## Alternative considered and refused

`single-source-the-receipt` (collapse the duplicates into committed pointers
naming one canonical file) was measured and then refused: it is unreachable for
a receipt group without rewriting receipt content, and in this case it would
delete the reproduction facts listed above. This file plus the three appended
pointers is the honest leg.

## Proof obligation, and how it was met

No focused checker in this repo audits these text receipts, so there is no
green-gate citation available for this row and none was manufactured:

```text
$ grep -rn 'reports/receipts' scripts tools tests .github Makefile   # exit 1, no match
```

`scripts/verify_construction.py` audits *dependency* receipts — JSON per-module
records with `exit_code`, `fingerprint` and `output_sha256` — never these
`reports/receipts/**` prose files, and `tools/module-closure-check.py` walks the
`Navier/**/*.lean` import closure only. Re-running the verifier to grade this
row would cost a 615-module build and would re-record proof, not dedup. The
measurements in this note are therefore the evidence leg; every number above is
reproducible with `git hash-object`, `wc -c`, `wc -l` and `grep -c` against the
paths named.

Read the raw reproduction check as: `M1` blob == `M2` blob, `M4` blob == `M5`
blob, and `M1` bytes found contiguously inside `M3` and inside
`release-check/construction.txt`.

## Tracking note: this tree is committed but gitignored

`.gitignore:11` carries `/reports/` with the comment "Compiler receipts and
generated reports stay local", yet every file named in the table above is
tracked in Git (they were committed as frozen evidence before the ignore
applied to new files, and once a path is tracked the ignore does not untrack
it). Two consequences for anyone re-checking this row:

- `git status` will not offer a new file under `reports/` — this very note had
  to be `git add -f`'d, which is why the force-add is named in the commit
  message instead of being left to be rediscovered.
- Nothing regenerates these receipts. There is no CI job or script that writes
  `reports/receipts/**` (the grep above returns nothing), so a duplicate here
  cannot be resolved by deleting one copy and rebuilding it: the deleted copy
  is gone for good.

## Rule for future dedup lanes

Text under `reports/receipts/<dated-dir>/` is frozen compiler output. Two
receipts that share bytes are two *runs*, not one file duplicated: check blob
equality and each directory's README citation before proposing any collapse, and
annotate rather than rewrite. A `duplicate_group` row over this tree is
dispositioned by naming the runs, never by deleting one of them.
