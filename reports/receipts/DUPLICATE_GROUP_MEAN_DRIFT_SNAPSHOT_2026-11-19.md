# Receipt duplicate group: live module / frozen source snapshot — disposition (retained, annotated)

**Row dispositioned.** RSI `duplicate_group` T0 risk row 14.2 (score 14.2), carrier
`Navier/Analysis/CriticalMildMeanDriftRemoval.lean`, generation
`93fa7be454194153a23d95d38f5a69cf`. Filed by lane `RST-NAVCMD-1116` on 2026-11-19,
following the rule set by `DUPLICATE_GROUP_AXIOMS_2026-11-15.md` (lane
`RST-NAVAXD-1116`, same generation) for this tree: annotate, never rewrite.

**Disposition type: `retained_with_reason` (this committed note + a pointer).**
Both members are kept byte-for-byte. The distinguishing statement is that the
group spans two different lifecycles: one member is the live, compiled carrier,
the other is the inert provenance capture of that carrier taken at the
2026-09-09 receipt, whose SHA-256 the receipt README pins.

## Members and measured relation (all numbers re-derivable at `a72c19b`)

Blob hashes are `git hash-object` output; byte counts `wc -c`; line counts `wc -l`.

| # | path | blob | bytes / lines | role |
|---|---|---|---|---|
| M1 | `Navier/Analysis/CriticalMildMeanDriftRemoval.lean` | `0415973b968e5d0540ac540ff8461d352128c32d` | 23930 / 559 | live build module |
| M2 | `reports/receipts/2026-09-09-critical-mild-mean-drift-removal/source-snapshot.lean.txt` | `0415973b968e5d0540ac540ff8461d352128c32d` | 23930 / 559 | frozen receipt capture |

- Group membership was measured exhaustively: at `origin/main` only these two
  paths share blob `0415973b...` (`git ls-tree -r origin/main --format='%(objectname) %(path)'`).
- Overlap is 100%: identical blob, and SHA-256
  `cbd082de5f1a75317361c55e8ac01f4d28df56a9635544ad59e79219f95e68ec` on both,
  the same value the receipt README pins as the audited source.
- M1's import edges: it imports `Navier.Analysis.CriticalMildZeroMode` (line 1)
  and is imported at `origin/main` by exactly two modules,
  `Navier/Analysis/CriticalMildGalileanVolterra.lean:1` and
  `Navier/Analysis/PeriodicMildClassicalRealization.lean:3`; their own
  dependents (`Navier.lean:88`, `CriticalMildModeDifferentiation.lean:1`,
  `CriticalMildRealityPreservation.lean:1`,
  `PeriodicSpatialSmoothReconstruction.lean:2`) put M1 inside the transitive
  cone of the `Navier` library root, so it is load-bearing build code.
- M2 is a `.txt` file under `reports/`, outside the `Navier` `lean_lib` roots
  declared in `lakefile.toml`; nothing compiles or imports it. It is cited as
  the frozen source of the run whose compile exit 0, empty LSP diagnostics and
  axiom probe the README records against base commit
  `1bd8c4f63d89045d783563b279ea4ee99d59a43b`.

## Why both exist

They are the same bytes because the live module has never been edited since it
was introduced: `git log HEAD -- Navier/Analysis/CriticalMildMeanDriftRemoval.lean`
names exactly one commit, `8431c71` (2026-09-09), and the carrier blob is
`0415973b...` in every revision since. The snapshot entered main already
byte-identical to the carrier at merge `f607736` (2026-09-24), the salvage fold
of the dead Codex swarm lane's row-12 work that preserved this receipt tree;
at that merge both paths resolve to the same blob. The README's base commit
`1bd8c4f6` is an ancestor in main's history that predates the file's
introduction (the path is absent from that tree), so the receipt captured the
audited worktree bytes of 2026-09-09 rather than tracking main — which is
exactly its purpose.

The snapshot's job is to pin *which* bytes passed the 2026-09-09 audit; the
module's job is to evolve. Byte-identity is a transient coincidence of an
untouched file, not redundancy: the next edit to M1 changes the blob and this
`duplicate_group` row self-resolves as no-longer-identical, while M2 correctly
continues to name the 2026-09-09 bytes.

## Alternatives considered and refused

- **Collapse to one carrier with the other importing it** — structurally
  unreachable here. M2 is not a module path, so it cannot import M1, and
  pointing the README's pinned SHA-256 at a floating live file would rewrite
  frozen receipt content and destroy the audit it certifies (the README's
  `cbd082de` citation would dangle).
- **Delete M2** — unrecoverable, not self-healing: per
  `DUPLICATE_GROUP_AXIOMS_2026-11-15.md`, no script, tool, test or CI job
  regenerates `reports/receipts/**` (`grep -rn 'reports/receipts' scripts tools
  tests .github Makefile` → exit 1), and the receipt README references M2.
- **Delete or alias M1** — impossible; two modules import it (cone above).

## Gate inventory for this change

This commit touches no `.lean` file: it adds this note and appends one pointer
section to the receipt README (append-only, 0 lines deleted; no `.txt`, `.log`
or `.json` receipt file modified). No focused checker in this repo audits text
under `reports/` or `*.md` (same grep as above). The focused `--check` run at
landing re-derives the two claims of this note against the merged tree:
blob-equality of M1 and M2, and presence of the pointer in the receipt README.
No Lean build was invoked, and none is required by a documentation disposition.

## Discovery pointer

Appended to
`reports/receipts/2026-09-09-critical-mild-mean-drift-removal/README.md`:
a pointer section naming this note, so a future dedup pass that finds the
identical blobs reads the disposition where it sees the pair.

This note is force-added because `.gitignore:11` carries `/reports/` while the
frozen receipts under it remain tracked (see the tracking note in
`DUPLICATE_GROUP_AXIOMS_2026-11-15.md`).
