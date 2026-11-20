#!/usr/bin/env python3
"""Regularity-status receipt-manifest integrity test — files only, zero Lean CPU.

Runs with stock Python 3 (stdlib, no lake, no network, no git):

    python3 -m unittest discover -s tests -p 'test_regularity_status_receipts.py' -v

Context. The Studio code map ranked
`reports/receipts/2026-09-09-regularity-status/obstruction-lsp-retry.txt` as a
byte-identical duplicate group (score 12.72). Inspection on main 3fff315
(ENGINE-COVERAGE-1119 / NAVIER-RSI-ed3b60) measured two groups in that
directory:

  * `obstruction-lsp.txt` and `obstruction-lsp-retry.txt` are byte-identical.
    They are the LSP diagnostic dumps of the initial call and of the single
    documented retry on `ConstructedFiniteTimeObstruction.lean`; the directory
    README states the client "emitted an EOF exception during shutdown on both
    the initial call and the single retry", and the identical bytes are the
    evidence that the retry reproduced the same diagnostics. Two calls, two
    receipts — the second is not a copy of the first.
  * `a-lsp.txt`, `abcd-lsp.txt`, `b-lsp.txt` and `c-lsp.txt` are all the
    three-byte file `[]\n`. Each attests zero error diagnostics from a
    separately named LSP run; the empty JSON array is the unique
    serialization of "no diagnostics", so identical bytes here are an
    artifact of emptiness, not of redundancy. The names bind each attestation
    to its endpoint.

Ownership and references: `hashes.json` in the same directory lists every one
of these six files individually under `"outputs"`, and it is the only
repo-wide referrer of their names. Deleting a "duplicate" would orphan its
manifest entry and rewrite the 2026-09-09 audit snapshot the README says is
preserved; consolidation is therefore not proposed.

What this test pins instead. The snapshot stays intact and self-consistent:

  1. every filename in `hashes.json["outputs"]` exists in the receipt
     directory and its SHA-256 equals the recorded digest — a deletion of a
     duplicate member fails this leg with the manifest's own dangling name;
  2. each member of both duplicate groups is named individually in the
     manifest (the pinning is per receipt, not per content);
  3. `obstruction-lsp.txt` and `obstruction-lsp-retry.txt` are byte-identical,
     and the four `*-lsp.txt` empty outputs are byte-identical to `[]\n` —
     the groups are faithful, exactly as the audit recorded them.

Failure semantics: editing or deleting any receipt named in `hashes.json`
fails (1); renaming one fails (1) and (2); any drift that breaks the
byte-identity the README describes fails (3) — that drift is real
information (a later re-run saw different diagnostics) and belongs in a fresh
receipt, not in a silent overwrite of this snapshot.

Nothing here proves or rebuilds a theorem: hashes describe text, and the
diagnostic content is read, not re-elaborated.
"""

from __future__ import annotations

import hashlib
import json
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RECEIPT_DIR = ROOT / "reports" / "receipts" / "2026-09-09-regularity-status"
HASHES = RECEIPT_DIR / "hashes.json"

OBSSTRUCTION_GROUP = ("obstruction-lsp.txt", "obstruction-lsp-retry.txt")
EMPTY_LSP_GROUP = ("a-lsp.txt", "abcd-lsp.txt", "b-lsp.txt", "c-lsp.txt")


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def manifest_outputs() -> dict:
    assert HASHES.is_file(), f"missing receipt manifest: {HASHES.relative_to(ROOT)}"
    return json.loads(HASHES.read_text())["outputs"]


class RegularityStatusReceiptIntegrity(unittest.TestCase):
    def test_all_manifest_outputs_exist_at_recorded_digest(self):
        outputs = manifest_outputs()
        self.assertGreaterEqual(
            len(outputs), 14, "manifest outputs shrank; receipts were dropped"
        )
        for name, digest in sorted(outputs.items()):
            path = RECEIPT_DIR / name
            self.assertTrue(
                path.is_file(),
                f"hashes.json names a receipt that is not in the tree: {name} "
                "(a 'duplicate' was deleted; the 2026-09-09 snapshot is immutable)",
            )
            self.assertEqual(
                sha256_of(path),
                digest,
                f"{name} drifted from its digest recorded in hashes.json; "
                "audit receipts are not rewritten — record new evidence as a fresh receipt",
            )

    def test_duplicate_group_members_are_pinned_individually(self):
        outputs = manifest_outputs()
        for name in OBSSTRUCTION_GROUP + EMPTY_LSP_GROUP:
            self.assertIn(
                name,
                outputs,
                f"{name} lost its individual manifest entry; the audit pins "
                "each LSP call, not one representative per identical content",
            )

    def test_duplicate_groups_are_faithful_copies(self):
        initial = (RECEIPT_DIR / OBSSTRUCTION_GROUP[0]).read_bytes()
        retry = (RECEIPT_DIR / OBSSTRUCTION_GROUP[1]).read_bytes()
        self.assertEqual(
            initial,
            retry,
            "obstruction-lsp.txt and obstruction-lsp-retry.txt are no longer "
            "byte-identical; the README's 'both the initial call and the single "
            "retry' claim must be re-audited if this drifts",
        )
        empties = [(RECEIPT_DIR / name).read_bytes() for name in EMPTY_LSP_GROUP]
        self.assertEqual(
            set(empties),
            {b"[]\n"},
            "an empty-diagnostic LSP receipt is no longer exactly b'[]\\n'; "
            "a non-empty diagnostic belongs in its own new receipt file",
        )


if __name__ == "__main__":
    unittest.main()
