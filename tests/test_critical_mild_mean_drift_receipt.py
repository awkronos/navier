#!/usr/bin/env python3
"""Critical-mild mean-drift-removal receipt integrity test — files only, zero Lean CPU.

Runs with stock Python 3 (stdlib, no lake, no network, no git):

    python3 -m unittest discover -s tests -p 'test_critical_mild_mean_drift_receipt.py' -v

Context. The Studio code map ranks
`Navier/Analysis/CriticalMildMeanDriftRemoval.lean` as a byte-identical
duplicate group with
`reports/receipts/2026-09-09-critical-mild-mean-drift-removal/source-snapshot.lean.txt`.
Inspection (ENGINE-COVERAGE-1119 / NAVIER-RSI-de9c1e-RETRY, measured on main
a72c19b) shows the duplication is intentional and load-bearing: the snapshot is
the audit record — the receipt pins the exact text that `lake env lean`
compiled at exit 0 with endpoints using only `propext`, `Classical.choice`,
and `Quot.sound` — and the audited source is imported by
`Navier/Analysis/CriticalMildGalileanVolterra.lean` and
`Navier/Analysis/PeriodicMildClassicalRealization.lean`. Merging or deleting
either side would void the receipt, so consolidation is not proposed.

What this test pins instead. The duplicate group is exactly as redundant as an
audit needs and no more:

  1. `source-sha256.txt` names the live module path and records a 64-hex digest;
  2. that digest equals the README's `SHA-256:` line;
  3. it equals the SHA-256 of `source-snapshot.lean.txt` (the recorded text
     matches the recorded hash);
  4. it equals the SHA-256 of the live
     `Navier/Analysis/CriticalMildMeanDriftRemoval.lean` (the audited source
     has not drifted since the receipt was minted);
  5. the snapshot and the live module are byte-identical (the group is a
     faithful copy, not a stale or edited one).

Failure semantics: an edit to the audited module fails (4) and (5); that is the
drift alarm — re-mint the receipt (new snapshot, hashes, compile/axiom logs,
README) instead of silently leaving a receipt that misdescribes its source.
An edit to the receipt files fails (1)–(3).

Nothing here proves or rebuilds a theorem: hashes describe text, and the
compiler claims quoted from the README are read, not re-executed.
"""

from __future__ import annotations

import hashlib
import re
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
RECEIPT_DIR = ROOT / "reports" / "receipts" / "2026-09-09-critical-mild-mean-drift-removal"
SNAPSHOT = RECEIPT_DIR / "source-snapshot.lean.txt"
SHA_FILE = RECEIPT_DIR / "source-sha256.txt"
README = RECEIPT_DIR / "README.md"
SOURCE = ROOT / "Navier" / "Analysis" / "CriticalMildMeanDriftRemoval.lean"

HEX64 = re.compile(r"\b[0-9a-f]{64}\b")


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class MeanDriftRemovalReceiptIntegrity(unittest.TestCase):
    def test_files_exist(self):
        self.assertTrue(RECEIPT_DIR.is_dir(), f"missing receipt directory: {RECEIPT_DIR.relative_to(ROOT)}")
        for path in (SNAPSHOT, SHA_FILE, README, SOURCE):
            self.assertTrue(path.is_file(), f"missing audit file: {path.relative_to(ROOT)}")

    def test_sha_file_names_the_live_module_path(self):
        # shasum -c format: "<digest>  <path>", two spaces.
        lines = SHA_FILE.read_text().splitlines()
        self.assertEqual(len(lines), 1, f"expected one recorded line, got {lines!r}")
        digest, recorded_path = lines[0].split()
        self.assertRegex(digest, r"\A[0-9a-f]{64}\Z", f"digest not 64-hex: {digest!r}")
        self.assertEqual(
            recorded_path,
            SOURCE.relative_to(ROOT).as_posix(),
            "source-sha256.txt describes a path other than the live audited module",
        )

    def test_receipt_hash_chain_is_consistent(self):
        recorded = SHA_FILE.read_text().split()[0]
        readme_text = README.read_text()
        readme_hashes = HEX64.findall(readme_text)
        # The README quotes the digest (SHA-256 line); its base commit is also a
        # 64-hex object id, so every quoted hash must agree with the recorded one
        # only where it labels the source text.
        sha_line = re.search(r"SHA-256: `([0-9a-f]{64})`", readme_text)
        self.assertIsNotNone(sha_line, "README carries no `SHA-256: <64-hex>` line")
        self.assertEqual(
            sha_line.group(1), recorded, "README SHA-256 disagrees with source-sha256.txt"
        )
        self.assertIn(
            recorded, readme_hashes, "recorded digest absent from README quoted hashes"
        )

    def test_snapshot_text_matches_recorded_digest(self):
        recorded = SHA_FILE.read_text().split()[0]
        self.assertEqual(
            sha256_of(SNAPSHOT), recorded, "source-snapshot.lean.txt drifted from its recorded digest"
        )

    def test_live_source_matches_recorded_digest(self):
        # Drift alarm: edit the audited module and the receipt must be re-minted.
        recorded = SHA_FILE.read_text().split()[0]
        self.assertEqual(
            sha256_of(SOURCE), recorded,
            "Navier/Analysis/CriticalMildMeanDriftRemoval.lean changed after the "
            "2026-09-09 receipt was minted; re-mint the receipt (snapshot, hashes, "
            "compile/axiom logs, README) before landing the edit",
        )

    def test_duplicate_group_is_a_faithful_copy(self):
        self.assertEqual(
            SNAPSHOT.read_bytes(),
            SOURCE.read_bytes(),
            "the receipt snapshot is no longer byte-identical to the audited source",
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
