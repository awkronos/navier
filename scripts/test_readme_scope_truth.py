#!/usr/bin/env python3
"""README scope-truth regression test — files only, zero Lean CPU.

Runs with stock Python 3 (stdlib; no PyYAML, no lake, no network):

    python3 -m unittest discover -s scripts -p 'test_readme_scope_truth.py' -v

What it pins. `formalization.yaml` is the machine-readable mirror of the
repository's claim set; `README.md` is its public face. The failure mode this
test closes is a README that reads as though the unforced three-dimensional
Navier-Stokes Millennium problem were settled, or whose reported row counts
drift from the manifest. Concretely:

  1. the H1 headline names forced whole-space alternative C and its carrier
     declaration `wholeSpaceBreakdown` as the claimed object;
  2. both the opening summary (H1 down to the first `## ` heading) and the
     `## Status summary` section name that object, state that the Clay unforced
     Navier-Stokes Millennium problem is open, and restate the manifest counts;
  3. every `N <STATUS>` and `N rows total` claim anywhere in README.md equals
     the count recomputed from formalization.yaml, in both directions (a status
     the manifest carries must be stated, and a stated status must not be
     miscounted);
  4. the manifest's `crown_C_whole_space_forced` row is still status `THEOREM`
     and still names the declaration README quotes, whose `theorem` keyword is
     located in the quoted source file;
  5. no phrasing claims the Millennium problem is solved, settled, resolved or
     disproved.

Nothing here proves or rebuilds a theorem: statuses are read from the manifest,
and the source-file probe is a regex over text.
"""

from __future__ import annotations

import importlib.util
import re
import sys
import unittest
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
README = ROOT / "README.md"
MANIFEST = ROOT / "formalization.yaml"

CROWN_C_ROW = "crown_C_whole_space_forced"

# Manifest status vocabulary, longest first so the alternation cannot split
# CONDITIONAL_THEOREM into THEOREM.
STATUS_TOKENS = ("CONDITIONAL_THEOREM", "FALSIFIED", "THEOREM", "OPEN")

# "6 `THEOREM`" / "4 OPEN" style claims. The trailing lookahead keeps a token
# from being matched as the prefix of a longer one.
_COUNT_TPL = r"(\d+)\s+`?(%s)`?(?![A-Za-z_])" % "|".join(STATUS_TOKENS)
COUNT_RE = re.compile(_COUNT_TPL)
TOTAL_RE = re.compile(r"(\d+)\s+rows\s+total")

# The claimed object: "forced whole-space alternative C" (`.` also absorbs an
# en dash) plus the carrier declaration name.
CLAIM_RE = re.compile(r"forced\s+whole.space\s+alternative\s+C\b", re.I)
DECL_RE = re.compile(r"wholeSpaceBreakdown", re.I)

# "Clay ... open" inside one sentence-ish window; \bopen\b cannot match OpenAI.
CLAY_WINDOW = 400
CLAY_OPEN_RE = re.compile(r"Clay.{0,%d}\bopen\b" % CLAY_WINDOW, re.I | re.S)
SOLVED_NEAR_CLAY_RE = re.compile(
    r"(?:Clay|Millennium).{0,120}\b(?:solved|settled|resolved|disproved)\b"
    r"|\b(?:solved|settled|resolved|disproved)\b.{0,120}(?:Clay|Millennium)",
    re.I | re.S,
)


def _load_manifest_rows(path: Path) -> list[dict]:
    """Parse formalization.yaml with the repo's own stdlib strict-subset loader.

    `check_formalization.load_yaml_subset` is the same reader CI uses via
    `--check`, so this test cannot disagree with it about what a row is.
    """
    try:
        from check_formalization import load_yaml_subset  # scripts/ on sys.path
    except ImportError:  # invoked outside discovery, e.g. `python3 scripts/x.py`
        spec = importlib.util.spec_from_file_location(
            "check_formalization", HERE / "check_formalization.py"
        )
        assert spec and spec.loader
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        load_yaml_subset = module.load_yaml_subset
    doc = load_yaml_subset(path)
    return doc.get("rows") or []


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _regions(readme: str) -> tuple[str, str, str]:
    """Return (h1 line, opening summary up to the first `## `, status summary)."""
    lines = readme.splitlines()
    h1 = next((ln for ln in lines if ln.startswith("# ")), "")
    h2 = [i for i, ln in enumerate(lines) if ln.startswith("## ")]
    opening = "\n".join(lines[: h2[0] if h2 else len(lines)])
    status = ""
    for i in h2:
        if lines[i].strip().lower().startswith("## status summary"):
            end = next((j for j in h2 if j > i), len(lines))
            status = "\n".join(lines[i:end])
            break
    return h1, opening, status


def _blob(region: str) -> str:
    """One line, so wrapped markdown cannot break a phrase the test needs."""
    return " ".join(region.split())


class ReadmeScopeTruth(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.readme = _read(README)
        cls.rows = _load_manifest_rows(MANIFEST)
        cls.counts = Counter(row.get("status", "") for row in cls.rows)
        cls.h1, cls.opening, cls.status_summary = _regions(cls.readme)

    # -- 1. headline ---------------------------------------------------------

    def test_h1_names_alternative_c_and_whole_space_breakdown(self) -> None:
        self.assertTrue(self.h1, "README.md has no `# ` H1 line")
        blob = _blob(self.h1)
        self.assertRegex(
            blob, CLAIM_RE,
            "H1 must name forced whole-space alternative C as the claimed object",
        )
        self.assertRegex(
            blob, DECL_RE,
            "H1 must name the carrier declaration wholeSpaceBreakdown",
        )
        self.assertNotRegex(
            blob, SOLVED_NEAR_CLAY_RE,
            "H1 must not read as solving the Clay Millennium problem",
        )

    # -- 2. both summaries carry the full scope -----------------------------

    def test_opening_summary_states_claimed_object_clay_open_and_counts(self) -> None:
        self._assert_summary(self.opening, "opening summary (H1 to first `## `)")

    def test_status_summary_section_states_claimed_object_clay_open_and_counts(self) -> None:
        self.assertTrue(
            self.status_summary,
            "README.md needs a `## Status summary` section restating the scope",
        )
        self._assert_summary(self.status_summary, "`## Status summary` section")

    def _assert_summary(self, region: str, label: str) -> None:
        blob = _blob(region)
        self.assertRegex(blob, CLAIM_RE, f"{label} must name forced whole-space alternative C")
        self.assertRegex(blob, DECL_RE, f"{label} must name wholeSpaceBreakdown")
        self.assertIn("clay", blob.lower(), f"{label} must mention the Clay problem")
        self.assertIn("millennium", blob.lower(), f"{label} must call it a Millennium problem")
        self.assertIn("unforced", blob.lower(), f"{label} must qualify the Clay problem as unforced")
        self.assertRegex(
            blob, CLAY_OPEN_RE,
            f"{label} must state that the Clay unforced Navier-Stokes problem is open",
        )
        self._assert_counts_present(blob, label)

    def _assert_counts_present(self, blob: str, label: str) -> None:
        for token in self.counts:
            self.assertRegex(
                blob, re.compile(r"\d+\s+`?" + token + r"`?(?![A-Za-z_])"),
                f"{label} must state the `{token}` row count from formalization.yaml",
            )
        self.assertRegex(
            blob, TOTAL_RE, f"{label} must state the total row count from formalization.yaml"
        )

    # -- 3. every count claim agrees with the manifest ----------------------

    def test_all_readme_status_counts_match_manifest(self) -> None:
        wrong = []
        seen: set[str] = set()
        for match in COUNT_RE.finditer(self.readme):
            number, token = int(match.group(1)), match.group(2)
            seen.add(token)
            if number != self.counts.get(token, 0):
                wrong.append(f"{number} `{token}` != {self.counts.get(token, 0)} in manifest")
        self.assertEqual(wrong, [], f"README.md miscounts formalization.yaml rows: {wrong}")

    def test_manifest_statuses_are_all_stated_in_readme(self) -> None:
        seen = {match.group(2) for match in COUNT_RE.finditer(self.readme)}
        missing = [token for token, n in sorted(self.counts.items()) if n and token not in seen]
        self.assertEqual(missing, [], f"README.md never states these manifest statuses: {missing}")

    def test_readme_total_row_count_matches_manifest(self) -> None:
        totals = [int(m.group(1)) for m in TOTAL_RE.finditer(self.readme)]
        self.assertTrue(totals, "README.md states no '<N> rows total' claim")
        bad = [n for n in totals if n != len(self.rows)]
        self.assertEqual(
            bad, [],
            f"README.md claims {bad} rows total; formalization.yaml has {len(self.rows)}",
        )

    # -- 4. the quoted crown is still a THEOREM row -------------------------

    def test_crown_c_row_is_theorem_and_readme_quotes_its_declaration(self) -> None:
        crown = [row for row in self.rows if row.get("id") == CROWN_C_ROW]
        self.assertEqual(len(crown), 1, f"expected exactly one {CROWN_C_ROW!r} row")
        row = crown[0]
        self.assertEqual(
            row.get("status"), "THEOREM",
            "README headlines alternative C as proved; formalization.yaml no longer says so",
        )
        declaration = row.get("declaration", "")
        name = declaration.rsplit(".", 1)[-1]
        self.assertIn(name, self.readme, f"README.md must quote declaration {declaration}")
        source = ROOT / row.get("file", "")
        self.assertTrue(source.is_file(), f"manifest row {CROWN_C_ROW} names a missing file")
        self.assertRegex(
            _read(source),
            re.compile(rf"^\s*(?:theorem|lemma)\s+{re.escape(name)}\b", re.M),
            f"{name} is not a theorem/lemma in {row.get('file')}",
        )

    # -- 5. no Millennium-solved phrasing anywhere --------------------------

    def test_readme_never_claims_the_millennium_problem_solved(self) -> None:
        blob = _blob(self.readme)
        self.assertNotRegex(
            blob, SOLVED_NEAR_CLAY_RE,
            "README.md phrasing reads as solving/settling the Clay Millennium problem",
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)
