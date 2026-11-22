"""Pin for `tools/dot_row_ambiguity.py`, the duplicate-row blast-radius census.

The instrument exists because lane NAVIER-RED-1122 found a trunk-red duplicate
by building for twenty minutes: Lean resolves a bare dotted term through every
namespace in scope, so two files dot-extending the SAME parent with the SAME row
name make that term ambiguous wherever both namespaces are open.  Two rows in
the tree went through that shape -- `LatticeDivergenceFree.add` (cured in
`586262a`) and
`SolvesBefore.integrable_secondDirectional_backwardHeatCurlField_mul_velocity`
(cured by lane NAVIER-RED-1122-CONT, which deleted the byte-identical salvage
copy `WholeSpaceSolenoidalHeatViscousLimit.lean`).

A static census that only ever reports "clean" on a clean tree proves nothing, so
the fixture below SYNTHESISES the ambiguous shape and requires the tool to name
both declaring sites and the at-risk consumer.  The repo half then requires the
two cured rows to report exactly one site each at this commit.
"""

from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest

REPO = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "tools"))

import dot_row_ambiguity  # noqa: E402

SOLVES_BEFORE_ROW = (
    "SolvesBefore.integrable_secondDirectional_backwardHeatCurlField_mul_velocity"
)
LATTICE_ROW = "LatticeDivergenceFree.add"
LATTICE_HOME = "Navier/Analysis/CriticalMildDuhamelBochner.lean"
SOLVES_BEFORE_HOME = "Navier/Analysis/WholeSpaceSolenoidalHeatViscousIntegrability.lean"
SALVAGE_COPY = "Navier/Analysis/WholeSpaceSolenoidalHeatViscousLimit.lean"

_FIXTURE = {
    "Alpha.lean": (
        "namespace Alpha\n"
        "structure Parent := mk ::\n"
        "theorem Parent.row : True := trivial\n"
        "end Alpha\n"
    ),
    "Beta.lean": (
        "namespace Beta\n"
        "theorem Parent.row : True := trivial\n"
        "end Beta\n"
    ),
    "Consumer.lean": (
        "open Alpha\n"
        "open Beta\n"
        "theorem uses_it : True := Parent.row\n"
    ),
    "MentionsOnly.lean": (
        "/-\n"
        "Prose only: Alpha.Parent.row is discussed here, and\n"
        "even a line that starts `theorem Parent.row` inside this\n"
        "block is documentation, not a declaration.\n"
        "-/\n"
        "namespace Gamma\n"
        "-- Alpha.Parent.row in a comment\n"
        "theorem unrelated : True := trivial\n"
        "end Gamma\n"
    ),
}


class DotRowAmbiguity(unittest.TestCase):
    def _report(self, root: pathlib.Path, row: str):
        return dot_row_ambiguity.analyse(root, row, (".",))

    def test_fixture_with_two_declaring_namespaces_is_flagged(self) -> None:
        """The ambiguous shape is detected, not silently passed."""
        with tempfile.TemporaryDirectory() as scratch:
            root = pathlib.Path(scratch)
            for name, text in _FIXTURE.items():
                (root / name).write_text(text, encoding="utf-8")
            report = self._report(root, "Parent.row")
        self.assertTrue(report["duplicate"], msg=str(report["declared_at"]))
        sites = {(item["file"], item["namespace"]) for item in report["declared_at"]}
        self.assertEqual(
            sites,
            {("Alpha.lean", "Alpha"), ("Beta.lean", "Beta")},
            msg="both declaring sites must be named with their namespaces",
        )
        risky = {item["file"] for item in report["at_risk_files"]}
        self.assertIn("Consumer.lean", risky, msg=str(report["at_risk_files"]))
        self.assertNotIn(
            "MentionsOnly.lean",
            risky,
            msg="a file that opens neither namespace is not in the blast radius",
        )

    def test_docstring_and_comment_mentions_are_not_declarations(self) -> None:
        """Comment prose never counts as a declaring site."""
        with tempfile.TemporaryDirectory() as scratch:
            root = pathlib.Path(scratch)
            (root / "MentionsOnly.lean").write_text(_FIXTURE["MentionsOnly.lean"],
                                                    encoding="utf-8")
            report = self._report(root, "Parent.row")
        self.assertEqual(report["declared_at"], [], msg=str(report))
        self.assertFalse(report["duplicate"])

    def test_usage_error_on_a_name_with_no_parent(self) -> None:
        with self.assertRaises(SystemExit):
            self._report(REPO, "row_without_parent")

    def test_cured_lattice_row_reports_one_site(self) -> None:
        report = dot_row_ambiguity.analyse(REPO, LATTICE_ROW, ("Navier",))
        self.assertFalse(report["duplicate"], msg=str(report["declared_at"]))
        self.assertEqual(
            [item["file"] for item in report["declared_at"]],
            [LATTICE_HOME],
            msg="the surviving `add` row has one home; a second declaration re-opens it",
        )

    def test_cured_solves_before_row_reports_one_site(self) -> None:
        report = dot_row_ambiguity.analyse(REPO, SOLVES_BEFORE_ROW, ("Navier",))
        self.assertFalse(report["duplicate"], msg=str(report["declared_at"]))
        self.assertEqual(
            [item["file"] for item in report["declared_at"]],
            [SOLVES_BEFORE_HOME],
            msg=(
                "the salvage copy is the file that would re-open the ambiguity; "
                "it must stay deleted, or its row deleted with it"
            ),
        )
        self.assertNotIn(
            SALVAGE_COPY,
            [item["file"] for item in report["declared_at"]],
        )

    def test_entry_point_exit_status_is_the_duplicate_flag(self) -> None:
        """rc 0 = clean census, rc 1 = duplicate: a CI leg can gate on it."""
        with tempfile.TemporaryDirectory() as scratch:
            root = pathlib.Path(scratch)
            for name, text in _FIXTURE.items():
                (root / name).write_text(text, encoding="utf-8")
            self.assertEqual(dot_row_ambiguity.main(
                ["Parent.row", "--root", str(root), "--dirs", "."]), 1)
            self.assertEqual(dot_row_ambiguity.main(
                [LATTICE_ROW, "--root", str(REPO), "--dirs", "Navier"]), 0)


if __name__ == "__main__":
    unittest.main()
