"""Namespace-row uniqueness ratchet: one public row per parent constant.

Lean resolves a dotted short name such as `LatticeDivergenceFree.add` through
every namespace in scope that carries a row of that shape onto the parent.  When
a second file dot-extends the SAME parent constant with the SAME row name, the
bare term becomes ambiguous for every consumer that opens both namespaces, and
the consumer refuses to elaborate.

This is the defect that made trunk red twice in one day.  `0ad0560` re-proved
`heatRegularizedSpectralOutput_divergenceFree` inside `CriticalMildDuhamelBochner`
and `ed32cd8` deleted that copy -- but the same commit family had left a second
`LatticeDivergenceFree.add`: the parent is defined in `CriticalMildDuhamelBochner`
and `c065664` (2026-07-30) had dot-extended an `add` row onto it from
`CriticalMildSelfMap`.  The bare term then resolved two ways and `lake build`
failed at trunk `ed32cd8e2375ad219e98b305d33a4205b1751ff4`, rc 1, one target:

    error: Navier/Analysis/PhysicalPeriodicCoerciveShellControl.lean:234:8:
    overloaded, errors ... Ambiguous term LatticeDivergenceFree.add
      CriticalMildSelfMap.LatticeDivergenceFree.add ...
      CriticalMildDuhamelBochner.LatticeDivergenceFree.add ...

The cure keeps the row in the namespace that defines its parent -- beside the
`zero` and `sub` siblings, which is also where the file's own internal caller
`(hu.sub hu').add hu'` at `CriticalMildDuhamelBochner.lean:817` needs it -- and
deletes the namespace-alien copy, retargeting the one declaration that named it
in full (`CriticalMildInteriorTimeModulus.lean:206`).  Deleting the parent's own
row instead would have forced that internal caller to re-derive the argument by
hand, which is the redundancy this ratchet exists to prevent.

Only rows whose parent constant has exactly one owner in the tree can go
ambiguously duplicate this way, so the census is restricted to those; a row name
reused under two separately-defined parents is ordinary namespacing, not a
hazard.  `BASELINE` was the ledger of sites lane NAVIER-RED-1122 measured and did
not clear.  Lane NAVIER-RED-1122-CONT closed the last of them, so the ratchet now
runs at its floor: an empty baseline, a stated-once duplicate fails the battery
instead of being added to a list.
"""

from __future__ import annotations

import pathlib
import re
import unittest

REPO = pathlib.Path(__file__).resolve().parents[1]
SOURCE_ROOT = REPO / "Navier"

_MODIFIERS = ("protected ", "noncomputable ")
_ROW_KEYWORDS = ("theorem", "lemma", "def", "abbrev")
_PARENT_KEYWORDS = ("def", "structure", "class", "inductive", "abbrev")
# Lines worth testing at all: a declaration keyword after leading blanks and any
# `protected`/`noncomputable` prefix.  Skipping the other ~half-million lines is
# what keeps this ratchet a fraction of a second per battery run.
_CANDIDATE_PREFIXES = tuple(
    prefix + keyword
    for prefix in ("", *_MODIFIERS)
    for keyword in sorted(set(_ROW_KEYWORDS) | set(_PARENT_KEYWORDS))
)
_NAME = r"([A-Za-z_][\w.']*)"
_ROW_RE = re.compile(
    r"^(?:" + "|".join(re.escape(m) for m in _MODIFIERS) + r")*"
    r"(?:" + "|".join(_ROW_KEYWORDS) + r")[ \t]+" + _NAME
)
_PARENT_RE = re.compile(
    r"^(?:" + "|".join(re.escape(m) for m in _MODIFIERS) + r")*"
    r"(?:" + "|".join(_PARENT_KEYWORDS) + r")[ \t]+" + _NAME
)

#: Rows dot-extended onto a single-owner parent from MORE THAN ONE file -- the
#: shape that went ambiguous on trunk (see this module's docstring).  The census
#: deliberately does NOT demand that a row live in its parent's own file:
#: measured at this commit, 69 rows extend another namespace's parent from a
#: consumer file, which is ordinary Lean practice and not a hazard.  Only a name
#: declared twice is ambiguous, so an entry may only ever be DELETED here: state
#: the fact once, retarget the consumers that named the other copy, and drop the
#: entry.  It is empty because lane NAVIER-RED-1122-CONT cleared the last site
#: lane NAVIER-RED-1122 had recorded -- see
#: `test_baseline_is_empty_and_the_cleared_row_has_one_home`.
BASELINE: dict[str, tuple[str, ...]] = {}

#: The row whose duplicate copy made the trunk build refuse (lane NAVIER-RED-1122).
FIXED_ROW = "LatticeDivergenceFree.add"
FIXED_ROW_HOME = "Navier/Analysis/CriticalMildDuhamelBochner.lean"

#: The last site `BASELINE` ever held, closed by lane NAVIER-RED-1122-CONT.  Its
#: parent `SolvesBefore` is owned by `CriticalControlDecomposition.lean`; two files
#: dot-extended the row onto it -- `WholeSpaceSolenoidalHeatViscousIntegrability.lean`
#: (`17df966`, 2026-09-09) and the byte-identical salvage copy
#: `WholeSpaceSolenoidalHeatViscousLimit.lean` (`9860d00`, 2026-09-10), which nothing
#: imported but the aggregator.  Every full-name proof consumer already named the
#: surviving home, so no proof term moved: the copy is deleted and its lone
#: file-local `#print axioms` trace moved onto the surviving declaration.
CLEARED_ROW = (
    "SolvesBefore.integrable_secondDirectional_backwardHeatCurlField_mul_velocity"
)
CLEARED_ROW_HOME = "Navier/Analysis/WholeSpaceSolenoidalHeatViscousIntegrability.lean"
#: The surviving declaration as a consumer writes it in full, and as the moved
#: `#print axioms` trace names it.
CLEARED_ROW_QUALIFIED = (
    "Navier.Analysis.WholeSpaceSolenoidalHeatViscousIntegrability." + CLEARED_ROW
)
CLEARED_DUPLICATE = "Navier/Analysis/WholeSpaceSolenoidalHeatViscousLimit.lean"
CLEARED_PARENT = "SolvesBefore"
CLEARED_PARENT_OWNER = "Navier/Analysis/CriticalControlDecomposition.lean"
#: The three full-name proof consumers measured at this commit; each must still name
#: the surviving home, and none may name the deleted copy.
CLEARED_ROW_CONSUMERS = (
    "Navier/Analysis/WholeSpaceSolenoidalHeatViscousCutoffLimit.lean",
    "Navier/Analysis/WholeSpaceSolenoidalHeatViscousProductLimit.lean",
    "Navier/Analysis/WholeSpaceSolenoidalHeatViscousDomination.lean",
)

_CENSUS: tuple[dict[str, set[str]], dict[str, str]] | None = None


def _strip_modifiers(line: str) -> str:
    for modifier in _MODIFIERS:
        if line.startswith(modifier):
            line = line[len(modifier):]
    return line


def census() -> tuple[dict[str, set[str]], dict[str, str]]:
    """``(row -> declaring files, parent -> declaring files)`` over ``Navier/``.

    Both maps are keyed by the dotted name as written in the declaration, so a
    row's key is ``parent.row`` only in the source's own spelling; the caller
    resolves the parent against the owner map.
    """
    global _CENSUS
    if _CENSUS is None:
        rows: dict[str, set[str]] = {}
        parents: dict[str, set[str]] = {}
        for path in sorted(SOURCE_ROOT.rglob("*.lean")):
            rel = str(path.relative_to(REPO))
            for raw in path.read_text(encoding="utf-8").splitlines():
                line = raw.lstrip(" \t")
                if not line.startswith(_CANDIDATE_PREFIXES):
                    continue
                body = _strip_modifiers(line)
                match = _ROW_RE.match(body)
                if match:
                    rows.setdefault(match.group(1), set()).add(rel)
                match = _PARENT_RE.match(body)
                if match:
                    parents.setdefault(match.group(1), set()).add(rel)
        _CENSUS = (rows, parents)
    return _CENSUS


def single_owner_parents() -> dict[str, str]:
    """Parent constant name -> its sole declaring file, for owned-once parents."""
    _, parents = census()
    return {name: next(iter(files)) for name, files in parents.items() if len(files) == 1}


def declaring_files(short_name: str) -> set[str]:
    """Files declaring a constant written exactly ``short_name``."""
    rows, _ = census()
    return set(rows.get(short_name, set()))


def duplicate_rows() -> dict[str, tuple[str, ...]]:
    """``parent.row`` -> declaring files, for rows on a single-owner parent."""
    rows, _ = census()
    parents = single_owner_parents()
    found: dict[str, tuple[str, ...]] = {}
    for name, files in rows.items():
        if "." not in name or len(files) < 2:
            continue
        head, _, row = name.rpartition(".")
        if head in parents:
            found[f"{head}.{row}"] = tuple(sorted(files))
    return found


class NamespaceRowUniqueness(unittest.TestCase):
    def test_divergence_free_add_has_one_public_row(self) -> None:
        """`LatticeDivergenceFree.add` is stated once, in its landed home."""
        declaring = declaring_files(FIXED_ROW)
        self.assertEqual(
            declaring,
            {FIXED_ROW_HOME},
            msg=(
                f"{FIXED_ROW} declared in {sorted(declaring)}; the bare term is "
                "ambiguous for every consumer that opens both namespaces and "
                "`lake build` refuses"
            ),
        )
        self.assertEqual(
            single_owner_parents().get("LatticeDivergenceFree"),
            "Navier/Analysis/CriticalMildDuhamelBochner.lean",
            msg="the divergence-free parent moved; this pin names its owner",
        )

    def test_baseline_is_empty_and_the_cleared_row_has_one_home(self) -> None:
        """The ratchet sits at its floor, and the last closed site stayed closed."""
        self.assertEqual(
            BASELINE,
            {},
            msg="BASELINE may only shrink; an entry here records a duplicate that "
            "makes the bare dotted term ambiguous for every consumer opening both "
            "namespaces",
        )
        self.assertEqual(
            declaring_files(CLEARED_ROW),
            {CLEARED_ROW_HOME},
            msg=(
                f"{CLEARED_ROW} declared in {sorted(declaring_files(CLEARED_ROW))}; "
                "lane NAVIER-RED-1122-CONT left exactly one home for it"
            ),
        )
        self.assertEqual(
            single_owner_parents().get(CLEARED_PARENT),
            CLEARED_PARENT_OWNER,
            msg="the `SolvesBefore` parent moved; this pin names its owner",
        )
        self.assertFalse(
            (REPO / CLEARED_DUPLICATE).exists(),
            msg=(
                "the byte-identical salvage copy is deleted; a file that returns "
                "and dot-extends `SolvesBefore` with this row name re-opens the "
                "trunk-ambiguous term this ratchet was written for"
            ),
        )
        aggregator = (REPO / "Navier.lean").read_text(encoding="utf-8")
        self.assertNotIn(
            "import Navier.Analysis.WholeSpaceSolenoidalHeatViscousLimit",
            aggregator,
            msg="the aggregator imports a module that no longer exists; `lake build` refuses",
        )
        for consumer in CLEARED_ROW_CONSUMERS:
            text = (REPO / consumer).read_text(encoding="utf-8")
            self.assertIn(
                CLEARED_ROW,
                text,
                msg=f"{consumer} no longer consumes the viscous integrability row",
            )
            self.assertNotIn(
                "WholeSpaceSolenoidalHeatViscousLimit." + CLEARED_ROW,
                text,
                msg=f"{consumer} names the deleted copy; it will not elaborate",
            )
        self.assertIn(
            "#print axioms " + CLEARED_ROW_QUALIFIED,
            (REPO / CLEARED_ROW_HOME).read_text(encoding="utf-8"),
            msg=(
                "the duplicate file's raw `#print axioms` trace moved onto the "
                "surviving declaration, so deleting the file did not shrink the "
                "audit surface"
            ),
        )

    def test_duplicate_row_census_matches_the_recorded_baseline(self) -> None:
        """No cross-namespace duplicate row anywhere: `BASELINE` is now empty."""
        found = duplicate_rows()
        self.assertEqual(
            found,
            BASELINE,
            msg=(
                "rows declared under a single-owner parent in more than one file: "
                f"{ {k: v for k, v in found.items() if BASELINE.get(k) != v} }. "
                "A second row onto the same parent makes the bare dotted term "
                "ambiguous and the trunk build refuses (see this module's "
                "docstring). State the fact once and retarget the consumer that "
                "named the other copy; BASELINE is empty and is only ever left "
                "empty."
            ),
        )

    def test_full_name_consumers_name_the_surviving_row(self) -> None:
        """`CriticalMildInteriorTimeModulus` no longer names the deleted duplicate."""
        text = (REPO / "Navier/Analysis/CriticalMildInteriorTimeModulus.lean").read_text(
            encoding="utf-8"
        )
        self.assertNotIn(
            "CriticalMildSelfMap.LatticeDivergenceFree.add",
            text,
            msg=(
                "the `add` row now lives once, in the namespace that defines "
                "`LatticeDivergenceFree`; a full-name consumer of the deleted "
                "copy will not elaborate"
            ),
        )
        self.assertIn(
            f"CriticalMildDuhamelBochner.{FIXED_ROW}",
            text,
            msg="the surviving row should be named by the consumer that needs it",
        )


if __name__ == "__main__":
    unittest.main()
