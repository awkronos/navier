#!/usr/bin/env python3
"""Static blast radius of a dotted namespace row.

Why this exists
---------------
Lean resolves a bare dotted term such as `LatticeDivergenceFree.add` through
EVERY namespace in scope that carries a row of that name.  When two files
dot-extend the same parent constant with the same row name, the term becomes
ambiguous and refuses to elaborate -- but only in a file that happens to have
BOTH declaring namespaces in scope.  Trunk went red twice in one day that way
(`ed32cd8` cured by `586262a`, lane NAVIER-RED-1122), and the consumer set could
not be found by a text grep for `Parent.row`: the use that finally refused was a
type-directed projection, `(hu.sub hu').add hu'` at
`CriticalMildDuhamelBochner.lean:817`, which never spells the parent.  The
compiler found it, twenty build minutes later.

So this tool is the cheap half of that job, and it states the split plainly:

* DUPLICATES -- it lists every declaration site that dot-extends `Parent` with
  `row`, with the namespace each sat in.  More than one is the trunk-red shape.
* BLAST RADIUS -- it lists every file where two or more declaring namespaces are
  simultaneously in scope (through `namespace`/`open`, including the ancestor
  namespaces Lean also resolves through).  Those are the files that can refuse.
* IT CANNOT see a bare `.row` projection's type, so it does not claim to know
  the consumer set.  Every run ends by naming the compiler leg that does.

Exit 0 here means "no static duplicate row", never "safe to delete".

Usage
-----
    python3 tools/dot_row_ambiguity.py LatticeDivergenceFree.add
    python3 tools/dot_row_ambiguity.py --dirs Navier --json SolvesBefore.integrable_secondDirectional_backwardHeatCurlField_mul_velocity

Exit status
-----------
    0  the row is declared at one site (or at none)
    1  the row is dot-extended onto the same parent from more than one site
    2  usage error
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

_DECL_KEYWORDS = ("theorem", "lemma", "def", "abbrev", "instance")
_DECL_PREFIX = re.compile(
    r"^(?:(?:protected|noncomputable)\s+)*(?:" + "|".join(_DECL_KEYWORDS) + r")\s+"
    r"([A-Za-z_][\w.']*)"
)
# A declaration keyword inside a `where` / structure body is a field, not a row.
_NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][\w.']*)")
_END_RE = re.compile(r"^end\s+([A-Za-z_][\w.']*)")
_OPEN_RE = re.compile(r"^open\s+(?:scoped\s+)?(.+)$")
# `#print axioms X.Parent.row` etc. are audit traces, not elaboration sites.
_TRACE_RE = re.compile(r"^#(print|check|eval|verify)\b")


def _line_comment(line: str) -> str:
    cut = line.find("--")
    return line if cut < 0 else line[:cut]


def code_only(lines: list[str]) -> list[tuple[int, str]]:
    """Strip comments from every kind of Lean comment block.

    Returns ``(line_number, code)`` pairs, keeping the line numbers so a report
    points at the real declaration.  Lean has two comment shapes: a `--` line
    comment, and a `/- ... -/` block that nests and may start or stop anywhere on
    a line -- including a doc comment (`/--` and `/--!`, which are blocks too).
    A `theorem Parent.row` written inside a docstring is prose about a row, not a
    declaring site, so it must never be counted as one.
    """
    out: list[tuple[int, str]] = []
    depth = 0
    for number, raw in enumerate(lines, start=1):
        pieces: list[str] = []
        rest = raw
        while True:
            if depth:
                open_at = rest.find("/-")
                close_at = rest.find("-/")
                if close_at < 0:
                    # Comment swallows the whole line, unless it re-opens a block.
                    if open_at >= 0:
                        depth += 1
                    break
                # `/-` inside a block is only an opener if it precedes the closer;
                # `-/-` would be a close followed by a line comment.
                if 0 <= open_at < close_at:
                    depth += 1
                    rest = rest[open_at + 2:]
                    continue
                depth -= 1
                rest = rest[close_at + 2:]
                continue
            body = _line_comment(rest)
            open_at = body.find("/-")
            if open_at < 0:
                pieces.append(body)
                break
            pieces.append(body[:open_at])
            rest = body[open_at + 2:]
            depth += 1
        code = "".join(pieces).strip()
        if code:
            out.append((number, code))
    return out


def _scopes_for(name: str) -> set[str]:
    """A dotted name plus every one of its ancestors."""
    parts = name.split(".")
    return {".".join(parts[:cut]) for cut in range(1, len(parts) + 1)}


def scan_file(path: pathlib.Path, root: pathlib.Path) -> dict:
    """Declarations (with their namespace at the declaration line), scope set."""
    rel = str(path.relative_to(root))
    stack: list[str] = []
    scopes: set[str] = set()
    declarations: list[dict] = []
    trace_uses: list[int] = []
    for number, body in code_only(path.read_text(encoding="utf-8").splitlines()):
        namespace = _NAMESPACE_RE.match(body)
        if namespace:
            stack.append(namespace.group(1))
            scopes |= _scopes_for(namespace.group(1))
            continue
        ended = _END_RE.match(body)
        if ended:
            if stack and (stack[-1] == ended.group(1) or stack[-1].endswith(
                "." + ended.group(1)
            )):
                stack.pop()
            continue
        opened = _OPEN_RE.match(body)
        if opened:
            for token in opened.group(1).split():
                if re.match(r"^[A-Za-z_][\w']*$", token):
                    scopes |= _scopes_for(token)
            continue
        declared = _DECL_PREFIX.match(body)
        if declared:
            declarations.append(
                {
                    "spelling": declared.group(1),
                    "namespace": stack[-1] if stack else "",
                    "line": number,
                }
            )
            continue
        if _TRACE_RE.match(body):
            trace_uses.append(number)
    return {
        "file": rel,
        "declarations": declarations,
        "scopes": sorted(scopes),
        "trace_lines": trace_uses,
    }


def analyse(root: pathlib.Path, row: str, dirs: tuple[str, ...]) -> dict:
    parent, _, tail = row.rpartition(".")
    if not parent or not tail:
        raise SystemExit(f"usage error: {row!r} must be spelled Parent.row")
    records: list[dict] = []
    scanned = 0
    for directory in dirs:
        base = root / directory
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*.lean")):
            scanned += 1
            records.append(scan_file(path, root))

    declared_at = [
        {
            "file": record["file"],
            "line": found["line"],
            "spelling": found["spelling"],
            "namespace": found["namespace"],
        }
        for record in records
        for found in record["declarations"]
        # The duplicate shape is one parent dot-extended from two namespaces;
        # a declaration written bare inside Parent's own namespace is the same
        # constant, so both spellings count.
        if found["spelling"] == row or (
            found["spelling"] == tail and found["namespace"].split(".")[-1] == parent
        )
    ]
    declaring_namespaces = {item["namespace"] for item in declared_at if item["namespace"]}

    in_scope = [
        {
            "file": record["file"],
            "declaring_namespaces": sorted(
                scope
                for scope in record["scopes"]
                if any(
                    scope == ns or ns.endswith("." + scope) or scope.endswith("." + ns)
                    for ns in declaring_namespaces
                )
            ),
        }
        for record in records
    ]
    at_risk = [
        item
        for item in in_scope
        if len(item["declaring_namespaces"]) >= 2
        and item["file"] not in {d["file"] for d in declared_at}
    ]

    return {
        "row": row,
        "parent": parent,
        "tail": tail,
        "lean_files_scanned": scanned,
        "declared_at": declared_at,
        "duplicate": len(declared_at) > 1,
        "declaring_namespaces": sorted(declaring_namespaces),
        "at_risk_files": at_risk,
        "consumer_set_caveat": (
            "a bare `.row` projection (e.g. `(hu.sub hu').add hu'`) never spells "
            "the parent and is invisible to any static scan; the consumer set is "
            "the compiler's answer -- run studio-seat-compile.py --seat <seat> "
            "--lane <LANE> --modules <umbrella> and read 'overloaded, errors' / "
            "'Invalid field' rows"
        ),
    }


def _text(report: dict) -> str:
    lines = [f"row: {report['row']}",
             f"scanned: {report['lean_files_scanned']} .lean files"]
    if report["declared_at"]:
        lines.append(f"declared at {len(report['declared_at'])} site(s):")
        for item in report["declared_at"]:
            lines.append(
                f"  {item['file']}:{item['line']}  [{item['spelling']}] in ns "
                f"{item['namespace'] or '-'}"
            )
    else:
        lines.append("declared at 0 sites")
    lines.append(
        "AMBIGUITY: the row is dot-extended onto the same parent from more than "
        "one namespace -- the bare dotted term is overloaded where both are in "
        "scope and `lake build` refuses there"
        if report["duplicate"]
        else "no static ambiguity: one declaring site"
    )
    if report["at_risk_files"]:
        lines.append("BLAST RADIUS (two or more declaring namespaces in scope):")
        for item in report["at_risk_files"]:
            lines.append(f"  {item['file']}: {', '.join(item['declaring_namespaces'])}")
    else:
        lines.append("blast radius: no file has two declaring namespaces in scope")
    lines.append(f"caveat: {report['consumer_set_caveat']}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("row", help="Parent.row to census")
    parser.add_argument("--root", default=".")
    parser.add_argument("--dirs", nargs="+", default=["Navier"])
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    report = analyse(pathlib.Path(args.root).resolve(), args.row, tuple(args.dirs))
    print(json.dumps(report, indent=2, sort_keys=True) if args.json else _text(report))
    return 1 if report["duplicate"] else 0


if __name__ == "__main__":
    sys.exit(main())
