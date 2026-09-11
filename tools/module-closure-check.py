#!/usr/bin/env python3
"""Import-closure ratchet for the Navier repository.

Every ``Navier/**/*.lean`` source module must sit inside the transitive
import closure of the aggregator ``Navier.lean`` (the library root), or be
listed below as an intentional standalone audit entry point.  An unwired
module is invisible to ``scripts/AuditAllAxioms.lean`` (which imports
``Navier``), to Mathlib-cache reuse, and to every whole-environment audit,
so its axiom trace is compiler-unverified no matter how clean its raw
receipts looked when it was first compiled.

Exit code 0 means the closure is complete; 1 lists each orphan.

Usage:
    python3 tools/module-closure-check.py [--repo PATH] [--verbose]
"""

from __future__ import annotations

import argparse
import collections
import pathlib
import re
import sys

IMPORT_RE = re.compile(r"^import ([A-Za-z_][\w.]*)", re.MULTILINE)

# Standalone audit surfaces and executables that are not (and must not be)
# imported from the library root: they print traces or scan environments when
# compiled directly by `make axioms` / `make conditional-audit`.
INTENTIONAL_LEAVES = {
    "Navier.AxiomAudit",
    "Navier.ConditionalAudit",
    "Main",
}


def module_name(root: pathlib.Path, path: pathlib.Path) -> str:
    return str(path.relative_to(root).with_suffix("")).replace("/", ".")


def collect(root: pathlib.Path) -> dict[str, tuple[pathlib.Path, list[str]]]:
    graph: dict[str, tuple[pathlib.Path, list[str]]] = {}
    for path in sorted((root / "Navier").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        graph[module_name(root, path)] = (path, IMPORT_RE.findall(text))
    for extra, name in ((root / "Navier.lean", "Navier"), (root / "Main.lean", "Main")):
        if extra.exists():
            graph[name] = (extra, IMPORT_RE.findall(extra.read_text(encoding="utf-8")))
    return graph


def closure(graph: dict, root_module: str) -> set[str]:
    seen: set[str] = set()
    queue = collections.deque([root_module])
    while queue:
        name = queue.popleft()
        if name in seen:
            continue
        seen.add(name)
        entry = graph.get(name)
        if entry is not None:
            queue.extend(entry[1])
    return seen


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=str(pathlib.Path(__file__).resolve().parents[1]))
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()
    root = pathlib.Path(args.repo)

    graph = collect(root)
    if "Navier" not in graph:
        print("ERROR: no Navier.lean aggregator found", file=sys.stderr)
        return 2
    reachable = closure(graph, "Navier")

    orphans = sorted(
        name
        for name in graph
        if name not in reachable and name not in INTENTIONAL_LEAVES
    )
    # Imports pointing at files that no longer exist.
    dangling = sorted(
        (f"{user} -> {dep}")
        for user, (_p, deps) in graph.items()
        for dep in deps
        if dep.startswith("Navier") and dep not in graph
    )

    if args.verbose:
        print(f"modules: {len(graph)}  reachable from Navier.lean: {len(reachable)}")
    if dangling:
        print("dangling imports (module files missing):")
        for line in dangling:
            print("  ", line)
    if orphans:
        print("NOT IN IMPORT CLOSURE of Navier.lean (wire into the aggregator):")
        for name in orphans:
            print("  ", name)
    if orphans or dangling:
        return 1
    print("module import closure complete: every Navier module is reachable "
          "from Navier.lean")
    return 0


if __name__ == "__main__":
    sys.exit(main())
