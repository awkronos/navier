"""Import-closure ratchet, pinned inside the battery CI actually runs.

``tools/module-closure-check.py`` is this repository's own gate: every
``Navier/**/*.lean`` module must sit in the transitive import closure of the
aggregator ``Navier.lean`` (or be a declared standalone audit leaf).  The gate
is not a style rule.  ``scripts/AuditAllAxioms.lean`` starts from ``import
Navier`` and walks the *imported* environment, and ``Navier/AxiomAudit.lean``
prints its raw ``#print axioms`` traces from the same closure; a module nothing
imports is therefore never axiom-censused by either auditor, however clean its
landing receipt looked.

Measured at trunk ``ed32cd8e2375ad219e98b305d33a4205b1751ff4``: eleven landed,
sorry-free modules sat outside the closure and the gate exited 1, while the
``python`` CI job -- the one job cheap enough to have said so -- never ran the
gate.  These tests bind both halves: the gate must exit 0, and the specific
modules measured unwired must be reachable from the aggregator.  A lane that
lands a module with no import leg now fails the battery instead of widening the
audit blind spot.
"""

from __future__ import annotations

import collections
import pathlib
import re
import subprocess
import sys
import unittest

REPO = pathlib.Path(__file__).resolve().parents[1]
GATE = REPO / "tools" / "module-closure-check.py"
# Column-0 `import <dotted name>`, matching the gate's own reading.  The prefix
# test keeps the scan off ~every line in the tree; only import headers reach the
# regex, so the ratchet stays a second rather than a tenth of the battery.
_IMPORT_PREFIX = "import "
_IMPORT_RE = re.compile(r"import ([A-Za-z_][\w.]*)")

# The eleven modules measured outside the closure at trunk ed32cd8.  The
# ContinuousLeiLinFourierEndpointTrace leg reaches the kernel audit through its
# consumer ContinuousLeiLinFourierEndpointBarrier, so it is named here even
# though only the barrier has a direct root import.  Each name is checked only
# while its file exists, so deleting an orphan module -- the other honest way
# out of this gate -- is never a failure here.
TRUNK_ORPHANS = (
    "Navier.AdjointBackpropagation",
    "Navier.Analysis.ContinuousLeiLinFourierEndpointBarrier",
    "Navier.Analysis.ContinuousLeiLinFourierEndpointTrace",
    "Navier.Analysis.CrownBridgeReduction",
    "Navier.Analysis.H3RestartSlice",
    "Navier.Analysis.MildTimeLeafX1CascadeFalsification",
    "Navier.Analysis.RestartAgreementOpen",
    "Navier.Analysis.SourceX1HeatKernelBound",
    "Navier.Analysis.WienerH3DampedProducer",
    "Navier.Transfer.MildSelfMapDefectBudget",
    "Navier.Transfer.MildSelfMapTransport",
)

# Standalone audit surfaces, exempt in the gate itself.
INTENTIONAL_LEAVES = frozenset(
    {"Navier.AxiomAudit", "Navier.ConditionalAudit", "Main"}
)


def module_path(name: str) -> pathlib.Path:
    return REPO / (name.replace(".", "/") + ".lean")


def _imports(text: str) -> list[str]:
    found: list[str] = []
    for line in text.splitlines():
        if not line.startswith(_IMPORT_PREFIX):
            continue
        match = _IMPORT_RE.match(line)
        if match:
            found.append(match.group(1))
    return found


def import_graph() -> dict[str, list[str]]:
    """Module name -> the modules it imports, read from its ``import`` lines."""
    graph: dict[str, list[str]] = {}
    for path in sorted((REPO / "Navier").rglob("*.lean")):
        name = str(path.relative_to(REPO).with_suffix("")).replace("/", ".")
        graph[name] = _imports(path.read_text(encoding="utf-8"))
    for name, path in (("Navier", REPO / "Navier.lean"), ("Main", REPO / "Main.lean")):
        if path.exists():
            graph[name] = _imports(path.read_text(encoding="utf-8"))
    return graph


def reachable_from(root: str, graph: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    queue = collections.deque([root])
    while queue:
        name = queue.popleft()
        if name in seen:
            continue
        seen.add(name)
        queue.extend(graph.get(name, ()))
    return seen


class ModuleClosureGate(unittest.TestCase):
    def test_repo_gate_exits_zero(self) -> None:
        """``make closure`` -- the repository's own ratchet -- is green."""
        proc = subprocess.run(
            [sys.executable, str(GATE), "--repo", str(REPO)],
            capture_output=True,
            text=True,
        )
        self.assertEqual(
            proc.returncode,
            0,
            msg=(
                f"module-closure gate rc={proc.returncode}\n"
                f"{(proc.stdout + proc.stderr).strip()}"
            ),
        )

    def test_trunk_orphans_are_reachable_from_the_aggregator(self) -> None:
        """Every module measured unwired at trunk has a live import leg."""
        graph = import_graph()
        reachable = reachable_from("Navier", graph)
        unwired = [
            name
            for name in TRUNK_ORPHANS
            if module_path(name).exists() and name not in reachable
        ]
        self.assertEqual(
            unwired,
            [],
            msg=(
                "modules invisible to scripts/AuditAllAxioms.lean "
                f"because nothing imports them: {unwired}"
            ),
        )


if __name__ == "__main__":
    unittest.main()
