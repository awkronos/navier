"""Battery-schedule ratchet: no test file may exist that no run executes.

Measured at origin/main ``80540a20c7d095876bdf69b9c52ba098f6845b64``::

    $ python3 -m unittest discover -s tests -v | grep -c '^Ran '
    1                       # one root, 58 tests
    $ python3 -m unittest discover -s tests -v 2>&1 | grep -ci readme
    0                       # the README scope gate is not in it

``scripts/test_readme_scope_truth.py`` is the gate ``README.md`` itself cites as
the instrument that "recomputes those counts from the manifest and fails this
page if the headline, either summary, or those numbers drift", and
``docs/POSITION.md`` calls it a maintenance law. It lived in a root that neither
``make test`` nor the CI python job discovered, so the only way it ever ran was a
human remembering the command in its own docstring. A test nobody runs pins
nothing, and README/``formalization.yaml`` drift would have been caught by no
scheduled check at all.

The fix is one battery definition (``Makefile:TEST_ROOTS``, which ``make test``
loops and CI calls) plus this ratchet, which binds four ways:

1. CI's python job runs ``make test`` and spells no discovery root of its own,
   so the workflow cannot drift behind the Makefile again;
2. every ``test_*.py`` in the tree that is a stdlib-``unittest`` file sits under
   a scheduled root, and every non-scheduled one is a *typed* exclusion that
   really needs another runner (pytest) and names the command that runs it;
3. CI's ``OR23-Q8`` selected-count leg is executed here against a synthetic
   two-root log, so a multi-root battery cannot be gated on one line again
   (``awk '{print $2}'`` over two ``Ran N tests`` lines yields ``58 8`` and
   ``test "58 8" -ge 1`` is a bash arithmetic error, not a pass);
4. every repository script the python job names exists, so a step cannot be
   enrolled against a carrier that a rename removed.

Nothing here compiles Lean; it reads files and runs one ``awk``.

Usage:
    python3 -m unittest discover -s tests -p 'test_battery_schedule.py' -v
"""

from __future__ import annotations

import importlib.abc
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest
from importlib import util as _importlib_util
from typing import cast

REPO = pathlib.Path(__file__).resolve().parents[1]
MAKEFILE = REPO / "Makefile"
CI = REPO / ".github" / "workflows" / "ci.yml"

# Directories that never hold repository tests.
SKIP_DIRS = frozenset(
    {".git", ".lake", ".venv", "node_modules", "__pycache__", ".codex", ".mypy_cache"}
)

# Files under a root the unittest battery cannot run, each with the command that
# DOES run it. An entry is refused unless the file genuinely needs the other
# runner (it imports pytest) -- so this table cannot be used to hide a
# stdlib-unittest file -- and is refused when the file disappears, so the debt
# cannot outlive its reason. None of these is scheduled by CI today; each names
# the consumer command its own docs print.
NON_UNITTEST_TESTS: dict[str, str] = {
    "solver/interval_cert/test_float64_cert.py": (
        "python3 -m pytest solver/interval_cert/test_float64_cert.py -q"
    ),
}

_TEST_GLOB = "test_*.py"


def repo_test_files() -> list[pathlib.Path]:
    """Every tracked-shape ``test_*.py`` in the tree, roots excluded."""
    out: list[pathlib.Path] = []
    for path in sorted(REPO.rglob(_TEST_GLOB)):
        if SKIP_DIRS & set(path.relative_to(REPO).parts):
            continue
        out.append(path)
    return out


def is_unittest_file(path: pathlib.Path) -> bool:
    """Stdlib-``unittest`` battery member: imports unittest or subclasses TestCase."""
    text = path.read_text(encoding="utf-8", errors="replace")
    return bool(
        re.search(r"^\s*(?:from|import)\s+unittest\b", text, re.M)
        or re.search(r"\(\s*unittest\.TestCase\s*\)|\(\s*TestCase\s*\)", text)
    )


def makefile_test_roots() -> list[str]:
    """The roots ``make test`` discovers, read from the Makefile's own binding."""
    text = MAKEFILE.read_text(encoding="utf-8")
    match = re.search(r"^TEST_ROOTS\s*[:?]?=\s*(.+)$", text, re.M)
    if not match:
        raise AssertionError("Makefile declares no TEST_ROOTS binding")
    roots = match.group(1).split()
    # Reject a root that the recipe cannot actually reach.
    for root in roots:
        if not (REPO / root).is_dir():
            raise AssertionError(f"Makefile TEST_ROOTS names a missing directory: {root}")
    return roots


def ci_python_job() -> str:
    """The ``run:`` body of the CI python job's checks step."""
    text = CI.read_text(encoding="utf-8")
    match = re.search(
        r"\n  python:\n.*?- name: Run Python checks\n\s+run: \|\n((?:[ ]{10,}.*\n?)*)",
        text,
        re.S,
    )
    if not match:
        raise AssertionError("ci.yml has no `Run Python checks` step in the python job")
    return match.group(1)


def ci_job_text(job: str) -> str:
    """The raw YAML text owned by ``jobs.<job>``, up to the next job key."""
    lines = CI.read_text(encoding="utf-8").splitlines()
    start = next(
        (i for i, line in enumerate(lines) if line.strip() == f"{job}:"),
        None,
    )
    if start is None:
        raise AssertionError(f"ci.yml has no `{job}` job")
    end = next(
        (i for i in range(start + 1, len(lines)) if re.match(r"^  \S[^:]*:\s*(#.*)?$", lines[i])),
        len(lines),
    )
    return "\n".join(lines[start:end])


class BatterySchedule(unittest.TestCase):
    def test_every_named_carrier_exists(self) -> None:
        """A step that names ``scripts/x.py`` or ``tests/x.py`` names a real file.

        The file-existence half of this ratchet's own law. ``test_ci_runs_the_makefile_battery``
        binds *how* the battery is invoked; nothing bound *what* the other steps
        invoke, so a step left behind by a rename would keep reading as an
        enrolled leg to whoever scanned the workflow, and `|| true`-tolerant steps
        would not even go red. Measured at f277dce649850b0cfedf0e48f2ba2520d7010b0b:
        all five paths named in the python job are in the tree, one of them the
        WorldSense CLI leg added on this lane.
        """
        job = ci_job_text("python")
        named = sorted(set(re.findall(r"\b(?:scripts|tests)/[A-Za-z0-9_./-]+\.py", job)))
        self.assertTrue(named, "the python job names no repository script at all")
        missing = [rel for rel in named if not (REPO / rel).is_file()]
        self.assertEqual(missing, [], f"CI python job invokes files that are not in the tree: {missing}")

    def test_ci_runs_the_makefile_battery(self) -> None:
        """CI calls ``make test`` and owns no discovery root of its own."""
        job = ci_python_job()
        self.assertRegex(
            job, r"(?m)^\s+make test\b", "CI python job no longer runs the Makefile battery"
        )
        inline = re.findall(r"unittest\s+discover\s+-s\s+(\S+)", job)
        self.assertEqual(
            inline,
            [],
            f"CI spells its own discovery root(s) {inline}; the Makefile is the one battery",
        )

    def test_every_unittest_test_file_is_scheduled(self) -> None:
        """No stdlib-unittest test lives outside ``TEST_ROOTS``."""
        roots = makefile_test_roots()
        unscheduled: list[str] = []
        for path in repo_test_files():
            rel = path.relative_to(REPO).as_posix()
            if rel in NON_UNITTEST_TESTS:
                continue
            if not is_unittest_file(path):
                continue
            if rel.split("/", 1)[0] not in roots:
                unscheduled.append(rel)
        self.assertEqual(
            unscheduled,
            [],
            "test files CI can run but no scheduled root discovers; add the root to "
            f"Makefile TEST_ROOTS (currently {roots}): {unscheduled}",
        )

    def test_scheduled_roots_collect_tests(self) -> None:
        """Each root yields at least one test, in-process, so a renamed root is not silent."""
        for root in makefile_test_roots():
            with self.subTest(root=root):
                loader = unittest.TestLoader()
                sys.path.insert(0, str(REPO / root))
                try:
                    suite = loader.discover(
                        start_dir=str(REPO / root), pattern=_TEST_GLOB, top_level_dir=str(REPO / root)
                    )
                finally:
                    sys.path.pop(0)
                collected = [
                    name for name in _suite_ids(suite) if "Failed to import" not in name
                ]
                self.assertTrue(collected, f"discover -s {root} collected nothing")
                self.assertGreaterEqual(
                    suite.countTestCases(), 1, f"discover -s {root} ran zero tests"
                )

    def test_the_cited_readme_scope_gate_is_in_the_battery(self) -> None:
        """README.md's own cited gate is collected by a scheduled root."""
        gate = REPO / "scripts" / "test_readme_scope_truth.py"
        self.assertTrue(gate.is_file(), "README.md cites a gate that is not in the tree")
        self.assertIn("scripts", makefile_test_roots(), "README's scope gate root unscheduled")
        spec = _importlib_util.spec_from_file_location("test_readme_scope_truth", gate)
        assert spec and spec.loader
        # ``spec.loader`` is typed as the base ``Loader``, which has no
        # ``exec_module``; the mixin that does is ``importlib.abc.ExecutionLoader``
        # (NOT ``importlib.machinery``, which is the other half of the usual
        # confusion). A spec built from a file location always carries a
        # SourceFileLoader, so this narrowing states a fact about the spec rather
        # than hoping for one — and without it the call below is an
        # attribute-access error under strict Pyright, which is how a green
        # untyped run hides a broken loader.
        loader = cast(importlib.abc.ExecutionLoader, spec.loader)
        module = _importlib_util.module_from_spec(spec)
        sys.path.insert(0, str(gate.parent))
        try:
            loader.exec_module(module)
            suite = unittest.TestLoader().loadTestsFromModule(module)
        finally:
            sys.path.pop(0)
        names = _suite_ids(suite)
        self.assertGreaterEqual(len(names), 1, "README scope gate collects zero tests")
        for name in names:
            self.assertTrue(name.startswith("test_readme_scope_truth."), name)

    def test_non_unittest_exclusions_are_real_and_used(self) -> None:
        """Each exclusion needs the other runner and names an existing command target."""
        for rel, command in NON_UNITTEST_TESTS.items():
            with self.subTest(rel=rel):
                path = REPO / rel
                self.assertTrue(path.is_file(), f"stale exclusion {rel}: file is gone")
                text = path.read_text(encoding="utf-8", errors="replace")
                self.assertRegex(
                    text, r"(?m)^\s*(?:import pytest|from pytest\b)", f"{rel} is not a pytest file"
                )
                for token in re.findall(r"(\S+\.(?:py|js|ts))", command):
                    if not token.startswith("solver/"):
                        continue
                    self.assertTrue((REPO / token).is_file(), f"{rel}: exclusion names missing {token}")
                root = rel.split("/", 1)[0]
                self.assertNotIn(root, makefile_test_roots(), f"{rel} root is already scheduled")

    def test_ci_selected_count_leg_sums_the_roots(self) -> None:
        """Run the gate that is IN ci.yml against a synthetic two-root log.

        The old leg read ``awk '{print $2}'``, which over two ``Ran N tests``
        lines yields ``58 8``; ``test "58 8" -ge 1`` is then a bash arithmetic
        error rather than a pass, so wiring the second root through the old gate
        would have red the job. This executes the workflow's own lines.
        """
        job = ci_python_job()
        lines = job.splitlines()
        try:
            start = next(i for i, ln in enumerate(lines) if ln.strip().startswith("n=$(grep -oE"))
            end = next(
                i for i, ln in enumerate(lines) if ln.strip() == 'test "${n:-0}" -ge 1'
            )
        except StopIteration:
            self.fail("ci.yml has no OR23-Q8 selected-count leg to bind")
        self.assertGreater(end, start, "the OR23-Q8 leg is out of order")
        leg = textwrap.dedent("\n".join(lines[start : end + 1]) + "\n")
        self.assertNotIn(
            "awk '{print $2}'", leg, "the count leg still reads the last line only"
        )
        with tempfile.TemporaryDirectory() as tmp:
            pathlib.Path(tmp, "or23-unittest.log").write_text(
                "Ran 58 tests in 6.412s\nOK (skipped=2)\nRan 8 tests in 0.006s\nOK\n",
                encoding="utf-8",
            )
            probe = subprocess.run(
                ["bash", "-c", "set -eo pipefail\n" + leg],
                capture_output=True,
                text=True,
                env={**os.environ, "RUNNER_TEMP": tmp},
            )
        self.assertEqual(probe.returncode, 0, msg=(probe.stdout + probe.stderr).strip())
        self.assertIn("OR23-Q8 selected: 66 tests", probe.stdout)



def _suite_ids(suite: unittest.TestSuite) -> list[str]:
    ids: list[str] = []
    stack: list[unittest.TestSuite | unittest.TestCase] = [suite]
    while stack:
        item = stack.pop()
        if isinstance(item, unittest.TestSuite):
            for child in item:
                stack.append(child)
        else:
            ids.append(item.id())
    return ids


if __name__ == "__main__":
    unittest.main(verbosity=2)
