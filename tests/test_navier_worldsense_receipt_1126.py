"""Battery for the CI sha-key cure and the WorldSense Navier-Stokes receipt.

Two deliverables land together on this lane, so two contracts are pinned here.

``CIShaKeyConcurrencyTest``
    ``.github/workflows/ci.yml`` must key ``main`` pushes on the commit and keep
    the ref key for pull requests. The assertions are not string-pinned: the test
    reads the workflow's own ``concurrency`` expressions and drives a model of
    GitHub's group semantics, so a rewrite of the expression that preserves the
    behaviour still passes and one that reintroduces the eviction fails.

    Why the cure exists. A concurrency group holds one running run plus one
    queued run; a third arrival into a full group cancels the OLDEST QUEUED run,
    and that eviction is NOT governed by ``cancel-in-progress: false``. Under the
    old ref key every ``main`` push shared one group, so a burst of fleet pushes
    buried verdicts before their builds started -- measured at
    5c847fb035efb5f4504018ec32029e8bf155efef, where two consecutive main Verify
    runs recorded ``conclusion=cancelled`` with nothing wrong in either tree.

``ReceiptInvariantsTest`` and its companions
    The physics the receipt exists to report: ``dE/dt = -2 nu Z <= 0``, a
    divergence-free field, an energy-neutral convective transfer, a finite
    Beale-Kato-Majda integral over ``[0, T]``, a replayable digest, and a hint
    that names where refinement would pay. Every one of these is a numerical
    observation on a truncated Fourier-Galerkin system. None of them is a
    statement about continuum regularity, and ``EpistemicInflationRefusalTest``
    is the gate that keeps the two apart.

``WorldSenseConsumerContractTest``
    This repository's mirror of Kagami's landed ``_DOMAIN_MARKERS``,
    ``_TIER_FIELDS``, ``_NESTED_GRADE_BLOCKS``, ``_DIGEST_FIELDS`` and schema
    text, re-pinned against ``origin/main`` read with ``git show`` — never
    against a sibling lane seat's working tree, which is how the mirror went
    quietly wrong while still printing OK.

``CiWorldSenseEnrollmentTest``
    The producer's CLI surface — ``--self-test``, the ``--out`` ->
    ``--check-file`` roundtrip, and two runs agreeing on ``receipt_sha256`` — is
    a lake-free step in ``ci.yml``'s python job, and its literal shell text is
    executed here, then executed once with a sabotaged flag, so enrollment
    cannot decay into a carrier that prints success regardless of what the
    script did.

Runs on the 3.9 interpreter with no third-party dependency beyond numpy; the
optional PyYAML leg skips when PyYAML is absent, exactly as the solver tests
skip when the reality checkout is absent.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.abc
import importlib.util
import inspect
import json
import math
import os
import re
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple, Union, cast

REPO = Path(__file__).resolve().parents[1]
SCRIPTS = REPO / "scripts"
WORKFLOW = REPO / ".github" / "workflows" / "ci.yml"

#: Absolute path of the module under test. Loading it by file location rather than by
#: name is what lets a strict type checker see the module at all: `scripts/` is not on
#: pyright's search path from `tests/`, so a bare ``import navier_worldsense_receipt``
#: resolves to ``reportMissingImports`` and every member access below degrades to
#: Unknown, which is the failure mode a green local run hides.
_SCRIPT_PATH = SCRIPTS / "navier_worldsense_receipt.py"

if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

try:
    _SPEC = importlib.util.spec_from_file_location("navier_worldsense_receipt", _SCRIPT_PATH)
    if _SPEC is None or _SPEC.loader is None:
        raise ImportError(f"no import spec for {_SCRIPT_PATH}")
    _MODULE = importlib.util.module_from_spec(_SPEC)
    # Register before executing. The receipt module opens with
    # ``from __future__ import annotations`` and declares dataclasses, and on 3.9
    # ``dataclasses._is_type`` resolves a string annotation through
    # ``sys.modules.get(cls.__module__).__dict__``; under an unregistered spec-loaded
    # module that lookup is None and the class statement raises AttributeError inside
    # the dataclass decorator. Measured on /usr/bin/python3 (3.9.6) at exactly
    # ``class Grid`` -- the first dataclass in the file.
    sys.modules["navier_worldsense_receipt"] = _MODULE
    # ``spec.loader`` is typed as the base Loader, which has no exec_module; the
    # subclass that does is ExecutionLoader, and a spec built from a file location
    # always carries a SourceFileLoader, so the narrowing is a fact about the spec,
    # not a hope.
    loader = cast(importlib.abc.ExecutionLoader, _SPEC.loader)
    loader.exec_module(_MODULE)
    # Typed Any: file-loaded modules have no stub, so every attribute would otherwise
    # be Unknown under strict. The leg that matters for correctness is not the
    # attribute types but the assertions on the payload, which are typed here.
    receipt = cast(Any, _MODULE)
except ImportError as exc:  # pragma: no cover - a runner with no numpy
    # ImportError ONLY, deliberately. numpy's absence arrives as ModuleNotFoundError,
    # which is an ImportError, and skipping for it is right; catching AttributeError or
    # TypeError too turns a broken loader into a skip of the whole file. Measured the
    # hard way: an importlib.abc-vs-machinery mix-up raised AttributeError at this line
    # and the file reported itself skipped rather than broken. A skip is a verdict about
    # the environment, not an escape hatch for a defect in this file — and under
    # `unittest discover` a module-level SkipTest can be counted per test, which is how
    # a red battery reads as a green one.
    raise unittest.SkipTest(f"navier_worldsense_receipt unimportable: {exc}")

#: The schedule this battery runs. N=8 and four reported steps are enough to
#: exercise every invariant and every code path while keeping the whole file
#: inside a couple of seconds -- the numbers being asserted are exact
#: identities (divergence, triad cancellation, the discrete solenoidal
#: relation), not convergence results, so they hold at machine precision at any
#: affordable resolution. The convergence legs are exercised, not tuned here.
FAST_GRIDS: Tuple[int, ...] = (8,)
FAST_VISCOSITIES: Tuple[float, ...] = (0.1, 0.2)
FAST_DT = 0.05
FAST_STEPS = 4
FAST_CONVERGENCE_GRIDS: Tuple[int, int] = (6, 8)

_CACHE: Dict[str, Dict[str, Any]] = {}


def shared_receipt(**overrides: Any) -> Dict[str, Any]:
    """Build once per key: the payload is immutable evidence, not a fixture to mutate."""
    kwargs: Dict[str, Any] = {
        "grids": FAST_GRIDS,
        "viscosities": FAST_VISCOSITIES,
        "dt": FAST_DT,
        "steps": FAST_STEPS,
        "convergence_grids": FAST_CONVERGENCE_GRIDS,
        "include_series": True,
    }
    kwargs.update(overrides)
    key = receipt.canonical_json(kwargs)
    if key not in _CACHE:
        _CACHE[key] = receipt.build_receipt(**kwargs)  # type: ignore[arg-type]
    return _CACHE[key]


def number(value: Any, name: str) -> float:
    """Read a payload field this test asserts on as the number it must be.

    Several receipts report ``None`` where a quantity is undefined (a
    Kolmogorov length with zero dissipation, a Simpson integral over too few
    samples). Comparing against ``None`` would raise ``TypeError`` and read as a
    crash rather than a verdict, so every such field goes through here: ``None``
    or a bool fails the test with the field's name in the message.
    """
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise AssertionError(f"{name} is {value!r}, expected a real number")
    return float(value)


#: A payload edit for the refusal tests: takes the receipt, mutates it in place.
Mutator = Callable[[Dict[str, Any]], None]


#: A payload path: mapping keys and sequence indices, as a walker sees them.
PathType = Tuple[Union[str, int], ...]


def set_field(path: PathType, value: object) -> Mutator:
    """Return a mutator that writes ``value`` at a dotted path.

    These are functions rather than lambdas for one reason: Python has no lambda
    parameter annotations, so `lambda p: p.__setitem__(...)` leaves `p` Unknown and
    every one of the ~30 refusal legs reports `reportUnknownLambdaType` under strict
    Pyright. A named helper annotates once and the legs stay checkable.
    """

    def mutate(payload: Dict[str, Any]) -> None:
        node: Any = payload
        for part in path[:-1]:
            node = node[part]
        node[path[-1]] = value

    return mutate


def drop_field(path: PathType) -> Mutator:
    """Return a mutator that deletes the key at a dotted path."""

    def mutate(payload: Dict[str, Any]) -> None:
        node: Any = payload
        for part in path[:-1]:
            node = node[part]
        del node[path[-1]]

    return mutate


def string_leaves(value: Any, path: str = "$") -> List[Tuple[str, Any]]:
    """Every leaf of a nested payload, with its JSON path.

    Deliberately the test's own walk, not the module's: the point of the leg that
    uses it is to cross-check the payload against a second reader. If it called the
    gate's private walker, a bug in that walker would hide behind the test.
    """
    found: List[Tuple[str, Any]] = []
    if isinstance(value, dict):
        mapping = cast(Dict[str, Any], value)
        for key, child in mapping.items():
            found.extend(string_leaves(child, f"{path}.{key}"))
    elif isinstance(value, (list, tuple)):
        # Cast before iterating: isinstance narrows Any to list[Unknown], and a
        # partially-unknown element type would silently make `child` untyped here.
        for index, child in enumerate(cast(Sequence[Any], value)):
            found.extend(string_leaves(child, f"{path}[{index}]"))
    else:
        found.append((path, value))
    return found


#: Values that are not ``False`` but read as if they were. The gate demands the
#: literal, because "0", "false" and [] have all been proposed as a way to state a
#: false claim without writing False.
TRUTHY_NOT_FALSE: Tuple[object, ...] = (1, "false", [], "TRUE", 0.0, "0")


# ---------------------------------------------------------------------------
# deliverable 1 -- the concurrency cure
# ---------------------------------------------------------------------------

#: The ternary form the cure takes: ``<event check> && <true arm> || <false arm>``,
#: captured as names so the test can evaluate what the FILE says rather than what
#: this test assumes it says.
_TERNARY_GROUP = re.compile(
    r"^[ \t]*group:[ \t]*verify-\$\{\{\s*github\.workflow\s*\}\}-\$\{\{\s*"
    r"github\.event_name[ \t]==[ \t]*'(?P<event>[a-z_]+)'"
    r"[ \t]&&[ \t]*github\.(?P<when_true>\w+)"
    r"[ \t]\|\|[ \t]*github\.(?P<when_false>\w+)\s*\}\}[ \t]*$",
    re.MULTILINE,
)
#: The shape that caused the eviction: one group per ref, for every event.
_REF_ONLY_GROUP = re.compile(
    r"^[ \t]*group:[ \t]*verify-\$\{\{\s*github\.workflow\s*\}\}-\$\{\{\s*github\.ref\s*\}\}[ \t]*$",
    re.MULTILINE,
)
_CANCEL_IN_PROGRESS = re.compile(
    r"^[ \t]*cancel-in-progress:[ \t]*\$\{\{\s*github\.event_name[ \t]==[ \t]*'(?P<event>[a-z_]+)'\s*\}\}[ \t]*$",
    re.MULTILINE,
)


class CIShaKeyConcurrencyTest(unittest.TestCase):
    """``main`` pushes own their group; PR bursts still collapse to the newest."""

    #: Declared so the static model helpers below type cleanly; setUpClass fills it.
    text: str = ""

    @classmethod
    def setUpClass(cls) -> None:
        if not WORKFLOW.is_file():
            raise unittest.SkipTest(f"no workflow at {WORKFLOW}")
        cls.text = WORKFLOW.read_text(encoding="utf-8")

    # -- the file says what the cure is ------------------------------------

    def test_group_uses_a_ternary_on_event_name(self) -> None:
        match = _TERNARY_GROUP.search(self.text)
        self.assertIsNotNone(
            match,
            "concurrency.group must key push runs on a per-commit value "
            "(CI-SHAKEY-1126 / pending-eviction-sha-group-cure-1123)",
        )
        assert match is not None  # note: the assert above IS the test's claim

    def test_push_events_are_keyed_on_the_sha(self) -> None:
        match = _TERNARY_GROUP.search(self.text)
        assert match is not None
        self.assertEqual(match.group("event"), "push")
        self.assertEqual(match.group("when_true"), "sha")
        self.assertEqual(match.group("when_false"), "ref")

    def test_ref_only_group_is_gone(self) -> None:
        self.assertIsNone(
            _REF_ONLY_GROUP.search(self.text),
            "the ref-only key is the defect: it puts every main push in one group "
            "and lets a later commit evict an earlier one's pending run",
        )

    def test_cancel_in_progress_is_pr_only(self) -> None:
        match = _CANCEL_IN_PROGRESS.search(self.text)
        assert match is not None, "cancel-in-progress must be an event expression"
        self.assertEqual(match.group("event"), "pull_request")

    def test_trigger_scope_is_main_and_prs(self) -> None:
        # Text scan first: this leg must work on a runner with no PyYAML.
        self.assertIn("branches: [main]", self.text)
        self.assertIn("name: Verify", self.text)

    def test_cure_is_documented_where_it_lives(self) -> None:
        """A fix without its mechanism nearby is a fix that gets reverted."""
        block = self.text[self.text.index("concurrency:") :]
        block = block[: block.index("jobs:")]
        for token in ("CI-SHAKEY-1126", "OLDEST", "pending-eviction-sha-group-cure-1123"):
            self.assertIn(token, block, f"the concurrency comment no longer names {token!r}")
        self.assertIn(
            "5c847fb035efb5f4504018ec32029e8bf155efef",
            block,
            "the comment no longer cites the measured cancelled pair",
        )

    # -- and the file does what the cure claims ----------------------------

    @staticmethod
    def _group_key(
        event_name: str, sha: str, ref: str, workflow: str = "Verify"
    ) -> str:
        """Evaluate the workflow's own group expression for one arrival.

        Only the expression the file contains is honoured: if the ternary is
        missing this raises, so the model cannot quietly fall back to a key the
        repository does not use.
        """
        match = _TERNARY_GROUP.search(CIShaKeyConcurrencyTest.text)
        if match is None:
            raise AssertionError("workflow has no event-ternary group expression to evaluate")
        arms = {"sha": sha, "ref": ref, "workflow": workflow}
        chosen = (
            match.group("when_true")
            if event_name == match.group("event")
            else match.group("when_false")
        )
        return f"verify-{workflow}-{arms[chosen]}"

    @staticmethod
    def _cancel_in_progress(event_name: str) -> bool:
        match = _CANCEL_IN_PROGRESS.search(CIShaKeyConcurrencyTest.text)
        assert match is not None
        return event_name == match.group("event")

    @staticmethod
    def _evictions(
        arrivals: List[Dict[str, str]], ref_key_for_all_events: bool = False
    ) -> List[str]:
        """Run arrivals through GitHub's group model; return the cancelled ids.

        The model is the documented concurrency behaviour, reduced to what the
        measured failure needs: one group holds one running plus one queued run;
        ``cancel-in-progress: true`` replaces the running run; with it false a new
        arrival queues, and a second arrival into an already-full group cancels
        the queued one. No arrival completes -- the builds run tens of minutes and
        the pushes arrived within minutes of each other, which is the regime that
        produced the cancelled pair.
        """
        running: Dict[str, Optional[str]] = {}
        pending: Dict[str, Optional[str]] = {}
        cancelled: List[str] = []
        for arrival in arrivals:
            if ref_key_for_all_events:
                key = f"verify-Verify-{arrival['ref']}"
            else:
                key = CIShaKeyConcurrencyTest._group_key(
                    arrival["event"], arrival["sha"], arrival["ref"]
                )
            if key not in running:
                running[key] = arrival["id"]
                pending[key] = None
                continue
            if CIShaKeyConcurrencyTest._cancel_in_progress(arrival["event"]):
                if running[key] is not None:
                    cancelled.append(str(running[key]))
                elif pending[key] is not None:
                    cancelled.append(str(pending[key]))
                running[key] = arrival["id"]
                continue
            if pending[key] is not None:
                cancelled.append(str(pending[key]))
            pending[key] = arrival["id"]
        return cancelled

    def test_main_push_burst_evicts_nothing(self) -> None:
        arrivals = [
            {"id": f"run{i}", "event": "push", "sha": f"{i:040x}", "ref": "refs/heads/main"}
            for i in range(1, 5)
        ]
        self.assertEqual(self._evictions(arrivals), [])

    def test_the_old_ref_key_did_evict(self) -> None:
        """The counterfactual: same arrivals, ref key, verdicts disappear.

        Without this leg the test above only proves the model is quiet; this one
        proves the model can see the defect at all. Four pushes to main leave two
        of them cancelled -- the shape measured at 5c847fb, where two consecutive
        runs recorded conclusion=cancelled.
        """
        arrivals = [
            {"id": f"run{i}", "event": "push", "sha": f"{i:040x}", "ref": "refs/heads/main"}
            for i in range(1, 5)
        ]
        self.assertEqual(self._evictions(arrivals, ref_key_for_all_events=True), ["run2", "run3"])

    def test_pr_burst_still_collapses_to_the_newest(self) -> None:
        """The behaviour that made this topology survivable must not be lost."""
        arrivals = [
            {"id": f"pr{i}", "event": "pull_request", "sha": f"{i:040x}", "ref": "refs/pull/7/head"}
            for i in range(1, 4)
        ]
        cancelled = self._evictions(arrivals)
        self.assertEqual(cancelled, ["pr1", "pr2"])
        self.assertNotIn("pr3", cancelled)

    def test_dispatch_does_not_share_a_key_with_pushes(self) -> None:
        push = self._group_key("push", "a" * 40, "refs/heads/main")
        dispatch = self._group_key("workflow_dispatch", "a" * 40, "refs/heads/main")
        self.assertNotEqual(push, dispatch)
        self.assertEqual(push, f"verify-Verify-{'a' * 40}")

    def test_yaml_structure_if_parseable(self) -> None:
        try:
            import yaml  # type: ignore[import-not-found]
        except ImportError:
            self.skipTest("PyYAML not installed; text legs above already ran")
            return
        if not hasattr(yaml, "safe_load"):
            # Measured on the 3.9 interpreter here: `import yaml` succeeds against
            # a namespace package with no attributes at all, so an import guard is
            # not an availability guard. Ask the module for the function instead.
            self.skipTest("`yaml` resolves to a namespace package, not PyYAML")
            return
        raw = yaml.safe_load(self.text)
        self.assertIsInstance(raw, dict)
        # Typed with an `Any` key, not `str`: YAML 1.1 loaders hand back the
        # boolean True for the `on:` key, and a `dict[str, Any]` annotation would
        # be a lie about the object the parser actually produced.
        doc = cast(Dict[Any, Any], raw)
        group = str(doc["concurrency"]["group"])
        self.assertIn("github.sha", group)
        self.assertIn("github.ref", group)
        self.assertIn("github.event_name", str(doc["concurrency"]["cancel-in-progress"]))
        self.assertEqual(sorted(doc["jobs"]), ["cargo", "lean", "python"])
        # `on:` is the boolean True under YAML 1.1 and the string "on" under a
        # 1.2-strict loader; the leg has to work under whichever one is installed.
        triggers = cast(Dict[Any, Any], doc[True] if True in doc else doc.get("on"))
        self.assertIsInstance(triggers, dict)
        push = cast(Dict[Any, Any], triggers["push"])
        self.assertEqual(push["branches"], ["main"])
        self.assertEqual(triggers["pull_request"]["branches"], ["main"])
        # The trigger scope the cure assumes: push is confined to main, so a
        # sha-keyed group cannot fan out across every branch a lane pushes to.
        self.assertIn("paths-ignore", push)


# ---------------------------------------------------------------------------
# deliverable 2 -- the receipt
# ---------------------------------------------------------------------------


class ReceiptInvariantsTest(unittest.TestCase):
    """What the run measured, and the identities that make the measurement honest."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = shared_receipt()
        cls.runs = cls.payload["runs"]

    def test_schedule_is_what_was_asked_for(self) -> None:
        config = self.payload["configuration"]
        self.assertEqual(config["grids"], list(FAST_GRIDS))
        self.assertEqual(config["viscosities"], list(FAST_VISCOSITIES))
        self.assertEqual(config["dt"], FAST_DT)
        self.assertEqual(config["steps"], FAST_STEPS)
        self.assertEqual(len(self.runs), len(FAST_GRIDS) * len(FAST_VISCOSITIES))
        for run in self.runs:
            self.assertEqual(run["substeps_per_report"], 2)
            self.assertEqual(run["t_final"], FAST_DT * FAST_STEPS)

    def test_energy_dissipates_and_never_rises(self) -> None:
        """The second-law leg: E decreases, and no substep increases it."""
        leray = self.payload["invariants"]["leray_energy_dissipation"]
        self.assertTrue(leray["energy_decayed"])
        self.assertLess(leray["energy_final_mean"], leray["energy_initial_mean"])
        self.assertEqual(leray["max_stepwise_energy_increase"], 0.0)
        for run in self.runs:
            self.assertEqual(run["max_energy_increase"], 0.0)
            self.assertLess(run["energy_ratio"], 1.0)
            self.assertGreater(run["energy_ratio"], 0.0)

    def test_energy_balance_matches_minus_two_nu_z(self) -> None:
        """dE/dt = -2 nu Z, checked two ways: per step and cumulative.

        The stepwise residual carries the integrator's truncation error (fourth
        order on advection, exact on Stokes), so it is bounded loosely and its
        smallness is reported rather than asserted away. The cumulative form
        telescopes the same identity over the whole interval and lands near
        machine precision, because the quadrature error does not accumulate a
        secular term.
        """
        leray = self.payload["invariants"]["leray_energy_dissipation"]
        self.assertLess(leray["stepwise_residual_max"], 1e-3)
        self.assertLess(leray["cumulative_residual_relative_max"], 1e-6)
        for run in self.runs:
            self.assertLess(
                number(
                    run["energy_balance_cumulative_residual_relative"],
                    "energy_balance_cumulative_residual_relative",
                ),
                1e-6,
            )

    def test_field_is_divergence_free(self) -> None:
        solenoidal = self.payload["invariants"]["solenoidal_constraint"]
        self.assertTrue(solenoidal["holds"])
        self.assertLess(
            solenoidal["max_abs_divergence_linf"], receipt.DIV_TOLERANCE
        )
        self.assertGreater(solenoidal["tolerance"], 0.0)
        for run in self.runs:
            assert run["divergence_linf_max"] is not None
            self.assertLess(run["divergence_linf_max"], receipt.DIV_TOLERANCE)

    def test_triad_cancellation_is_machine_precision(self) -> None:
        """<u, P_L((u.grad)u)> = 0, absolutely and pointwise.

        Two readings, deliberately: the weak form (the inner product) and the
        pointwise scalar triple product u . (omega x u), which vanishes because u
        appears twice. The second is what makes the first independent of the
        dealiasing choice.
        """
        triad = self.payload["invariants"]["triad_cancellation"]
        self.assertTrue(triad["holds"])
        self.assertLess(triad["abs_max"], receipt.CONVECTIVE_TOLERANCE)
        self.assertLess(
            triad["pointwise_triple_product_max"], receipt.CONVECTIVE_TOLERANCE
        )
        self.assertEqual(triad["gated_on"], "abs_max")

    def test_enstrophy_is_positive_and_finite(self) -> None:
        for run in self.runs:
            self.assertGreater(run["enstrophy_initial"], 0.0)
            self.assertGreaterEqual(run["enstrophy_peak"], run["enstrophy_final"])
            self.assertGreaterEqual(run["enstrophy_peak"], run["enstrophy_initial"])
            integral = number(run["integral_enstrophy_simpson"], "integral_enstrophy_simpson")
            self.assertTrue(math.isfinite(integral))
            self.assertGreater(integral, 0.0)

    def test_discrete_solenoidal_relation(self) -> None:
        """mean|grad u|^2 = 2Z exactly for a periodic divergence-free Galerkin field."""
        budget = self.payload["invariants"]["enstrophy_budget"]
        self.assertLess(budget["mean_grad_u_sq_minus_2z_max"], receipt.DIV_TOLERANCE)
        for run in self.runs:
            self.assertLess(run["mean_grad_u_sq_minus_2z_max"], receipt.DIV_TOLERANCE)

    def test_bkm_integral_is_finite_and_positive(self) -> None:
        bkm = self.payload["invariants"]["beale_kato_majda"]
        self.assertTrue(bkm["all_positive_finite"])
        high = number(bkm["integral_max"], "integral_max")
        low = number(bkm["integral_min"], "integral_min")
        self.assertTrue(math.isfinite(high))
        self.assertGreater(low, 0.0)
        self.assertLessEqual(low, high)
        # The payload states its own limit in words, beside the number a reader
        # might otherwise over-read: this is a resolution statement, not a
        # regularity statement.
        self.assertIn("says nothing about continuum regularity", bkm["scope_note"])
        self.assertIn("resolution", bkm["scope_note"])
        self.assertIn("resolution", bkm["scope_note"])
        self.assertIn("says nothing about continuum regularity", bkm["scope_note"])

    def test_simpson_and_trapezoid_agree_on_bkm(self) -> None:
        """Two quadratures of one smooth sampled curve: their gap is the error bar.

        Measured at this schedule: 2.0e-6 relative at nu=0.1 and 1.7e-5 at
        nu=0.2, the larger one carrying the bound. Simpson is exact for a
        quadratic through three points and the trapezoid is not, so a gap this
        small says the sampled ||omega||_inf curve is smooth on the reporting
        grid -- it says nothing about whether a finer grid would find a spike
        between the samples, which is the whole reason the receipt reports the
        pair instead of one number.
        """
        for run in self.runs:
            simpson = number(run["bkm_integral_simpson"], "bkm_integral_simpson")
            trapezoid = number(run["bkm_integral_trapezoid"], "bkm_integral_trapezoid")
            self.assertGreater(simpson, 0.0)
            self.assertLess(abs(simpson - trapezoid) / simpson, 1e-3)

    def test_vorticity_and_production_peaks_are_inside_the_interval(self) -> None:
        """A peak time outside [0, T] would mean the argmax and the axis disagree."""
        for run in self.runs:
            t_final = number(run["t_final"], "t_final")
            vorticity_peak = number(run["vorticity_linf_peak_t"], "vorticity_linf_peak_t")
            production_peak = number(
                run["enstrophy_production_peak_t"], "enstrophy_production_peak_t"
            )
            enstrophy_peak = number(run["enstrophy_peak_t"], "enstrophy_peak_t")
            for name, value in (
                ("vorticity_linf_peak_t", vorticity_peak),
                ("enstrophy_production_peak_t", production_peak),
                ("enstrophy_peak_t", enstrophy_peak),
            ):
                self.assertGreaterEqual(value, 0.0, name)
                self.assertLessEqual(value, t_final + 1e-12, name)
            # The peak value itself must be the largest sampled one, or the hint
            # is naming an event the data does not contain.
            self.assertGreaterEqual(
                run["vorticity_linf_peak"],
                max(run["vorticity_linf_initial"], run["vorticity_linf_final"]),
            )

    def test_resolution_is_reported_as_a_number_not_a_claim(self) -> None:
        """k_max*eta < 1 is the honest "underresolved" flag; None means undecidable."""
        for run in self.runs:
            self.assertGreater(run["grid_spacing"], 0.0)
            if run["kolmogorov_length"] is None:
                self.assertIsNone(run["resolution_ratio"])
                self.assertIsNone(run["underresolved"])
                continue
            eta = number(run["kolmogorov_length"], "kolmogorov_length")
            ratio = number(run["resolution_ratio"], "resolution_ratio")
            self.assertGreater(eta, 0.0)
            self.assertGreater(ratio, 0.0)
            self.assertIsInstance(run["underresolved"], bool)
            # The flag is the ratio, not a prose judgement: they cannot disagree.
            self.assertEqual(run["underresolved"], ratio < 1.0)

    def test_time_series_axes_line_up(self) -> None:
        series = self.runs[0]["time_series"]
        reports = FAST_STEPS + 1  # sampled every second half step, including t=0
        self.assertEqual(len(series["t_report"]), reports)
        self.assertEqual(len(series["divergence_linf"]), reports)
        self.assertEqual(len(series["mean_grad_u_sq"]), reports)
        self.assertEqual(len(series["convective_skew_abs"]), reports)
        self.assertEqual(len(series["energy"]), 2 * FAST_STEPS + 1)
        self.assertEqual(len(series["t"]), 2 * FAST_STEPS + 1)
        self.assertEqual(series["t_report"][0], 0.0)
        self.assertAlmostEqual(series["t_report"][-1], FAST_DT * FAST_STEPS, places=12)

    def test_refinement_legs_are_present_and_scoped(self) -> None:
        refinement = self.payload["refinement"]
        temporal = refinement["temporal"]
        self.assertEqual(temporal["dt_fine"], FAST_DT / 2.0)
        self.assertGreaterEqual(temporal["abs_difference"], 0.0)
        self.assertIn("not an order proof", temporal["note"])
        spatial = refinement["spatial"]
        self.assertEqual(spatial["grids"], list(FAST_CONVERGENCE_GRIDS))
        self.assertEqual(len(spatial["energy_final"]), 2)
        self.assertIn("error bar", spatial["note"])

    def test_reactor_hint_names_a_window_the_data_supports(self) -> None:
        hint = self.payload["reactor_optimization_hint"]
        self.assertEqual(hint["kind"], "adaptive_refinement")
        self.assertEqual(hint["driver"], "enstrophy_stretching")
        self.assertIn(hint["nu_star"], list(FAST_VISCOSITIES))
        self.assertIn(hint["grid_star"], list(FAST_GRIDS))
        window = hint["window"]
        self.assertEqual(len(window), 2)
        low = number(window[0], "window[0]")
        high = number(window[1], "window[1]")
        self.assertLessEqual(low, high)
        t_star = number(hint["t_star"], "reactor_optimization_hint.t_star")
        self.assertLessEqual(low, t_star)
        self.assertGreaterEqual(high, t_star)
        self.assertGreater(
            number(hint["peak_enstrophy_production"], "peak_enstrophy_production"), 0.0
        )
        self.assertGreater(number(hint["peak_vorticity_linf"], "peak_vorticity_linf"), 0.0)
        # The window is one reported step wide on each side of the peak, and it is
        # clipped at t=0 -- the hint names a boundary of the measured interval when
        # the peak sits at the end, and says so rather than inventing an interior.
        self.assertAlmostEqual(high - low, 2.0 * FAST_DT, places=9)
        self.assertGreaterEqual(low, 0.0)
        self.assertEqual(hint["peak_at_window_edge"], t_star >= FAST_DT * FAST_STEPS - FAST_DT)
        # Refinement buys fidelity, never tier. The hint says so in the payload,
        # so a consumer that reads the hint cannot inherit the wrong lesson.
        self.assertIn("never raises its tier", hint["epistemic_note"])

    def test_meter_counts_the_work(self) -> None:
        meter = self.payload["z8_meter"]
        n_runs = len(FAST_GRIDS) * len(FAST_VISCOSITIES)
        self.assertEqual(meter["runs"], n_runs + 4)  # + temporal(2) + spatial(2)
        self.assertEqual(meter["solver_steps"], 2 * FAST_STEPS * (n_runs + 5))
        self.assertEqual(meter["grid_points_per_run"], [8 ** 3] * n_runs)
        self.assertTrue(meter["deterministic"])
        self.assertGreater(meter["wall_ms"], 0.0)

    def test_receipt_declares_its_epistemic_status_in_both_places(self) -> None:
        payload = self.payload
        probably = payload["probably"]
        self.assertEqual(payload["tier"], receipt.TIER_PROBABLY)
        self.assertEqual(payload["layer"], receipt.LAYER_PROBABLY)
        self.assertEqual(payload["epistemic_tier"], receipt.EPISTEMIC_TIER)
        self.assertIs(probably["deductive_proof"], False)
        self.assertIs(probably["clay_3d_global_regularity_claimed"], False)
        self.assertEqual(probably["schema"], receipt.PROBABLY_SCHEMA)
        self.assertTrue(
            any("Clay" in line for line in probably["what_this_does_not_establish"]),
            "the negation block must name the Clay problem it does not settle",
        )


#: A repr() of a float: sign, digits, mandatory fraction or exponent.
_NUMERIC_RE = re.compile(r"^-?\d+(?:\.\d+)?(?:e[-+]?\d+)?$")


class DeterminismTest(unittest.TestCase):
    """The digest is a claim about reproducibility, so it is tested as one."""

    def test_replay_reproduces_the_digest(self) -> None:
        first = receipt.build_receipt(
            grids=FAST_GRIDS,
            viscosities=FAST_VISCOSITIES,
            dt=FAST_DT,
            steps=FAST_STEPS,
            convergence_grids=FAST_CONVERGENCE_GRIDS,
        )
        second = receipt.build_receipt(
            grids=FAST_GRIDS,
            viscosities=FAST_VISCOSITIES,
            dt=FAST_DT,
            steps=FAST_STEPS,
            convergence_grids=FAST_CONVERGENCE_GRIDS,
        )
        self.assertEqual(
            first["z8_meter"]["digest_sha256"], second["z8_meter"]["digest_sha256"]
        )

    def test_digest_is_self_consistent_and_recomputable(self) -> None:
        payload = shared_receipt()
        self.assertEqual(
            receipt.payload_sha256(payload), payload["z8_meter"]["digest_sha256"]
        )
        self.assertRegex(payload["z8_meter"]["digest_sha256"], r"^[0-9a-f]{64}$")

    def test_volatile_fields_are_outside_the_digest(self) -> None:
        """A different host, clock or wall time must not change the measurement."""
        payload = shared_receipt()
        mutated = copy.deepcopy(payload)
        mutated["generated_utc"] = "1970-01-01T00:00:00Z"
        mutated["provenance"] = {"host": "somewhere else", "python": "0.0"}
        mutated["z8_meter"]["wall_ms"] = -1.0
        self.assertEqual(receipt.payload_sha256(mutated), payload["z8_meter"]["digest_sha256"])
        self.assertNotEqual(
            receipt.canonical_json(mutated), receipt.canonical_json(payload)
        )

    def test_measurement_fields_are_inside_the_digest(self) -> None:
        payload = shared_receipt()
        mutated = copy.deepcopy(payload)
        mutated["runs"][0]["energy_final"] += 1e-9
        self.assertNotEqual(
            receipt.payload_sha256(mutated), payload["z8_meter"]["digest_sha256"]
        )

    def test_declared_volatile_fields_exist_and_are_dropped(self) -> None:
        """The receipt's own list of what varies must name fields it emits.

        A `nondeterministic_fields` entry pointing at a key the payload never
        carries is self-description that has drifted from the digest rule, and a
        varying key missing from the list understates what a replay cannot
        reproduce. Both directions are checked here.
        """
        payload = shared_receipt()
        for dotted in payload["z8_meter"]["nondeterministic_fields"]:
            node: Any = payload
            for part in dotted.split("."):
                self.assertIn(part, node, f"{dotted!r} is not a field of this payload")
                node = node[part]
        # And the excluded paths really are excluded from the digest.
        for key in ("generated_utc", "provenance"):
            mutated = copy.deepcopy(payload)
            mutated[key] = "sentinel" if key == "generated_utc" else {"sentinel": 1}
            self.assertEqual(
                receipt.payload_sha256(mutated), payload["z8_meter"]["digest_sha256"]
            )
        mutated = copy.deepcopy(payload)
        mutated["z8_meter"]["wall_ms"] = -1.0
        self.assertEqual(
            receipt.payload_sha256(mutated), payload["z8_meter"]["digest_sha256"]
        )

    def test_canonical_json_is_stable_ascii_and_key_sorted(self) -> None:
        payload = shared_receipt()
        text = receipt.canonical_json(payload)
        self.assertEqual(receipt.canonical_json(json.loads(text)), text)
        text.encode("ascii")  # raises if any byte is non-ASCII
        # Compact separators, proven on a probe rather than on the payload: prose
        # fields legitimately contain ", " inside their own strings, so scanning
        # the whole document for it would test the physics notes, not the encoder.
        self.assertEqual(receipt.canonical_json({"b": 1, "a": [1.5, 2]}), '{"a":[1.5,2],"b":1}')

    def test_floats_enter_the_digest_as_exact_reprs(self) -> None:
        """The stable view renders every float through ``repr``, and repr round-trips.

        This is why the digest is host-independent: ``str()`` or a ``%g`` field
        width would let formatting decide whether two identical runs share a
        digest, and ``repr()`` of a float64 is the shortest string that reads back
        as the same double on every platform. The assertion is that the view
        contains NO float leaves -- each one became its repr -- and that those
        strings read back exactly.
        """
        payload = shared_receipt()
        view = receipt.stable_view(payload)

        original: List[Any] = []
        rendered: List[Any] = []
        for _path, leaf in string_leaves(payload):
            original.append(leaf)
        for _path, leaf in string_leaves(view):
            rendered.append(leaf)
        self.assertTrue(any(isinstance(leaf, float) for leaf in original))
        self.assertFalse([leaf for leaf in rendered if isinstance(leaf, float)])
        numeric = [leaf for leaf in rendered if isinstance(leaf, str) and _NUMERIC_RE.match(leaf)]
        self.assertTrue(numeric, "the stable view rendered no numbers at all")
        for text in numeric:
            self.assertEqual(repr(float(text)), text)


class BeltramiAnalyticTest(unittest.TestCase):
    """One configuration where the answer is known before the run."""

    def test_abc_decays_as_exp_minus_two_nu_t(self) -> None:
        engine = receipt.resolve_engine("auto")
        run = receipt.run_once(engine, FAST_GRIDS[0], 0.1, FAST_DT, FAST_STEPS, "abc")
        expected = math.exp(-2.0 * 0.1 * FAST_DT * FAST_STEPS)
        self.assertAlmostEqual(
            number(run["energy_exact_ratio_beltrami"], "energy_exact_ratio_beltrami"),
            expected,
            places=15,
        )
        # Measured 5.6e-16: the integrating factor is exact for a single
        # wavenumber shell, so this is the analytic answer, not an approximation
        # of it. The leg exists to catch a projector or a Laplacian sign error.
        self.assertLess(
            number(run["energy_exact_error_beltrami"], "energy_exact_error_beltrami"), 1e-12
        )
        self.assertAlmostEqual(number(run["energy_ratio"], "energy_ratio"), expected, delta=1e-12)

    def test_abc_absolute_cancellation_holds_even_as_the_relative_one_degrades(self) -> None:
        """The conditioning note, tested rather than asserted in prose.

        On Beltrami data ||P_L((u.grad)u)|| goes to zero, so the RELATIVE triad
        residual is O(1e-2) while the ABSOLUTE one stays O(1e-18). A gate that
        watched the relative number would refuse a correct run; this pins which
        of the two readings the receipt actually gates on.
        """
        run = receipt.run_once(
            receipt.resolve_engine("builtin"), FAST_GRIDS[0], 0.1, FAST_DT, FAST_STEPS, "abc"
        )
        skew = run["convective_skew"]
        self.assertLess(number(skew["projected_convective_max"], "projected_convective_max"), 1e-12)
        self.assertGreater(
            number(skew["projected_convective_relative_max"], "relative_max"), 1e-6
        )

    def test_abc_still_dissipates_and_reports_finite_bkm(self) -> None:
        run = receipt.run_once(
            receipt.resolve_engine("builtin"), FAST_GRIDS[0], 0.1, FAST_DT, FAST_STEPS, "abc"
        )
        self.assertGreater(number(run["bkm_integral_simpson"], "bkm_integral_simpson"), 0.0)
        self.assertLess(run["energy_final"], run["energy_initial"])
        self.assertEqual(run["max_energy_increase"], 0.0)


class EngineAgreementTest(unittest.TestCase):
    """The CI fallback and the canonical core must be the same solver.

    The brief permits a self-contained integrator for hosted runners that carry
    no reality checkout. A fallback that merely exists is an assumption; one that
    reproduces the canonical measurement makes the CI number the same number the
    dev host reports.

    What that claim IS, measured rather than asserted. Bit-identity between the
    two engines was the original pin and it is not a property of the solver: each
    engine takes its transforms through the backend it resolves --
    ``provenance.engine.transform_backend`` says which, and the core brings its own
    -- and two FFT builds round a 3-D inverse differently in the last bit. On
    2026-11-26 this leg passed on ``/usr/bin/python3`` (numpy 2.0.2 / scipy 1.13.1)
    and FAILED on ``/opt/homebrew/bin/python3.14`` (numpy 2.5.0 / scipy 1.17.1) at
    ``energy_final`` 0.11084867265661255 vs 0.11084867265661254: one unit in the
    last place, the same run, the same commit. A green that depends on which
    interpreter started it is not a contract, so the budget is stated
    (:data:`receipt.ENGINE_AGREEMENT_ATOL` and :data:`receipt.ENGINE_AGREEMENT_RTOL`,
    as ``|a-b| <= ATOL + RTOL*max(|a|,|b|)``) and bit-exactness is asserted only
    where the two engines name the SAME backend, which is the only condition under
    which a differing bit means a differing algorithm.
    """

    def _payload(self, preference: str) -> Optional[Dict[str, Any]]:
        try:
            engine = receipt.resolve_engine(preference)
        except RuntimeError:
            return None
        return receipt.build_receipt(
            grids=FAST_GRIDS,
            viscosities=(0.1,),
            dt=FAST_DT,
            steps=FAST_STEPS,
            convergence_grids=FAST_CONVERGENCE_GRIDS,
            engine=engine,
        )

    @staticmethod
    def _epsilon_multiples(gap: float) -> float:
        """How large a gap is against machine epsilon at UNIT scale.

        Not ULPs of the operands: the fields that disagree most in relative terms
        here are residuals whose true value is zero, and the ULP of 4.2e-6 is
        ~8.5e-22, so 2.9e-16 of disagreement between two engines that agree as
        closely as doubles allow prints as 344064 ULP. Measured against epsilon
        itself the same gap reads 1.3 -- one bit of rounding, which is what it is.
        """
        return gap / sys.float_info.epsilon

    def test_builtin_and_canonical_agree_within_the_stated_tolerance(self) -> None:
        canonical = self._payload("canonical")
        if canonical is None:
            self.skipTest("no reality checkout on this host: the shim cannot be imported")
            return
        builtin = self._payload("builtin")
        self.assertIsNotNone(builtin)
        assert builtin is not None and canonical is not None
        worst_scaled = 0.0
        worst_abs = 0.0
        worst_rel = 0.0
        worst_eps = 0.0
        worst_field = ""
        for mine, theirs in zip(canonical["runs"], builtin["runs"]):
            self.assertEqual(sorted(mine), sorted(theirs), "the engines report different fields")
            pairs: List[Tuple[str, Any, Any]] = [
                (key, value, theirs.get(key)) for key, value in mine.items()
            ]
            skew = mine.get("convective_skew")
            if isinstance(skew, dict):
                # Cast, not inference: narrowing an ``Any`` with ``isinstance``
                # leaves pyright with ``dict[Unknown, Unknown]``, and the loop below
                # then reports an unknown key and value for every skew field it
                # walks. These are JSON objects read back from a payload this module
                # built, so ``Dict[str, Any]`` is the fact being asserted.
                skew_fields = cast(Dict[str, Any], skew)
                other_raw: object = theirs.get("convective_skew")
                other_skew: Dict[str, Any] = (
                    cast(Dict[str, Any], other_raw) if isinstance(other_raw, dict) else {}
                )
                pairs += [
                    (f"convective_skew.{key}", value, other_skew.get(key))
                    for key, value in skew_fields.items()
                ]
            for key, value, other in pairs:
                if not isinstance(value, float) or not isinstance(other, float):
                    continue
                if not (math.isfinite(value) and math.isfinite(other)):
                    self.assertEqual(value, other, f"{key}: one engine reports a non-finite")
                    continue
                gap = abs(value - other)
                budget = receipt.ENGINE_AGREEMENT_ATOL + receipt.ENGINE_AGREEMENT_RTOL * max(
                    abs(value), abs(other)
                )
                scaled = gap / budget if budget else 0.0
                if scaled > worst_scaled:
                    worst_scaled = scaled
                    worst_field = key
                    worst_abs = gap
                    worst_rel = gap / max(abs(value), abs(other), 1e-300)
                    worst_eps = self._epsilon_multiples(gap)
                self.assertLessEqual(
                    gap,
                    budget,
                    f"engine disagreement at {key}: {value!r} vs {other!r} "
                    f"(|gap| {gap:.3e} > budget {budget:.3e})",
                )
        # Reported, not asserted: the budget is the contract, these numbers say how
        # far from it this host sits, which is what a future upgrade needs to read.
        print(
            f"[engine agreement] worst {worst_field}: |gap| {worst_abs:.3e} "
            f"= {worst_eps:.1f} machine epsilons (relative {worst_rel:.3e}), "
            f"{worst_scaled * 100:.1f}% of budget; backends "
            f"{canonical['provenance']['engine']['transform_backend']} vs "
            f"{builtin['provenance']['engine']['transform_backend']}"
        )

    def test_bitwise_agreement_is_required_only_between_the_same_backend(self) -> None:
        """Where both engines round through one library, they must print one number.

        This is the strong leg kept alive in the only condition where it means
        what it says: same backend, same bits. Different backends are allowed to
        differ by the tolerance above, and this leg says so out loud instead of
        going red on a library upgrade.
        """
        canonical = self._payload("canonical")
        if canonical is None:
            self.skipTest("no reality checkout on this host: the shim cannot be imported")
        builtin = self._payload("builtin")
        assert builtin is not None
        canonical_backend = canonical["provenance"]["engine"]["transform_backend"]
        builtin_backend = builtin["provenance"]["engine"]["transform_backend"]
        if canonical_backend != builtin_backend:
            self.skipTest(
                f"backends differ ({canonical_backend} vs {builtin_backend}): bit-exactness "
                "across two FFT libraries measures the libraries, not the solver; the "
                "tolerance leg above is the contract here"
            )
            return
        self.assertEqual(canonical["runs"], builtin["runs"])
        self.assertEqual(
            canonical["z8_meter"]["digest_sha256"], builtin["z8_meter"]["digest_sha256"]
        )

    def test_the_engines_name_the_backends_that_explain_any_gap(self) -> None:
        """A disagreement must be attributable, or the tolerance leg is unfalsifiable.

        ``transform_backend`` and the library versions are what turn "the engines
        differ by 1e-16" into "the core rounds through pyfftw and the fallback
        through scipy". Without them a ULP gap is a mystery that a future reader
        can only pin by deleting the test.
        """
        builtin = self._payload("builtin")
        assert builtin is not None
        engine = builtin["provenance"]["engine"]
        for key in ("name", "transform_backend", "numpy_version", "scipy_version"):
            self.assertIn(key, engine, f"provenance does not report {key!r}")
        self.assertIsInstance(engine["scipy_version"], (str, type(None)))

    def test_engine_names_reach_the_provenance(self) -> None:
        builtin = self._payload("builtin")
        assert builtin is not None
        name = builtin["provenance"]["engine"]["name"]
        self.assertTrue(name.startswith("builtin"), name)

    def test_canonical_preference_fails_loudly_when_absent(self) -> None:
        # On a host WITH reality this raises nothing; the assertion is that the
        # refusal, when it happens, is a RuntimeError naming the checkout.
        try:
            engine = receipt.resolve_engine("canonical")
        except RuntimeError as exc:
            self.assertIn("reality", str(exc))
            return
        self.assertEqual(engine.name, "reality_shim")


class EpistemicInflationRefusalTest(unittest.TestCase):
    """The gate refuses every upgrade a finite grid cannot support, and rewrites nothing."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = shared_receipt()

    def _refused(self, mutate: Mutator, needle: str = "") -> Dict[str, Any]:
        """Apply one inflation and require a ValueError; return the mutated copy."""
        candidate = copy.deepcopy(self.payload)
        mutate(candidate)
        with self.assertRaises(ValueError) as caught:
            receipt.validate_navier_receipt_epistemics(candidate)
        if needle:
            self.assertIn(needle, str(caught.exception))
        return candidate

    def test_the_honest_receipt_passes(self) -> None:
        verdict = receipt.validate_navier_receipt_epistemics(self.payload)
        self.assertIs(verdict["ok"], True)
        self.assertEqual(verdict["tier"], receipt.TIER_PROBABLY)

    def test_probably_is_not_a_refusal_word(self) -> None:
        """The gate polices proof claims; PROBABLY is the state this receipt is in.

        Without this leg, a gate that refused every strong-sounding word would pass
        the whole suite while making the honest tier unemittable -- and an
        unemittable PROBABLY is how producers end up writing PROVABLY quietly.
        """
        self.assertNotIn("PROBABLY", receipt.PROOF_TIER_WORDS)
        self.assertNotIn("NUMERICAL_OBSERVATION", receipt.PROOF_TIER_WORDS)
        self.assertEqual(receipt.TIER_PROBABLY, "PROBABLY")

    def test_theorem_word_anywhere_is_refused(self) -> None:
        """Not only the tier fields: a nested run string naming itself THEOREM goes too.

        The needle is the JSON path, so the refusal is also checked to be located --
        a message that says "bad word" without saying where is a message a producer
        cannot act on.
        """
        self._refused(set_field(("runs", 0, "initial_condition"), "THEOREM"), "$.runs")
        self._refused(
            set_field(("probably", "what_this_establishes", 0), "KERNEL_CLEAN"), "$.probably"
        )

    def test_lowercase_theorem_word_is_refused(self) -> None:
        """Case is for comparison only; a gate with a lowercase hole polices nothing."""
        self._refused(set_field(("status",), "theorem"), "theorem")
        self._refused(set_field(("status",), "  Theorem  "), "Theorem")

    def test_every_owner_tier_word_is_refused(self) -> None:
        """``weave.THEOREM_WORDS`` plus PROVABLY, mirrored, not imported.

        The ingest side builds its refusal vocabulary from the weave's set; a word
        the owner polices and this gate does not is a hole sized exactly to that
        word. The mirror is a mirror because the flow needs Python 3.11+ and this
        battery runs on 3.9 -- importing the owner would trade a green CI leg for an
        ImportError.
        """
        for word in ("THEOREM", "CLOSED", "PROVED", "KERNEL_CLEAN", "PROVABLY"):
            self.assertIn(word, receipt.PROOF_TIER_WORDS, f"gate no longer polices {word}")
            self._refused(set_field(("status",), word), word)

    def test_deductive_proof_true_is_refused(self) -> None:
        self._refused(set_field(("deductive_proof",), True), "deductive_proof")
        self._refused(set_field(("probably", "deductive_proof"), True), "deductive_proof")

    def test_clay_claim_is_refused(self) -> None:
        self._refused(
            set_field(("clay_3d_global_regularity_claimed",), True),
            "clay_3d_global_regularity_claimed",
        )
        self._refused(
            set_field(("probably", "clay_3d_global_regularity_claimed"), True),
            "clay_3d_global_regularity_claimed",
        )

    def test_truthy_not_false_is_still_refused(self) -> None:
        """The flag must be exactly ``False``: 1, "false", [] and 0.0 are all claims.

        A truthiness check (`if not receipt["deductive_proof"]`) accepts the string
        "false" as false and lets a lie through; identity against the literal is the
        only reading that cannot be argued past.
        """
        for value in TRUTHY_NOT_FALSE:
            self._refused(set_field(("deductive_proof",), value))

    def test_missing_flags_are_refused(self) -> None:
        """An absent claim is not a false claim."""
        self._refused(drop_field(("deductive_proof",)), "missing")
        self._refused(drop_field(("probably", "clay_3d_global_regularity_claimed")), "missing")

    def test_missing_probably_block_is_refused(self) -> None:
        self._refused(drop_field(("probably",)), "probably")

    def test_tier_and_layer_inflation_are_refused(self) -> None:
        self._refused(set_field(("layer",), "Provably"), "layer")
        self._refused(set_field(("probably", "layer"), "Provably"), "layer")
        self._refused(set_field(("epistemic_tier",), "THEOREM"), "epistemic_tier")
        self._refused(set_field(("probably", "epistemic_tier"), "PROVABLY"), "epistemic_tier")
        self._refused(set_field(("probably", "schema"), "z8.provably/1"), "schema")
        self._refused(set_field(("schema",), "worldsense.proven_receipt/1"), "schema")
        self._refused(set_field(("domain",), "navier_stokes_3d_proved"), "domain")

    def test_disagreeing_schema_fields_are_refused(self) -> None:
        """One true schema field may not vouch for a second, different one.

        The classifier concatenates schema/kind/type/operation/receipt_type/event
        before matching, so a payload with `receipt_schema` correct and `schema`
        inflated reaches the reader as a hybrid and files under whichever substring
        lands first. The original single-witness check let exactly that through --
        measured: setting schema="worldsense.proven_receipt/1" on an otherwise honest
        receipt passed it, because receipt_schema still said the true thing.
        """
        self._refused(
            set_field(("receipt_schema",), "worldsense.proven_receipt/1"), "receipt_schema"
        )
        # Values chosen so the refusal can only come from the agreement rule: none of
        # them is a bare tier word, so the standalone-word walk leaves them alone.
        self._refused(set_field(("type",), "worldsense.proven_receipt/1"), "type")
        self._refused(set_field(("receipt_type",), "worldsense.proven_receipt/1"), "receipt_type")

    def test_absent_optional_schema_fields_are_allowed(self) -> None:
        """Absence cannot misattribute: the reader's `.get(key, "")` adds nothing.

        Pairs with the leg above. Requiring all six schema-ish fields to be present
        would refuse a producer that legitimately names only one, and the classifier
        treats a missing field as empty text, not as a claim.

        The blank string is the same case as the missing key and the gate must read it
        that way -- measured: the first version of the agreement rule tested only
        `is not None`, so an honest receipt with `type=""` was refused while the same
        receipt with no `type` key passed, even though the classifier concatenates both
        to identical text. A producer that blanks optional fields would have had no
        emittable honest receipt. The boundary is pinned from both sides: blanking the
        one field that carries the true schema is still refused, because then nothing
        names the schema at all.
        """
        for field in ("type", "receipt_type", "event", "kind"):
            honest = copy.deepcopy(self.payload)
            honest[field] = ""
            self.assertIs(
                receipt.validate_navier_receipt_epistemics(honest)["ok"],
                True,
                f"blank {field} treated as a schema claim",
            )
        honest = copy.deepcopy(self.payload)
        del honest["receipt_schema"]
        self.assertIs(receipt.validate_navier_receipt_epistemics(honest)["ok"], True)
        honest = copy.deepcopy(self.payload)
        honest["type"] = ""
        honest["event"] = ""
        self.assertIs(receipt.validate_navier_receipt_epistemics(honest)["ok"], True)
        # Both schema-carrying fields blank: absence is not a claim, but zero claims is
        # also nothing for the reader to file by, so this is the refusal half.
        def blank_both_schema_fields(payload: Dict[str, Any]) -> None:
            payload["schema"] = ""
            payload["receipt_schema"] = ""

        self._refused(blank_both_schema_fields, "no 'worldsense.scientific_receipt/1'")

    def test_whitespace_schema_field_is_refused(self) -> None:
        """A space is garbage, not absence: only the exact empty string is skipped."""
        self._refused(set_field(("type",), " "), "type")

    def test_foreign_schema_in_a_concatenated_free_text_field_is_refused(self) -> None:
        """``kind``/``operation``/``event`` are free text, not a side door.

        The reader concatenates all six schema-ish fields before matching, so a second
        family name arriving through one of the three it does not pin re-attributes the
        run just as surely as an inflated ``schema``. The gate cannot demand a fixed
        value from them -- ``kind`` names the receipt, not its schema -- so it refuses
        the SHAPE: text ending in ``/digit`` is an identifier, and an identifier this
        receipt does not declare does not belong in the filing string.
        """
        self._refused(set_field(("kind",), "worldsense.proven_receipt/1"), "kind")
        self._refused(set_field(("operation",), "z8.theorem/1"), "operation")
        self._refused(set_field(("event",), "worldsense.kernel_clean/1"), "event")

    def test_slashed_prose_still_passes(self) -> None:
        """The shape test fires on ``/N``, not on every slash.

        Without this half, the rule above would be a ban on ordinary naming: this
        repository writes "Navier/Analysis" and "k/2" as prose all day, and a gate that
        refuses descriptive text trains producers to stop describing.
        """
        for value in ("navier-stokes/3D", "abc/ABC", "k/2-step", "Navier/Analysis"):
            honest = copy.deepcopy(self.payload)
            honest["kind"] = value
            self.assertIs(
                receipt.validate_navier_receipt_epistemics(honest)["ok"],
                True,
                f"prose {value!r} read as a schema identifier",
            )

    def test_axioms_field_is_refused_whatever_it_holds(self) -> None:
        """Empty, strict or invented: an axiom list is a kernel attestation."""
        self._refused(set_field(("axioms",), []), "axioms")
        self._refused(
            set_field(("axioms",), ["propext", "Classical.choice", "Quot.sound"]), "axioms"
        )
        self._refused(set_field(("axioms",), ["sorryAx"]), "axioms")
        self._refused(set_field(("probably", "axioms"), ["propext"]), "axioms")

    def test_non_mapping_input_is_refused(self) -> None:
        for value in (None, [], "", 0, [{"tier": "THEOREM"}]):
            with self.assertRaises(ValueError):
                receipt.validate_navier_receipt_epistemics(value)

    def test_refusal_rewrites_nothing(self) -> None:
        """A gate that quietly downgrades is indistinguishable from no gate.

        The inflated candidate must still be inflated after the refusal and the
        honest payload must still be byte-identical: the gate raises and leaves both
        exactly as it found them, so a caller that catches the error cannot end up
        publishing a receipt the gate "fixed" on its way past.
        """
        before = receipt.canonical_json(self.payload)
        inflated = copy.deepcopy(self.payload)
        inflated["tier"] = "PROVED"
        inflated["probably"]["deductive_proof"] = True
        snapshot = receipt.canonical_json(inflated)
        with self.assertRaises(ValueError):
            receipt.validate_navier_receipt_epistemics(inflated)
        self.assertEqual(receipt.canonical_json(inflated), snapshot)
        self.assertEqual(receipt.canonical_json(self.payload), before)
        self.assertEqual(self.payload["tier"], receipt.TIER_PROBABLY)


class WorldSenseConsumerContractTest(unittest.TestCase):
    """Pins what ``worldsense_scientific_flow`` reads, so the fold cannot misfile this.

    The consumer lives in awkronos/kagami and is not a dependency of this
    repository, so its tables are mirrored here as data with their source
    location, and re-checked against the owner's LANDED ref whenever a kagami
    repository is reachable on this host.

    Re-pinned 2026-11-26 against ``origin/main``
    ``e9c73add653530ed86d95684644928c71eb4cce9``. All three mirrored tuples had
    drifted, and the ratchet that exists to catch that had been answering
    ``ok`` while doing so — see
    :meth:`test_the_owner_probe_reads_a_landed_ref_not_a_lane_seat`.
    """

    #: The landed owner ref this mirror was cut against, so a future reader can
    #: diff the mirror against an object rather than against somebody's memory.
    OWNER_REF = "e9c73add653530ed86d95684644928c71eb4cce9"
    OWNER_MODULE = "packages/kagami/core/omni/worldsense_scientific_flow.py"
    #: The sibling owner module that mints the proof-word vocabulary this gate
    #: refuses against. Named rather than spelled inline so the ``git show`` ref and
    #: the path cannot drift apart between the two probes.
    OWNER_WEAVE_MODULE = "packages/kagami/core/omni/closed_loop_research_weave.py"

    #: ``kagami.core.omni.worldsense_scientific_flow._DOMAIN_MARKERS``, in order
    #: (most specific first; the first substring hit wins). 53 pairs at the ref
    #: above, up from the 16 this mirror carried.
    DOMAIN_MARKERS: Tuple[Tuple[str, str], ...] = (
        ("provably-notary", "lean_kernel_notary"),
        ("provably.notary", "lean_kernel_notary"),
        ("reactor-z8-meter", "z8_meter"),
        ("z8.meter", "z8_meter"),
        ("omni.quantum-reactor", "quantum_reactor"),
        ("z8.probably", "z8_probably"),
        # The two pairs this repository mirrors by name. The owner's own comment
        # says why navier stays behind the producer's word: rows that carry a
        # ``domain`` field never reach this scan, so this leg serves BARE rows only.
        ("navier", "navier_ifrk4"),
        ("ifrk4", "navier_ifrk4"),
        ("zke8", "zke8"),
        ("kagami_prover", "kagami_prover"),
        ("kagami-prover", "kagami_prover"),
        ("waterfill", "kagami_prover"),
        ("hodge_kahler", "hodge_kahler_geometry"),
        ("lefschetz", "hodge_kahler_geometry"),
        ("mathematical_economics", "mathematical_economics"),
        ("active_inference", "active_inference_fep"),
        ("reimann", "reimann"),
        ("riemann", "reimann"),
        ("zeta", "reimann"),
        ("imo2026", "imo2026"),
        ("antichain", "imo2026"),
        ("selfapproach", "selfapproach"),
        ("self-approach", "selfapproach"),
        ("banach", "selfapproach"),
        ("durable_execution", "durable_execution"),
        ("huddle", "durable_execution"),
        ("medverify", "medverify.clinical_audit"),
        ("frey_modular", "frey_modular_numbers"),
        ("fermat", "frey_modular_numbers"),
        ("bsd_elliptic", "bsd_elliptic_curves"),
        ("bsd", "bsd_elliptic_curves"),
        ("hft", "hft"),
        ("yang_mills", "yang_mills_lattice"),
        ("yang-mills", "yang_mills_lattice"),
        ("chess_vision", "chess_vision"),
        ("chess-vision", "chess_vision"),
        ("held_karp", "tsp_held_karp"),
        ("heldkarp", "tsp_held_karp"),
        ("rime_deterministic_simulation", "rime_deterministic_simulation"),
        ("detsim", "rime_deterministic_simulation"),
        ("knowledge_provenance", "knowledge_provenance"),
        ("tome_provenance", "knowledge_provenance"),
        ("tome", "knowledge_provenance"),
        ("hermes", "hermes"),
        ("corpus_compression", "hermes"),
        ("transfer_matrix", "reality_ym_transfer_matrix"),
        ("ym-transfer", "reality_ym_transfer_matrix"),
        ("protein", "protein_reactor_dag"),
        ("absorb_tree", "tsp_absorb_tree"),
        ("tsp", "tsp_absorb_tree"),
        ("e8", "world_e8"),
        ("benchmark", "benchmark_ratio"),
        ("ratio", "benchmark_ratio"),
    )
    #: The eight fields ``_receipt_schema_text`` concatenates, in its order. Six
    #: here until 2026-11-26; the owner added ``receipt_schema`` and
    #: ``artifact_kind`` because that is the name the landed producers write. The
    #: navier receipt stamps ``receipt_schema`` ITSELF, so a six-field mirror reads
    #: a field the consumer reads and calls it the whole surface.
    SCHEMA_FIELDS: Tuple[str, ...] = (
        "schema",
        "kind",
        "type",
        "operation",
        "receipt_type",
        "event",
        "receipt_schema",
        "artifact_kind",
    )
    #: The flow's own ``_TIER_FIELDS``: only these keys may assert a tier to it.
    #: Nine at the landed ref; this mirror carried seven and was missing
    #: ``epistemic_tier`` and ``claim_tier`` -- and this receipt STAMPS
    #: ``epistemic_tier`` at the top level and again inside ``probably``, so the
    #: two names the consumer reads on this row were the two not pinned here.
    CONSUMER_TIER_FIELDS: Tuple[str, ...] = (
        "tier",
        "scientific_tier",
        "epistemic_tier",
        "claim_tier",
        "claim",
        "verdict",
        "status",
        "evidence",
        "strength",
    )
    #: ``_NESTED_GRADE_BLOCKS``: the blocks whose tier fields the gate also reads.
    NESTED_GRADE_BLOCKS: Tuple[str, ...] = ("probably", "z8_probably")
    #: ``_DIGEST_FIELDS``: the names a row may carry its digest under. The gate
    #: refuses a scientific receipt with none of these at its top level or in a
    #: nested grade block (``no_digest_on_a_scientific_receipt``), which is how
    #: this receipt arrived until 2026-11-26 -- its digest lived at
    #: ``z8_meter.digest_sha256``, a block that reader never opens.
    OWNER_DIGEST_FIELDS: Tuple[str, ...] = (
        "receipt_sha256",
        "replay_sha256",
        "canonical_input_sha256",
        "digest_sha256",
        "payload_sha256",
        "notary_digest",
    )
    #: ``closed_loop_research_weave.THEOREM_WORDS`` | {quantum.PROVABLY}.
    CONSUMER_PROOF_WORDS: Tuple[str, ...] = (
        "THEOREM",
        "CLOSED",
        "PROVED",
        "KERNEL_CLEAN",
        "PROVABLY",
    )
    #: The epistemic-tier spellings the owner recognises but does NOT treat as a
    #: kernel claim (``_EPISTEMIC_TIER_VOCAB``). ``NUMERICAL_OBSERVATION`` is in
    #: that set, which is why this receipt can state it without quarantining.
    OWNER_EPISTEMIC_TIER_VOCAB: Tuple[str, ...] = (
        "CONDITIONAL_THEOREM",
        "CONJECTURE",
        "EXPERIMENT",
        "FORMAL_THEOREM",
        "FRAMEWORK",
        "NUMERICAL_OBSERVATION",
        "RAW_MEASUREMENT",
        "SORRY",
        "SPECULATION",
        "STATISTICAL_INFERENCE",
    )

    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = shared_receipt()

    def schema_text(self) -> str:
        return " ".join(
            str(self.payload.get(key, "")) for key in self.SCHEMA_FIELDS
        ).lower()

    def _route1_domain(self) -> str:
        """What ``classify_receipt`` route 1 answers for this row.

        Route 1 is the row's own ``domain`` field, taken verbatim, and it runs
        BEFORE the marker scan: the owner's docstring is explicit that "a
        substring heuristic is a strictly worse witness than the answer".
        """
        declared = self.payload.get("domain")
        return declared.strip() if isinstance(declared, str) else ""

    def _route3_domain(self) -> Tuple[str, str]:
        """The (marker, domain) the bare-row marker scan lands on, first hit wins."""
        text = self.schema_text()
        for marker, domain in self.DOMAIN_MARKERS:
            if marker in text:
                return marker, domain
        return "", "unattributed"

    def test_the_declared_domain_is_the_route_that_files_this_receipt(self) -> None:
        """Route 1 fires for this row, and its answer is the producer's own word.

        The owner kept ``("navier", "navier_ifrk4")`` in the marker table while
        saying, in the comment above it, that "rows that carry the producer's
        ``domain`` field still land in ``navier_stokes_3d`` — route 1 takes the
        declaration; this leg is only for bare rows". Two buckets for one repo is
        therefore the landed design, not a drift, and the honest pin names which
        route this receipt actually takes. Before this file knew about route 1 it
        asserted ``navier_ifrk4`` for a row the owner files under
        ``navier_stokes_3d`` -- a green test about a bucket nothing lands in.
        """
        self.assertEqual(
            self._route1_domain(),
            "navier_stokes_3d",
            "DOMAIN is what the consumer takes verbatim; changing it moves this "
            "receipt's bucket in the estate census",
        )
        self.assertTrue(
            self._route1_domain(),
            "a row with no declared domain falls through to the marker scan, which "
            "is a different (and weaker) attribution",
        )

    def test_a_bare_row_still_files_in_the_navier_bucket(self) -> None:
        """Strip the declaration and the marker scan must still land on navier.

        This is the leg the owner's comment refers to, and the one this file used
        to present as the whole of attribution.
        """
        text = self.schema_text()
        self.assertTrue(text, "every field the reader concatenates is empty")
        marker, domain = self._route3_domain()
        self.assertEqual(
            domain,
            "navier_ifrk4",
            f"the first marker to hit is {marker!r}, which files a bare row elsewhere",
        )
        self.assertIn(marker, ("navier", "ifrk4"))

    def test_schema_text_avoids_the_preceding_markers(self) -> None:
        """A marker ahead of ``navier`` in that table would steal the bare-row bucket.

        ``[:6]`` here was the count of entries ahead of navier in the 16-pair
        mirror. The landed table has 53 pairs and navier sits at the same index,
        so the slice still happened to be right -- a coincidence held by a
        literal. The bound is now derived from where ``navier`` actually is, so
        inserting a marker ahead of it fails this leg instead of passing it.
        """
        text = self.schema_text()
        navier_at = next(
            i for i, (marker, _) in enumerate(self.DOMAIN_MARKERS) if marker == "navier"
        )
        for marker, domain in self.DOMAIN_MARKERS[:navier_at]:
            self.assertNotIn(
                marker,
                text,
                f"{marker!r} (files as {domain!r}) now precedes navier in the classifier",
            )

    def test_only_a_probably_tier_is_asserted_in_the_fields_the_owner_reads(self) -> None:
        """Across all nine tier fields, top level and nested, no proof word appears.

        Scanning seven names and only the top level was the mirror's own blind
        spot: this receipt stamps ``epistemic_tier`` -- one of the two names that
        were missing -- at both places.
        """
        sources: List[Tuple[str, Dict[str, Any]]] = [("receipt", self.payload)]
        for block in self.NESTED_GRADE_BLOCKS:
            value = self.payload.get(block)
            if isinstance(value, dict):
                sources.append((block, cast(Dict[str, Any], value)))
        claimed: List[Tuple[str, str]] = []
        for where, holder in sources:
            for field in self.CONSUMER_TIER_FIELDS:
                raw = holder.get(field)
                if isinstance(raw, str):
                    # The owner's own normalisation: ``_tier_key`` uppercases and
                    # maps spaces to underscores, so "NUMERICAL OBSERVATION" and
                    # "NUMERICAL_OBSERVATION" are one word to the gate. The path is
                    # kept alongside the word so a refusal names WHICH field at
                    # WHICH height inflated, not just that something did.
                    claimed.append(
                        (f"{where}.{field}", raw.strip().upper().replace(" ", "_"))
                    )
        words = {word for _, word in claimed}
        self.assertIn("PROBABLY", words, "no tier field asserts PROBABLY at any height")
        self.assertTrue(
            any(not path.startswith("receipt.") for path, _ in claimed),
            "only the top level carries a tier field, so the nested scan measured nothing",
        )
        proof = [f"{path}={word}" for path, word in claimed if word in self.CONSUMER_PROOF_WORDS]
        self.assertEqual(proof, [], f"tier fields assert a proof word: {proof}")
        unknown = [
            f"{path}={word}"
            for path, word in claimed
            if word not in self.OWNER_EPISTEMIC_TIER_VOCAB
            and word not in self.CONSUMER_PROOF_WORDS
            and word != "PROBABLY"
        ]
        self.assertEqual(
            unknown, [], f"tier words the owner would grade as unknown: {unknown}"
        )

    def test_the_gate_mirrors_the_owner_vocabulary(self) -> None:
        self.assertTrue(
            set(self.CONSUMER_PROOF_WORDS).issubset(set(receipt.PROOF_TIER_WORDS)),
            "the consumer polices a word this gate does not",
        )

    def test_this_gate_polices_every_field_the_owner_reads(self) -> None:
        """The producer's own tier scan must be a SUPERSET of the consumer's.

        A producer that checks fewer fields than its consumer reports green for a
        reason it cannot see. ``claim_tier`` was the missing name on 2026-11-26:
        this file's gate accepted a row the owner quarantines.
        """
        missing = [f for f in self.CONSUMER_TIER_FIELDS if f not in receipt.TIER_FIELDS]
        self.assertEqual(
            missing, [], f"the owner reads tier fields this gate does not police: {missing}"
        )

    def test_no_kernel_attestation_channel_is_open(self) -> None:
        for key in ("axioms", "notary", "kernel_clean", "axiom_audit", "print_axioms"):
            self.assertNotIn(key, self.payload, f"{key!r} would attest a kernel audit")
            self.assertNotIn(key, self.payload["probably"])

    def test_receipt_states_a_digest_the_owner_can_find(self) -> None:
        """``verify_scientific_receipt_envelope`` requires a digest at the row's top level.

        Measured at the landed ref against this payload: with the digest only at
        ``z8_meter.digest_sha256`` the gate returned
        ``ok=False, refusals=['no_digest_on_a_scientific_receipt']`` -- a
        self-verifying receipt arriving unverified because the reader scans a
        different height than the writer stamps.
        """
        stated = {
            name: self.payload.get(name)
            for name in self.OWNER_DIGEST_FIELDS
            if name in self.payload
        }
        self.assertTrue(stated, "no top-level field carries a digest the owner scans")
        values = [v for v in stated.values() if isinstance(v, str) and v]
        self.assertTrue(values, "every digest field is present and empty (digest_field_null)")
        for name, value in stated.items():
            self.assertTrue(
                isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None,
                f"{name} is not 64 lowercase hex",
            )
        self.assertEqual(
            self.payload["receipt_sha256"],
            self.payload["z8_meter"]["digest_sha256"],
            "the two spellings of the measurement digest disagree",
        )
        self.assertEqual(
            self.payload["receipt_sha256"],
            receipt.payload_sha256(self.payload),
            "the stamped digest does not reproduce from this payload's stable view",
        )

    def test_pinned_tables_match_the_owner_source_when_reachable(self) -> None:
        source = self._owner_source()
        if source is None:
            self.skipTest("no landed kagami ref reachable on this host")
            return
        markers = self._extract_markers(source)
        self.assertEqual(markers, list(self.DOMAIN_MARKERS), "_DOMAIN_MARKERS drifted")
        self.assertEqual(
            self._extract_tuple(source, "_TIER_FIELDS"),
            list(self.CONSUMER_TIER_FIELDS),
            "_TIER_FIELDS drifted",
        )
        self.assertEqual(
            self._extract_tuple(source, "_NESTED_GRADE_BLOCKS"),
            list(self.NESTED_GRADE_BLOCKS),
            "_NESTED_GRADE_BLOCKS drifted",
        )
        self.assertEqual(
            self._extract_tuple(source, "_DIGEST_FIELDS"),
            list(self.OWNER_DIGEST_FIELDS),
            "_DIGEST_FIELDS drifted",
        )
        self.assertEqual(
            self._extract_schema_text_fields(source),
            list(self.SCHEMA_FIELDS),
            "the fields _receipt_schema_text concatenates drifted",
        )
        weave = self._owner_weave_source()
        if weave is None:
            return
        theorem = re.search(r"THEOREM_WORDS\s*=\s*frozenset\(\{([^}]*)\}\)", weave)
        assert theorem is not None
        words = tuple(
            w.strip().strip('"').upper() for w in theorem.group(1).split(",") if w.strip()
        )
        self.assertTrue(
            set(words).issubset(set(receipt.PROOF_TIER_WORDS)),
            f"the owner quarantines words this gate does not: {words}",
        )

    def test_the_owner_probe_reads_a_landed_ref_not_a_lane_seat(self) -> None:
        """The ratchet used to verify itself against a sibling lane's working tree.

        ``_kagami_packages`` globbed ``~/seats/*/*/packages/...`` and returned the
        first hit, so on 2026-11-26 this leg answered ``ok`` by comparing a 16-pair
        mirror with a 16-pair mirror: seven kagami seats on this host carry the
        pre-fold file, and the estate's canonical ``~/projects/kagami`` has no
        ``packages/`` directory at all. A pin checked against an arbitrary lane's
        uncommitted tree pins nothing -- the lane can be ahead, behind, or mid-edit,
        and nothing in the verdict says which. The landed ref is the only answer
        this repository is allowed to measure itself against.
        """
        resolver = inspect.getsource(WorldSenseConsumerContractTest._owner_source)
        self.assertNotIn(
            "seats/", resolver, "the owner probe is globbing lane seats again"
        )
        self.assertIn("origin/main", resolver, "the owner probe reads no landed ref")
        source = self._owner_source()
        if source is None:
            self.skipTest("no landed kagami ref reachable on this host")
            return
        self.assertIn("_DOMAIN_MARKERS", source)

    @staticmethod
    def _kagami_repo() -> Optional[Path]:
        """The kagami repository on this host, if one is present.

        Deliberately does NOT search ``~/seats``: a lane seat is somebody's working
        branch, and the fold this mirror is pinned against may not be in it.
        """
        configured = os.environ.get("KAGAMI_REPO", "").strip()
        candidates = [Path(configured)] if configured else []
        candidates.append(Path.home() / "projects" / "kagami")
        candidates.append(REPO.parent / "kagami")
        for root in candidates:
            if (root / ".git").exists():
                return root
        return None

    @classmethod
    def _owner_source(cls) -> Optional[str]:
        """The flow module's text AT ``origin/main``, via git.

        ``git show`` reads the committed object, so a dirty working tree, a lane
        branch, or an uncommitted edit in the primary checkout cannot answer for
        the estate. Returns None when no landed object is reachable, which the
        caller reports as UNMEASURED rather than as a pass.
        """
        root = cls._kagami_repo()
        if root is None:
            env = os.environ.get("KAGAMI_PACKAGES", "").strip()
            if env:
                probe = Path(env) / "kagami" / "core" / "omni" / "worldsense_scientific_flow.py"
                if probe.is_file():
                    return probe.read_text(encoding="utf-8")
            return None
        for ref in ("origin/main", "HEAD"):
            probe = subprocess.run(
                ["git", "-C", str(root), "show", f"{ref}:{cls.OWNER_MODULE}"],
                capture_output=True,
                text=True,
            )
            if probe.returncode == 0 and "_DOMAIN_MARKERS" in probe.stdout:
                return probe.stdout
        return None

    @classmethod
    def _owner_weave_source(cls) -> Optional[str]:
        root = cls._kagami_repo()
        if root is None:
            return None
        probe = subprocess.run(
            [
                "git", "-C", str(root), "show",
                "origin/main:" + cls.OWNER_WEAVE_MODULE,
            ],
            capture_output=True,
            text=True,
        )
        return probe.stdout if probe.returncode == 0 else None

    @staticmethod
    def _extract_markers(source: str) -> List[Tuple[str, str]]:
        """The ``_DOMAIN_MARKERS`` pairs, bounded by the literal's own closing paren.

        The previous extraction ran from the table's name to ``def
        _receipt_schema_text``, which on the landed file sweeps in
        ``DEFAULT_ESTATE_PRODUCERS`` and :func:`_tier_key`'s replacement pairs --
        five extra tuples that are not markers at all. Read against the landed ref
        that over-run made the ratchet itself wrong before it made it red.
        """
        lines = source.splitlines()
        start = next(i for i, line in enumerate(lines) if line.startswith("_DOMAIN_MARKERS"))
        stop = next(i for i in range(start + 1, len(lines)) if lines[i].rstrip() == ")")
        return [
            (a, b)
            for a, b in re.findall(r'\(\s*"([^"]+)",\s*"([^"]+)"\s*\)', "\n".join(lines[start:stop]))
        ]

    @staticmethod
    def _extract_tuple(source: str, name: str) -> List[str]:
        """One module-level ``NAME = ("a", "b", ...)`` as a list of its entries."""
        match = re.search(rf"^{re.escape(name)}\s*=\s*\(([^)]*)\)", source, re.M)
        assert match is not None, f"{name} is not a module-level tuple at the owner ref"
        return [
            item.strip().strip('"') for item in match.group(1).split(",") if item.strip().strip('"')
        ]

    @staticmethod
    def _extract_schema_text_fields(source: str) -> List[str]:
        """The key tuple inside :func:`_receipt_schema_text`'s generator."""
        match = re.search(
            r"def _receipt_schema_text.*?for key in \(\s*(.*?)\s*\)\s*\n\s*\)",
            source,
            re.S,
        )
        assert match is not None, "could not locate the schema-text field tuple"
        return [
            item.strip().strip('"') for item in match.group(1).split(",") if item.strip().strip('"')
        ]


class CliTest(unittest.TestCase):
    """The documented invocation surface, run as a subprocess the way CI runs it."""

    script = SCRIPTS / "navier_worldsense_receipt.py"

    def run_cli(self, *args: str) -> subprocess.CompletedProcess[str]:
        env = dict(os.environ)
        env["PYTHONPATH"] = str(SCRIPTS) + os.pathsep + env.get("PYTHONPATH", "")
        return subprocess.run(
            [sys.executable, str(self.script), *args],
            capture_output=True,
            text=True,
            timeout=600,
            env=env,
            cwd=str(REPO),
        )

    def test_json_mode_prints_a_self_verifying_payload(self) -> None:
        proc = self.run_cli(
            "--grid", "8", "--viscosities", "0.1", "--dt", "0.05", "--steps", "4",
            "--convergence-grids", "6", "8", "--json",
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        payload = json.loads(proc.stdout)
        self.assertEqual(payload["schema"], receipt.RECEIPT_SCHEMA)
        self.assertEqual(receipt.payload_sha256(payload), payload["z8_meter"]["digest_sha256"])

    def test_out_mode_writes_a_digest_wrapped_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / "receipt.json"
            proc = self.run_cli(
                "--grid", "8", "--viscosities", "0.1", "--dt", "0.05", "--steps", "4",
                "--convergence-grids", "6", "8", "--out", str(target),
            )
            self.assertEqual(proc.returncode, 0, proc.stderr)
            wrapper = json.loads(proc.stdout)
            self.assertEqual(set(wrapper), {"payload_sha256", "output", "bytes"})
            self.assertTrue(target.is_file())
            written = json.loads(target.read_text(encoding="utf-8"))
            body = receipt.canonical_json(written["payload"])
            self.assertEqual(
                written["payload_sha256"], hashlib.sha256(body.encode("utf-8")).hexdigest()
            )
            self.assertEqual(wrapper["payload_sha256"], written["payload_sha256"])
            self.assertEqual(written["payload"]["tier"], receipt.TIER_PROBABLY)
            # `bytes` is the write receipt on stdout, not a field of the file.
            self.assertEqual(wrapper["output"], str(target.resolve()))
            self.assertGreater(wrapper["bytes"], 0)
            self.assertEqual(wrapper["bytes"], target.stat().st_size)

    def test_summary_mode_prints_one_line(self) -> None:
        proc = self.run_cli(
            "--grid", "8", "--viscosities", "0.1", "--dt", "0.05", "--steps", "4",
            "--convergence-grids", "6", "8", "--summary",
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertEqual(len(proc.stdout.strip().splitlines()), 1)
        for token in ("digest=", "BKM=", "div=", "skew=", "engine="):
            self.assertIn(token, proc.stdout)

    def test_default_mode_prints_the_digest_view(self) -> None:
        proc = self.run_cli(
            "--grid", "8", "--viscosities", "0.1", "--dt", "0.05", "--steps", "4",
            "--convergence-grids", "6", "8",
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        view = json.loads(proc.stdout)
        for key in ("digest", "tier", "epistemic_tier", "invariants", "reactor_optimization_hint"):
            self.assertIn(key, view)
        self.assertEqual(view["tier"], receipt.TIER_PROBABLY)
        # Same schedule, no --include-series: this digest must equal the one the
        # --json leg of this class recomputes from the full payload.
        self.assertRegex(view["digest"], r"^[0-9a-f]{64}$")
        json_proc = self.run_cli(
            "--grid", "8", "--viscosities", "0.1", "--dt", "0.05", "--steps", "4",
            "--convergence-grids", "6", "8", "--json",
        )
        self.assertEqual(json_proc.returncode, 0, json_proc.stderr)
        self.assertEqual(
            view["digest"], json.loads(json_proc.stdout)["z8_meter"]["digest_sha256"]
        )
        self.assertIn("--json", view["hint"])

    def test_odd_grid_is_refused_before_any_run(self) -> None:
        proc = self.run_cli("--grid", "7", "--viscosities", "0.1", "--steps", "1")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("even", proc.stderr)
        self.assertEqual(proc.stdout, "")

    def test_engine_flag_selects_the_backend(self) -> None:
        proc = self.run_cli(
            "--grid", "8", "--viscosities", "0.1", "--dt", "0.05", "--steps", "4",
            "--convergence-grids", "6", "8", "--engine", "builtin", "--summary",
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("engine=builtin", proc.stdout)

    def test_include_series_survives_the_cli(self) -> None:
        proc = self.run_cli(
            "--grid", "8", "--viscosities", "0.1", "--dt", "0.05", "--steps", "4",
            "--convergence-grids", "6", "8", "--include-series", "--json",
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        payload = json.loads(proc.stdout)
        series = payload["runs"][0]["time_series"]
        self.assertIn("production", series)
        self.assertIn("t_report", series)
        self.assertEqual(receipt.payload_sha256(payload), payload["z8_meter"]["digest_sha256"])

    def test_abc_initial_condition_runs_through_the_cli(self) -> None:
        proc = self.run_cli(
            "--grid", "8", "--viscosities", "0.1", "--dt", "0.05", "--steps", "4",
            "--convergence-grids", "6", "8", "--ic", "abc", "--summary",
        )
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn("ic=abc", proc.stdout)


def _ci_job_window(text: str, job: str) -> Tuple[int, int]:
    """``[start, end)`` line indices owned by ``jobs.<job>`` in a workflow.

    Raises rather than returning an empty window: a renamed job is a missing
    carrier, and a test that silently scans nothing is the defect this file is
    here to close, not a pass to record.
    """
    lines = text.splitlines()
    start = next(
        (i for i, line in enumerate(lines) if re.match(rf"^  {re.escape(job)}:\s*$", line)),
        None,
    )
    if start is None:
        raise AssertionError(f"workflow has no `jobs.{job}`")
    end = next(
        (i for i in range(start + 1, len(lines)) if re.match(r"^  \S[^:]*:\s*(#.*)?$", lines[i])),
        len(lines),
    )
    return start, end


def _ci_step_run(text: str, job: str, name_fragment: str) -> str:
    """The ``run: |`` body of a named step, dedented, or ``AssertionError``.

    Parsed from the workflow's text rather than with PyYAML because this battery
    runs on interpreters with no PyYAML (the module's own docstring says so), and
    because the object under guard is the literal shell text CI will execute —
    the thing returned here is fed to ``bash`` unchanged by
    :meth:`CiWorldSenseEnrollmentTest.test_the_leg_executes_verbatim`, so a parse
    that smoothed the text over would defeat the point.
    """
    start, stop = _ci_job_window(text, job)
    lines = text.splitlines()
    step_at = None
    for i in range(start, stop):
        if lines[i].strip().startswith("- name:") and name_fragment in lines[i]:
            step_at = i
            break
    if step_at is None:
        raise AssertionError(
            f"workflow job `{job}` has no step naming {name_fragment!r} inside "
            f"lines {start + 1}-{stop}; the WorldSense CLI leg is unenrolled"
        )
    run_at = None
    for i in range(step_at + 1, stop):
        if lines[i].strip() == "run: |":
            run_at = i
            break
        if lines[i].strip().startswith("- name:"):
            break
    if run_at is None:
        raise AssertionError(f"step {name_fragment!r} has no `run: |` block")
    run_indent = len(lines[run_at]) - len(lines[run_at].lstrip())
    body: List[str] = []
    for i in range(run_at + 1, len(lines)):
        line = lines[i]
        if line.strip() and (len(line) - len(line.lstrip())) <= run_indent:
            break
        body.append(line)
    assert body, f"step {name_fragment!r} has an empty run body"
    return textwrap.dedent("\n".join(body)) + "\n"


class CiWorldSenseEnrollmentTest(unittest.TestCase):
    """The WorldSense producer's CLI leg is enrolled in CI, lake-free, and load-bearing.

    What this closes. ``make test`` already collects this file (``scripts`` and
    ``tests`` are both in ``Makefile:TEST_ROOTS`` and the python job calls
    ``make test``), so the *import* surface of the receipt had a scheduled verdict.
    The three paths a WorldSense consumer actually walks — ``--self-test``, the
    ``--out`` → ``--check-file`` roundtrip, and two independent runs agreeing on
    ``receipt_sha256`` — had none: measured at ``f277dce649850b0cfedf0e48f2ba2520d7010b0b``,
    ``ci.yml`` mentioned ``navier_worldsense_receipt`` zero times. A digest that no
    run recomputes is a digest that no run proves stable, and a refusal path no run
    exercises rots the first time a field is renamed.

    The guard is therefore executable, not textual. The last three legs take the
    workflow's own shell text and hand it to ``bash`` with ``$PYTHON`` bound to the
    interpreter running this test, so the step cannot describe a command that fails:
    it is run verbatim, then run once with a deliberately broken flag to prove a
    red leg is still possible — an always-zero leg would pass this too, and an
    always-zero leg is decoration (``declared carrier is decoration``, 1126).
    """

    JOB = "python"
    STEP = "Navier WorldSense"

    @classmethod
    def setUpClass(cls) -> None:
        cls.workflow = WORKFLOW.read_text(encoding="utf-8")
        cls.leg = _ci_step_run(cls.workflow, cls.JOB, cls.STEP)

    def test_the_leg_is_lake_free(self) -> None:
        """No ``lake``/``lean`` in the step: the python job runs on a hosted runner.

        The brief's constraint is stronger than "does not fail" — a lake build on
        that runner is a multi-hour cold graph, which is the exact topology this
        workflow was rewritten away from (see the header comment's 2026-09-22
        measurement). The step must therefore be pure Python.
        """
        self.assertNotRegex(self.leg, r"\b(lake|lean)\b", f"the step is not lake-free: {self.leg!r}")
        self.assertNotIn("Mathlib", self.leg)

    def test_the_leg_names_all_three_consumer_paths(self) -> None:
        flags = ("--self-test", "--out", "--check-file", "--json")
        for flag in flags:
            with self.subTest(flag=flag):
                self.assertIn(
                    flag,
                    self.leg,
                    f"the WorldSense step never invokes {flag}, so that consumer "
                    "path has no scheduled verdict",
                )
        self.assertIn("receipt_sha256", self.leg, "the leg does not read the measurement digest")

    def test_the_leg_compares_digests_and_fails_loudly(self) -> None:
        """Determinism is asserted on the digest, twice, with a named refusal.

        stdout of two runs differs by construction — ``generated_utc`` and
        ``z8_meter.wall_ms`` are listed in the receipt's own
        ``nondeterministic_fields`` — so a step that diffed the payloads would be
        red for the wrong reason and would train its reader to ignore it.
        """
        self.assertGreaterEqual(
            self.leg.count("measurement_digest"),
            3,
            "the leg does not run the digest twice through one definition",
        )
        self.assertRegex(self.leg, r"receipt_sha256", "the leg reads some other field")
        self.assertRegex(
            self.leg, r"::error::", "a digest divergence would exit nonzero with no message"
        )

    def test_the_leg_executes_verbatim(self) -> None:
        """Run the workflow's own shell text here, on this interpreter."""
        with tempfile.TemporaryDirectory() as tmp:
            proc = self._run(self.leg, tmp)
        self.assertEqual(proc.returncode, 0, msg=(proc.stdout + proc.stderr).strip())
        self.assertIn("self-test OK", proc.stdout)
        self.assertRegex(
            proc.stdout, r"measurement digest stable across runs: [0-9a-f]{64}"
        )
        self.assertNotIn("Traceback", proc.stderr)

    def test_a_broken_carrier_reddens_the_leg(self) -> None:
        """The control: sabotage one flag and require the leg to notice.

        Without this, a leg that echoes success regardless of what the script
        printed passes every other assertion in this class.
        """
        self.assertIn("--check-file", self.leg)
        broken = self.leg.replace("--check-file", "--check-file-renamed-away")
        with tempfile.TemporaryDirectory() as tmp:
            proc = self._run(broken, tmp)
        self.assertNotEqual(
            proc.returncode, 0, "the leg reports success against a flag that does not exist"
        )
        self.assertNotIn("measurement digest stable", proc.stdout)

    def test_the_receipt_written_by_the_leg_is_the_one_check_file_accepts(self) -> None:
        """The wrapper the step writes is the wrapper the step verifies.

        Two digests live at two heights and CI reads both: ``payload_sha256`` is
        the wrapper's SHA-256 over the canonical payload text (it is what catches
        a post-write edit), ``receipt_sha256`` is the measurement digest over the
        stable view. Asserting they are equal would be wrong; asserting the
        report reproduces each from the file on disk is the actual contract.
        """
        out_dir = tempfile.TemporaryDirectory()
        self.addCleanup(out_dir.cleanup)
        target = Path(out_dir.name) / "receipt.json"
        write = self._invoke("--out", str(target))
        self.assertEqual(write.returncode, 0, write.stderr)
        check = self._invoke("--check-file", str(target))
        self.assertEqual(check.returncode, 0, check.stderr)
        report = json.loads(check.stdout)
        wrapper = json.loads(target.read_text(encoding="utf-8"))
        payload = wrapper["payload"]
        body = receipt.canonical_json(payload)
        self.assertEqual(report["payload_sha256"], hashlib.sha256(body.encode("utf-8")).hexdigest())
        self.assertEqual(report["payload_sha256"], wrapper["payload_sha256"])
        self.assertEqual(report["receipt_sha256"], payload["receipt_sha256"])
        self.assertEqual(report["stable_view_digest"], report["receipt_sha256"])
        self.assertEqual(report["tier"], receipt.TIER_PROBABLY)
        self.assertEqual(report["domain"], receipt.DOMAIN)

    def test_the_step_lives_where_the_battery_lives(self) -> None:
        """Same job as ``make test``, after it: a leg in a droppable job enrolls nothing."""
        start, stop = _ci_job_window(self.workflow, self.JOB)
        lines = self.workflow.splitlines()
        step_at = [
            i for i in range(start, stop) if lines[i].strip().startswith("- name:")
            and self.STEP in lines[i]
        ]
        self.assertTrue(step_at, "the WorldSense step is not inside the python job")
        make_test = [i for i in range(start, stop) if re.match(r"^\s+make test\b", lines[i])]
        self.assertTrue(make_test, "the python job no longer runs the Makefile battery")
        self.assertGreater(
            step_at[0],
            make_test[0],
            "the CLI leg runs before the battery, so a battery failure hides it",
        )

    # -- helpers ---------------------------------------------------------

    def _env(self, tmp: str) -> Dict[str, str]:
        env = dict(os.environ)
        env["PYTHON"] = sys.executable
        env["RUNNER_TEMP"] = tmp
        env["PYTHONPATH"] = str(SCRIPTS) + os.pathsep + env.get("PYTHONPATH", "")
        return env

    def _run(self, script: str, tmp: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", "-c", f"set -euo pipefail\n{script}"],
            capture_output=True,
            text=True,
            timeout=600,
            env=self._env(tmp),
            cwd=str(REPO),
        )

    def _invoke(self, *args: str) -> "subprocess.CompletedProcess[str]":
        return subprocess.run(
            [sys.executable, str(SCRIPTS / "navier_worldsense_receipt.py"), *args],
            capture_output=True,
            text=True,
            timeout=600,
            cwd=str(REPO),
        )


class InputGuardTest(unittest.TestCase):
    """A schedule that cannot mean what it says must be refused, not measured."""

    def test_odd_and_small_grids_are_refused(self) -> None:
        engine = receipt.resolve_engine("builtin")
        for grid in (7, 2, 0):
            with self.assertRaises(ValueError):
                receipt.run_once(engine, grid, 0.1, FAST_DT, 1)

    def test_nonpositive_dt_and_steps_are_refused(self) -> None:
        engine = receipt.resolve_engine("builtin")
        with self.assertRaises(ValueError):
            receipt.run_once(engine, 8, 0.1, 0.0, 4)
        with self.assertRaises(ValueError):
            receipt.run_once(engine, 8, 0.1, FAST_DT, 0)
        with self.assertRaises(ValueError):
            receipt.run_once(engine, 8, -0.1, FAST_DT, 4)
        with self.assertRaises(ValueError):
            receipt.run_once(engine, 8, float("nan"), FAST_DT, 4)

    def test_unknown_initial_condition_is_refused(self) -> None:
        engine = receipt.resolve_engine("builtin")
        with self.assertRaises(KeyError):
            receipt.run_once(engine, 8, 0.1, FAST_DT, 1, "kelvin_helmholtz")

    def test_empty_schedule_is_refused(self) -> None:
        with self.assertRaises(ValueError):
            receipt.build_receipt(grids=(), viscosities=(0.1,))
        with self.assertRaises(ValueError):
            receipt.build_receipt(grids=(8,), viscosities=())


class ToleranceHonestyTest(unittest.TestCase):
    """The numbers quoted as tolerances are the numbers the payload gates on."""

    def test_declared_tolerances_are_the_ones_applied(self) -> None:
        payload = shared_receipt()
        self.assertEqual(
            payload["invariants"]["triad_cancellation"]["tolerance"], receipt.CONVECTIVE_TOLERANCE
        )
        self.assertEqual(
            payload["invariants"]["solenoidal_constraint"]["tolerance"], receipt.DIV_TOLERANCE
        )

    def test_holds_flags_agree_with_their_numbers(self) -> None:
        payload = shared_receipt()
        triad = payload["invariants"]["triad_cancellation"]
        self.assertEqual(
            triad["holds"], triad["abs_max"] < triad["tolerance"]
        )
        solenoidal = payload["invariants"]["solenoidal_constraint"]
        self.assertEqual(
            solenoidal["holds"],
            solenoidal["max_abs_divergence_linf"] < solenoidal["tolerance"],
        )

    def test_no_field_in_the_payload_claims_a_proof_tier(self) -> None:
        """Deep scan by a SECOND reader: the payload, not the gate's own walk.

        The gate passing is already asserted elsewhere. This leg walks the shipped
        payload with the test's own traverser and compares against the refusal
        vocabulary, so a bug in the module's walker -- a container shape it forgets
        to descend -- shows up here instead of hiding behind the gate it should have
        been caught by.
        """
        offenders = [
            (path, leaf)
            for path, leaf in string_leaves(shared_receipt())
            if isinstance(leaf, str) and leaf.strip().upper() in receipt.PROOF_TIER_WORDS
        ]
        self.assertEqual(offenders, [])


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
