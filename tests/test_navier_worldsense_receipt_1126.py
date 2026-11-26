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

Runs on the 3.9 interpreter with no third-party dependency beyond numpy; the
optional PyYAML leg skips when PyYAML is absent, exactly as the solver tests
skip when the reality checkout is absent.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.abc
import importlib.util
import json
import math
import os
import re
import subprocess
import sys
import tempfile
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
    is bit-identical to the canonical engine makes the CI number the same number
    the dev host reports. That is what this leg pins.
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

    def test_builtin_and_canonical_agree_to_the_bit(self) -> None:
        canonical = self._payload("canonical")
        if canonical is None:
            self.skipTest("no reality checkout on this host: the shim cannot be imported")
            return
        builtin = self._payload("builtin")
        self.assertIsNotNone(builtin)
        assert builtin is not None and canonical is not None
        self.assertEqual(canonical["runs"], builtin["runs"])
        self.assertEqual(
            canonical["z8_meter"]["digest_sha256"], builtin["z8_meter"]["digest_sha256"]
        )
        self.assertNotEqual(canonical["provenance"]["engine"], builtin["provenance"]["engine"])

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
    location, and re-checked against the real file whenever a kagami checkout is
    reachable on this host.
    """

    #: kagami.core.omni.worldsense_scientific_flow._DOMAIN_MARKERS, in order
    #: (most specific first; the first substring hit wins).
    DOMAIN_MARKERS: Tuple[Tuple[str, str], ...] = (
        ("provably-notary", "lean_kernel_notary"),
        ("provably.notary", "lean_kernel_notary"),
        ("reactor-z8-meter", "z8_meter"),
        ("z8.meter", "z8_meter"),
        ("omni.quantum-reactor", "quantum_reactor"),
        ("z8.probably", "z8_probably"),
        ("navier", "navier_ifrk4"),
        ("ifrk4", "navier_ifrk4"),
        ("transfer_matrix", "reality_ym_transfer_matrix"),
        ("ym-transfer", "reality_ym_transfer_matrix"),
        ("protein", "protein_reactor_dag"),
        ("absorb_tree", "tsp_absorb_tree"),
        ("tsp", "tsp_absorb_tree"),
        ("e8", "world_e8"),
        ("benchmark", "benchmark_ratio"),
        ("ratio", "benchmark_ratio"),
    )
    #: The six fields ``_receipt_schema_text`` concatenates, in its order.
    SCHEMA_FIELDS: Tuple[str, ...] = (
        "schema",
        "kind",
        "type",
        "operation",
        "receipt_type",
        "event",
    )
    #: The flow's own ``_TIER_FIELDS``: only these keys may assert a tier to it.
    CONSUMER_TIER_FIELDS: Tuple[str, ...] = (
        "tier",
        "scientific_tier",
        "claim",
        "verdict",
        "status",
        "evidence",
        "strength",
    )
    #: ``closed_loop_research_weave.THEOREM_WORDS`` | {quantum.PROVABLY}.
    CONSUMER_PROOF_WORDS: Tuple[str, ...] = (
        "THEOREM",
        "CLOSED",
        "PROVED",
        "KERNEL_CLEAN",
        "PROVABLY",
    )

    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = shared_receipt()

    def schema_text(self) -> str:
        return " ".join(
            str(self.payload.get(key, "")) for key in self.SCHEMA_FIELDS
        ).lower()

    def test_receipt_is_attributed_to_the_navier_domain(self) -> None:
        text = self.schema_text()
        self.assertTrue(text, "every field the reader concatenates is empty")
        for marker, domain in self.DOMAIN_MARKERS:
            if marker in text:
                self.assertEqual(
                    domain,
                    "navier_ifrk4",
                    f"the first marker to hit is {marker!r}, which files this elsewhere",
                )
                return
        self.fail(f"classify_receipt would file this as unattributed; schema text {text[:160]!r}")

    def test_schema_text_avoids_the_preceding_markers(self) -> None:
        """A marker ahead of ``navier`` in that table would steal the domain."""
        text = self.schema_text()
        ahead = [m for m, _ in self.DOMAIN_MARKERS[:6]]
        for marker in ahead:
            self.assertNotIn(marker, text, f"{marker!r} now precedes navier in the classifier")

    def test_only_a_probably_tier_is_asserted_at_the_top_level(self) -> None:
        words = [
            self.payload[key].strip().upper()
            for key in self.CONSUMER_TIER_FIELDS
            if isinstance(self.payload.get(key), str)
        ]
        self.assertEqual(words, ["PROBABLY"])
        self.assertFalse([w for w in words if w in self.CONSUMER_PROOF_WORDS])

    def test_the_gate_mirrors_the_owner_vocabulary(self) -> None:
        self.assertTrue(
            set(self.CONSUMER_PROOF_WORDS).issubset(set(receipt.PROOF_TIER_WORDS)),
            "the consumer polices a word this gate does not",
        )

    def test_no_kernel_attestation_channel_is_open(self) -> None:
        for key in ("axioms", "notary", "kernel_clean", "axiom_audit", "print_axioms"):
            self.assertNotIn(key, self.payload, f"{key!r} would attest a kernel audit")
            self.assertNotIn(key, self.payload["probably"])

    def test_pinned_tables_match_the_owner_source_when_reachable(self) -> None:
        root = self._kagami_packages()
        if root is None:
            self.skipTest("no kagami checkout reachable on this host")
            return
        flow = (root / "kagami" / "core" / "omni" / "worldsense_scientific_flow.py").read_text(
            encoding="utf-8"
        )
        weave = (root / "kagami" / "core" / "omni" / "closed_loop_research_weave.py").read_text(
            encoding="utf-8"
        )
        start = flow.index("_DOMAIN_MARKERS")
        stop = flow.index("def _receipt_schema_text", start)
        live = [
            (a, b)
            for a, b in re.findall(r'\(\s*"([^"]+)",\s*"([^"]+)"\s*\)', flow[start:stop])
        ]
        self.assertEqual(live, list(self.DOMAIN_MARKERS), "_DOMAIN_MARKERS drifted")
        theorem = re.search(r"THEOREM_WORDS\s*=\s*frozenset\(\{([^}]*)\}\)", weave)
        assert theorem is not None
        words = tuple(w.strip().strip('"').upper() for w in theorem.group(1).split(",") if w.strip())
        self.assertTrue(set(words).issubset(set(receipt.PROOF_TIER_WORDS)), f"unpoliced {words}")
        tier_fields = re.search(r"_TIER_FIELDS\s*=\s*\(([^)]*)\)", flow)
        assert tier_fields is not None
        found = tuple(
            w.strip().strip('"') for w in tier_fields.group(1).split(",") if w.strip().strip('"')
        )
        self.assertEqual(found, self.CONSUMER_TIER_FIELDS, "_TIER_FIELDS drifted")

    @staticmethod
    def _kagami_packages() -> Optional[Path]:
        """Locate a checkout carrying the flow module, without scanning the volume."""
        candidates: List[Path] = []
        env = os.environ.get("KAGAMI_PACKAGES", "").strip()
        if env:
            candidates.append(Path(env))
        candidates.append(Path.home() / "projects" / "kagami" / "packages")
        for root in candidates:
            probe = root / "kagami" / "core" / "omni" / "worldsense_scientific_flow.py"
            if probe.is_file():
                return root
        for probe in sorted(Path.home().glob("seats/*/*/packages/kagami/core/omni/worldsense_scientific_flow.py")):
            return probe.parents[3]
        return None


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
