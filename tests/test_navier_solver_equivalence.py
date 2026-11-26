"""Guards for the pseudo-spectral solver's accelerated path and its metrics.

Before this file the solver had NO test coverage: nothing under ``tests/`` or
in the CI workflow referenced ``navier_solver_bench``,
``navier_spectral_core`` or ``navier_accel``, so the only thing standing
between an optimisation and a silently wrong benchmark was whoever was
looking.  The accelerated path exists purely to go faster, so the property
that matters is that it changes nothing, and that is checked here as BIT
equality rather than a tolerance.

Skipped wholesale when numpy is unavailable (the CI registry job installs no
scientific stack).  The accelerator-specific cases skip again when the C
library or pyFFTW is absent, which is the supported degraded configuration --
never a failure.
"""

from __future__ import annotations

import hashlib
import math
import os
import sys
import unittest

sys.path.insert(
    0,
    os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"),
)

try:
    import numpy as np

    import navier_accel
    import navier_solver_bench as bench
    import navier_spectral_core as core
except ImportError as exc:  # pragma: no cover - environment without numpy
    raise unittest.SkipTest(f"solver stack unavailable: {exc}") from exc


def _digest(state) -> str:
    return hashlib.sha256(np.ascontiguousarray(state).tobytes()).hexdigest()


def _states() -> dict[str, str]:
    """Final states for a spread of configurations, as content digests."""
    out: dict[str, str] = {}
    for n, steps in ((8, 7), (16, 12)):
        sp = core.spectral(n)
        field = core.leray(core.forward(core.taylor_green_field(n)), sp)
        for viscosity, dealias in ((0.05, True), (0.0, True), (0.05, False)):
            out[f"tgv-{n}-{viscosity}-{dealias}"] = _digest(
                core.evolve(field, sp, viscosity, 0.037, steps, dealias)
            )
        _, exact_hat, forcing = core.mms_problem(sp, 0.05)
        out[f"mms-{n}"] = _digest(
            core.evolve(exact_hat(0.0), sp, 0.05, 0.05, steps, True, forcing, 0.0)
        )
        out[f"nl-{n}"] = _digest(core.nonlinear_hat(field, sp, True))
    return out


class AcceleratorTest(unittest.TestCase):
    def test_self_check_passes_or_accelerator_is_disabled(self) -> None:
        """A live accelerator must have verified itself against numpy.

        ``navier_accel`` runs :func:`self_check` at import and clears ``LIB``
        on any disagreement, so a non-None LIB with a status other than "ok"
        would mean the guard had been bypassed.
        """
        if navier_accel.LIB is None:
            self.assertNotEqual(navier_accel.status(), "ok")
            return
        self.assertEqual(navier_accel.status(), "ok")
        passed, why = navier_accel.self_check()
        self.assertTrue(passed, f"kernel disagrees with numpy: {why}")

    def test_accelerated_path_is_bit_identical(self) -> None:
        """Same bytes out of the fast path and the numpy reference.

        Run in child processes because the accelerator is selected at import
        time from NAVIER_ACCEL.
        """
        if not core._fast_available():
            self.skipTest(f"accelerator inactive: {navier_accel.status()}")

        import json
        import subprocess

        script = (
            "import json,sys;"
            f"sys.path.insert(0, {os.path.dirname(os.path.abspath(core.__file__))!r});"
            f"sys.path.insert(0, {os.path.dirname(os.path.abspath(__file__))!r});"
            "from test_navier_solver_equivalence import _states;"
            "print(json.dumps(_states()))"
        )
        results = {}
        for flag in ("1", "0"):
            env = dict(os.environ, NAVIER_ACCEL=flag, OMP_NUM_THREADS="1")
            proc = subprocess.run(
                [sys.executable, "-c", script],
                capture_output=True, text=True, env=env, timeout=600,
            )
            self.assertEqual(proc.returncode, 0, proc.stderr[-2000:])
            results[flag] = json.loads(proc.stdout)

        self.assertGreaterEqual(len(results["1"]), 8)
        self.assertEqual(
            results["1"], results["0"],
            "accelerated path changed the numerical result",
        )


class MetricContractTest(unittest.TestCase):
    """Pins on the reported metrics at the registered smoke resolution: an
    exact manufactured solution, the design order of the integrator, a
    grid-independent carrier invariant, and two round-off floors.

    Values recorded 2026-08-31 and cross-checked against the pre-optimisation
    commit 0c4b08a in a separate worktree.  These are analytic properties of
    the discretisation, not timings, so they are stable across hosts -- but
    only to the reproducibility floor of the arithmetic that produces them,
    which is NOT the last bit.  The distinction was established by measuring
    the same quantity under two numpy builds on this host (``numpy`` 2.0.2
    and 2.5.1, ``OMP_NUM_THREADS=1``):

    * ``l2_rel_error``      6.090625495414642e-07 / 6.090625495672906e-07
      -- absolute spread 2.6e-17, i.e. 4.2e-11 relative;
    * ``time_convergence_order``, the log-ratio of two such errors,
      4.019322768300311 / 4.019322767391321 -- spread 9.1e-10.

    The order statistic is therefore roughly a thousand times *less*
    reproducible than the errors it is built from, and the reason is arithmetic
    rather than numerical: both errors carry the same additive round-off offset
    ``d`` (~2.6e-17 here, set by the backend's FFT round-trip and its libm
    transcendentals), and a common offset does not cancel in a ratio -- it
    enters the smaller error with far greater relative weight:

        shift in p  ~=  (d / ln 2) * (E1 - E2) / (E1 * E2)  ~=  3.6e7 * d,

    i.e. an amplification of order ``1 / E2``.  With ``E1 = 6.09e-7``,
    ``E2 = 3.76e-8`` and ``d = 2.6e-17`` that predicts a 9.4e-10 shift, which is
    the 9.1e-10 observed between the two builds.  A pin tighter than ~1e-8 on
    this quantity therefore constrains the backend's round-off realisation, not
    the discretisation, so it cannot be a regression guard: the previous
    ``delta=1e-12`` on the order matched no interpreter available here and
    red-flagged a correct solver.

    What is asserted instead, per quantity, and in decreasing order of
    strength:

    1. the Richardson ladder (``test_ifrk4_richardson_ladder_...``), which
       proves O(dt^4) as a limit law over three successive refinements and is
       insensitive to the offset because the difference form cancels it;
    2. an exact-value anchor on the offset-cancelling difference ratio
       ``|E0-E1| / |E1-E2|``, reproducible to 2e-9 and pinned to 1e-6;
    3. the two-point order and the five-point log-log fit, to 1e-6 and 1e-5
       of their recorded values and 0.05 of the design value 4.

    A change past any of these bands means the mathematics moved and wants
    explaining, not a tolerance widening.
    """

    SMOKE = dict(grid=16, steps=20, viscosity=0.05, dt=0.05, case="all",
                 final_time=1.0)

    @classmethod
    def setUpClass(cls) -> None:
        cls.metrics = bench.solve(reps=1, warmup=0, **cls.SMOKE)

    @classmethod
    def _mms_error_ladder(cls, levels: int = 4) -> list[float]:
        """Relative-L2 MMS error at ``final_time / (steps * 2**level)``.

        Same grid, same manufactured solution, same reference field; only the
        time step halves.  Level 0 is the SMOKE configuration the headline
        metrics report, so the ladder is an extension of the pinned run rather
        than a different experiment.
        """
        sp = core.spectral(cls.SMOKE["grid"])
        _, exact_hat, forcing = core.mms_problem(sp, cls.SMOKE["viscosity"])
        reference = exact_hat(cls.SMOKE["final_time"])
        errors: list[float] = []
        for level in range(levels):
            steps = cls.SMOKE["steps"] * 2 ** level
            dt = cls.SMOKE["final_time"] / steps
            state = core.evolve(
                exact_hat(0.0), sp, cls.SMOKE["viscosity"], dt, steps, True,
                forcing, 0.0,
            )
            errors.append(core.relative_l2(state, reference, sp))
        return errors

    def test_manufactured_solution_error(self) -> None:
        self.assertAlmostEqual(
            self.metrics["l2_rel_error"], 6.0906254951665697e-07, delta=1e-15
        )

    def test_integrator_realises_design_order_four(self) -> None:
        # IFRK4 is fourth order; both the two-point ratio and the five-point
        # log-log fit must land on 4, which is the registered anchor
        # navier.spectral.ifrk4_time_order.
        #
        # Deltas are set from the measured cross-backend spread recorded in the
        # class docstring (9.1e-10 and 9.2e-8 respectively), so each anchor
        # keeps two to three orders of margin over round-off while staying
        # thousands of times tighter than the design band below it.  The finest
        # level of the multi-dt fit is dt/8, where the error has decayed to
        # ~1.5e-10 and the same additive offset is already a ~1.8e-7 relative
        # perturbation -- which is why that fit carries the wider delta.
        self.assertAlmostEqual(
            self.metrics["time_convergence_order"], 4.019322768300311, delta=1e-6
        )
        self.assertAlmostEqual(
            self.metrics["time_convergence_order_multi_dt"],
            4.011072118935021, delta=1e-5,
        )
        self.assertAlmostEqual(self.metrics["time_convergence_order"], 4.0, delta=0.05)
        self.assertAlmostEqual(
            self.metrics["time_convergence_order_multi_dt"], 4.0, delta=0.05
        )

    def test_ifrk4_richardson_ladder_proves_fourth_order_scaling(self) -> None:
        """O(dt^4) as a limit law over three refinements, not as one decimal.

        For a scheme whose leading truncation term is exactly ``C dt^4``, the
        successive Richardson ratios ``p_j = log2(E_j / E_{j+1})`` tend to 4,
        and the excess ``p_j - 4`` -- produced by the next, O(dt^5) term --
        halves every time dt halves.  Both statements hold on the measured
        ladder, level by level:

        ======  ===========  ==============  ====================
        level   dt           p_j             p_j - 4 (ratio to prior)
        ======  ===========  ==============  ====================
        0       5.0000e-02   4.0193227683    1.9323e-02
        1       2.5000e-02   4.0096150566    9.6151e-03  (0.4976)
        2       1.2500e-02   4.0049883368    4.9883e-03  (0.5188)
        ======  ===========  ==============  ====================

        The difference form ``|E_j - E_{j+1}| / |E_{j+1} - E_{j+2}|`` is the
        quantity to anchor hard: subtracting two errors cancels their common
        round-off offset, so it is reproducible to 2e-9 across backends and can
        be pinned at 1e-6 without constraining the arithmetic.  Its measured
        values 16.22293635709301 and 16.110416021550055 bracket 16 = 2**4, and
        their excesses over 16 halve as well (0.11041602 / 0.22293636 = 0.4953).

        The ladder stops at four error levels on purpose.  A fifth (dt/16,
        measured error 9.108e-12) would form ``p_3 = log2(E3 / E4)``, and there
        the round-off offset is a ~2.9e-6 relative perturbation of the error:
        ``p_3`` was measured at 3.9951609114 / 3.9951560326, i.e. it dips below
        4 and reproducibility degrades to ~5e-6 -- three orders of magnitude
        worse than ``p_0``.  A pin that deep would be measuring the backend
        again, which is the mistake this rewrite removes.
        """
        errors = self._mms_error_ladder(levels=4)
        self.assertEqual(len(errors), 4)
        for err in errors:
            self.assertGreater(err, 0.0)
            self.assertTrue(math.isfinite(err))
        # The ladder really is refining: each level is at least 10x better
        # than the last, so no ratio below is taken from a stalled run.
        for level in range(1, len(errors)):
            self.assertLess(errors[level] * 10.0, errors[level - 1])

        # 1. Successive order ratios converge on the design order 4.
        ratios = [
            math.log2(errors[level] / errors[level + 1])
            for level in range(len(errors) - 1)
        ]
        for ratio in ratios:
            self.assertAlmostEqual(ratio, 4.0, delta=0.08)

        # 2. The excess above 4 halves as dt halves: leading term is dt^4,
        #    contaminating term is dt^5.  This is the convergence-order proof;
        #    a scheme that was merely "close to 4th order at one dt" fails it.
        excess = [ratio - 4.0 for ratio in ratios]
        self.assertGreater(excess[0], 0.0)
        for level in range(1, 3):
            self.assertAlmostEqual(
                excess[level] / excess[level - 1], 0.5, delta=0.05,
                msg=f"excess halving broken at level {level}: {excess}",
            )

        # 3. Difference form: offset-cancelling, hence anchorable to 1e-6.
        diffs = [
            abs(errors[level] - errors[level + 1])
            for level in range(len(errors) - 1)
        ]
        diff_ratios = [
            diffs[level] / diffs[level + 1] for level in range(len(diffs) - 1)
        ]
        self.assertAlmostEqual(diff_ratios[0], 16.22293635709301, delta=1e-6)
        for diff_ratio in diff_ratios:
            self.assertGreater(diff_ratio, 16.0)
            self.assertLess(diff_ratio, 16.5)
        self.assertAlmostEqual(
            (diff_ratios[1] - 16.0) / (diff_ratios[0] - 16.0), 0.5, delta=0.05
        )

        # 4. The ladder's level 0 must agree with the headline metric the
        #    benchmark publishes, so the two cannot drift apart silently.
        self.assertAlmostEqual(
            ratios[0], self.metrics["time_convergence_order"], delta=1e-9
        )

    def test_nonlinearity_is_not_saturated(self) -> None:
        # The saturation guard: exactly 1/2 on the Taylor-Green carrier and
        # round-off on the Beltrami one.  If the first collapses toward the
        # second the benchmark is measuring FFT round-trip noise again.
        self.assertAlmostEqual(self.metrics["nonlinear_activity"], 0.5, delta=1e-12)
        self.assertLess(self.metrics["nonlinear_activity_abc"], 1e-12)

    def test_conservation_floors(self) -> None:
        self.assertLess(self.metrics["inviscid_energy_drift"], 1e-8)
        self.assertLess(self.metrics["energy_decay_rel_error"], 1e-13)
        self.assertLess(self.metrics["divergence_linf"], 1e-14)
        self.assertLess(self.metrics["tgv_divergence_linf"], 1e-14)

    def test_exactly_one_instance_reports_a_throughput(self) -> None:
        """Regression guard for a bug that silently voided the headline.

        run_mms and run_tgv both used to write a key named
        spectral_grid_updates_per_s into one shared dict; --case all ran mms
        then tgv, so the published headline was the TGV timing and the MMS
        timing was overwritten and lost.  Timing belongs to run_throughput
        alone.
        """
        horizon = self.SMOKE["final_time"]
        g, s, v = self.SMOKE["grid"], self.SMOKE["steps"], self.SMOKE["viscosity"]
        rate_keys = set()
        for produced in (
            bench.run_mms(g, s, v, horizon),
            bench.run_tgv(g, s, v, horizon),
            bench.run_abc(g, s, v, self.SMOKE["dt"]),
        ):
            rate_keys |= {k for k in produced if "per_s" in k}
        self.assertEqual(
            rate_keys, set(),
            f"accuracy instance reports a rate and will collide: {rate_keys}",
        )
        self.assertIn(
            "spectral_grid_updates_per_s",
            bench.run_throughput(g, s, v, horizon, 1, 0),
        )

    def test_timing_is_stamped_with_its_clock_and_thread_invariant(self) -> None:
        timed = bench.run_throughput(16, 6, 0.05, 1.0, 3, 1)
        self.assertEqual(timed["timing_clock"], "cpu_process_time_best_of_n")
        # CPU time only stands in for quiet-host wall time while the process
        # is single-threaded; the run must say which it was.
        self.assertIn("timing_single_threaded", timed)
        self.assertLessEqual(timed["timing_cpu_over_wall"], 1.05)
        self.assertGreater(timed["spectral_grid_updates_per_s"], 0.0)

    def test_thread_caps_are_pinned_before_numpy_loads(self) -> None:
        for var in ("OMP_NUM_THREADS", "MKL_NUM_THREADS", "OPENBLAS_NUM_THREADS",
                    "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS"):
            self.assertIsNotNone(os.environ.get(var), f"{var} not pinned")


if __name__ == "__main__":
    unittest.main()
