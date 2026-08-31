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
    """Pins on the reported metrics at the registered smoke resolution.

    Values recorded 2026-08-31 and cross-checked against the pre-optimisation
    commit 0c4b08a in a separate worktree.  These are analytic properties of
    the discretisation, not timings, so they are reproducible to the last bit
    on any IEEE-754 host: an exact manufactured solution, the design order of
    the integrator, a grid-independent carrier invariant, and two round-off
    floors.  A change here means the mathematics moved and wants explaining,
    not a tolerance widening.
    """

    SMOKE = dict(grid=16, steps=20, viscosity=0.05, dt=0.05, case="all",
                 final_time=1.0)

    @classmethod
    def setUpClass(cls) -> None:
        cls.metrics = bench.solve(reps=1, warmup=0, **cls.SMOKE)

    def test_manufactured_solution_error(self) -> None:
        self.assertAlmostEqual(
            self.metrics["l2_rel_error"], 6.0906254951665697e-07, delta=1e-15
        )

    def test_integrator_realises_design_order_four(self) -> None:
        # IFRK4 is fourth order; both the two-point ratio and the five-point
        # log-log fit must land on 4, which is the registered anchor
        # navier.spectral.ifrk4_time_order.
        self.assertAlmostEqual(
            self.metrics["time_convergence_order"], 4.0193227690092499, delta=1e-12
        )
        self.assertAlmostEqual(self.metrics["time_convergence_order"], 4.0, delta=0.05)
        self.assertAlmostEqual(
            self.metrics["time_convergence_order_multi_dt"], 4.0, delta=0.05
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
