"""Continuum-manufactured forcing exercises the consumer, not its RHS oracle."""

import math
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
try:
    import navier_adaptive_bench as bench
    import navier_spectral_core as core
except ImportError as exc:
    raise unittest.SkipTest(f"solver stack unavailable: {exc}") from exc


class AnalyticForcingTest(unittest.TestCase):
    def test_continuum_forcing_fourth_order(self):
        sp = core.spectral(8)
        exact, forcing = bench.analytic_taylor_green_problem(sp, 0.05)
        errors = []
        for steps in (4, 8, 16):
            got = core.evolve(exact(0), sp, 0.05, 0.4 / steps, steps, True, forcing)
            errors.append(core.relative_l2(got, exact(0.4), sp))
        self.assertGreater(math.log2(errors[0] / errors[1]), 3.8)
        self.assertGreater(math.log2(errors[1] / errors[2]), 3.8)

    def test_adaptive_refinement_consumer(self):
        result = bench.run_refinement(grids=(8, 12), final_time=0.4, initial_dt=0.4,
                                      rtol=1e-8, atol=1e-11)
        for row in result["runs"]:
            self.assertEqual(row["final_time"], 0.4)
            self.assertGreater(row["accepted_steps"], 0)
            self.assertLess(row["relative_l2_error"], 2e-7)
            self.assertFalse(row["underresolved"])

    def test_grid_validation(self):
        for grids in ((), (7,), (9,), (12, 8), (8, 8), (True,)):
            with self.subTest(grids=grids), self.assertRaises(ValueError):
                bench.run_refinement(grids=grids)


if __name__ == "__main__":
    unittest.main()
