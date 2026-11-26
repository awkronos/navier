#!/usr/bin/env python3
"""Tests for scripts/ns_paired_benchmark.py — the paired A/B solver benchmark
and the two negative controls the lane brief asks for.

Skipped wholesale when numpy is unavailable, exactly like the repo's other
solver tests (`test_navier_solver_equivalence.py`, `test_navier_adaptive_bench.py`):
CI's python job installs no scientific stack, so a missing numpy here is the
supported degraded configuration, never a failure.

What this file pins, in order of the brief's requirements:

  1. the mass-escape control's *logical shape* — that the naive pointwise +
     bounded-energy instruments pass at every sampled time while the
     tail-aware L2 instrument fails at every sampled time. This is the whole
     point of the control (it mirrors commit 80540a2's obstruction) and the
     only thing here that could be silently broken by an editing mistake in
     `mass_escape_witness` without any other test noticing.
  2. that the smooth-shear control still does not raise a false blowup alarm.
  3. that the paired benchmark's "delta" fields are real differences between
     the two arms, not a copy of one arm's own value (a defect this module
     actually had and had to be fixed for).
  4. receipt determinism where determinism is claimed, and the round-trip
     through `write_receipt`/`payload_sha256`.
  5. that the scope separation required by the brief — this is not a
     regularity/breakdown/Clay A-B/C-D result — is present verbatim in the
     emitted artifact, so a future edit that drops it fails a test instead of
     silently widening what the receipt appears to claim.
"""

from __future__ import annotations

import hashlib
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(
    0,
    os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "scripts"),
)

try:
    import numpy as np

    import ns_paired_benchmark as pbench
except ImportError as exc:  # pragma: no cover - environment without numpy
    raise unittest.SkipTest(f"solver stack unavailable: {exc}") from exc

# Small fixed configuration: every numerical assertion below is on a
# deterministic (no RNG, no timing) quantity for these exact arguments, so it
# can be pinned tightly instead of with a loose tolerance.
SMALL = dict(grid=12, steps=8, dt=0.05, viscosity=0.05)


class MassEscapeControlTest(unittest.TestCase):
    """Requirement 2(b): the 80540a2 witness, reproduced numerically.

    These are the assertions that make the control worth having at all: the
    naive pair of checks must pass (no escape detected), and the tail-aware
    invariant must fail (escape detected), at the same sampled times.
    """

    @classmethod
    def setUpClass(cls) -> None:
        cls.witness = pbench.mass_escape_witness()

    def test_naive_checks_pass_and_the_tail_invariant_fails(self):
        self.assertTrue(
            self.witness["naive_checks_miss_the_escape"],
            "the naive pointwise + bounded-energy checks must be satisfied "
            "while the tail-aware L2 invariant is not — that gap IS the "
            "obstruction this control exists to reproduce",
        )
        self.assertTrue(self.witness["tail_invariant_catches_the_escape"])
        self.assertFalse(self.witness["l2_gap_tends_to_zero"])

    def test_pointwise_max_on_the_central_window_decays_to_zero(self):
        series = self.witness["naive_pointwise_max_on_central_window"]
        self.assertTrue(self.witness["naive_pointwise_converges_to_zero"])
        self.assertGreater(series[0], 0.5)
        self.assertLess(series[-1], 1e-9)
        for earlier, later in zip(series, series[1:]):
            self.assertLessEqual(later, earlier + 1e-12)

    def test_energy_is_bounded_flat_and_the_initial_slice_is_zero(self):
        self.assertEqual(self.witness["initial_slice_energy"], 0.0)
        self.assertTrue(self.witness["naive_energy_bounded_and_flat"])
        self.assertLess(self.witness["naive_energy_relative_spread"], 1e-9)

    def test_l2_gap_series_is_constant_nonzero(self):
        gap = self.witness["l2_gap_to_initial_slice"]
        self.assertGreater(min(gap), 1e-3)
        # Translation-invariant bump: the gap over the tracking window is the
        # same number at every sampled time, not a drifting one.
        self.assertAlmostEqual(max(gap) - min(gap), 0.0, delta=1e-9)

    def test_tail_mass_fraction_grows_to_one(self):
        fractions = self.witness["tail_mass_fraction_outside_central_window"]
        self.assertTrue(self.witness["tail_fraction_is_non_decreasing"])
        self.assertGreater(fractions[-1], 0.99)

    def test_witness_is_deterministic_across_calls(self):
        # No RNG, no wall-clock anywhere in this function: two calls in the
        # same process must agree to the last bit.
        again = pbench.mass_escape_witness()
        self.assertEqual(
            pbench.canonical_json(self.witness), pbench.canonical_json(again)
        )

    def test_rejects_impossible_grid_and_radius_arguments(self):
        with self.assertRaises(ValueError):
            pbench.mass_escape_witness(central_grid=8)
        with self.assertRaises(ValueError):
            pbench.mass_escape_witness(sigma=1.0, track_radius=2.0)
        with self.assertRaises(ValueError):
            pbench.mass_escape_witness(escape_times=(0.0, 0.5))

    def test_scope_note_denies_being_an_ns_evolution(self):
        self.assertIn("not a Navier-Stokes evolution", self.witness["scope_note"])


class SmoothShearNegativeControlTest(unittest.TestCase):
    """Requirement 2(a): bounded-energy smooth shear must not alarm."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.control = pbench.smooth_shear_negative_control(
            SMALL["grid"], SMALL["steps"], SMALL["dt"]
        )

    def test_no_false_blowup_alarm(self):
        self.assertFalse(self.control["ever_underresolved"])
        self.assertFalse(
            self.control["false_blowup_alarm"],
            "an exact steady Euler state must never raise the under-resolved "
            "flag; if this fires, the diagnostic is measuring its own "
            "discretisation error and every other use of it is suspect",
        )

    def test_stationary_state_stays_stationary(self):
        self.assertLess(self.control["velocity_linf_drift"], 1e-12)
        self.assertLess(self.control["vorticity_linf_drift"], 1e-12)
        self.assertLess(self.control["energy_drift_rel"], 1e-12)


class PairedBenchmarkTest(unittest.TestCase):
    """Requirement 2(a): the A/B pair itself, differing only in `dealias`."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.pair = pbench.paired_solver_benchmark(**SMALL)

    def test_three_arms_are_present_and_differ_only_in_the_dealias_flag(self):
        for section in ("inviscid_energy_conservation", "tgv", "mms"):
            self.assertIn(section, self.pair)
            arm = self.pair[section]
            self.assertFalse(arm["baseline"]["dealias"])
            self.assertTrue(arm["improved"]["dealias"])
            self.assertEqual(arm["baseline"]["grid"], arm["improved"]["grid"])

    def test_inviscid_energy_drift_is_round_off_on_both_arms(self):
        inviscid = self.pair["inviscid_energy_conservation"]
        self.assertLess(inviscid["baseline"]["energy_drift_rel"], 1e-8)
        self.assertLess(inviscid["improved"]["energy_drift_rel"], 1e-8)

    def test_delta_fields_are_real_differences_not_copies(self):
        """The `tgv` arm's delta used to be a mislabelled copy of the improved
        arm's own `energy_drift_rel` (which for a viscous run measures physical
        dissipation, not a solver difference at all). This pins that every
        `delta` value equals `improved - baseline` for its own section."""
        for section in ("inviscid_energy_conservation", "tgv", "mms"):
            arm = self.pair[section]
            baseline, improved, delta = arm["baseline"], arm["improved"], arm["delta"]
            for key, value in delta.items():
                if key == "energy_drift_rel":
                    expect = improved["energy_drift_rel"] - baseline["energy_drift_rel"]
                elif key == "divergence_linf_final":
                    expect = improved["divergence_linf_final"] - baseline["divergence_linf_final"]
                elif key == "enstrophy_final":
                    expect = improved["enstrophy_final"] - baseline["enstrophy_final"]
                elif key == "high_frequency_energy_fraction_final":
                    expect = (
                        improved["blowup_diagnostic"]["high_frequency_energy_fraction"]["final"]
                        - baseline["blowup_diagnostic"]["high_frequency_energy_fraction"]["final"]
                    )
                elif key == "relative_l2_error":
                    expect = (
                        improved["mms_relative_l2_error"] - baseline["mms_relative_l2_error"]
                    )
                elif key == "relative_linf_error":
                    expect = (
                        improved["mms_relative_linf_error"] - baseline["mms_relative_linf_error"]
                    )
                else:  # pragma: no cover - guard against a new, unpinned delta key
                    self.fail(f"unpinned delta key {key!r} in section {section!r}")
                self.assertAlmostEqual(value, expect, delta=1e-18)

    def test_dealiasing_does_not_hurt_mms_accuracy(self):
        mms = self.pair["mms"]
        self.assertLessEqual(
            mms["delta"]["relative_l2_error"],
            0.0,
            "the 2/3-dealiased arm should be at least as accurate as the "
            "undealiased baseline on the manufactured solution",
        )

    def test_every_arm_reports_latency_and_memory(self):
        for section in ("inviscid_energy_conservation", "tgv", "mms"):
            arm = self.pair[section]
            for which in ("baseline", "improved"):
                run = arm[which]
                latency = run["step_latency_ms"]
                self.assertEqual(latency["samples"], SMALL["steps"])
                self.assertLessEqual(latency["p50"], latency["p95"])
                self.assertLessEqual(latency["min"], latency["max"])
                self.assertGreater(latency["p50"], 0.0)
                memory = run["memory"]
                self.assertGreater(memory["traced_peak_bytes"], 0)
                self.assertGreaterEqual(memory["live_allocation_blocks_after_run"], 0)

    def test_divergence_stays_machine_precision_after_the_run(self):
        for section in ("inviscid_energy_conservation", "tgv", "mms"):
            for which in ("baseline", "improved"):
                run = self.pair[section][which]
                self.assertLess(run["divergence_linf_final"], 1e-13)


class GridConvergenceTest(unittest.TestCase):
    """Requirement 2's "grid convergence rate" leg."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.conv = pbench.grid_convergence_rate(
            "mms", SMALL["viscosity"], SMALL["steps"] * SMALL["dt"], (12, 16), dealias=True
        )

    def test_finer_grid_has_smaller_error_and_positive_order(self):
        self.assertGreater(self.conv["error_reduction_ratio"], 1.0)
        self.assertLess(
            self.conv["fine"]["relative_l2_error"], self.conv["coarse"]["relative_l2_error"]
        )
        self.assertGreater(self.conv["equivalent_polynomial_order"], 2.0)

    def test_rejects_a_third_grid_and_odd_grids(self):
        with self.assertRaises(ValueError):
            pbench.grid_convergence_rate("mms", 0.05, 1.0, (12, 16, 20), True)
        with self.assertRaises(ValueError):
            pbench.grid_convergence_rate("mms", 0.05, 1.0, (12, 15), True)


class ReplayKeyTest(unittest.TestCase):
    """Requirement 2's "exact source SHA and replay keys" leg."""

    def test_obstruction_provenance_is_stamped(self):
        keys = pbench.replay_keys()
        self.assertEqual(len(keys["obstruction_commit"]), 40)
        self.assertEqual(keys["obstruction_commit"], pbench.OBSTRUCTION_COMMIT)
        self.assertEqual(
            keys["obstruction_axioms"], ["propext", "Classical.choice", "Quot.sound"]
        )
        self.assertEqual(keys["navier_commit"], pbench.navier_source_sha())

    def test_source_digests_include_this_test_file_and_the_benchmark(self):
        keys = pbench.replay_keys()
        digests = keys["source_sha256"]
        self.assertIn("scripts/ns_paired_benchmark.py", digests)
        self.assertIn("tests/test_ns_paired_benchmark.py", digests)
        self.assertIsNone(keys["random_seed"])
        self.assertTrue(keys["thread_caps_pinned"])

    def test_replay_keys_are_deterministic_within_a_process(self):
        self.assertEqual(
            pbench.canonical_json(pbench.replay_keys()),
            pbench.canonical_json(pbench.replay_keys()),
        )


class ReceiptTest(unittest.TestCase):
    """The hermetic receipt: write it, read it back, recompute its digest."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.receipt = pbench.build_receipt(
            SMALL["grid"], SMALL["steps"], SMALL["dt"], SMALL["viscosity"], (12, 16)
        )

    def test_write_then_read_round_trips_and_digest_matches_body(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "receipt.json"
            written = pbench.write_receipt(self.receipt, output)
            self.assertTrue(output.is_file())
            stored = json.loads(output.read_text())
            self.assertEqual(written["payload_sha256"], stored["payload_sha256"])
            recomputed = pbench.canonical_json(stored["payload"])
            self.assertEqual(
                hashlib.sha256(recomputed.encode("utf-8")).hexdigest(),
                stored["payload_sha256"],
            )

    def test_receipt_carries_every_required_metric_family(self):
        paired = self.receipt["paired_solver_benchmark"]
        mms_improved = paired["mms"]["improved"]
        self.assertIn("mms_relative_l2_error", mms_improved)
        self.assertIn("mms_relative_linf_error", mms_improved)
        self.assertIn("divergence_linf_final", mms_improved)
        self.assertIn("energy_drift_rel", paired["inviscid_energy_conservation"]["baseline"])
        self.assertIn("step_latency_ms", mms_improved)
        self.assertIn("memory", mms_improved)
        self.assertIn("error_reduction_ratio", self.receipt["grid_convergence"])
        self.assertIn("equivalent_polynomial_order", self.receipt["grid_convergence"])
        controls = self.receipt["negative_controls"]
        self.assertEqual(set(controls), {"smooth_shear", "mass_escape"})
        self.assertFalse(controls["smooth_shear"]["false_blowup_alarm"])
        self.assertTrue(controls["mass_escape"]["naive_checks_miss_the_escape"])
        self.assertTrue(controls["mass_escape"]["tail_invariant_catches_the_escape"])

    def test_scope_separation_is_in_the_emitted_artifact(self):
        """Requirement 1: this receipt is never a regularity, finite-time
        breakdown, or Clay A/B / forced C-D result — pin that the emitted
        artifact says so, in both its own words and the mass-escape control's
        own, so a silent edit that widens the claim fails here."""
        scope = self.receipt["scope_note"]
        for phrase in (
            "Does not establish",
            "global regularity",
            "finite-time breakdown",
            "Clay A/B",
            "forced C/D",
            pbench.OBSTRUCTION_COMMIT,
        ):
            self.assertIn(phrase, scope)
        self.assertIn("not a Navier-Stokes evolution", self.receipt[
            "negative_controls"]["mass_escape"]["scope_note"
        ])

    def test_blowup_diagnostic_series_is_populated_and_finite(self):
        for section in ("inviscid_energy_conservation", "tgv", "mms"):
            for which in ("baseline", "improved"):
                diag = self.receipt["paired_solver_benchmark"][section][which]["blowup_diagnostic"]
                for key in (
                    "velocity_linf",
                    "vorticity_linf",
                    "strain_frobenius_linf",
                    "high_frequency_energy_fraction",
                ):
                    triple = diag[key]
                    self.assertIn("initial", triple)
                    self.assertIn("final", triple)
                    self.assertIn("max", triple)
                    self.assertTrue(np.isfinite(triple["max"]))
                self.assertGreater(len(diag["energy_series"]), 0)


class PercentileHelperTest(unittest.TestCase):
    def test_nearest_rank_boundaries(self):
        values = [1.0, 2.0, 3.0, 4.0]
        self.assertEqual(pbench._percentile(values, 0.0), 1.0)
        self.assertEqual(pbench._percentile(values, 0.5), 2.0)
        self.assertEqual(pbench._percentile(values, 0.95), 4.0)
        self.assertEqual(pbench._percentile(values, 1.0), 4.0)

    def test_rejects_empty_and_out_of_range(self):
        with self.assertRaises(ValueError):
            pbench._percentile([], 0.5)
        with self.assertRaises(ValueError):
            pbench._percentile([1.0], 1.5)


if __name__ == "__main__":
    unittest.main()
