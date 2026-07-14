"""Regression tests for the exact observation-only symmetrized triad scan."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXPERIMENTS = ROOT / "experiments"
if str(EXPERIMENTS) not in sys.path:
    sys.path.insert(0, str(EXPERIMENTS))

from exact_symmetrized_triad_scan import (  # noqa: E402
    OLD_CANCELLING_WITNESS,
    UNEQUAL_RADIUS_WITNESS,
    GaussianRational,
    TriadConfiguration,
    divergence_free_polarizations,
    dot,
    scan_exact_triads,
    six_mode_coefficients,
    six_mode_leakage,
    squared_frequency_weighted_sum,
    symmetrized_receiver_rates,
    validate_configuration,
)


class ExactSymmetrizedTriadTests(unittest.TestCase):
    def test_known_witnesses_are_exact_divergence_free_triads(self) -> None:
        for witness in (OLD_CANCELLING_WITNESS, UNEQUAL_RADIUS_WITNESS):
            validate_configuration(witness)
            self.assertEqual(
                tuple(sum(entries) for entries in zip(witness.k, witness.l, witness.m)),
                (0, 0, 0),
            )
            self.assertEqual(dot(witness.k, witness.a), 0)
            self.assertEqual(dot(witness.l, witness.b), 0)
            self.assertEqual(dot(witness.m, witness.c), 0)

    def test_old_selected_output_cancels_after_symmetrization(self) -> None:
        rates = symmetrized_receiver_rates(OLD_CANCELLING_WITNESS)
        self.assertEqual(rates.as_tuple(), (1, -1, 0))
        self.assertEqual(rates.m, 0)
        self.assertEqual(rates.total, 0)

    def test_unequal_radius_witness_has_exact_weighted_transfer(self) -> None:
        rates = symmetrized_receiver_rates(UNEQUAL_RADIUS_WITNESS)
        self.assertEqual(rates.as_tuple(), (0, -1, 1))
        self.assertEqual(rates.total, 0)
        self.assertEqual(
            squared_frequency_weighted_sum(UNEQUAL_RADIUS_WITNESS, rates), 1
        )

    def test_constructive_polarizations_are_nonzero_and_divergence_free(self) -> None:
        wave = (1, 2, -1)
        candidates = divergence_free_polarizations(wave, 2)
        self.assertTrue(candidates)
        self.assertEqual(candidates, divergence_free_polarizations(wave, 2))
        for candidate in candidates:
            self.assertNotEqual(candidate, (0, 0, 0))
            self.assertEqual(dot(wave, candidate), 0)

    def test_scan_is_deterministic_and_finds_unequal_shell_transfer(self) -> None:
        first = scan_exact_triads(1, 1)
        second = scan_exact_triads(1, 1)
        self.assertEqual(first, second)
        self.assertGreater(first.triad_count, 0)
        self.assertGreater(len(first.unequal_shell_transfer_cases), 0)
        configurations = {
            case.configuration for case in first.unequal_shell_transfer_cases
        }
        self.assertIn(UNEQUAL_RADIUS_WITNESS.canonical(), configurations)
        for case in first.unequal_shell_transfer_cases:
            self.assertEqual(case.rates.total, 0)
            self.assertNotEqual(case.weighted_sum, 0)

    def test_non_divergence_free_tuple_is_rejected(self) -> None:
        invalid = TriadConfiguration(
            k=(1, 0, 0), l=(0, 1, 0), m=(-1, -1, 0),
            a=(1, 1, 1), b=(1, 0, 0), c=(1, -1, 1),
        )
        with self.assertRaisesRegex(ValueError, "not divergence-free"):
            symmetrized_receiver_rates(invalid)

    def test_six_mode_table_is_conjugate_and_leaks_exactly(self) -> None:
        coefficients = six_mode_coefficients(UNEQUAL_RADIUS_WITNESS)
        for wave, coefficient in coefficients.items():
            opposite = coefficients[tuple(-entry for entry in wave)]
            self.assertEqual(opposite, tuple(entry.conjugate() for entry in coefficient))
        first = six_mode_leakage(UNEQUAL_RADIUS_WITNESS)
        second = six_mode_leakage(UNEQUAL_RADIUS_WITNESS)
        self.assertEqual(first, second)
        self.assertFalse(first.is_closed)
        self.assertEqual(first.off_support_ordered_pairs, 24)
        self.assertEqual(first.off_support_outputs, 13)
        self.assertEqual(len(first.nonzero_outputs), 6)
        leakage = first.nonzero_outputs[0]
        self.assertEqual(leakage.output, (-2, -1, 0))
        self.assertEqual(
            leakage.ordered_pairs,
            (
                ((-1, -1, 0), (-1, 0, 0)),
                ((-1, 0, 0), (-1, -1, 0)),
            ),
        )
        self.assertEqual(
            leakage.coefficient,
            (
                GaussianRational(Fraction(1, 5), Fraction(0)),
                GaussianRational(Fraction(-2, 5), Fraction(0)),
                GaussianRational(Fraction(2), Fraction(0)),
            ),
        )
        for item in first.nonzero_outputs:
            self.assertEqual(
                sum(
                    Fraction(component) * entry.real
                    for component, entry in zip(
                        item.output, item.coefficient, strict=True
                    )
                ),
                0,
            )
            self.assertEqual(
                sum(
                    Fraction(component) * entry.imag
                    for component, entry in zip(
                        item.output, item.coefficient, strict=True
                    )
                ),
                0,
            )

    def test_cli_is_explicitly_falsification_only(self) -> None:
        completed = subprocess.run(
            [
                sys.executable,
                str(EXPERIMENTS / "exact_symmetrized_triad_scan.py"),
                "--max-examples",
                "1",
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=True,
        )
        report = json.loads(completed.stdout)
        self.assertEqual(report["status"], "FALSIFICATION_ONLY")
        self.assertFalse(report["closes_clay_endpoint"])
        self.assertFalse(report["six_mode_leakage"]["closed_under_projected_convolution"])
        self.assertNotIn("PROVED", completed.stdout)


if __name__ == "__main__":
    unittest.main()
