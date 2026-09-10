"""Regression tests for the cross-backend finite-grid diagnostic contract."""

import math
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import navier_diagnostic_score as score


def exact_shear_diagnostic(*, viscosity: float, mode: int, final_time: float, steps: int):
    """Analytic u=(exp(-nu*m^2*t) sin(my),0,0) observation record."""
    decay_rate = 2.0 * viscosity * mode**2
    initial_energy = 0.25
    times = [final_time * index / steps for index in range(steps + 1)]

    def energy(time):
        return initial_energy * math.exp(-decay_rate * time)

    rates = [decay_rate * energy(time) for time in times]
    cumulative = math.fsum(
        0.5 * (rates[index] + rates[index + 1]) * (times[index + 1] - times[index])
        for index in range(steps)
    )
    final_energy = energy(final_time)
    defect = final_energy + cumulative - initial_energy
    final_rate = rates[-1]
    return {
        "time": final_time,
        "energy": final_energy,
        "enstrophy": final_rate / (2.0 * viscosity),
        "divergenceRms": 0.0,
        "energyDissipationRate": final_rate,
        "highFrequencyEnergyFraction": 0.0,
        "tailTolerance": 1.0e-8,
        "initialEnergy": initial_energy,
        "cumulativeEnergyDissipation": cumulative,
        "energyBalanceDefect": defect,
        "energyBalanceRelativeError": defect / initial_energy,
        "meanEnergyDissipationRate": cumulative / final_time,
        "minimumSampledEnergyDissipationRate": final_rate,
        "minimumSampledDissipationTime": final_time,
        "energyBudgetStartTime": 0.0,
        "energyBudgetEndTime": final_time,
        "energyBudgetMaxInterval": final_time / steps,
        "energyBudgetSamples": steps + 1,
        "energyBudgetQuadrature": "trapezoidal-diagnostics-observations",
        "energyBalanceApplicable": True,
        "underresolved": False,
        "finite": True,
    }


class DiagnosticScoreTest(unittest.TestCase):
    def test_reset_seed_is_one_observation_and_zero_trapezoids(self):
        viscosity = 0.05
        mode = 2
        current_rate = 0.5 * viscosity * mode**2
        diagnostic = exact_shear_diagnostic(
            viscosity=viscosity, mode=mode, final_time=1.0, steps=20
        )
        diagnostic.update(
            time=0.0,
            energy=0.25,
            enstrophy=mode**2 / 4.0,
            energyDissipationRate=current_rate,
            initialEnergy=0.25,
            cumulativeEnergyDissipation=0.0,
            energyBalanceDefect=0.0,
            energyBalanceRelativeError=0.0,
            meanEnergyDissipationRate=current_rate,
            minimumSampledEnergyDissipationRate=current_rate,
            minimumSampledDissipationTime=0.0,
            energyBudgetStartTime=0.0,
            energyBudgetEndTime=0.0,
            energyBudgetMaxInterval=0.0,
            energyBudgetSamples=1,
        )
        result = score.evaluate_energy_diagnostic(
            diagnostic,
            viscosity=viscosity,
            energy_balance_relative_tolerance=0.0,
            divergence_rms_tolerance=0.0,
            identity_relative_tolerance=64.0 * sys.float_info.epsilon,
        )
        self.assertTrue(result["pass"], result["failedChecks"])
        self.assertEqual(result["measured"]["observationIntervalMean"], 0.0)

    def test_exact_viscous_shear_obeys_analytic_trapezoid_bound(self):
        viscosity = 0.05
        mode = 2
        final_time = 1.0
        steps = 20
        diagnostic = exact_shear_diagnostic(
            viscosity=viscosity, mode=mode, final_time=final_time, steps=steps
        )
        interval = final_time / steps
        decay_rate = 2.0 * viscosity * mode**2
        # Composite trapezoid error: T*h^2*max|D''|/12.  Here
        # D(t)=lambda*E0*exp(-lambda*t); division by E0 cancels E0.
        analytic_relative_bound = final_time * interval**2 * decay_rate**3 / 12.0
        result = score.evaluate_energy_diagnostic(
            diagnostic,
            viscosity=viscosity,
            energy_balance_relative_tolerance=(
                analytic_relative_bound + 32.0 * sys.float_info.epsilon
            ),
            divergence_rms_tolerance=1.0e-14,
            identity_relative_tolerance=64.0 * sys.float_info.epsilon,
        )
        self.assertTrue(result["pass"], result["failedChecks"])
        self.assertEqual(result["quadrature"]["cadence"], "diagnostic observation endpoints")
        self.assertIn("does not verify", result["scope"])

    def test_exact_shear_defect_converges_at_trapezoid_order(self):
        coarse = exact_shear_diagnostic(viscosity=0.05, mode=2, final_time=1.0, steps=20)
        fine = exact_shear_diagnostic(viscosity=0.05, mode=2, final_time=1.0, steps=40)
        comparison = score.compare_observation_cadence(
            coarse, fine, uniform_observation_cadence=True
        )
        self.assertTrue(comparison["refinementReducesAbsoluteDefect"])
        self.assertAlmostEqual(comparison["observedDefectOrder"], 2.0, delta=0.01)

    def test_corrupt_balance_and_resolution_flag_fail_closed(self):
        diagnostic = exact_shear_diagnostic(
            viscosity=0.05, mode=2, final_time=1.0, steps=20
        )
        diagnostic["energyBalanceDefect"] *= 0.5
        diagnostic["underresolved"] = True
        result = score.evaluate_energy_diagnostic(
            diagnostic,
            viscosity=0.05,
            energy_balance_relative_tolerance=1.0,
            divergence_rms_tolerance=1.0,
            identity_relative_tolerance=1.0e-12,
        )
        self.assertFalse(result["pass"])
        self.assertIn("energy_balance_defect_is_reproducible", result["failedChecks"])
        self.assertIn("spatial_resolution_flag_clear", result["failedChecks"])

    def test_forced_or_other_inapplicable_budget_fails_closed(self):
        diagnostic = exact_shear_diagnostic(
            viscosity=0.05, mode=2, final_time=1.0, steps=20
        )
        diagnostic["energyBalanceApplicable"] = False
        result = score.evaluate_energy_diagnostic(
            diagnostic,
            viscosity=0.05,
            energy_balance_relative_tolerance=1.0,
            divergence_rms_tolerance=1.0,
            identity_relative_tolerance=1.0e-12,
        )
        self.assertFalse(result["pass"])
        self.assertIn("energy_budget_is_applicable", result["failedChecks"])

    def test_raw_cpu_legacy_aliases_are_normalized_but_conflicts_fail(self):
        diagnostic = exact_shear_diagnostic(
            viscosity=0.05, mode=2, final_time=1.0, steps=20
        )
        for legacy, current in score.CPU_LEGACY_ALIASES.items():
            diagnostic[legacy] = diagnostic.pop(current)
        result = score.evaluate_energy_diagnostic(
            diagnostic,
            viscosity=0.05,
            energy_balance_relative_tolerance=1.0,
            divergence_rms_tolerance=1.0,
            identity_relative_tolerance=1.0e-12,
        )
        self.assertTrue(result["pass"], result["failedChecks"])

        diagnostic["divergenceRms"] = 1.0
        conflict = score.evaluate_energy_diagnostic(
            diagnostic,
            viscosity=0.05,
            energy_balance_relative_tolerance=1.0,
            divergence_rms_tolerance=1.0,
            identity_relative_tolerance=1.0e-12,
        )
        self.assertFalse(conflict["pass"])
        self.assertIn("legacy_aliases_do_not_conflict", conflict["failedChecks"])

    def test_missing_or_nonfinite_diagnostics_fail_without_nan_output(self):
        for diagnostic in ({}, {name: 0.0 for name in score.REQUIRED_FIELDS}):
            with self.subTest(diagnostic=diagnostic):
                result = score.evaluate_energy_diagnostic(
                    diagnostic,
                    viscosity=0.05,
                    energy_balance_relative_tolerance=1.0e-4,
                    divergence_rms_tolerance=1.0e-10,
                    identity_relative_tolerance=1.0e-12,
                )
                self.assertFalse(result["pass"])
                self.assertTrue(result["failedChecks"])

    def test_negative_divergence_or_physical_time_fails_closed(self):
        for field in (
            "divergenceRms",
            "time",
            "minimumSampledDissipationTime",
            "energyBudgetMaxInterval",
        ):
            diagnostic = exact_shear_diagnostic(
                viscosity=0.05, mode=2, final_time=1.0, steps=20
            )
            diagnostic[field] = -1.0
            with self.subTest(field=field):
                result = score.evaluate_energy_diagnostic(
                    diagnostic,
                    viscosity=0.05,
                    energy_balance_relative_tolerance=1.0,
                    divergence_rms_tolerance=1.0,
                    identity_relative_tolerance=1.0e-12,
                )
                self.assertFalse(result["pass"])
                expected = (
                    "nonnegative_energy_and_dissipation"
                    if field == "divergenceRms"
                    else "nonnegative_physical_times"
                )
                self.assertIn(expected, result["failedChecks"])

    def test_nonuniform_cadence_cannot_claim_uniform_order(self):
        coarse = exact_shear_diagnostic(
            viscosity=0.05, mode=2, final_time=1.0, steps=20
        )
        fine = exact_shear_diagnostic(
            viscosity=0.05, mode=2, final_time=1.0, steps=40
        )
        with self.assertRaises(ValueError):
            score.compare_observation_cadence(
                coarse, fine, uniform_observation_cadence=False
            )


if __name__ == "__main__":
    unittest.main()
