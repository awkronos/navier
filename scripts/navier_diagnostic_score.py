#!/usr/bin/env python3
"""Score the finite-grid energy diagnostic emitted by the Rust solvers.

The WebGPU and normalized browser-worker objects use camelCase. Raw native and
CPU-WASM serialization retains four legacy snake_case field names; this scorer
normalizes those explicit aliases and rejects conflicting duplicates. Energy
uses physical volume means on ``[0, 2*pi)^3``. The scorer compares the numerical
budget against the zero-defect target

    energy(t) + cumulativeEnergyDissipation(t) = initialEnergy.

The cumulative term is a trapezoidal quadrature over diagnostic observation
times, not over every accepted solver step.  Accordingly, callers must supply
tolerances established for their backend and observation cadence.  Passing
this check is numerical regression evidence; it is not a certificate of the
continuum hypotheses in ``PhysicalPeriodicDissipationBudget``.

The Lean raw Fourier identity has a factor ``2 * viscosity`` multiplying raw
dissipation. Since ``A = -i*uHat_R`` on the Rust box, division by two gives the
Rust volume-mean identity above. Equivalently, division by
``2 * (2*pi)^2`` gives the energy identity after the repository's period-one
velocity rescaling. The dimensionless relative defect is unchanged.
"""

from __future__ import annotations

import argparse
import json
import math
import numbers
import sys
from collections.abc import Mapping


NUMERIC_FIELDS = (
    "time",
    "energy",
    "enstrophy",
    "divergenceRms",
    "energyDissipationRate",
    "highFrequencyEnergyFraction",
    "tailTolerance",
    "initialEnergy",
    "cumulativeEnergyDissipation",
    "energyBalanceDefect",
    "energyBalanceRelativeError",
    "meanEnergyDissipationRate",
    "minimumSampledEnergyDissipationRate",
    "minimumSampledDissipationTime",
    "energyBudgetStartTime",
    "energyBudgetEndTime",
    "energyBudgetMaxInterval",
)
INTEGER_FIELDS = ("energyBudgetSamples",)
BOOLEAN_FIELDS = ("finite", "underresolved", "energyBalanceApplicable")
TEXT_FIELDS = ("energyBudgetQuadrature",)
REQUIRED_FIELDS = NUMERIC_FIELDS + INTEGER_FIELDS + BOOLEAN_FIELDS + TEXT_FIELDS
CPU_LEGACY_ALIASES = {
    "divergence_rms": "divergenceRms",
    "energy_dissipation_rate": "energyDissipationRate",
    "high_frequency_energy_fraction": "highFrequencyEnergyFraction",
    "tail_tolerance": "tailTolerance",
}


def _finite_real(value: object) -> bool:
    return (
        isinstance(value, numbers.Real)
        and not isinstance(value, bool)
        and math.isfinite(float(value))
    )


def _configuration_value(name: str, value: object, *, positive: bool = False) -> float:
    if not _finite_real(value) or (float(value) <= 0.0 if positive else float(value) < 0.0):
        relation = "positive" if positive else "nonnegative"
        raise ValueError(f"{name} must be finite and {relation}")
    return float(value)


def _relative_close(left: float, right: float, tolerance: float) -> bool:
    scale = max(abs(left), abs(right), sys.float_info.min)
    return abs(left - right) <= tolerance * scale


def evaluate_energy_diagnostic(
    diagnostic: Mapping[str, object],
    *,
    viscosity: float,
    energy_balance_relative_tolerance: float,
    divergence_rms_tolerance: float,
    identity_relative_tolerance: float,
) -> dict[str, object]:
    """Evaluate one accumulated Rust diagnostic without inventing tolerances.

    The three tolerances are required experimental inputs.  In particular,
    the energy tolerance must be selected from observation-cadence refinement
    (or an analytic quadrature bound), because the accumulated dissipation is
    sampled only when diagnostics are observed.
    """
    viscosity = _configuration_value("viscosity", viscosity)
    budget_tolerance = _configuration_value(
        "energy_balance_relative_tolerance", energy_balance_relative_tolerance
    )
    divergence_tolerance = _configuration_value(
        "divergence_rms_tolerance", divergence_rms_tolerance
    )
    identity_tolerance = _configuration_value(
        "identity_relative_tolerance", identity_relative_tolerance, positive=True
    )

    canonical = dict(diagnostic)
    alias_conflicts = []
    for legacy, current in CPU_LEGACY_ALIASES.items():
        if legacy not in canonical:
            continue
        if current in canonical and canonical[current] != canonical[legacy]:
            alias_conflicts.append((legacy, current))
        else:
            canonical[current] = canonical[legacy]

    fields_present = all(name in canonical for name in REQUIRED_FIELDS)
    numeric_domain = fields_present and all(
        _finite_real(canonical[name]) for name in NUMERIC_FIELDS
    )
    integer_domain = fields_present and all(
        isinstance(canonical[name], int)
        and not isinstance(canonical[name], bool)
        and canonical[name] >= 0
        for name in INTEGER_FIELDS
    )
    boolean_domain = fields_present and all(
        isinstance(canonical[name], bool) for name in BOOLEAN_FIELDS
    )
    text_domain = fields_present and all(
        isinstance(canonical[name], str) for name in TEXT_FIELDS
    )
    domain = (
        fields_present
        and numeric_domain
        and integer_domain
        and boolean_domain
        and text_domain
        and not alias_conflicts
    )

    checks: dict[str, bool] = {
        "required_fields_present": fields_present,
        "finite_numeric_domain": numeric_domain,
        "integer_sample_count_domain": integer_domain,
        "boolean_flag_domain": boolean_domain,
        "text_metadata_domain": text_domain,
        "legacy_aliases_do_not_conflict": not alias_conflicts,
    }
    measured: dict[str, float | int | None] = {
        "absoluteEnergyBalanceRelativeError": None,
        "energyBalanceToleranceRatio": None,
        "divergenceToleranceRatio": None,
        "observationIntervalMean": None,
        "observationIntervalMaximum": None,
    }

    if domain:
        value = {name: float(canonical[name]) for name in NUMERIC_FIELDS}
        samples = int(canonical["energyBudgetSamples"])
        duration = value["energyBudgetEndTime"] - value["energyBudgetStartTime"]
        time_scale = max(
            abs(value["time"]),
            abs(value["energyBudgetStartTime"]),
            abs(value["energyBudgetEndTime"]),
            sys.float_info.min,
        )
        time_slack = identity_tolerance * time_scale
        recomputed_defect = (
            value["energy"]
            + value["cumulativeEnergyDissipation"]
            - value["initialEnergy"]
        )
        if value["initialEnergy"] == 0.0:
            recomputed_relative = 0.0 if recomputed_defect == 0.0 else math.nan
        else:
            recomputed_relative = recomputed_defect / value["initialEnergy"]
        rate_from_enstrophy = 2.0 * viscosity * value["enstrophy"]

        checks.update(
            {
                "solver_marks_diagnostic_finite": bool(canonical["finite"]),
                "energy_budget_is_applicable": bool(canonical["energyBalanceApplicable"]),
                "quadrature_rule_matches_contract": (
                    canonical["energyBudgetQuadrature"]
                    == "trapezoidal-diagnostics-observations"
                ),
                "nonnegative_energy_and_dissipation": all(
                    value[name] >= 0.0
                    for name in (
                        "energy",
                        "enstrophy",
                        "divergenceRms",
                        "energyDissipationRate",
                        "initialEnergy",
                        "cumulativeEnergyDissipation",
                        "meanEnergyDissipationRate",
                        "minimumSampledEnergyDissipationRate",
                    )
                ),
                "nonnegative_physical_times": all(
                    value[name] >= 0.0
                    for name in (
                        "time",
                        "minimumSampledDissipationTime",
                        "energyBudgetStartTime",
                        "energyBudgetEndTime",
                        "energyBudgetMaxInterval",
                    )
                ),
                "dissipation_rate_matches_enstrophy": _relative_close(
                    value["energyDissipationRate"], rate_from_enstrophy, identity_tolerance
                ),
                "energy_balance_defect_is_reproducible": _relative_close(
                    value["energyBalanceDefect"], recomputed_defect, identity_tolerance
                ),
                "energy_balance_relative_error_is_reproducible": math.isfinite(
                    recomputed_relative
                )
                and _relative_close(
                    value["energyBalanceRelativeError"],
                    recomputed_relative,
                    identity_tolerance,
                ),
                "budget_coverage_is_ordered": duration >= -time_slack,
                "budget_coverage_ends_at_diagnostic_time": abs(
                    value["energyBudgetEndTime"] - value["time"]
                )
                <= time_slack,
                "minimum_rate_time_is_covered": (
                    value["energyBudgetStartTime"] - time_slack
                    <= value["minimumSampledDissipationTime"]
                    <= value["energyBudgetEndTime"] + time_slack
                ),
                "sample_count_matches_coverage": (
                    samples == 1 if duration <= time_slack else samples >= 2
                ),
                "maximum_interval_matches_coverage": (
                    value["energyBudgetMaxInterval"] == 0.0
                    if duration <= time_slack
                    else 0.0 < value["energyBudgetMaxInterval"] <= duration + time_slack
                ),
                "maximum_interval_bounds_observation_mean": (
                    samples <= 1
                    or duration / (samples - 1)
                    <= value["energyBudgetMaxInterval"] + time_slack
                ),
                "sampled_minimum_does_not_exceed_mean": (
                    duration <= time_slack
                    or value["minimumSampledEnergyDissipationRate"]
                    <= value["meanEnergyDissipationRate"]
                    * (1.0 + identity_tolerance)
                ),
                "mean_rate_reproduces_quadrature": (
                    duration <= time_slack
                    and value["cumulativeEnergyDissipation"] == 0.0
                    and _relative_close(
                        value["meanEnergyDissipationRate"],
                        value["energyDissipationRate"],
                        identity_tolerance,
                    )
                    or duration > time_slack
                    and _relative_close(
                        value["meanEnergyDissipationRate"],
                        value["cumulativeEnergyDissipation"] / duration,
                        identity_tolerance,
                    )
                ),
                "divergence_within_declared_tolerance": (
                    value["divergenceRms"] <= divergence_tolerance
                ),
                "energy_balance_within_declared_tolerance": (
                    abs(value["energyBalanceRelativeError"]) <= budget_tolerance
                ),
                "tail_fraction_domain": 0.0
                <= value["highFrequencyEnergyFraction"]
                <= 1.0,
                "tail_tolerance_domain": 0.0 <= value["tailTolerance"] <= 1.0,
                "clear_resolution_flag_matches_current_tail": (
                    bool(canonical["underresolved"])
                    or value["highFrequencyEnergyFraction"] <= value["tailTolerance"]
                ),
                "spatial_resolution_flag_clear": not bool(canonical["underresolved"]),
            }
        )
        absolute_relative_error = abs(value["energyBalanceRelativeError"])
        measured.update(
            {
                "absoluteEnergyBalanceRelativeError": absolute_relative_error,
                "energyBalanceToleranceRatio": (
                    absolute_relative_error / budget_tolerance
                    if budget_tolerance > 0.0
                    else 0.0 if absolute_relative_error == 0.0 else None
                ),
                "divergenceToleranceRatio": (
                    value["divergenceRms"] / divergence_tolerance
                    if divergence_tolerance > 0.0
                    else 0.0 if value["divergenceRms"] == 0.0 else None
                ),
                "observationIntervalMean": duration / (samples - 1) if samples > 1 else 0.0,
                "observationIntervalMaximum": value["energyBudgetMaxInterval"],
            }
        )

    failed = [name for name, passed in checks.items() if not passed]
    return {
        "pass": not failed,
        "checks": checks,
        "failedChecks": failed,
        "measured": measured,
        "criteria": {
            "viscosity": viscosity,
            "energyBalanceRelativeTolerance": budget_tolerance,
            "divergenceRmsTolerance": divergence_tolerance,
            "identityRelativeTolerance": identity_tolerance,
        },
        "quadrature": {
            "rule": "trapezoidal",
            "cadence": "diagnostic observation endpoints",
            "sampleCountField": "energyBudgetSamples (observations; trapezoids = samples - 1)",
            "coverageFields": ["energyBudgetStartTime", "energyBudgetEndTime"],
        },
        "normalization": (
            "physical volume-mean kinetic energy on [0,2pi)^3; "
            "E(t)+integral(2*viscosity*enstrophy)=E(0)"
        ),
        "scope": (
            "finite-grid solver diagnostic regression; does not verify the "
            "continuum mild-solution hypotheses or global regularity"
        ),
    }


def compare_observation_cadence(
    coarse: Mapping[str, object],
    fine: Mapping[str, object],
    *,
    uniform_observation_cadence: bool,
) -> dict[str, object]:
    """Report convergence for two caller-declared uniform observation meshes.

    Counts and means cannot establish order for nonuniform meshes. Those runs
    need their full meshes or an error bound using ``energyBudgetMaxInterval``.
    """
    if uniform_observation_cadence is not True:
        raise ValueError("cadence order requires a caller-declared uniform protocol")
    required = (
        "initialEnergy",
        "energy",
        "energyBudgetStartTime",
        "energyBudgetEndTime",
        "energyBudgetSamples",
        "energyBalanceDefect",
        "energyBudgetMaxInterval",
    )
    if any(name not in coarse or name not in fine for name in required):
        raise ValueError("both diagnostics must contain the energy-budget cadence fields")
    numeric = tuple(name for name in required if name != "energyBudgetSamples")
    if any(not _finite_real(item[name]) for item in (coarse, fine) for name in numeric):
        raise ValueError("cadence comparison fields must be finite")
    for name in ("initialEnergy", "energy", "energyBudgetStartTime", "energyBudgetEndTime"):
        if float(coarse[name]) != float(fine[name]):
            raise ValueError(f"cadence comparison requires identical {name}")
    coarse_samples = coarse["energyBudgetSamples"]
    fine_samples = fine["energyBudgetSamples"]
    if (
        not isinstance(coarse_samples, int)
        or isinstance(coarse_samples, bool)
        or not isinstance(fine_samples, int)
        or isinstance(fine_samples, bool)
        or coarse_samples <= 1
        or fine_samples <= coarse_samples
    ):
        raise ValueError("fine diagnostic must use more positive-width observations")
    duration = float(coarse["energyBudgetEndTime"]) - float(coarse["energyBudgetStartTime"])
    if duration <= 0.0:
        raise ValueError("cadence comparison requires positive common coverage")
    coarse_h = duration / (coarse_samples - 1)
    fine_h = duration / (fine_samples - 1)
    if not math.isclose(float(coarse["energyBudgetMaxInterval"]), coarse_h) or not math.isclose(
        float(fine["energyBudgetMaxInterval"]), fine_h
    ):
        raise ValueError("reported maximum interval is inconsistent with uniform cadence")
    coarse_error = abs(float(coarse["energyBalanceDefect"]))
    fine_error = abs(float(fine["energyBalanceDefect"]))
    ratio = coarse_error / fine_error if fine_error > 0.0 else math.inf
    observed_order = (
        math.log(ratio) / math.log(coarse_h / fine_h)
        if coarse_error > 0.0 and fine_error > 0.0
        else None
    )
    return {
        "coarseObservationIntervalMean": coarse_h,
        "fineObservationIntervalMean": fine_h,
        "absoluteDefectReductionRatio": ratio if math.isfinite(ratio) else None,
        "observedDefectOrder": observed_order,
        "refinementReducesAbsoluteDefect": fine_error < coarse_error,
        "scope": "observation-quadrature convergence, not continuum convergence",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("diagnostic", nargs="?", help="JSON file; stdin when omitted")
    parser.add_argument("--viscosity", type=float, required=True)
    parser.add_argument("--energy-balance-relative-tolerance", type=float, required=True)
    parser.add_argument("--divergence-rms-tolerance", type=float, required=True)
    parser.add_argument("--identity-relative-tolerance", type=float, required=True)
    args = parser.parse_args()
    source = open(args.diagnostic, encoding="utf-8") if args.diagnostic else sys.stdin
    try:
        payload = json.load(source)
    finally:
        if args.diagnostic:
            source.close()
    diagnostic = payload.get("diagnostics", payload) if isinstance(payload, dict) else payload
    if not isinstance(diagnostic, dict):
        parser.error("input must be a diagnostic JSON object")
    result = evaluate_energy_diagnostic(
        diagnostic,
        viscosity=args.viscosity,
        energy_balance_relative_tolerance=args.energy_balance_relative_tolerance,
        divergence_rms_tolerance=args.divergence_rms_tolerance,
        identity_relative_tolerance=args.identity_relative_tolerance,
    )
    print(json.dumps(result, indent=2, allow_nan=False))
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
