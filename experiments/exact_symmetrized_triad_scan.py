#!/usr/bin/env python3
"""Exact finite triad falsifier; this is not a Navier--Stokes proof.

All search arithmetic is integer-valued.  The secondary six-mode leakage
diagnostic uses ``Fraction``-valued Gaussian rationals for the normalized
Leray projection.  No floating-point conversion occurs.
"""

# ruff: noqa: E741 -- k, l, m are the standard triad wavevector labels.

from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Iterator


Vector = tuple[int, int, int]
ZERO_VECTOR: Vector = (0, 0, 0)


def add(left: Vector, right: Vector) -> Vector:
    return tuple(x + y for x, y in zip(left, right, strict=True))  # type: ignore[return-value]


def negate(vector: Vector) -> Vector:
    return tuple(-entry for entry in vector)  # type: ignore[return-value]


def dot(left: Vector, right: Vector) -> int:
    return sum(x * y for x, y in zip(left, right, strict=True))


def squared_norm(vector: Vector) -> int:
    return dot(vector, vector)


@dataclass(frozen=True)
class TriadConfiguration:
    k: Vector
    l: Vector
    m: Vector
    a: Vector
    b: Vector
    c: Vector

    def canonical(self) -> "TriadConfiguration":
        ordered = sorted(((self.k, self.a), (self.l, self.b), (self.m, self.c)))
        return TriadConfiguration(
            ordered[0][0], ordered[1][0], ordered[2][0],
            ordered[0][1], ordered[1][1], ordered[2][1],
        )


@dataclass(frozen=True)
class ReceiverRates:
    k: int
    l: int
    m: int

    def as_tuple(self) -> tuple[int, int, int]:
        return (self.k, self.l, self.m)

    @property
    def total(self) -> int:
        return self.k + self.l + self.m


OLD_CANCELLING_WITNESS = TriadConfiguration(
    k=(1, 0, 0), l=(0, 1, 0), m=(-1, -1, 0),
    a=(0, 1, 0), b=(1, 0, 0), c=(1, -1, 0),
)
UNEQUAL_RADIUS_WITNESS = TriadConfiguration(
    k=(1, 0, 0), l=(0, 1, 0), m=(-1, -1, 0),
    a=(0, 1, 1), b=(1, 0, 0), c=(1, -1, 1),
)


def validate_configuration(configuration: TriadConfiguration) -> None:
    waves = (configuration.k, configuration.l, configuration.m)
    if any(wave == ZERO_VECTOR for wave in waves):
        raise ValueError("wavevectors must be nonzero")
    if add(add(configuration.k, configuration.l), configuration.m) != ZERO_VECTOR:
        raise ValueError("wavevectors do not form a triad")
    for label, wave, polarization in zip(
        ("a", "b", "c"), waves,
        (configuration.a, configuration.b, configuration.c), strict=True,
    ):
        if polarization == ZERO_VECTOR:
            raise ValueError(f"polarization {label} must be nonzero")
        if dot(wave, polarization) != 0:
            raise ValueError(f"polarization {label} is not divergence-free")


def symmetrized_receiver_rates(configuration: TriadConfiguration) -> ReceiverRates:
    """Return rates at receivers ``a``, ``b``, ``c`` (modes ``k``, ``l``, ``m``)."""
    validate_configuration(configuration)
    k, l, m = configuration.k, configuration.l, configuration.m
    a, b, c = configuration.a, configuration.b, configuration.c
    rates = ReceiverRates(
        k=dot(b, m) * dot(c, a) + dot(c, l) * dot(b, a),
        l=dot(c, k) * dot(a, b) + dot(a, m) * dot(c, b),
        m=dot(a, l) * dot(b, c) + dot(b, k) * dot(a, c),
    )
    if rates.total != 0:
        raise AssertionError("exact constant-weight energy cancellation failed")
    return rates


def squared_frequency_weighted_sum(
    configuration: TriadConfiguration, rates: ReceiverRates | None = None,
) -> int:
    rates = rates or symmetrized_receiver_rates(configuration)
    return sum(
        squared_norm(wave) * rate
        for wave, rate in zip(
            (configuration.k, configuration.l, configuration.m),
            rates.as_tuple(), strict=True,
        )
    )


def divergence_free_polarizations(wave: Vector, radius: int) -> tuple[Vector, ...]:
    """Construct bounded integer solutions of ``wave · polarization = 0``.

    Two coordinates are enumerated and the first nonzero wave coordinate is
    solved exactly.  This is a parametrization of the integer constraint, not
    a floating-point projection or tolerance filter.
    """
    if wave == ZERO_VECTOR:
        raise ValueError("cannot polarize the zero wavevector")
    if radius < 1:
        raise ValueError("polarization radius must be positive")
    pivot = next(index for index, entry in enumerate(wave) if entry != 0)
    free = tuple(index for index in range(3) if index != pivot)
    candidates: set[Vector] = set()
    for first, second in itertools.product(range(-radius, radius + 1), repeat=2):
        entries = [0, 0, 0]
        entries[free[0]], entries[free[1]] = first, second
        numerator = -sum(wave[index] * entries[index] for index in free)
        quotient, remainder = divmod(numerator, wave[pivot])
        if remainder == 0 and -radius <= quotient <= radius:
            entries[pivot] = quotient
            candidate = tuple(entries)
            if candidate != ZERO_VECTOR:
                candidates.add(candidate)  # type: ignore[arg-type]
    return tuple(sorted(candidates))


def integer_triads(radius: int) -> Iterator[tuple[Vector, Vector, Vector]]:
    if radius < 1:
        raise ValueError("wave radius must be positive")
    vectors = tuple(
        vector for vector in itertools.product(range(-radius, radius + 1), repeat=3)
        if vector != ZERO_VECTOR
    )
    vector_set = set(vectors)
    for k in vectors:
        for l in vectors:
            m = negate(add(k, l))
            triad = (k, l, m)
            if m in vector_set and triad == tuple(sorted(triad)):
                yield triad


@dataclass(frozen=True)
class ScanCase:
    configuration: TriadConfiguration
    rates: ReceiverRates
    shells: tuple[int, int, int]
    weighted_sum: int


@dataclass(frozen=True)
class ScanReport:
    wave_radius: int
    polarization_radius: int
    triad_count: int
    polarization_configurations: int
    nonzero_rate_configurations: int
    unequal_shell_transfer_cases: tuple[ScanCase, ...]


def scan_exact_triads(wave_radius: int = 1, polarization_radius: int = 1) -> ScanReport:
    triad_count = configuration_count = nonzero_count = 0
    unequal_cases: list[ScanCase] = []
    for k, l, m in integer_triads(wave_radius):
        triad_count += 1
        candidates = tuple(
            divergence_free_polarizations(wave, polarization_radius)
            for wave in (k, l, m)
        )
        for a, b, c in itertools.product(*candidates):
            configuration_count += 1
            configuration = TriadConfiguration(k, l, m, a, b, c)
            rates = symmetrized_receiver_rates(configuration)
            if rates.as_tuple() != (0, 0, 0):
                nonzero_count += 1
            shells = tuple(squared_norm(wave) for wave in (k, l, m))
            weighted = squared_frequency_weighted_sum(configuration, rates)
            if len(set(shells)) > 1 and weighted != 0:
                unequal_cases.append(ScanCase(configuration, rates, shells, weighted))
    return ScanReport(
        wave_radius, polarization_radius, triad_count, configuration_count,
        nonzero_count, tuple(unequal_cases),
    )


@dataclass(frozen=True, order=True)
class GaussianRational:
    real: Fraction
    imag: Fraction

    def __add__(self, other: "GaussianRational") -> "GaussianRational":
        return GaussianRational(self.real + other.real, self.imag + other.imag)

    def __sub__(self, other: "GaussianRational") -> "GaussianRational":
        return GaussianRational(self.real - other.real, self.imag - other.imag)

    def __mul__(self, other: "GaussianRational") -> "GaussianRational":
        return GaussianRational(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )

    def scale(self, scalar: Fraction | int) -> "GaussianRational":
        scalar = Fraction(scalar)
        return GaussianRational(self.real * scalar, self.imag * scalar)

    def times_i(self) -> "GaussianRational":
        return GaussianRational(-self.imag, self.real)

    def conjugate(self) -> "GaussianRational":
        return GaussianRational(self.real, -self.imag)

    @property
    def is_zero(self) -> bool:
        return self.real == 0 and self.imag == 0


GaussianVector = tuple[GaussianRational, GaussianRational, GaussianRational]
GAUSSIAN_ZERO = GaussianRational(Fraction(0), Fraction(0))
GAUSSIAN_ONE = GaussianRational(Fraction(1), Fraction(0))
GAUSSIAN_I = GaussianRational(Fraction(0), Fraction(1))
GAUSSIAN_MINUS_I = GaussianRational(Fraction(0), Fraction(-1))


def phase_times_real(phase: GaussianRational, amplitude: Vector) -> GaussianVector:
    return tuple(phase.scale(entry) for entry in amplitude)  # type: ignore[return-value]


def six_mode_coefficients(configuration: TriadConfiguration) -> dict[Vector, GaussianVector]:
    validate_configuration(configuration)
    assignments = (
        (configuration.k, configuration.a, GAUSSIAN_MINUS_I),
        (configuration.l, configuration.b, GAUSSIAN_ONE),
        (configuration.m, configuration.c, GAUSSIAN_ONE),
        (negate(configuration.k), configuration.a, GAUSSIAN_I),
        (negate(configuration.l), configuration.b, GAUSSIAN_ONE),
        (negate(configuration.m), configuration.c, GAUSSIAN_ONE),
    )
    coefficients = {
        wave: phase_times_real(phase, amplitude)
        for wave, amplitude, phase in assignments
    }
    if len(coefficients) != 6:
        raise ValueError("six-mode leakage diagnostic requires six distinct modes")
    return coefficients


def _add_gaussian_vectors(left: GaussianVector, right: GaussianVector) -> GaussianVector:
    return tuple(x + y for x, y in zip(left, right, strict=True))  # type: ignore[return-value]


def _gaussian_dot_real(vector: GaussianVector, wave: Vector) -> GaussianRational:
    total = GAUSSIAN_ZERO
    for coefficient, entry in zip(vector, wave, strict=True):
        total = total + coefficient.scale(entry)
    return total


def _normalized_leray(output: Vector, vector: GaussianVector) -> GaussianVector:
    denominator = squared_norm(output)
    if denominator == 0:
        return vector
    radial = _gaussian_dot_real(vector, output)
    return tuple(
        entry - radial.scale(Fraction(component, denominator))
        for entry, component in zip(vector, output, strict=True)
    )  # type: ignore[return-value]


@dataclass(frozen=True)
class LeakageOutput:
    output: Vector
    ordered_pairs: tuple[tuple[Vector, Vector], ...]
    coefficient: GaussianVector


@dataclass(frozen=True)
class SixModeLeakageReport:
    off_support_ordered_pairs: int
    off_support_outputs: int
    nonzero_outputs: tuple[LeakageOutput, ...]

    @property
    def is_closed(self) -> bool:
        return not self.nonzero_outputs


def six_mode_leakage(configuration: TriadConfiguration) -> SixModeLeakageReport:
    """Compute ``i P_r Σ_(p+q=r) (U_p·q) U_q`` at off-support outputs."""
    coefficients = six_mode_coefficients(configuration)
    support = tuple(sorted(coefficients))
    grouped: dict[Vector, list[tuple[Vector, Vector]]] = {}
    for first, second in itertools.product(support, repeat=2):
        output = add(first, second)
        if output not in coefficients:
            grouped.setdefault(output, []).append((first, second))
    nonzero: list[LeakageOutput] = []
    for output, pairs in sorted(grouped.items()):
        raw: GaussianVector = (GAUSSIAN_ZERO, GAUSSIAN_ZERO, GAUSSIAN_ZERO)
        for first, second in pairs:
            scalar = _gaussian_dot_real(coefficients[first], second)
            term = tuple(
                scalar * entry for entry in coefficients[second]
            )  # type: ignore[assignment]
            raw = _add_gaussian_vectors(raw, term)
        projected = _normalized_leray(output, raw)
        coefficient = tuple(entry.times_i() for entry in projected)
        if any(not entry.is_zero for entry in coefficient):
            nonzero.append(LeakageOutput(output, tuple(pairs), coefficient))
    return SixModeLeakageReport(
        sum(len(pairs) for pairs in grouped.values()), len(grouped), tuple(nonzero)
    )


def _fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def _configuration_json(configuration: TriadConfiguration) -> dict[str, list[int]]:
    return {
        name: list(getattr(configuration, name))
        for name in ("k", "l", "m", "a", "b", "c")
    }


def _case_json(configuration: TriadConfiguration) -> dict[str, object]:
    rates = symmetrized_receiver_rates(configuration)
    return {
        "configuration": _configuration_json(configuration),
        "rates_k_l_m": list(rates.as_tuple()),
        "constant_weight_sum": rates.total,
        "squared_frequency_weighted_sum": squared_frequency_weighted_sum(
            configuration, rates
        ),
    }


def _leakage_json(report: SixModeLeakageReport, limit: int) -> dict[str, object]:
    return {
        "closed_under_projected_convolution": report.is_closed,
        "phase_convention": "+k:-i, +l:1, +m:1; opposite coefficients conjugated",
        "projection": "normalized Leray projection; identity at zero output",
        "off_support_ordered_pairs": report.off_support_ordered_pairs,
        "off_support_outputs": report.off_support_outputs,
        "nonzero_output_count": len(report.nonzero_outputs),
        "examples": [
            {
                "output": list(item.output),
                "ordered_pairs": [[list(first), list(second)] for first, second in item.ordered_pairs],
                "coefficient": [
                    {"real": _fraction_text(entry.real), "imag": _fraction_text(entry.imag)}
                    for entry in item.coefficient
                ],
            }
            for item in report.nonzero_outputs[:limit]
        ],
    }


def build_report(wave_radius: int, polarization_radius: int, limit: int) -> dict[str, object]:
    scan = scan_exact_triads(wave_radius, polarization_radius)
    leakage = six_mode_leakage(UNEQUAL_RADIUS_WITNESS)
    return {
        "status": "FALSIFICATION_ONLY",
        "closes_clay_endpoint": False,
        "arithmetic": "exact integers and rational normalized projections; no floats",
        "old_selected_output_cancellation": _case_json(OLD_CANCELLING_WITNESS),
        "unequal_radius_witness": _case_json(UNEQUAL_RADIUS_WITNESS),
        "scan": {
            "wave_radius": scan.wave_radius,
            "polarization_radius": scan.polarization_radius,
            "triad_count": scan.triad_count,
            "polarization_configurations": scan.polarization_configurations,
            "nonzero_rate_configurations": scan.nonzero_rate_configurations,
            "unequal_shell_weighted_transfer_count": len(scan.unequal_shell_transfer_cases),
            "examples": [
                {
                    **_case_json(case.configuration),
                    "shells": list(case.shells),
                }
                for case in scan.unequal_shell_transfer_cases[:limit]
            ],
        },
        "six_mode_leakage": _leakage_json(leakage, limit),
        "scope": (
            "finite exact algebraic falsification; not a Navier--Stokes solution, "
            "closed Galerkin model, or Clay proof"
        ),
    }


def parse_args(arguments: Iterable[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--wave-radius", type=int, default=1)
    parser.add_argument("--polarization-radius", type=int, default=1)
    parser.add_argument("--max-examples", type=int, default=5)
    parser.add_argument(
        "--output-artifact",
        action="store_true",
        help=(
            "also write the canonical replay artifact under artifacts/runs; "
            "stdout remains identical"
        ),
    )
    return parser.parse_args(arguments)


def main(arguments: Iterable[str] | None = None) -> int:
    args = parse_args(arguments)
    if args.max_examples < 0:
        raise SystemExit("--max-examples must be nonnegative")
    report = build_report(args.wave_radius, args.polarization_radius, args.max_examples)
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output_artifact:
        artifact = Path("artifacts/runs/exact_symmetrized_triad_scan.json")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
