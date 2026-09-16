#!/usr/bin/env python3
"""Outward-rounded float64 interval certificates for the periodic solver's
energy-balance diagnostics score.

EVIDENCE STATUS (FALSIFICATION_LEDGER F-012): the enclosed quantities are
interval bounds on *declared arithmetic expressions evaluated at reported
float64 operands*.  They certify the rounding envelope of the score's
algebra.  They do NOT certify the continuum residual, the FFT internals that
produced the operands, or any regularity/breakdown theorem.  Values emitted
here are OBSERVATIONS proposing falsifiable inequalities, never closure
claims.

Soundness argument (why one ulp of outward widening suffices)
--------------------------------------------------------------
Python's ``+ - * /`` and ``math.sqrt`` on floats are correctly rounded
(IEEE-754 round-to-nearest, ties-to-even): for operands ``a, b`` the result
``fl(a op b)`` satisfies ``|fl(a op b) - (a op b)| <= 0.5 ulp``, and rounding
is monotone.  If every operand of an expression lies inside a closed interval
``X`` and the interval operation widens the exact result interval ``X op Y``
by at least one ulp outward on each end, then the correctly-rounded float64
evaluation — carried out in *any* order of that same expression's operations —
lies inside the widened interval, by induction over the operations (the
induction step uses that ``fl`` of a point of ``X op Y`` deviates from that
point by at most 0.5 ulp < 1 ulp of widening).  Converting a finite float to
an interval via ``[nextafter(x, -inf), nextafter(x, +inf)]`` (or a singleton
for infinities handled explicitly) gives the same margin.  Hence every number
this module returns as ``hi`` is a *proven* upper bound for the exact real
value of the enclosed expression and for its float64 evaluation in the *same*
operation order the interval walk uses.  Evaluations in a different order
(e.g. numpy pairwise summation) remain enclosed for the exact value, but
their own deviation from it requires a separate order-aware bound (Higham
``gamma_n`` style); this module never claims otherwise.  ``hi - lo`` is the
rounding envelope.

The companion test module verifies enclosure independently with mpmath
exact re-evaluation of the same expressions on the same float64 operands.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np

__all__ = [
    "Interval",
    "enclose",
    "inflate",
    "i_add",
    "i_sub",
    "i_mul",
    "i_div",
    "i_sqrt",
    "certify_energy_balance_defect",
    "certify_energy_balance_series",
    "certify_cumulative_dissipation",
    "certificate_record",
    "SCOPE_STATEMENT",
]

SCOPE_STATEMENT = (
    "Interval enclosure of the declared diagnostic expression evaluated at "
    "the reported float64 operands (plus any caller-declared input radius). "
    "It bounds round-off of the score's algebra only; it is not a bound on "
    "the continuum momentum/dissipation residual and not proof evidence "
    "(FALSIFICATION_LEDGER F-012: numerics remain observation-only)."
)


def _down(x: float) -> float:
    return math.nextafter(x, -math.inf)


def _up(x: float) -> float:
    return math.nextafter(x, math.inf)


@dataclass(frozen=True, slots=True)
class Interval:
    """Closed interval [lo, hi]; lo/hi are float64 or infinities.

    No invariant is *assumed* (lo <= hi) at construction; every operation
    maintains it and :func:`certify_energy_balance_defect` reports the flag
    ``well_ordered`` from the final endpoints.
    """

    lo: float
    hi: float

    @property
    def midpoint(self) -> float:
        return 0.5 * (self.lo + self.hi)

    @property
    def width(self) -> float:
        return self.hi - self.lo


def enclose(x: float) -> Interval:
    """Widen a float64 point by one ulp each way (exact float -> interior)."""
    x = float(x)
    if not math.isfinite(x):
        # An infinite operand makes every enclosure infinite; propagate NaN.
        if math.isnan(x):
            return Interval(float("nan"), float("nan"))
        return Interval(x, x)
    return Interval(_down(x), _up(x))


def exact_point(x: float) -> Interval:
    """Singleton interval for a value that is itself exact float64 data.

    Used where the operand is a reported coefficient (already float64): the
    expression's exact value uses the operand exactly, so widening the
    operand would double-count.  Rounding margin is carried by the *operation*
    widenings only.
    """
    x = float(x)
    return Interval(x, x)


def inflate(x: float, rel: float) -> Interval:
    """Operand with declared relative input radius ``rel`` (>= 0).

    Models uncertainty that introduced ``x`` (e.g. the round-off of the
    upstream pipeline that produced it), which the in-expression envelope
    cannot see.
    """
    if not (math.isfinite(rel) and rel >= 0.0):
        raise ValueError("input radius must be finite and >= 0")
    x = float(x)
    d = math.copysign(abs(x) * rel, x) if x != 0.0 else rel
    return Interval(_down(x - d), _up(x + d))


# --- interval operations: exact interval of endpoint results, widened 1 ulp.

def i_add(a: Interval, b: Interval) -> Interval:
    return Interval(_down(a.lo + b.lo), _up(a.hi + b.hi))


def i_sub(a: Interval, b: Interval) -> Interval:
    return Interval(_down(a.lo - b.hi), _up(a.hi - b.lo))


def i_mul(a: Interval, b: Interval) -> Interval:
    p = (a.lo * b.lo, a.lo * b.hi, a.hi * b.lo, a.hi * b.hi)
    return Interval(_down(min(p)), _up(max(p)))


def i_div(a: Interval, b: Interval) -> Interval:
    if b.lo <= 0.0 <= b.hi:
        if b.lo == 0.0 and b.hi == 0.0:
            return Interval(float("nan"), float("nan"))
        # straddling denominator: enclosure blows up to infinity (honest).
        return Interval(-math.inf, math.inf)
    q = (a.lo / b.lo, a.lo / b.hi, a.hi / b.lo, a.hi / b.hi)
    return Interval(_down(min(q)), _up(max(q)))


def i_sqrt(a: Interval) -> Interval:
    if a.hi < 0.0:
        return Interval(float("nan"), float("nan"))
    lo = math.sqrt(max(a.lo, 0.0))
    return Interval(_down(lo), _up(math.sqrt(a.hi)))


# --- the diagnostic score's expressions.

def _widen_result(i: Interval) -> Interval:
    return Interval(_down(i.lo), _up(i.hi))


def certify_energy_balance_defect(
    energy: float,
    cumulative_dissipation: float,
    initial_energy: float,
    *,
    input_radius: float = 0.0,
) -> dict:
    """Enclose ``defect = E + D - E0`` and ``relative = defect / E0``.

    Mirrors the recomputation in ``scripts/navier_diagnostic_score.py``
    (``recomputed_defect``/``recomputed_relative``, lines ~174-182).  With
    ``input_radius = 0`` the enclosure covers the round-off of evaluating
    that expression; pass a caller-declared radius to additionally enclose
    operand uncertainty from the emitting solver.
    """
    e = (enclose if input_radius == 0.0 else lambda v: inflate(v, input_radius))(energy)
    d = (enclose if input_radius == 0.0 else lambda v: inflate(v, input_radius))(
        cumulative_dissipation
    )
    e0 = (enclose if input_radius == 0.0 else lambda v: inflate(v, input_radius))(
        initial_energy
    )
    defect = _widen_result(i_sub(i_add(e, d), e0))
    # i_div is honest at zero-straddling denominators: infinite or NaN
    # interval, never a fabricated finite bound.
    rel = _widen_result(i_div(defect, e0))
    point = float(energy) + float(cumulative_dissipation) - float(initial_energy)
    return {
        "defect_interval": defect,
        "relative_interval": rel,
        "point_value": point,
        "point_inside": (
            math.isnan(point) or (defect.lo <= point <= defect.hi)
        ),
        "well_ordered": defect.lo <= defect.hi and (
            rel is None or rel.lo <= rel.hi
        ),
        "input_radius": float(input_radius),
    }


def certify_cumulative_dissipation(
    rates,
    dt: float,
    *,
    input_radius: float = 0.0,
) -> Interval:
    """Enclose the trapezoidal sum ``0.5*dt*sum_i (r_i + r_{i+1})``.

    Operands are the reported float64 dissipation rates at equally spaced
    observation times; the returned interval contains the exact value of the
    trapezoidal expression and its float64 evaluation in this left-to-right
    order (see module docstring for the other-order caveat).
    """
    conv = enclose if input_radius == 0.0 else (lambda v: inflate(v, input_radius))
    dt_iv = conv(dt)
    total = Interval(0.0, 0.0)
    prev = None
    half = _widen_result(i_mul(exact_point(0.5), dt_iv))
    for r in rates:
        iv = conv(r)
        if prev is not None:
            total = _widen_result(i_add(total, _widen_result(i_mul(half, i_add(prev, iv)))))
        prev = iv
    return total


def certify_energy_balance_series(
    energies,
    cumulative_dissipations,
    initial_energy: float,
    *,
    input_radius: float = 0.0,
) -> dict:
    """Worst-case envelope over a series of observation rows.

    Returns the pointwise-worst absolute defect bound ``max_defect_abs`` =
    max over rows of max(|lo|, |hi|), the summed rounding envelope width, and
    per-row records.  A zero-defect target with ``max_defect_abs`` strictly
    below the caller's tolerance is a *verified* interval statement about the
    reported score data (still not about the continuum residual).
    """
    rows = []
    worst = 0.0
    widths = 0.0
    all_inside = True
    for e, d in zip(energies, cumulative_dissipations):
        r = certify_energy_balance_defect(
            e, d, initial_energy, input_radius=input_radius
        )
        iv = r["defect_interval"]
        rows.append((e, d, iv))
        worst = max(worst, abs(iv.lo), abs(iv.hi))
        widths += iv.width
        all_inside = all_inside and r["point_inside"]
    return {
        "n_rows": len(rows),
        "max_defect_abs_bound": worst,
        "total_envelope_width": widths,
        "all_point_values_inside": all_inside,
        "rows": rows,
        "initial_energy": float(initial_energy),
        "input_radius": float(input_radius),
    }


def certificate_record(payload: dict, *, backend: str, seed: int | None = None) -> dict:
    """Serialize a machine-readable observation record with scope guard."""
    return {
        "kind": "float64_rounding_envelope_observation",
        "scope": SCOPE_STATEMENT,
        "backend": backend,
        "seed": seed,
        "numpy_version": np.__version__,
        "finite_certification": bool(
            payload.get("point_inside")
            and payload.get("well_ordered")
            and math.isfinite(payload["defect_interval"].lo)
            and math.isfinite(payload["defect_interval"].hi)
        )
        if "defect_interval" in payload
        else False,
        "defect_interval": [
            payload["defect_interval"].lo,
            payload["defect_interval"].hi,
        ]
        if "defect_interval" in payload
        else None,
        "max_defect_abs_bound": payload.get("max_defect_abs_bound"),
        "input_radius": payload.get("input_radius"),
    }
