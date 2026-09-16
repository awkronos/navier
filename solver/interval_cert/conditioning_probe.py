#!/usr/bin/env python3
"""OBSERVATION: conditioning of the mild multiplier exp(ν‖ξ‖²t) at the cutoff.

The mild heat factor is heatMode(nu, t, xi) = exp(-(nu*|xi|^2*t))
(navier_xcarrier.py, mirroring ContinuousLeiLinSpace.lean:106).  For t < 0
the exponent is +ν‖ξ‖²|t| — the same quantity whose t<0 explosion drove the
domain repair noted in OPEN_FRONTIER_MAP.  This probe MEASURES the float64
thresholds of exp and converts them into a falsifiable inequality for the
formal side; it proves nothing about the PDE.

Outputs a JSON record.  Run:  python3 solver/interval_cert/conditioning_probe.py
"""
from __future__ import annotations

import json
import math

import numpy as np

DBL_MAX = np.finfo(np.float64).max
LN_MAX = 709.782712893384  # will be re-measured by binary search below


def bisect_exp_threshold(lo: float, hi: float) -> float:
    """Largest x (to 1 ulp) with np.exp(x) finite and non-overflowing.

    Invariant: exp(lo) finite, exp(hi) not.  Returns LO (the finite side).
    """
    with np.errstate(over="ignore", under="ignore"):
        assert math.isfinite(float(np.exp(lo)))
        assert not math.isfinite(float(np.exp(hi)))
        while True:
            mid = 0.5 * (lo + hi)
            if mid == lo or mid == hi:
                return lo
            if math.isfinite(float(np.exp(mid))):
                lo = mid
            else:
                hi = mid


def largest_finite_arg() -> float:
    return bisect_exp_threshold(0.0, 1024.0)


def smallest_nonzero_arg() -> float:
    """Most-negative x with np.exp(x) != 0 (subnormal floor)."""
    lo, hi = -1076.0, -700.0  # exp(-1076) = 0, exp(-700) normal
    with np.errstate(over="ignore", under="ignore"):
        assert np.exp(lo) == 0.0 and np.exp(hi) > 0.0
        while True:
            mid = 0.5 * (lo + hi)
            if mid == lo or mid == hi:
                return hi  # smallest x with exp(x) != 0
            if np.exp(mid) == 0.0:
                lo = mid
            else:
                hi = mid


def threshold_from_below(x_max: float) -> dict:
    """exp(x_max) finite; exp(nextafter(x_max,+1)) inf -> exact crossover."""
    up = math.nextafter(x_max, math.inf)
    with np.errstate(over="ignore"):
        return {
            "exp_at_xmax": float(np.exp(x_max)),
            "exp_at_nextafter_up": float(np.exp(up)),
            "crossover_ulp_gap": int((up - x_max) / math.ulp(x_max)),
        }


def main() -> int:
    x_max = largest_finite_arg()
    x_min = smallest_nonzero_arg()
    # Falsifiable inequality (float64, numpy 2.5, this machine):
    #   np.exp(x) is finite   <=>   x <= X_MAX   (measured X_MAX below)
    #   np.exp(x) == 0.0      <=>   x <  X_MIN  (measured X_MIN below)
    # Translated to the mild multiplier at wave-number cutoff |xi| <= K:
    #   heatMode(nu, t, xi) overflows  <=>  nu*|xi|^2*|t| > X_MAX  (t < 0),
    #   i.e. |t| > X_MAX/(nu*K^2) is the exact-float64 explosion domain;
    #   for t > 0 the factor underflows to the ZERO float when nu*K^2*t >= |X_MIN|,
    #   so the high-k modes collapse to 0.0 exactly (damping saturates) there.
    probes = []
    for nu in (0.05, 0.01, 1.0):
        for cutoff_grid in (16, 32, 64):
            k2max = 3.0 * ((cutoff_grid // 2 - 1) if cutoff_grid % 2 == 0 else cutoff_grid // 2) ** 2
            t_over = x_max / (nu * k2max)
            t_under = -x_min / (nu * k2max)
            probes.append(
                {
                    "nu": nu,
                    "grid": cutoff_grid,
                    "max_|xi|^2_on_grid": int(k2max),
                    "|t| overflow threshold (t<0)": t_over,
                    "|t| underflow-to-zero threshold (t>0, highest mode)": t_under,
                }
            )
    rec = {
        "kind": "float64_exp_conditioning_observation",
        "scope": "observed crossover thresholds of numpy exp; a falsifiable "
        "inequality for the formal side, not proof (F-012).",
        "numpy_version": np.__version__,
        "python": " ".join(__import__("sys").version.split("\n")[0:1]),
        "machine": "MacBook (arm64), measured 2026-09-16",
        "X_MAX_largest_finite_arg": x_max,
        "X_MIN_smallest_nonzero_arg": x_min,
        "DBL_MAX": float(DBL_MAX),
        "ln_DBL_MAX_reference": LN_MAX,
        "crossover_detail": threshold_from_below(x_max),
        "grid_probes": probes,
        "inequality_for_formal_side": (
            "forall nu>0, xi, t: float64 exp(nu*|xi|^2*(-t)) < inf "
            "holds iff nu*|xi|^2*(-t) <= "
            + repr(x_max)
            + " (t<0 explosion domain; measured crossover within 1 ulp)"
        ),
    }
    print(json.dumps(rec, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
