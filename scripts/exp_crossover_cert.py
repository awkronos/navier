#!/usr/bin/env python3
"""Native interval certificate for the float64 exp crossover points.

NUMERICAL OBSERVATION (F-012 / learn-kernel discipline): this script checks
exact rational inequalities about the real exponential at four anchors, and
separately probes what this platform's C libm `exp` returns at those anchors.
It certifies nothing about any libm implementation; the Lean file
Navier/Analysis/FloatExpCrossover.lean states the same four comparisons as
propositions about Real.exp at the exact rationals.

Anchors (IEEE64 values, from the repository's solver overflow guards):
  X_MAX  =  709.782712893384       (largest float whose libm exp is finite)
  nextUp(X_MAX)                    (smallest float whose libm exp overflows)
  X_MIN  = -745.1332191019411      (most-negative float whose libm exp is
                                    nonzero subnormal)
  nextDown(X_MIN)                  (float whose libm exp underflows to 0)

Thresholds (round-to-nearest crossover points of the float64 grid):
  T  = (2^54 - 1) * 2^970  (midpoint between 2^1024 - 2^971 and 2^1024: exp
      passes it between X_MAX and nextUp)
  H  = 2^-1075             (midpoint below the smallest positive subnormal)

Method (mirrors the Lean proof exactly):
  exp x = exp(x/1024)^1024. With w = x/1024 (|w| <= 0.73) and n = 40:
    sum_{k<=n} w^k/k!  <=  exp w  <=  sum_{k<=n} w^k/k! + 2(w/2)^{n+1}/(1-w/2),
  the tail bound using k! >= 2^(k-1) (k >= 1). The enclosing sums are rounded
  to dyadics with 128 fractional bits (cost 1024*2^-128 << the tightest
  margin, 1.1e-14 relative), then raised to the 1024th power in exact
  rational arithmetic. All comparisons below are exact Fraction comparisons;
  the four dyadic bound literals are printed and are the same constants the
  Lean file Navier/Analysis/FloatExpCrossover.lean proves against.

Usage: python3 scripts/exp_crossover_cert.py   (stdlib only, ~1 s)
Exit 0 iff all four exact comparisons and the four libm probes hold.
"""

from __future__ import annotations

import math
import struct
import sys
from fractions import Fraction as F

N_TAYLOR = 40
FRAC_BITS = 128
SPLIT = 1024

X_MAX = 709.782712893384
X_MIN = -745.1332191019411
U1 = math.nextafter(X_MAX, math.inf)     # X_MAX + 1 ulp
D1 = math.nextafter(X_MIN, -math.inf)    # X_MIN - 1 ulp

T = F((2**54 - 1) * 2**970)               # overflow threshold (as real)
H = F(1, 2**1075)                         # underflow threshold

DBL_MAX = float.fromhex("0x1.fffffffffffffp+1023")
SMALLEST = 5e-324


def bits(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def taylor_lower(w: F, n: int) -> F:
    """sum_{k<=n} w^k/k!, exact, for 0 <= w < 1."""
    s = F(0)
    term = F(1)
    for k in range(n + 1):
        if k > 0:
            term = term * w / k
        s += term
    return s


def tail_bound(w: F, n: int) -> F:
    """2*(w/2)^(n+1)/(1 - w/2) >= sum_{k>n} w^k/k! for 0 <= w < 2."""
    return 2 * (w / 2) ** (n + 1) / (1 - w / 2)


def ceil_dyadic(q: F, b: int) -> F:
    s = 1 << b
    return F(-((-q.numerator * s) // q.denominator), s)


def floor_dyadic(q: F, b: int) -> F:
    s = 1 << b
    return F((q.numerator * s) // q.denominator, s)


def main() -> int:
    ok = True
    print("anchors (IEEE64 bit patterns):")
    for name, v in (("X_MAX", X_MAX), ("nextUp", U1),
                    ("X_MIN", X_MIN), ("nextDown", D1)):
        f = F(v)
        print("  %-9s %#018x  = %d / %d" % (name, bits(v),
                                            f.numerator, f.denominator))
    print()

    checks = [
        # (label, x, want_upper: True => prove exp(x) < BOUND, False => exp(x) > BOUND)
        ("exp(X_MAX)      < T  (finite at RN threshold)",
         F(X_MAX), True, T),
        ("exp(nextUp X_MAX) > T  (overflow)",
         F(U1), False, T),
        ("exp(X_MIN)      > H  (nonzero subnormal)",
         -F(X_MIN), True, 1 / H),   # exp(-X_MIN) < 1/H  <=>  exp(X_MIN) > H
        ("exp(nextDown X_MIN) < H  (underflow to zero)",
         -F(D1), False, 1 / H),     # exp(-D1) > 2^1075
    ]

    tightest = None
    for label, xabs, is_upper, bound in checks:
        assert xabs > 0
        w = xabs / SPLIT
        assert 0 < w < 1
        s = taylor_lower(w, N_TAYLOR)
        if is_upper:  # exp(xabs) <= (ceil(s + tail))^SPLIT < bound
            b = ceil_dyadic(s + tail_bound(w, N_TAYLOR), FRAC_BITS)
            holds = b ** SPLIT < bound
            margin = (bound - b ** SPLIT) / bound
            # budget of the bound vs the sum: rounding + tail, per-w relative
            budget = (b - s) / s
        else:          # exp(xabs) >= (floor(s))^SPLIT > bound
            b = floor_dyadic(s, FRAC_BITS)
            holds = b ** SPLIT > bound
            margin = (b ** SPLIT - bound) / bound
            budget = (s - b) / s
        print("%s : %s" % ("PASS" if holds else "FAIL", label))
        print("     n=%d  dyadic=%d-bit  relative margin ~%.3e" %
              (N_TAYLOR, b.numerator.bit_length(), margin))
        print("     per-w bound budget ~%.3e (1024x-amplified ~%.3e)" %
              (budget, budget * SPLIT))
        ratio = margin / budget
        if tightest is None or ratio < tightest[0]:
            tightest = (ratio, label)
        print("     literal = %d / %d" % (b.numerator, b.denominator))
        ok = ok and holds

    print()
    print("tightest margin/budget ratio: %.3e  (%s)" % tightest)

    # Independent high-precision sanity cross-check via decimal ln2 scaling is
    # NOT used; instead: the libm probe, kept separate from the exact math.
    print()
    print("this-platform C libm probe (observation only, not part of the")
    print("exact certificate; a different libm may differ at these points):")
    probes = [
        ("exp(X_MAX)", lambda: math.exp(X_MAX),
         lambda r: math.isfinite(r) and r < DBL_MAX),
        ("exp(nextUp X_MAX)", lambda: _try_exp(U1),
         lambda r: r is None),
        ("exp(X_MIN)", lambda: math.exp(X_MIN),
         lambda r: r == SMALLEST and r > 0.0),
        ("exp(nextDown X_MIN)", lambda: _try_exp(D1),
         lambda r: r == 0.0 or r is None),
    ]
    for name, fn, pred in probes:
        r = fn()
        good = pred(r)
        print("  %-22s -> %-24s  %s" % (name, repr(r),
                                        "PASS" if good else "FAIL"))
        ok = ok and good
    print()
    print("VERDICT:", "ALL EXACT COMPARISONS + PROBES PASS" if ok else "FAIL")
    print("NUMERICAL OBSERVATION ONLY (F-012): exact comparisons bound the")
    print("real exponential at four stated rationals; the probe records this")
    print("libm's behavior and certifies nothing about any implementation.")
    return 0 if ok else 1


def _try_exp(x: float):
    try:
        return math.exp(x)
    except OverflowError:
        return None


if __name__ == "__main__":
    sys.exit(main())
