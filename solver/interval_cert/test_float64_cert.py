#!/usr/bin/env python3
"""Tests for the float64 rounding-envelope certificates.

Every enclosure claim is verified two independent ways:

1. against ``mpmath`` *exact* re-evaluation of the same expression on the
   same float64 operands (50 decimal digits — mpf(float) conversion is
   exact via ``as_integer_ratio``), and
2. against the plain float64 point evaluation, which the widening argument
   says must also land inside the interval.
"""

from __future__ import annotations

import math
import random
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent))

import mpmath

mpmath.mp.dps = 50

from float64_cert import (  # noqa: E402
    Interval,
    certificate_record,
    certify_cumulative_dissipation,
    certify_energy_balance_defect,
    certify_energy_balance_series,
    enclose,
    i_add,
    i_div,
    i_mul,
    i_sub,
    i_sqrt,
    inflate,
)


def mp(x: float) -> mpmath.mpf:
    return mpmath.mpf(x)  # exact conversion of a float64 value


def test_point_enclosure_contains_exact_and_float():
    rng = random.Random(20260916)
    for trial in range(200):
        e = rng.uniform(-1e3, 1e3) * rng.choice([1.0, 1e-9, 1e9])
        d = rng.uniform(-1e3, 1e3)
        e0 = rng.uniform(1e-6, 1e3)
        r = certify_energy_balance_defect(e, d, e0)
        iv = r["defect_interval"]
        exact = mp(e) + mp(d) - mp(e0)
        assert mp(iv.lo) <= exact <= mp(iv.hi), trial
        assert iv.lo <= r["point_value"] <= iv.hi, trial
        # relative enclosure too
        rel_exact = exact / mp(e0)
        assert mp(r["relative_interval"].lo) <= rel_exact <= mp(r["relative_interval"].hi)


def test_cancellation_adversary():
    # E + D - E0 with E, E0 huge and defect tiny: naive float loses bits;
    # the envelope must still contain the exact value.
    e0 = 1.0 + 2**-40
    e = 1.0
    d = 2**-40
    r = certify_energy_balance_defect(e, d, e0)
    exact = mp(e) + mp(d) - mp(e0)
    iv = r["defect_interval"]
    assert mp(iv.lo) <= exact <= mp(iv.hi)
    assert iv.width > 0.0


def test_input_radius_inflation_widens_monotonically():
    tight = certify_energy_balance_defect(1.0, 2.0, 3.0)
    loose = certify_energy_balance_defect(1.0, 2.0, 3.0, input_radius=1e-12)
    assert tight["defect_interval"].lo >= loose["defect_interval"].lo
    assert tight["defect_interval"].hi <= loose["defect_interval"].hi
    exact = mp(1.0) + mp(2.0) - mp(3.0)
    assert mp(loose["defect_interval"].lo) <= exact <= mp(loose["defect_interval"].hi)


def test_nonfinite_operand_refuses_certification():
    r = certify_energy_balance_defect(float("inf"), 1.0, 1.0)
    assert not r["well_ordered"] or not math.isfinite(r["defect_interval"].hi)
    assert not certificate_record(r, backend="test")["finite_certification"]
    r2 = certify_energy_balance_defect(1.0, 1.0, 0.0)
    # zero initial energy: relative bound must not be a fabricated finite
    assert not (math.isfinite(r2["relative_interval"].lo)
                and math.isfinite(r2["relative_interval"].hi))


def test_series_worst_case_bound():
    rng = random.Random(7)
    energies = [1.0 * (1.0 - 0.01 * i) for i in range(50)]
    cums = [0.01 * i for i in range(50)]
    s = certify_energy_balance_series(energies, cums, 1.0)
    assert s["all_point_values_inside"]
    for e, d, iv in s["rows"]:
        exact = mp(e) + mp(d) - mp(1.0)
        assert mp(iv.lo) <= exact <= mp(iv.hi)
        assert abs(exact) <= mp(s["max_defect_abs_bound"])


def test_interval_operation_primitives_vs_mp():
    a = Interval(0.1, 0.30000000000000004)
    b = Interval(-2.5, 1e-8)
    for iv in (i_add(a, b), i_sub(a, b), i_mul(a, b), i_div(a, b)):
        assert iv.lo <= iv.hi
    # mul endpoint check: exact products inside
    for x in (0.1, 0.30000000000000004):
        for y in (-2.5, 1e-8):
            p = i_mul(Interval(x, x), Interval(y, y))
            assert mp(p.lo) <= mp(x) * mp(y) <= mp(p.hi)
    s = i_sqrt(Interval(2.0, 3.0))
    assert mp(s.lo) <= mpmath.sqrt(mp(2.0)) and mpmath.sqrt(mp(3.0)) <= mp(s.hi)


def test_enclose_and_inflate_basics():
    x = 0.1
    iv = enclose(x)
    assert iv.lo < x < iv.hi and iv.lo > _prev(x) - 2 * abs(_ulp(x))
    inf0 = inflate(0.0, 1e-9)
    assert inf0.lo <= 0.0 <= inf0.hi
    with pytest.raises(ValueError):
        inflate(1.0, -0.5)


def test_cumulative_dissipation_trapezoid():
    rng = random.Random(99)
    rates = [rng.uniform(-3.0, 9.0) for _ in range(200)]
    dt = 0.05
    iv = certify_cumulative_dissipation(rates, dt)
    # exact trapezoidal value in mpmath
    total = mp(0.0)
    for i in range(len(rates) - 1):
        total += 0.5 * mp(dt) * (mp(rates[i]) + mp(rates[i + 1]))
    assert mp(iv.lo) <= total <= mp(iv.hi)
    # fixed-order float64 evaluation must land inside as well
    acc = 0.0
    half_dt = 0.5 * dt
    for i in range(len(rates) - 1):
        acc += half_dt * (rates[i] + rates[i + 1])
    assert iv.lo <= acc <= iv.hi
    # np.trapezoid (different, pairwise order): exact value is enclosed; the
    # float64 point may differ from acc by order effects but both must be
    # within the ENVELOPE widened by at most a few ulp of the result scale.
    import numpy as _np
    trapz = float(_np.trapezoid(_np.asarray(rates) * 1.0, dx=dt))
    pad = 64 * math.ulp(max(abs(iv.hi), 1.0))
    assert iv.lo - pad <= trapz <= iv.hi + pad


def _ulp(x: float) -> float:
    return math.ulp(x)


def _prev(x: float) -> float:
    return math.nextafter(x, -math.inf)


def test_determinism_seed_recorded():
    r = certify_energy_balance_defect(0.1, 0.2, 0.30000000000000004)
    rec = certificate_record(r, backend="pytest", seed=20260916)
    assert rec["kind"] == "float64_rounding_envelope_observation"
    assert "F-012" in rec["scope"] or "observation" in rec["scope"]
    assert rec["defect_interval"][0] <= rec["defect_interval"][1]
