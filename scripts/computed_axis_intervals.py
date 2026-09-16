#!/usr/bin/env python3
"""Interval regeneration of the COMPUTED_AXIS diagnostic table.

NUMERICAL OBSERVATION TOOLING (F-012 / learn-kernel discipline). This script
does not certify a continuum PDE statement and proves nothing about the Lean
theorem. It re-evaluates the fixed-order expression implemented by
`solver/src/construction.rs` at the declared default configuration,
tau = 0.05, grid 7^3, under an outward-rounded float64 interval envelope:
every binary arithmetic operation and every transcendental call on the dual
path is widened by 1 ulp on each side (math.nextafter).

Soundness model (same fixed-order monotone-rounding induction as the
NS5-SOLVER lane's solver/interval_cert/float64_cert.py, which is not on this
base): the enclosure bounds the value of the declared fixed-order expression
under any assignment whose per-operation result lies within 1 ulp of
correctly-rounded IEEE64 -- a class that includes compiler contraction (FMA)
and libm exp/ln/pow variation at that level.

Branch decisions (Newton termination, clamps, comparison tests, and
interpolation-cell selection) follow the POINT run. Every interpolated
evaluation checks that the eta enclosure stays inside the point-selected cell;
boundary-crossing events are counted and reported (an enclosure whose branch
was crossed makes no claim about the other branch's expression).

Containment of the fresh cargo baseline floats and of the committed docs-table
floats is an OBSERVED per-entry check reported in ulp units, not a consequence
of the enclosure.

The operation order and every constant below are transliterated from
solver/src/construction.rs at navier 3ed567cd; --verbose additionally
compares intermediate checkpoints against a NAVIER_DUMP=1 cargo run.

Usage:
  python3 scripts/computed_axis_intervals.py             # run + report
  python3 scripts/computed_axis_intervals.py --verbose   # + checkpoint deltas
  python3 scripts/computed_axis_intervals.py --markdown  # + docs table block

Dependencies: stdlib only. Runtime: minutes (pure-Python dual arithmetic).
"""

from __future__ import annotations

import argparse
import math
import sys

# ---------------------------------------------------------------------------
# Reference data (inputs to the checks, not outputs of this script).
# ---------------------------------------------------------------------------

# The committed docs table at regeneration time
# (docs/COMPUTED_AXIS_CONSTRUCTION.md, tau=0.05, 7^3 grid, config defaults).
DOCS_TABLE = {
    "angular profile RMS": 1.9921418144623968e-6,
    "axial profile RMS": 1.7733879359490666e-8,
    "pressure profile RMS": 3.3903453327861445e-9,
    "divergence RMS": 8.500463463624519e-3,
    "momentum residual RMS": 1.4123532691928133e5,
    "maximum sampled speed": 1.004429420038561e1,
    "displayed-domain energy": 2.4958636773964515e-1,
    "minimum normalized swirl": 2.6162692837448365e-1,
}

# Fresh `cargo test construction::tests -- --nocapture` on this machine
# (rustc 1.98.1, macOS arm64, navier 3ed567cd), test
# `reconstructed_field_is_finite_and_numerically_solenoidal`. The divergence
# and momentum entries differ from DOCS_TABLE by ~5e-13 relative (last-bit
# regression drift recorded in docs/NS5-SOLVER-FINDINGS.md section 5).
BASELINE = {
    "angular profile RMS": 1.9921418144623968e-6,
    "axial profile RMS": 1.7733879359490666e-8,
    "pressure profile RMS": 3.3903453327861445e-9,
    "divergence RMS": 0.008500463463628559,
    "momentum residual RMS": 141235.32691935662,
    "maximum sampled speed": 10.04429420038561,
    "displayed-domain energy": 0.24958636773964515,
    "minimum normalized swirl": 0.26162692837448365,
}

# Intermediates from the same build under NAVIER_DUMP=1, used by --verbose to
# localize porting mistakes. Point-path values only.
CHECKPOINTS = {
    "rho": 4.679129860476019e-8,
    "drop_length": 12.718281828459045,
    "wait": 193.13254949209204,
    "endpoint": 532.8508313205512,
    "flatten_length": 63.383246250395075,
    "flatten_end": 596.2340775709463,
    "release_start": 692.8003523169923,
    "second_ramp_start": 28.631021115928547,
    "ramp_end": 29.631021115928547,
    "tail_debt": 3.469518054892579e-7,
    "lag": 17.381620045980256,
    "decay_hold": 17.747240524976085,
    "tail_start": 740.1786139578969,
    "tail_end": 743.1786139578969,
    "quad_steps": 29728.0,
    "dy": 0.024999280609455627,
    "p0": -3.3145919451079413,
    "pmid": -13.258367780431765,
    "plast": -3.3145919451079413,
    "pe0": -6.629183890215883,
    "pemid": 0.0,
    "pelast": 6.629183890215883,
    "spacing": 0.0078125,
    "sigma": 3.9833360017358166e-5,
    "swirl": 3.3003039907216096e79,
    "min_h2": 6.346786281089873e-7,
    "phi_star_mid": 1.0,
    "chi_mid": 0.9984158170473851,
    "zeta_mid": -998.4158170473852,
    "z_star_mid": -0.004501,
    "u_star_mid": 0.001,
    "h_star_mid": 0.001,
    "w_star_mid": -3.0,
    "phi_mid0": 1.0,
    "phi_mid5": 0.0003335832226969739,
    "phi_mid12": -3.5252536188544414e-10,
    "ax_mid1": 0.0022505,
    "ax_mid12": 2.3062875051782873e-14,
    "pinc_mid0": 0.0,
    "pinc_mid12": 1.1283784288046055e-167,
    "fpd": 0.0,
}

ENTRY_ORDER = list(DOCS_TABLE.keys())

Y_LIMIT = 3.2
ETA_LIMIT = 0.8

# ---------------------------------------------------------------------------
# Dual (point, lo, hi) scalar algebra. A value is a 3-tuple (p, lo, hi) where
# p is the IEEE64 point run (drives control flow and is reported as the
# regenerated value) and [lo, hi] is the outward-rounded enclosure of the
# declared operation under the 1-ulp-per-operation deviation model. Every
# helper below reproduces Rust's left-to-right operation order at the point
# bit level; the enclosure widens each operation by one representable step per
# side. Exact float constants enter through s_const and are not widened.
# ---------------------------------------------------------------------------

_NINF = float("-inf")
_INF = float("inf")


def s_const(x):
    return (x, x, x)


def s_add(a, b):
    return (a[0] + b[0], math.nextafter(a[1] + b[1], _NINF),
            math.nextafter(a[2] + b[2], _INF))


def s_sub(a, b):
    return (a[0] - b[0], math.nextafter(a[1] - b[2], _NINF),
            math.nextafter(a[2] - b[1], _INF))


def s_mul(a, b):
    q = (a[1] * b[1], a[1] * b[2], a[2] * b[1], a[2] * b[2])
    return (a[0] * b[0], math.nextafter(min(q), _NINF),
            math.nextafter(max(q), _INF))


def s_scale(a, c):
    """a * c where c is an exact float constant (one operation)."""
    if c >= 0.0:
        return (a[0] * c, math.nextafter(a[1] * c, _NINF),
                math.nextafter(a[2] * c, _INF))
    return (a[0] * c, math.nextafter(a[2] * c, _NINF),
            math.nextafter(a[1] * c, _INF))


def s_neg(a):
    return (-a[0], -a[2], -a[1])


def s_div(a, b):
    if b[1] <= 0.0 <= b[2]:
        raise ValueError("division by interval containing zero: %r" % (b,))
    if b[1] > 0.0:
        q = (a[1] / b[1], a[1] / b[2], a[2] / b[1], a[2] / b[2])
    else:
        q = (a[2] / b[1], a[1] / b[1], a[2] / b[2], a[1] / b[2])
    return (a[0] / b[0], math.nextafter(min(q), _NINF),
            math.nextafter(max(q), _INF))


def s_exp(a):
    return (math.exp(a[0]), math.nextafter(math.exp(a[1]), _NINF),
            math.nextafter(math.exp(a[2]), _INF))


def s_ln(a):
    if a[1] <= 0.0:
        raise ValueError("ln interval endpoint <= 0: %r" % (a,))
    return (math.log(a[0]), math.nextafter(math.log(a[1]), _NINF),
            math.nextafter(math.log(a[2]), _INF))


def s_pow(a, p):
    """a ** p for a fixed float exponent p, with a > 0 on the declared path."""
    if a[1] <= 0.0:
        raise ValueError("pow interval endpoint <= 0: %r" % (a,))
    if p >= 0.0:
        return (math.pow(a[0], p), math.nextafter(math.pow(a[1], p), _NINF),
                math.nextafter(math.pow(a[2], p), _INF))
    return (math.pow(a[0], p), math.nextafter(math.pow(a[2], p), _NINF),
            math.nextafter(math.pow(a[1], p), _INF))


def s_sqrt(a):
    if a[2] < 0.0:
        raise ValueError("sqrt interval entirely negative: %r" % (a,))
    lo = max(a[1], 0.0)
    return (math.sqrt(a[0]), math.nextafter(math.sqrt(lo), _NINF),
            math.nextafter(math.sqrt(a[2]), _INF))


def s_abs(a):
    if a[1] >= 0.0:
        return a
    if a[2] <= 0.0:
        return (-a[0], -a[2], -a[1])
    return (abs(a[0]), 0.0, math.nextafter(max(-a[1], a[2]), _INF))


def s_max(a, b):
    # range of max(x, y) over x in [a1,a2], y in [b1,b2] is [max lo, max hi]
    return (max(a[0], b[0]), max(a[1], b[1]), max(a[2], b[2]))


def s_min(a, b):
    # range of min(x, y) over x in [a1,a2], y in [b1,b2] is [min lo, min hi]
    return (min(a[0], b[0]), min(a[1], b[1]), min(a[2], b[2]))


EPS = 2.220446049250313e-16
F64_MAX = 1.7976931348623157e308
TIE_EVENTS = [0]
BOUNDARY_EVENTS = [0]


def ck_tie():
    TIE_EVENTS[0] += 1


def ck_boundary():
    BOUNDARY_EVENTS[0] += 1


def idx(order, node, degree):
    return node * (order + 1) + degree


class Config:
    """AxisConstructionConfig::default()."""

    def __init__(self):
        self.h = 0.001
        self.j0 = 0.001
        self.schedule_lambda = 0.04
        self.schedule_m = 1.0
        self.radial_scale = 48.0
        self.pressure_amplitude = 2.0
        self.radial_order = 12
        self.eta_nodes = 257
        self.iterations = 18


# ---------------------------------------------------------------------------
# Appendix-A pressure schedule (build_pressure_axis, transliterated).
# ---------------------------------------------------------------------------


def smooth_step(x):
    if x[0] <= 0.0:
        return s_const(0.0)
    if x[0] >= 1.0:
        return s_const(1.0)
    left = s_exp(s_div(s_const(-1.0), s_mul(x, x)))
    om = s_sub(s_const(1.0), x)
    right = s_exp(s_div(s_const(-1.0), s_mul(om, om)))
    return s_div(left, s_add(left, right))


def smooth_step_derivative(x):
    if not (0.0 < x[0] < 1.0):
        return s_const(0.0)
    value = smooth_step(x)
    om = s_sub(s_const(1.0), x)
    # powi(3): x*x*x as two rounded multiplications, not libm pow.
    x3 = s_mul(s_mul(x, x), x)
    o3 = s_mul(s_mul(om, om), om)
    inner = s_add(s_div(s_const(2.0), x3), s_div(s_const(2.0), o3))
    return s_mul(s_mul(value, s_sub(s_const(1.0), value)), inner)


def simpson2048(f):
    """simpson(0.0, 3.0, 2048, f); intervals + intervals % 2 == 2048."""
    intervals = 2048
    step = 3.0 / intervals
    acc = s_add(f(0.0), f(3.0))
    for i in range(1, intervals):
        w = 2.0 if i % 2 == 0 else 4.0
        acc = s_add(acc, s_mul(s_const(w), f(i * step)))
    return s_div(s_mul(acc, s_const(step)), s_const(3.0))


def build_pressure_axis(eta, h, lam, m, amplitude, ck):
    """Returns (point_pressure, point_pressure_eta, P_enc, PE_enc)."""
    n = len(eta)
    step_bound = 8.0
    rho = s_div(s_scale(s_exp(s_const(-5.0)), h),
                s_const(16.0 * (step_bound + 1.0)))
    drop_length = s_add(s_exp(s_const(m)), s_const(10.0))
    ln_inv_lam = s_ln(s_div(s_const(1.0), s_const(lam)))
    wait = s_scale(ln_inv_lam, 60.0)
    endpoint = s_add(s_add(s_add(drop_length, s_const(2.0)), wait),
                     s_div(s_const(13.0), s_const(lam)))
    ln2 = s_ln(s_const(2.0))
    flatten_length = s_add(s_mul(s_const(10.0 * (step_bound + 1.0)), ln2),
                           s_const(1.0))
    flatten_end = s_add(endpoint, flatten_length)
    release_start = s_add(flatten_end, s_scale(ln_inv_lam, 30.0))
    second_ramp_start = s_add(
        s_const(1.0), s_scale(s_ln(s_div(s_const(1.0), s_const(h))), 4.0))
    ramp_end = s_add(second_ramp_start, s_const(1.0))

    ck("rho", rho)
    ck("drop_length", drop_length)
    ck("wait", wait)
    ck("endpoint", endpoint)
    ck("flatten_length", flatten_length)
    ck("flatten_end", flatten_end)
    ck("release_start", release_start)
    ck("second_ramp_start", second_ramp_start)
    ck("ramp_end", ramp_end)

    def tail_shape(t):
        ss = smooth_step(s_scale(s_sub(s_const(t), s_const(1.0)), 0.5))
        return s_add(s_sub(s_const(1.0), rho), s_mul(rho, ss))

    def tail_shape_derivative(t):
        ssd = smooth_step_derivative(
            s_scale(s_sub(s_const(t), s_const(1.0)), 0.5))
        return s_mul(s_mul(s_const(0.5), rho), ssd)

    one_m_h = 1.0 - h
    one_m_lam = 1.0 - lam

    tail_debt = s_div(simpson2048(
        lambda t: s_mul(s_exp(s_const(one_m_h * t)), tail_shape_derivative(t))),
        s_sub(s_const(1.0), rho))
    ck("tail_debt", tail_debt)

    def release_slope(ts):
        term1 = s_neg(s_const(lam))
        term2 = s_mul(s_const(one_m_lam), smooth_step(ts))
        term3 = s_mul(s_const(one_m_h),
                      smooth_step(s_sub(ts, second_ramp_start)))
        return s_add(s_sub(term1, term2), term3)

    lag = s_div(s_sub(s_const(lam), s_const(h)), s_sub(s_const(1.0), s_const(lam)))
    ode_steps = 32768
    ode_step = s_div(ramp_end, s_const(float(ode_steps)))
    ode_step_pt = ode_step[0]
    half_pt = ode_step_pt / 2.0

    def rhs(t, value):
        slope = release_slope(s_const(t))
        return s_sub(s_sub(s_neg(slope), s_const(h)),
                     s_mul(s_add(s_const(1.0), slope), value))

    for i in range(ode_steps):
        t = i * ode_step_pt
        k1 = rhs(t, lag)
        k2 = rhs(t + half_pt, s_add(lag, s_scale(k1, half_pt)))
        k3 = rhs(t + half_pt, s_add(lag, s_scale(k2, half_pt)))
        k4 = rhs(t + ode_step_pt, s_add(lag, s_scale(k3, ode_step_pt)))
        tot = s_add(s_add(s_add(k1, s_scale(k2, 2.0)), s_scale(k3, 2.0)), k4)
        lag = s_add(lag, s_div(s_mul(s_const(ode_step_pt), tot), s_const(6.0)))
    ck("lag", lag)

    decay_hold = s_div(s_ln(s_div(lag, tail_debt)), s_const(one_m_h))
    tail_start = s_add(s_add(release_start, ramp_end), decay_hold)
    tail_end = s_add(tail_start, s_const(3.0))
    ck("decay_hold", decay_hold)
    ck("tail_start", tail_start)
    ck("tail_end", tail_end)

    requested = math.ceil(tail_end[0] / 0.025)
    if not (1.0 <= float(requested) <= 1_000_000.0):
        raise RuntimeError(
            "Appendix-A pressure schedule exceeds the quadrature budget")
    steps = int(requested)
    dy = s_div(tail_end, s_const(float(steps)))
    dy_pt = dy[0]
    ck("quad_steps", s_const(float(steps)))
    ck("dy", dy)

    P = [s_const(0.0) for _ in range(n)]
    PE = [s_const(0.0) for _ in range(n)]
    log_radial = s_ln(s_const(amplitude))
    release_adjustment = s_const(0.0)
    log_1pe2 = [s_ln(s_add(s_const(1.0), s_const(e * e))) for e in eta]

    for si in range(steps):
        y = (si + 0.5) * dy_pt
        yv = s_const(y)
        slope = s_sub(
            s_scale(s_sub(s_const(1.0), smooth_step(yv)), 0.6),
            s_mul(s_const(lam),
                  smooth_step(s_sub(s_sub(yv, drop_length), s_const(1.0)))))
        half = s_scale(dy, 0.5)
        lrm = s_add(log_radial, s_mul(s_sub(slope, s_const(0.5)), half))
        release_t = s_const(y - release_start[0])
        rs = release_slope(release_t)
        rm = s_add(release_adjustment, s_mul(s_add(rs, s_const(lam)), half))
        flatten = smooth_step(s_div(s_sub(yv, endpoint), flatten_length))
        tail = s_div(tail_shape(y - tail_start[0]),
                    s_sub(s_const(1.0), rho))
        fm1 = s_sub(flatten, s_const(1.0))
        one_m_flatten = s_sub(s_const(1.0), flatten)
        fln2 = s_mul(flatten, ln2)
        for node in range(n):
            log_shape = s_sub(s_mul(fm1, log_1pe2[node]), fln2)
            arg = s_add(s_add(lrm, log_shape), rm)
            angular = s_mul(s_exp(arg), tail)
            square = s_mul(angular, angular)
            P[node] = s_add(P[node], s_mul(square, dy))
            PE[node] = s_add(PE[node],
                             s_mul(s_mul(one_m_flatten, square), dy))
        log_radial = s_add(log_radial, s_mul(s_sub(slope, s_const(0.5)), dy))
        release_adjustment = s_add(
            release_adjustment, s_mul(s_add(rs, s_const(lam)), dy))

    # Analytic tails (y < 0 power law and y >= tail_end constant).
    amp2 = s_mul(s_mul(s_const(5.0), s_const(amplitude)), s_const(amplitude))
    ln_amp = s_ln(s_const(amplitude))
    tv = s_mul(s_const(amplitude),
               s_exp(s_add(s_sub(log_radial, ln_amp), release_adjustment)))
    tv = s_div(s_scale(tv, 0.5), s_sub(s_const(1.0), rho))
    tv2_over = s_div(s_mul(tv, tv), s_const(1.0 + 2.0 * h))
    for node in range(n):
        e = eta[node]
        f = s_div(s_const(1.0), s_add(s_const(1.0), s_const(e * e)))
        add_term = s_mul(s_mul(amp2, f), f)
        P[node] = s_add(P[node], add_term)
        PE[node] = s_add(PE[node], add_term)
        P[node] = s_add(P[node], tv2_over)
        P[node] = s_mul(P[node], s_const(-0.5))
        PE[node] = s_mul(PE[node], s_div(s_const(2.0 * e),
                                         s_add(s_const(1.0), s_const(e * e))))
    for node in range(n):
        for v in (P[node], PE[node]):
            if not math.isfinite(v[0]):
                raise RuntimeError("non-finite pressure profile")
            if not (math.isfinite(v[1]) and math.isfinite(v[2])):
                raise RuntimeError("non-finite pressure enclosure endpoint")
    mid = n // 2
    ck("p0", P[0])
    ck("pmid", P[mid])
    ck("plast", P[n - 1])
    ck("pe0", PE[0])
    ck("pemid", PE[mid])
    ck("pelast", PE[n - 1])
    return [x[0] for x in P], [x[0] for x in PE], P, PE


# ---------------------------------------------------------------------------
# Radial/eta profile helpers (transliterated; all on the dual path).
# ---------------------------------------------------------------------------


def eta_derivative(values, nodes, order, spacing_c):
    out = [None] * (nodes * (order + 1))
    denom = s_const(12.0 * spacing_c)
    for degree in range(order + 1):
        at = lambda n: values[idx(order, n, degree)]
        for node in range(nodes):
            if node >= 2 and node + 2 < nodes:
                num = s_sub(s_add(s_sub(at(node - 2), s_scale(at(node - 1), 8.0)),
                                  s_scale(at(node + 1), 8.0)), at(node + 2))
            elif node == 0:
                num = s_sub(s_add(s_add(s_add(s_scale(at(0), -25.0),
                                               s_scale(at(1), 48.0)),
                                        s_scale(at(2), -36.0)),
                                 s_scale(at(3), 16.0)),
                          s_scale(at(4), -3.0))
            elif node == 1:
                num = s_add(s_sub(s_add(s_add(s_scale(at(0), -3.0),
                                              s_scale(at(1), -10.0)),
                                       s_scale(at(2), 18.0)),
                                s_scale(at(3), -6.0)),
                         at(4))
            elif node + 1 == nodes:
                num = s_add(s_sub(s_add(s_add(s_scale(at(node), 25.0),
                                             s_scale(at(node - 1), -48.0)),
                                      s_scale(at(node - 2), 36.0)),
                               s_scale(at(node - 3), -16.0)),
                        s_scale(at(node - 4), 3.0))
            else:
                num = s_sub(s_add(s_add(s_add(s_scale(at(node + 1), 3.0),
                                            s_scale(at(node), 10.0)),
                                     s_scale(at(node - 1), -18.0)),
                              s_scale(at(node - 2), 6.0)),
                       at(node - 3))
            out[idx(order, node, degree)] = s_div(num, denom)
    return out


def multiply(a, b, nodes, order):
    out = [s_const(0.0)] * (nodes * (order + 1))
    for node in range(nodes):
        base = node * (order + 1)
        for n in range(order + 1):
            s = s_const(0.0)
            for k in range(n + 1):
                s = s_add(s, s_mul(a[base + k], b[base + n - k]))
            out[base + n] = s
    return out


def j_operator(source, nodes, order, nu):
    out = [s_const(0.0)] * len(source)
    for node in range(nodes):
        base = node * (order + 1)
        for n in range(order):
            out[base + n + 1] = s_div(
                source[base + n], s_const(float((n + 1) * (n + nu))))
    return out


def radial_average(source, nodes, order):
    out = list(source)
    for node in range(nodes):
        base = node * (order + 1)
        for n in range(order + 1):
            out[base + n] = s_div(out[base + n], s_const(float(n + 1)))
    return out


def radial_integral(source, nodes, order):
    out = [s_const(0.0)] * len(source)
    for node in range(nodes):
        base = node * (order + 1)
        for n in range(order):
            out[base + n + 1] = s_div(source[base + n], s_const(float(n + 1)))
    return out


def radial_log_derivative(source, nodes, order):
    out = list(source)
    for node in range(nodes):
        base = node * (order + 1)
        for n in range(order + 1):
            out[base + n] = s_scale(out[base + n], float(n))
    return out


def evaluate(coeffs, node, order, y):
    """y is a dual value (its 1-ulp deviation propagates through Horner)."""
    value = s_const(0.0)
    for n in reversed(range(order + 1)):
        value = s_add(s_mul(value, y), coeffs[idx(order, node, n)])
    return value


def evaluate_derivative(coeffs, node, order, y):
    value = s_const(0.0)
    for n in reversed(range(1, order + 1)):
        value = s_add(s_mul(value, y),
                      s_scale(coeffs[idx(order, node, n)], float(n)))
    return value


def evaluate_second_derivative(coeffs, node, order, y):
    value = s_const(0.0)
    for n in reversed(range(2, order + 1)):
        value = s_add(s_mul(value, y),
                      s_scale(coeffs[idx(order, node, n)], float(n * (n - 1))))
    return value


# ---------------------------------------------------------------------------
# AxisConstruction::new.
# ---------------------------------------------------------------------------


class AxisConstruction:
    def __init__(self, config=None, ck=None):
        config = config or Config()
        ck = ck or (lambda name, v: None)
        self.config = config
        nodes = config.eta_nodes
        order = config.radial_order
        h = config.h
        scale = config.radial_scale
        spacing = 2.0 / (nodes - 1)
        eta = [-1.0 + i * spacing for i in range(nodes)]
        self.spacing = spacing
        self.eta = eta
        a = 0.5 + h
        d_exp = 0.5 - h
        ck("spacing", s_const(spacing))
        (pa, pae, pa_enc, pae_enc) = build_pressure_axis(
            eta, h, config.schedule_lambda, config.schedule_m,
            config.pressure_amplitude, ck)
        self.pa_enc = pa_enc
        self.pae_enc = pae_enc

        e_arr = [s_const(e) for e in eta]
        one = s_const(1.0)
        u_star = [None] * nodes
        h_star = [None] * nodes
        w_star = [None] * nodes
        z_star = [None] * nodes
        for i, e in enumerate(eta):
            ec = e_arr[i]
            d = s_sub(one, s_mul(ec, ec))
            us = s_add(s_scale(ec, 4.0), s_const(config.j0))
            hs = s_add(s_scale(ec, d_exp), s_mul(d, us))
            ws = s_sub(s_sub(one, s_scale(d, 4.0)),
                       s_mul(s_mul(s_const(2.0 * d_exp), ec), us))
            inner = s_sub(one, s_mul(s_scale(ec, 2.0), us))
            t4 = s_mul(s_mul(s_const(4.0 * a), ec), pa_enc[i])
            zs = s_add(s_sub(s_sub(s_mul(s_mul(s_neg(s_const(a)), inner), us),
                                   s_scale(hs, 4.0)),
                             s_mul(d, pae_enc[i])),
                       t4)
            u_star[i] = us
            h_star[i] = hs
            w_star[i] = ws
            z_star[i] = zs
        ck("u_star_mid", u_star[nodes // 2])
        ck("h_star_mid", h_star[nodes // 2])
        ck("w_star_mid", w_star[nodes // 2])
        ck("z_star_mid", z_star[nodes // 2])

        # sigma: Z*-transition locator (point-driven comparisons; ties and
        # sign-flips inside the enclosure are recorded as branch events).
        delta = config.j0 / 10.0
        min_pt = float("inf")
        min_dual = s_const(float("inf"))
        for i in range(nodes - 1):
            if abs(z_star[i][0]) <= delta:
                cand = s_mul(h_star[i], h_star[i])
                if cand[0] < min_pt:
                    min_pt, min_dual = cand[0], cand
                elif abs(cand[0] - min_pt) <= math.ulp(min_pt):
                    min_dual = s_min(min_dual, cand)
                    ck_tie()
            prod = s_mul(z_star[i], z_star[i + 1])
            if prod[0] <= 0.0:
                if prod[1] <= 0.0 <= prod[2]:
                    ck_tie()
                ai = s_abs(z_star[i])
                aj = s_abs(z_star[i + 1])
                weight = s_div(ai, s_max(s_add(ai, aj), s_const(1.0e-300)))
                value = s_add(h_star[i],
                              s_mul(weight, s_sub(h_star[i + 1], h_star[i])))
                cand = s_mul(value, value)
                if cand[0] < min_pt:
                    min_pt, min_dual = cand[0], cand
                elif abs(cand[0] - min_pt) <= math.ulp(min_pt):
                    min_dual = s_min(min_dual, cand)
                    ck_tie()
        if not (math.isfinite(min_pt) and min_pt > 0.0):
            raise RuntimeError("could not locate the Appendix-B Z* transition")
        ck("min_h2", min_dual)
        sigma = s_div(s_sqrt(min_dual), s_const(20.0))
        ck("sigma", sigma)
        chi = [None] * nodes
        zeta = [None] * nodes
        for i, e in enumerate(eta):
            l = s_sub(one, s_mul(s_mul(s_const(2.0 * h), e_arr[i]), e_arr[i]))
            hs2 = s_mul(h_star[i], h_star[i])
            denom = s_add(hs2, s_mul(sigma, sigma))
            chi[i] = s_div(hs2, denom)
            zeta[i] = s_div(s_mul(s_neg(l), h_star[i]), denom)
        ck("chi_mid", chi[nodes // 2])
        ck("zeta_mid", zeta[nodes // 2])

        zero = (nodes - 1) // 2
        primitive = [s_const(0.0)] * nodes
        half_spacing = s_const(0.5 * spacing)
        for i in range(zero + 1, nodes):
            primitive[i] = s_add(
                primitive[i - 1],
                s_mul(half_spacing, s_add(zeta[i - 1], zeta[i])))
        for i in range(zero - 1, -1, -1):
            primitive[i] = s_sub(
                primitive[i + 1],
                s_mul(half_spacing, s_add(zeta[i + 1], zeta[i])))
        phi_star = [s_exp(s_scale(p, scale)) for p in primitive]
        if any(not math.isfinite(v[0]) for v in phi_star):
            raise RuntimeError("axis azimuthal datum overflowed")
        ck("phi_star_mid", phi_star[nodes // 2])

        size = nodes * (order + 1)
        phi0 = [s_const(0.0)] * size
        axial0 = [s_const(0.0)] * size
        for node in range(nodes):
            factorial = 1.0
            next_factorial = 1.0
            power = s_const(1.0)
            base = node * (order + 1)
            for n in range(order + 1):
                if n > 0:
                    factorial *= float(n)
                    next_factorial *= float(n + 1)
                    power = s_mul(power, s_mul(s_const(-0.5), chi[node]))
                phi0[base + n] = s_div(power,
                                       s_const(factorial * next_factorial))
            e = eta[node]
            axial0[base + 1] = s_div(
                s_neg(z_star[node]),
                s_const(2.0 * (1.0 - (((2.0 * h) * e) * e))))
        max_star = s_const(1.0)
        for v in phi_star:
            max_star = s_max(max_star, v)
        swirl = s_scale(max_star, 4.0)
        ck("swirl", swirl)

        phi = list(phi0)
        axial = list(axial0)
        fpd = float("inf")
        pinc = [s_const(0.0)] * size
        ang_rem = [s_const(0.0)] * size
        ax_rem = [s_const(0.0)] * size
        scale_c = s_const(scale)
        two_scale = s_const(2.0 * scale)

        for iteration in range(config.iterations + 1):
            phi_eta = eta_derivative(phi, nodes, order, spacing)
            axial_eta = eta_derivative(axial, nodes, order, spacing)
            avg = radial_average(axial, nodes, order)
            avg_eta = eta_derivative(avg, nodes, order, spacing)
            axial_dx = radial_log_derivative(axial, nodes, order)
            phi_dx = radial_log_derivative(phi, nodes, order)
            phi_sq = multiply(phi, phi, nodes, order)
            axial_sq = multiply(axial, axial, nodes, order)
            ax_ax_eta = multiply(axial, axial_eta, nodes, order)

            psrc = [s_const(0.0)] * size
            for node in range(nodes):
                g = s_div(phi_star[node], swirl)
                g2 = s_mul(g, g)
                base = node * (order + 1)
                for n in range(order + 1):
                    psrc[base + n] = s_mul(phi_sq[base + n], g2)
            pinc = radial_integral(psrc, nodes, order)
            pre_eta = eta_derivative(pinc, nodes, order, spacing)
            pre_dx = radial_log_derivative(pinc, nodes, order)

            b = [s_const(0.0)] * size
            w = [s_const(0.0)] * size
            hc = [s_const(0.0)] * size
            for node in range(nodes):
                e = eta[node]
                ec = e_arr[node]
                d = s_sub(one, s_mul(ec, ec))
                base = node * (order + 1)
                m_b = s_mul(s_const(2.0 * d_exp), ec)
                for n in range(order + 1):
                    at = base + n
                    b[at] = s_sub(s_mul(s_neg(m_b), avg[at]),
                                  s_mul(d, avg_eta[at]))
                    w[at] = s_div(b[at], scale_c)
                    hc[at] = s_div(s_mul(d, axial[at]), scale_c)
                w[base] = s_add(w[base], w_star[node])
                hc[base] = s_add(hc[base], h_star[node])

            w_phi_dx = multiply(w, phi_dx, nodes, order)
            hc_phi_eta = multiply(hc, phi_eta, nodes, order)
            w_axial_dx = multiply(w, axial_dx, nodes, order)
            r1 = [s_const(0.0)] * size
            r2 = [s_const(0.0)] * size
            for node in range(nodes):
                e = eta[node]
                ec = e_arr[node]
                d = 1.0 - e * e
                l = 1.0 - ((2.0 * h) * e) * e
                base = node * (order + 1)
                us = u_star[node]
                hs = h_star[node]
                # Rust operand order per term of the r1 bracket:
                #   w - ((2*h)*e)*u_full + (d*zeta)*u_n + (h if n==0)
                m_w = s_mul(s_const(2.0 * h), ec)
                m_dz = s_scale(zeta[node], d)
                m_r2a = s_mul(s_const(2.0 * a), ec)
                for n in range(order + 1):
                    at = base + n
                    u_n = axial[at]
                    if n == 0:
                        u_full = s_add(s_div(u_n, scale_c), us)
                        add_h = s_const(h)
                    else:
                        u_full = s_div(u_n, scale_c)
                        add_h = s_const(0.0)
                    r1[at] = s_add(
                        s_add(s_sub(w[at], s_mul(m_w, u_full)),
                              s_mul(m_dz, u_n)),
                        add_h)
                    t1 = s_mul(
                        s_add(s_mul(s_const(a),
                                    s_sub(one, s_mul(s_scale(ec, 4.0), us))),
                              s_const(4.0 * d)),
                        u_n)
                    val = s_sub(t1,
                                s_div(s_mul(m_r2a, axial_sq[at]), scale_c))
                    val = s_add(val, w_axial_dx[at])
                    val = s_add(val, s_mul(hs, axial_eta[at]))
                    val = s_add(val,
                                s_div(s_mul(s_const(d), ax_ax_eta[at]),
                                      scale_c))
                    val = s_sub(val, s_mul(s_const(4.0 * a * e), pinc[at]))
                    val = s_add(val, s_mul(s_const(d), pre_eta[at]))
                    val = s_sub(val, s_scale(s_mul(ec, pre_dx[at]), 2.0))
                    r2[at] = s_div(val, s_const(l))
            r1 = multiply(r1, phi, nodes, order)
            for node in range(nodes):
                e = eta[node]
                lden = s_const(1.0 - ((2.0 * h) * (e * e)))
                base = node * (order + 1)
                for n in range(order + 1):
                    at = base + n
                    r1[at] = s_div(s_add(s_add(r1[at], w_phi_dx[at]),
                                         hc_phi_eta[at]), lden)
            ang_rem = r1
            ax_rem = r2
            if iteration == config.iterations:
                break

            corr_phi = j_operator(r1, nodes, order, 2)
            corr_ax = j_operator(r2, nodes, order, 1)
            next_phi = list(phi0)
            next_axial = list(axial0)
            for node in range(nodes):
                base = node * (order + 1)
                solved = [s_const(0.0)] * (order + 1)
                for n in range(order + 1):
                    at = base + n
                    rhs_v = s_div(corr_phi[at], two_scale)
                    if n == 0:
                        solved[n] = rhs_v
                    else:
                        solved[n] = s_sub(
                            rhs_v,
                            s_div(s_mul(chi[node], solved[n - 1]),
                                  s_const(2.0 * n * (n + 1))))
                    next_phi[at] = s_add(next_phi[at], solved[n])
                    next_axial[at] = s_add(
                        next_axial[at], s_div(corr_ax[at], two_scale))
            fpd = 0.0
            for lst_a, lst_b in ((next_phi, phi), (next_axial, axial)):
                for at in range(size):
                    dv = s_abs(s_sub(lst_a[at], lst_b[at]))[0]
                    if dv > fpd:
                        fpd = dv
            phi = next_phi
            axial = next_axial

        self.phi = phi
        self.axial = axial
        self.axial_average = radial_average(axial, nodes, order)
        self.pinc = pinc
        self.ang_rem = ang_rem
        self.ax_rem = ax_rem
        self.phi_star = phi_star
        self.swirl = swirl
        self.chi = chi
        self.z_star = z_star
        self.u_star = u_star
        self.fpd = fpd
        ck("fpd", s_const(fpd))
        ck("pinc_mid0", pinc[idx(order, nodes // 2, 0)])
        ck("pinc_mid12", pinc[idx(order, nodes // 2, 12)])
        mid = nodes // 2
        ck("phi_mid0", phi[idx(order, mid, 0)])
        ck("phi_mid5", phi[idx(order, mid, 5)])
        ck("phi_mid12", phi[idx(order, mid, 12)])
        ck("ax_mid1", axial[idx(order, mid, 1)])
        ck("ax_mid12", axial[idx(order, mid, 12)])


    # ---- interpolation ----

    def node_fraction(self, eta_v):
        cfg = self.config
        scaled = s_scale(s_mul(s_add(eta_v, s_const(1.0)), s_const(0.5)),
                         float(cfg.eta_nodes - 1))
        scaled_pt = min(max(scaled[0], 0.0), float(cfg.eta_nodes - 1))
        if scaled[1] < 0.0 or scaled[2] > float(cfg.eta_nodes - 1):
            ck_boundary()
        left = min(int(math.floor(scaled_pt)), cfg.eta_nodes - 2)
        if not (scaled[1] > float(left) and scaled[2] < float(left + 1)):
            ck_boundary()
        return left, scaled_pt - float(left)

    @staticmethod
    def _cubic(p0, p1, p2, p3, w):
        w2 = s_mul(w, w)
        w3 = s_mul(w2, w)
        t0 = s_scale(p1, 2.0)
        t1 = s_mul(s_add(s_neg(p0), p2), w)
        poly2 = s_add(s_add(s_add(s_scale(p0, 2.0), s_scale(p1, -5.0)),
                            s_scale(p2, 4.0)), s_neg(p3))
        t2 = s_mul(poly2, w2)
        poly3 = s_add(s_add(s_add(s_neg(p0), s_scale(p1, 3.0)),
                            s_scale(p2, -3.0)), p3)
        t3 = s_mul(poly3, w3)
        return s_scale(s_add(s_add(s_add(t0, t1), t2), t3), 0.5)

    def _cell(self, eta_v):
        cfg = self.config
        left, weight = self.node_fraction(eta_v)
        return (max(left - 1, 0), left, left + 1,
                min(left + 2, cfg.eta_nodes - 1), s_const(weight))

    def interpolate_polynomial(self, coefficients, eta_v, y):
        order = self.config.radial_order
        i0, i1, i2, i3, w = self._cell(eta_v)
        return self._cubic(
            evaluate(coefficients, i0, order, y),
            evaluate(coefficients, i1, order, y),
            evaluate(coefficients, i2, order, y),
            evaluate(coefficients, i3, order, y), w)

    def interpolate_scalar(self, values, eta_v):
        i0, i1, i2, i3, w = self._cell(eta_v)
        return self._cubic(values[i0], values[i1], values[i2], values[i3], w)

    def interpolate_polynomial_eta_derivative(self, coefficients, eta_v, y):
        cfg = self.config
        order = cfg.radial_order
        i0, i1, i2, i3, w = self._cell(eta_v)
        p0 = evaluate(coefficients, i0, order, y)
        p1 = evaluate(coefficients, i1, order, y)
        p2 = evaluate(coefficients, i2, order, y)
        p3 = evaluate(coefficients, i3, order, y)
        poly1 = s_add(s_neg(p0), p2)
        poly2 = s_add(s_add(s_add(s_scale(p0, 2.0), s_scale(p1, -5.0)),
                            s_scale(p2, 4.0)), s_neg(p3))
        poly3 = s_add(s_add(s_add(s_neg(p0), s_scale(p1, 3.0)),
                            s_scale(p2, -3.0)), p3)
        # 0.5 * ((-p0+p2) + 2.0*poly2*weight + 3.0*poly3*weight*weight)
        dw = s_scale(
            s_add(s_add(poly1, s_mul(s_scale(poly2, 2.0), w)),
                  s_mul(s_mul(s_scale(poly3, 3.0), w), w)), 0.5)
        # derivative_weight * (eta_nodes - 1) / 2.0
        return s_scale(s_scale(dw, float(cfg.eta_nodes - 1)), 0.5)

    # ---- similarity coordinates ----

    def similarity_q(self, tau, z):
        h = self.config.h
        if not (math.isfinite(tau) and tau > 0.0 and math.isfinite(z)):
            raise RuntimeError("tau must be finite and positive, z finite")
        z2 = z * z
        if not math.isfinite(z2):
            raise RuntimeError("z too large")
        if z2 == 0.0:
            return s_const(tau)
        d_exp = 0.5 - h
        two_h = 2.0 * h
        root_floor = s_pow(s_abs(s_const(z)), 1.0 / d_exp)
        if not (math.isfinite(root_floor[0]) and math.isfinite(root_floor[1])
                and math.isfinite(root_floor[2])):
            raise RuntimeError("similarity lower bracket overflowed")
        tau_c = s_const(tau)
        lo = tau_c
        hi = s_max(tau_c, root_floor)
        while True:
            value = s_sub(s_sub(hi, s_mul(s_const(z2), s_pow(hi, two_h))),
                          tau_c)
            if not math.isfinite(value[0]):
                raise RuntimeError("bracket residual non-finite")
            if value[0] > 0.0:
                break
            if hi[0] > F64_MAX / 2.0:
                raise RuntimeError("similarity root overflowed")
            hi = s_scale(hi, 2.0)
        q = hi
        for _ in range(64):
            power = s_pow(q, two_h)
            nonlinear = s_mul(s_const(z2), power)
            value = s_sub(s_sub(q, nonlinear), tau_c)
            scale = s_max(s_max(s_abs(q), s_abs(nonlinear)), tau_c)
            if math.isfinite(value[0]) and abs(value[0]) <= 8.0 * EPS * scale[0]:
                if tau <= 32.0 * EPS * scale[0]:
                    raise RuntimeError("tau below floating-point resolution")
                return q
            if value[0] > 0.0:
                hi = q
            else:
                lo = q
            derivative = s_sub(s_const(1.0),
                               s_div(s_mul(s_const(2.0 * h * z2), power), q))
            nxt = s_sub(q, s_div(value, derivative))
            if (math.isfinite(nxt[0]) and lo[0] < nxt[0] < hi[0]):
                q = nxt
            else:
                q = s_scale(s_add(lo, hi), 0.5)
        q = s_scale(s_add(lo, hi), 0.5)
        nonlinear = s_mul(s_const(z2), s_pow(q, two_h))
        value = s_sub(s_sub(q, nonlinear), tau_c)
        scale = s_max(s_max(s_abs(q), s_abs(nonlinear)), tau_c)
        if math.isfinite(value[0]) and abs(value[0]) <= 16.0 * EPS * scale[0]:
            if tau <= 32.0 * EPS * scale[0]:
                raise RuntimeError("tau below floating-point resolution")
            return q
        raise RuntimeError("similarity root did not converge")

    def domain_half_extent(self, tau):
        scale = self.config.radial_scale
        xy = math.sqrt(tau * Y_LIMIT / scale)
        qz = tau / (1.0 - ETA_LIMIT * ETA_LIMIT)
        z = ETA_LIMIT * math.pow(qz, 0.5 - self.config.h)
        extent = [xy, xy, z]
        if any(not (v > 0.0 and math.isfinite(v)) for v in extent):
            raise RuntimeError("tau outside chart range")
        return extent

    def point(self, tau, xyz):
        cfg = self.config
        scale = cfg.radial_scale
        if not all(math.isfinite(c) for c in xyz):
            raise RuntimeError("coordinates must be finite")
        q = self.similarity_q(tau, xyz[2])
        d_exp = 0.5 - cfg.h
        a = 0.5 + cfg.h
        scale_c = s_const(scale)
        eta = s_div(s_const(xyz[2]), s_pow(q, d_exp))
        x = s_div(s_add(s_mul(s_const(xyz[0]), s_const(xyz[0])),
                        s_mul(s_const(xyz[1]), s_const(xyz[1]))),
                  s_scale(q, 2.0))
        y = s_scale(x, scale)
        if abs(eta[0]) > 0.98 or y[0] > 4.05:
            raise RuntimeError("point outside chart")
        phi = self.interpolate_polynomial(self.phi, eta, y)
        u_correction = self.interpolate_polynomial(self.axial, eta, y)
        u_star = s_add(s_scale(eta, 4.0), s_const(cfg.j0))
        axial = s_add(u_star, s_div(u_correction, scale_c))
        averaged = self.interpolate_polynomial(self.axial_average, eta, y)
        averaged_eta = self.interpolate_polynomial_eta_derivative(
            self.axial_average, eta, y)
        d = s_sub(s_const(1.0), s_mul(eta, eta))
        l = s_sub(s_const(1.0),
                  s_mul(s_mul(s_const(2.0 * cfg.h), eta), eta))
        v0 = s_div(
            s_sub(
                s_sub(s_mul(s_scale(eta, 2.0), axial),
                      s_mul(s_mul(s_const(2.0 * d_exp), eta),
                            s_add(u_star, s_div(averaged, scale_c)))),
                s_mul(d, s_add(s_const(4.0),
                               s_div(averaged_eta, scale_c)))),
            l)
        f = s_div(s_mul(self.interpolate_scalar(self.phi_star, eta), phi),
                  self.swirl)
        pressure_profile = s_add(
            self.interpolate_scalar(self.pa_enc, eta),
            s_div(self.interpolate_polynomial(self.pinc, eta, y), scale_c))
        swirl_scale = s_mul(s_pow(q, -a - 0.5), f)
        vel0 = s_sub(s_div(s_mul(v0, s_const(xyz[0])), s_scale(q, 2.0)),
                     s_mul(swirl_scale, s_const(xyz[1])))
        vel1 = s_add(s_div(s_mul(v0, s_const(xyz[1])), s_scale(q, 2.0)),
                     s_mul(swirl_scale, s_const(xyz[0])))
        vel2 = s_mul(s_pow(q, -a), axial)
        pres = s_mul(s_pow(q, -2.0 * a), pressure_profile)
        for v in (vel0, vel1, vel2, pres):
            if not (math.isfinite(v[0]) and math.isfinite(v[1])
                    and math.isfinite(v[2])):
                raise RuntimeError("physical reconstruction non-finite")
        return vel0, vel1, vel2, pres

    def point_residual(self, tau, xyz, extent, relative_step=2.0e-4):
        center = self.point(tau, xyz)
        v = center[:3]
        p = center[3]
        grad = [[None] * 3 for _ in range(3)]
        lap = [s_const(0.0), s_const(0.0), s_const(0.0)]
        pgrad = [None] * 3
        for d in range(3):
            step = extent[d] * relative_step
            plus = list(xyz)
            minus = list(xyz)
            plus[d] += step
            minus[d] -= step
            vp = self.point(tau, plus)
            vm = self.point(tau, minus)
            two_step = s_const(2.0 * step)
            sq = s_const(step * step)
            for comp in range(3):
                grad[comp][d] = s_div(s_sub(vp[comp], vm[comp]), two_step)
                lap[comp] = s_add(
                    lap[comp],
                    s_div(s_add(s_sub(vp[comp], s_scale(v[comp], 2.0)),
                                vm[comp]), sq))
            pgrad[d] = s_div(s_sub(vp[3], vm[3]), two_step)
        dtau = tau * relative_step
        if not (dtau > 0.0 and tau - dtau > 0.0):
            raise RuntimeError("temporal residual step not representable")
        later = self.point(tau + dtau, xyz)
        earlier = self.point(tau - dtau, xyz)
        two_dtau = s_const(2.0 * dtau)
        residual = []
        for comp in range(3):
            temporal = s_div(s_sub(earlier[comp], later[comp]), two_dtau)
            adv = s_add(s_add(s_mul(v[0], grad[comp][0]),
                              s_mul(v[1], grad[comp][1])),
                        s_mul(v[2], grad[comp][2]))
            residual.append(
                s_add(s_sub(s_add(temporal, adv), lap[comp]),
                      pgrad[comp]))
        divergence = s_add(s_add(grad[0][0], grad[1][1]), grad[2][2])
        return residual, divergence

    # ---- grid diagnostics ----

    def min_normalized_swirl(self):
        order = self.config.radial_order
        mn = None
        for node in range(self.config.eta_nodes):
            if abs(self.eta[node]) <= ETA_LIMIT:
                for sample in range(33):
                    y = s_const(Y_LIMIT * sample / 32.0)
                    value = evaluate(self.phi, node, order, y)
                    if mn is None:
                        mn = value
                    elif value[0] < mn[0]:
                        if mn[0] - value[0] <= math.ulp(abs(mn[0])):
                            mn = s_min(mn, value)
                            ck_tie()
                        else:
                            mn = value
                    elif value[0] - mn[0] <= math.ulp(abs(mn[0])):
                        mn = s_min(mn, value)
                        ck_tie()
        return mn

    def profile_equation_rms(self):
        cfg = self.config
        order = cfg.radial_order
        ang_sum = s_const(0.0)
        ax_sum = s_const(0.0)
        pre_sum = s_const(0.0)
        count = 0
        scale_c = s_const(cfg.radial_scale)
        for node in range(2, cfg.eta_nodes - 2):
            if abs(self.eta[node]) > ETA_LIMIT:
                continue
            eta = self.eta[node]
            l = 1.0 - ((2.0 * cfg.h) * eta) * eta
            g = s_div(self.phi_star[node], self.swirl)
            g2 = s_mul(g, g)
            for sample in range(33):
                yv = Y_LIMIT * sample / 32.0
                y = s_const(yv)
                phi = evaluate(self.phi, node, order, y)
                phi_y = evaluate_derivative(self.phi, node, order, y)
                phi_yy = evaluate_second_derivative(self.phi, node, order, y)
                axial_y = evaluate_derivative(self.axial, node, order, y)
                axial_yy = evaluate_second_derivative(
                    self.axial, node, order, y)
                ang_rem = evaluate(self.ang_rem, node, order, y)
                ax_rem = evaluate(self.ax_rem, node, order, y)
                pressure_y = evaluate_derivative(
                    self.pinc, node, order, y)
                angular = s_sub(
                    s_add(s_scale(s_add(s_scale(phi_yy, yv),
                                        s_scale(phi_y, 2.0)), 2.0),
                          s_mul(self.chi[node], phi)),
                    s_div(ang_rem, scale_c))
                axial = s_add(
                    s_add(s_scale(s_add(s_scale(axial_yy, yv), axial_y), 2.0),
                          s_div(self.z_star[node], s_const(l))),
                    s_neg(s_div(ax_rem, scale_c)))
                pressure = s_sub(pressure_y, s_mul(s_mul(g2, phi), phi))
                ang_sum = s_add(ang_sum, s_mul(angular, angular))
                ax_sum = s_add(ax_sum, s_mul(axial, axial))
                pre_sum = s_add(pre_sum, s_mul(pressure, pressure))
                count += 1
        divisor = s_const(float(max(count, 1)))
        return (s_sqrt(s_div(ang_sum, divisor)),
                s_sqrt(s_div(ax_sum, divisor)),
                s_sqrt(s_div(pre_sum, divisor)))

    def evaluate_grid(self, grid, tau):
        extent = self.domain_half_extent(tau)
        count = grid ** 3
        residual_sum = s_const(0.0)
        divergence_sum = s_const(0.0)
        energy_sum = s_const(0.0)
        max_speed = s_const(0.0)
        for i in range(grid):
            xv = -extent[0] + 2.0 * extent[0] * i / (grid - 1)
            for j in range(grid):
                yv = -extent[1] + 2.0 * extent[1] * j / (grid - 1)
                for k in range(grid):
                    zv = -extent[2] + 2.0 * extent[2] * k / (grid - 1)
                    pt = self.point(tau, [xv, yv, zv])
                    res, div = self.point_residual(tau, [xv, yv, zv], extent)
                    speed2 = s_add(s_add(s_mul(pt[0], pt[0]),
                                         s_mul(pt[1], pt[1])),
                                   s_mul(pt[2], pt[2]))
                    max_speed = s_max(max_speed, s_sqrt(speed2))
                    weight = ((0.5 if i in (0, grid - 1) else 1.0)
                              * (0.5 if j in (0, grid - 1) else 1.0)
                              * (0.5 if k in (0, grid - 1) else 1.0))
                    energy_sum = s_add(
                        energy_sum,
                        s_mul(s_scale(speed2, 0.5), s_const(weight)))
                    res_sq = s_add(s_add(s_mul(res[0], res[0]),
                                         s_mul(res[1], res[1])),
                                   s_mul(res[2], res[2]))
                    residual_sum = s_add(residual_sum, res_sq)
                    divergence_sum = s_add(divergence_sum, s_mul(div, div))
        cell_volume = ((2.0 * extent[0] / (grid - 1))
                       * (2.0 * extent[1] / (grid - 1))
                       * (2.0 * extent[2] / (grid - 1)))
        ang, ax, pre = self.profile_equation_rms()
        count_c = s_const(float(count))
        return {
            "angular profile RMS": ang,
            "axial profile RMS": ax,
            "pressure profile RMS": pre,
            "divergence RMS": s_sqrt(s_div(divergence_sum, count_c)),
            "momentum residual RMS": s_sqrt(s_div(residual_sum, count_c)),
            "maximum sampled speed": max_speed,
            "displayed-domain energy": s_scale(energy_sum, cell_volume),
            "minimum normalized swirl": self.min_normalized_swirl(),
        }


# ---------------------------------------------------------------------------
# Reporting.
# ---------------------------------------------------------------------------


def ulp_distance(a, b):
    if a == b:
        return 0.0
    if a == 0.0 or b == 0.0:
        return float("inf")
    return abs(a - b) / max(math.ulp(min(abs(a), abs(b))), 5e-324)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--markdown", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()

    recorded = {}

    def ck(name, value):
        recorded[name] = value[0]
        if not (math.isfinite(value[1]) and math.isfinite(value[2])):
            raise RuntimeError("enclosure endpoint overflow at %s" % name)

    construction = AxisConstruction(ck=ck)
    diag = construction.evaluate_grid(7, 0.05)

    bad = 0
    if args.verbose:
        print("checkpoint point deltas (this run vs NAVIER_DUMP cargo run):")
        for name, want in CHECKPOINTS.items():
            got = recorded.get(name)
            if got is None:
                print("  %-20s MISSING" % name)
                bad += 1
                continue
            d = ulp_distance(got, want)
            flag = "OK " if d <= 1.0 else "BAD"
            if d > 1.0:
                bad += 1
            print("  %s %-20s got=%r want=%r ulp=%s"
                  % (flag, name, got, want, "%.2f" % d))
        print()

    header = ("entry                       point value            "
              "enclosure                                          "
              "width_ulp docs_ulp fresh_ulp docs_in fresh_in")
    print(header)
    results = {}
    for name in ENTRY_ORDER:
        p, lo, hi = diag[name]
        assert lo <= p <= hi, (name, lo, p, hi)
        docs_v = DOCS_TABLE[name]
        base_v = BASELINE[name]
        w_ulp = (hi - lo) / max(math.ulp(abs(p)), 5e-324)
        d_docs = ulp_distance(p, docs_v)
        d_base = ulp_distance(p, base_v)
        in_docs = lo <= docs_v <= hi
        in_base = lo <= base_v <= hi
        results[name] = dict(p=p, lo=lo, hi=hi, w_ulp=w_ulp, d_docs=d_docs,
                             d_base=d_base, in_docs=in_docs, in_base=in_base)
        print("%-26s %22r  [%24r, %24r]  %8.1f %8.1f %8.1f %6s %6s"
              % (name, p, lo, hi, w_ulp, d_docs, d_base, in_docs, in_base))

    max_w = max(r["w_ulp"] for r in results.values())
    all_in = all(r["in_docs"] and r["in_base"] for r in results.values())
    print()
    print("MAX-WIDTH %.1f ulp-of-value" % max_w)
    print("CONTAINMENT %s (docs table and fresh cargo baseline inside "
          "enclosures)" % ("PASS" if all_in else "FAIL"))
    print("BRANCH EVENTS interpolation-cell/clamp crossings: %d; "
          "tie events (min/branch ties inside enclosure): %d"
          % (BOUNDARY_EVENTS[0], TIE_EVENTS[0]))
    if bad:
        print("CHECKPOINTS %d BAD (port does not reproduce the cargo point run)"
              % bad)
    else:
        print("CHECKPOINTS ALL MATCH (<=1 ulp) the NAVIER_DUMP cargo run")
    print("NUMERICAL OBSERVATION ONLY (F-012): enclosures bound the declared "
          "fixed-order expression; branch control follows the point run.")

    if args.markdown:
        print()
        print("```text")
        for name in ENTRY_ORDER:
            r = results[name]
            print("%-24s %.17e  [%r, %r]" % (name, r["p"], r["lo"], r["hi"]))
        print("```")
    return 1 if (bad or not all_in) else 0


if __name__ == "__main__":
    sys.exit(main())
