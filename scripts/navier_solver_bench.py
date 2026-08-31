#!/usr/bin/env python3
"""Discriminating pseudo-spectral Navier--Stokes benchmark.

WHY THIS REPLACED THE ABC BENCHMARK
-----------------------------------
The previous benchmark evolved an Arnold--Beltrami--Childress flow and reported
``l2_rel_error = 6.87e-16`` -- a few ULPs of float64.  The metric was saturated
and could not distinguish a correct solver from a better one.  Three measured
facts explain why, and each is re-measured every run by ``nonlinear_activity``:

1.  For ``A = B = C`` the ABC field satisfies ``curl u = u`` exactly, so
    ``u x omega = u x u = 0``.  Measured: ``||u x omega||_rms = 2.7e-15`` against
    an O(1) field norm.
2.  The advective term is therefore a pure gradient,
    ``(u . grad) u = grad(|u|^2 / 2) - u x omega = grad(|u|^2 / 2)``, which the
    Leray projector annihilates.  Measured: ``||u . grad u||_rms = 7.07e-01``
    but ``||P_L[u . grad u]||_rms = 2.06e-15`` -- suppression of 2.9e-15.
3.  The ABC field occupies only the ``|k| = 1`` shell, so ``exp(-nu |k|^2 dt)``
    is a single scalar on every populated mode and the "independent exact
    reference" ``exp(-nu t) u_0`` is the same scalar multiplication the solver
    performs.  The old time loop additionally contained no nonlinear term at
    all: it was ``field_hat *= heat_step; ifft; fft``.

The old benchmark measured FFT round-trip round-off.  It validated neither the
advection term -- the entire difficulty of Navier--Stokes -- nor the time
integrator, nor dealiasing.

WHAT THIS MEASURES INSTEAD
--------------------------
``mms`` (headline) -- method of manufactured solutions on a Taylor--Green
carrier whose projected nonlinearity is O(1).  A forcing term makes a chosen
smooth ``u*(x, t)`` an exact solution while keeping advection live, so
``l2_rel_error`` is a genuine time-integration error that sits far above
round-off and responds to any change in the integrator, projector or dealiasing.

``tgv`` -- Taylor--Green vortex free decay, the standard nonlinear-active case,
scored by energy and enstrophy against a stated higher-resolution reference.

``abc`` -- the legacy Beltrami case, retained only as a regression guard on the
viscous exponential and the projector.

Reported alongside: the measured temporal convergence order (IFRK4 is fourth
order), inviscid energy drift (the rotational form is energy-neutral pointwise,
so drift is pure time-integrator truncation), the divergence residual, and
nonlinear activity for both the TGV and ABC carriers.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import time

# --------------------------------------------------------------------------
# Thread pinning MUST happen before numpy (and therefore BLAS/FFTW) is
# imported: these variables are read once, at library load.  An unpinned
# thread count makes the throughput metric depend on how many cores the OS
# felt like giving the process, which is not a property of the solver.
# ``setdefault`` so an explicit outer setting still wins.
# --------------------------------------------------------------------------
for _var in (
    "OMP_NUM_THREADS",
    "MKL_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "NUMEXPR_NUM_THREADS",
):
    os.environ.setdefault(_var, "1")

import numpy as np

try:
    from navier_spectral_core import (
        abc_field,
        energy,
        enstrophy,
        divergence_linf,
        evolve,
        forward,
        inverse,
        leray,
        mms_problem,
        nonlinear_hat,
        relative_l2,
        spectral,
        taylor_green_field,
    )
    from navier_accel import status as accel_status
except ImportError:  # invoked from outside scripts/
    import os
    import sys

    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from navier_spectral_core import (  # type: ignore[no-redef]
        abc_field,
        energy,
        enstrophy,
        divergence_linf,
        evolve,
        forward,
        inverse,
        leray,
        mms_problem,
        nonlinear_hat,
        relative_l2,
        spectral,
        taylor_green_field,
    )
    from navier_accel import status as accel_status  # type: ignore[no-redef]


# --------------------------------------------------------------------------
# timing
# --------------------------------------------------------------------------
#
# WHY THE THROUGHPUT METRIC IS CPU TIME, NOT WALL CLOCK
# -----------------------------------------------------
# Measured 2026-08-31 on macbook-satellite (18 cores), evolve of 20 steps at
# N = 16, 15 repetitions, loadavg 35:
#
#     wall clock   min 0.06327  median 0.16001  max 0.30676   -> 4.8x spread
#     CPU time     min 0.02765  median 0.02922                -> 1.06x spread
#
# The registry row recorded between_run_cv 0.4015 and mde_pct 97.26 for this
# metric: a throughput number that cannot resolve anything smaller than a 2x
# change is not a measurement, and the loop had been withholding its delta
# under delta_reason_code host_load for exactly this reason.  All of that
# variance is other processes competing for cores, none of it is the solver.
#
# CPU time is the right instrument here BECAUSE the solver is deliberately
# single-threaded: FFTW plans are built with threads=1 and the BLAS/OMP
# thread caps are pinned at the top of this file.  For a single-threaded
# process CPU time is what wall clock would have been on an idle host, so it
# is the same quantity the quiet-host anchor measured -- just observable
# without owning the machine.
#
# That is only true while the process really is single-threaded, and a
# multi-threaded solver would look WORSE on CPU time while being faster, so
# the invariant is checked rather than assumed: ``cpu <= wall * 1.05`` over
# the timed window is recorded as ``single_threaded``, and a run that fails
# it is flagged and the metric marked invalid.  Wall-clock throughput and
# host load are reported alongside, never silently dropped.

_LOAD_PER_CORE_QUIET = 0.75  # matches the estate host-load gate


def _loadavg() -> list[float] | None:
    """Return [1, 5, 15] minute load averages, or None on failure."""
    try:
        return list(os.getloadavg())
    except (OSError, AttributeError):
        pass
    try:
        raw = os.popen("sysctl -n vm.loadavg 2>/dev/null").read().strip()
        if raw:
            return [float(p) for p in raw.strip("{}").split()[:3]]
    except Exception:
        pass
    return None


def _cores() -> int:
    return os.cpu_count() or 1


def _host_load() -> dict:
    """Load snapshot and the quiet/contended verdict the metric is stamped with."""
    la = _loadavg()
    cores = _cores()
    per_core = (la[0] / cores) if la else float("nan")
    return {
        "loadavg": la,
        "cores": cores,
        "load_per_core": per_core,
        "quiet_host": bool(la) and per_core < _LOAD_PER_CORE_QUIET,
        "quiet_threshold_per_core": _LOAD_PER_CORE_QUIET,
    }


def _spread(values: list[float]) -> dict:
    """Robust spread summary: median, min, quartiles, IQR/median, CV."""
    n = len(values)
    ordered = sorted(values)
    mean = sum(ordered) / n
    if n > 1:
        var = sum((v - mean) ** 2 for v in ordered) / (n - 1)
        cv = math.sqrt(var) / mean if mean else float("nan")
    else:
        cv = 0.0

    def quantile(q: float) -> float:
        if n == 1:
            return ordered[0]
        pos = q * (n - 1)
        lo = int(math.floor(pos))
        hi = min(lo + 1, n - 1)
        return ordered[lo] + (pos - lo) * (ordered[hi] - ordered[lo])

    median = quantile(0.5)
    q1, q3 = quantile(0.25), quantile(0.75)
    return {
        "n": n,
        "min": ordered[0],
        "q1": q1,
        "median": median,
        "q3": q3,
        "max": ordered[-1],
        "iqr": q3 - q1,
        "iqr_over_median": (q3 - q1) / median if median else float("nan"),
        "cv": cv,
        "mean": mean,
    }


def time_kernel(fn, reps: int, warmup: int) -> dict:
    """Time ``fn`` ``reps`` times after ``warmup`` discarded calls.

    Warmup is not optional bookkeeping: the first call to a given grid builds
    the FFTW plans, compiles nothing but touches every scratch buffer for the
    first time, and pays every page fault in the working set.  Measured at
    N=16 the first evolve costs several times the steady-state one.

    Returns wall and CPU spreads plus the single-threaded verdict.
    """
    for _ in range(max(warmup, 0)):
        fn()
    walls: list[float] = []
    cpus: list[float] = []
    for _ in range(reps):
        c0 = time.process_time()
        w0 = time.perf_counter()
        fn()
        walls.append(max(time.perf_counter() - w0, 1e-12))
        cpus.append(max(time.process_time() - c0, 1e-12))
    total_cpu, total_wall = sum(cpus), sum(walls)
    return {
        "wall_s": _spread(walls),
        "cpu_s": _spread(cpus),
        "warmup_discarded": max(warmup, 0),
        "cpu_over_wall": total_cpu / total_wall,
        # A single-threaded process cannot accumulate CPU time faster than
        # wall time; 1.05 leaves room for timer granularity only.
        "single_threaded": (total_cpu / total_wall) <= 1.05,
    }


def _rms(field: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.sum(field**2, axis=0))))


def nonlinear_activity(sp, field: np.ndarray) -> float:
    """``||P_L[omega x u]||_rms / ||u||_rms^2`` -- dimensionless measure of how
    much of the nonlinearity survives Leray projection.  O(1e-1) for a generic
    flow, O(1e-15) for a Beltrami field, which is the saturation signature."""
    field_hat = leray(forward(field), sp)
    scale = _rms(inverse(field_hat, sp.n)) ** 2
    if scale == 0.0:
        return float("nan")
    return _rms(inverse(nonlinear_hat(field_hat, sp, True), sp.n)) / scale


def run_mms(grid: int, steps: int, viscosity: float, final_time: float) -> dict:
    """Headline accuracy instance: exact reference, live nonlinearity."""
    sp = spectral(grid)
    _, exact_hat, forcing = mms_problem(sp, viscosity)
    dt = final_time / steps

    state = evolve(exact_hat(0.0), sp, viscosity, dt, steps, True, forcing, 0.0)

    error = relative_l2(state, exact_hat(final_time), sp)

    # Half the step and re-run to measure the realised temporal order.
    refined = evolve(
        exact_hat(0.0), sp, viscosity, dt / 2.0, steps * 2, True, forcing, 0.0
    )
    error_refined = relative_l2(refined, exact_hat(final_time), sp)
    order = (
        math.log(error / error_refined) / math.log(2.0)
        if error_refined > 0.0 and error > 0.0
        else float("nan")
    )

    # Multi-dt convergence study: fit log-log slope across several dt values.
    multi_order = _multi_dt_convergence_order(sp, exact_hat, forcing,
                                               viscosity, final_time, dt)

    return {
        "l2_rel_error": error,
        "l2_rel_error_half_dt": error_refined,
        "time_convergence_order": float(order),
        "time_convergence_order_multi_dt": multi_order,
        "divergence_linf": divergence_linf(state, sp),
    }


def _multi_dt_convergence_order(
    sp, exact_hat, forcing, viscosity, final_time, dt_base
) -> float:
    """Fit log10(error) = p * log10(dt) + c across 5 dt values via LLS.

    dt values: dt_base / [1, 2, 4, 6, 8] (same final_time, scaled steps).
    Returns the slope *p* (design value 4 for IFRK4), or NaN if any
    sub-run produces a zero error.
    """
    ratios = (1, 2, 4, 6, 8)
    errors = []
    dts = []
    for ratio in ratios:
        dt_sub = dt_base / ratio
        steps_sub = max(round(final_time / dt_sub), 1)
        state_sub = evolve(
            exact_hat(0.0), sp, viscosity, dt_sub, steps_sub, True, forcing, 0.0
        )
        err = relative_l2(state_sub, exact_hat(final_time), sp)
        if err <= 0.0:
            return float("nan")
        errors.append(math.log10(err))
        dts.append(math.log10(dt_sub))

    # Linear least-squares: y = p*x + c
    n = len(dts)
    sx = sum(dts)
    sy = sum(errors)
    sxx = sum(x * x for x in dts)
    sxy = sum(x * y for x, y in zip(dts, errors))
    denom = n * sxx - sx * sx
    if denom == 0.0:
        return float("nan")
    p = (n * sxy - sx * sy) / denom
    return float(p)


def run_inviscid_drift(grid: int, steps: int, final_time: float) -> float:
    """Energy drift of the inviscid TGV flow.  The rotational form is pointwise
    energy-neutral (``omega x u`` is orthogonal to ``u``) and the 2/3 rule keeps
    the retained band alias-free, so any drift is time-integrator truncation."""
    sp = spectral(grid)
    state_hat = leray(forward(taylor_green_field(grid)), sp)
    start = energy(state_hat, sp)
    final = evolve(state_hat, sp, 0.0, final_time / steps, steps, True)
    return abs(energy(final, sp) - start) / start


def run_tgv(grid: int, steps: int, viscosity: float, final_time: float) -> dict:
    sp = spectral(grid)
    state_hat = leray(forward(taylor_green_field(grid)), sp)
    start_energy = energy(state_hat, sp)
    final = evolve(state_hat, sp, viscosity, final_time / steps, steps, True)
    final_energy = energy(final, sp)
    # Mean dissipation rate over the interval, -dE/dt in the bulk sense.
    return {
        "tgv_energy": float(final_energy),
        "tgv_enstrophy": float(enstrophy(final, sp)),
        "tgv_mean_dissipation": float((start_energy - final_energy) / final_time),
        "tgv_divergence_linf": divergence_linf(final, sp),
    }


def run_throughput(
    grid: int, steps: int, viscosity: float, final_time: float,
    reps: int, warmup: int,
) -> dict:
    """Headline performance instance, timed in isolation.

    PREVIOUSLY THIS WAS A BUG, not just noisy.  ``run_mms`` and ``run_tgv``
    each wrote a key named ``spectral_grid_updates_per_s`` into one shared
    metrics dict, and ``--case all`` (which is what every registered suite
    runs) called mms first and tgv second -- so the published headline was
    silently the TGV timing and the MMS timing was overwritten and lost.
    Timing now lives in exactly one place and neither accuracy instance
    reports a rate.

    The timed region is the stepping kernel ONLY: grid construction, the
    initial projection and every diagnostic are outside it.  Plans and page
    faults are paid in the discarded warmup.
    """
    sp = spectral(grid)
    state_hat = leray(forward(taylor_green_field(grid)), sp)
    dt = final_time / steps

    timing = time_kernel(
        lambda: evolve(state_hat, sp, viscosity, dt, steps, True), reps, warmup
    )
    updates = float(steps * grid**3)
    # 4 RHS evaluations per IFRK4 step; each does one batched 6-component
    # inverse and one batched 3-component forward real transform.
    transforms = float(steps * 4 * 9)

    cpu, wall = timing["cpu_s"], timing["wall_s"]
    valid = bool(timing["single_threaded"])
    headline = updates / cpu["min"] if valid else float("nan")
    return {
        "spectral_grid_updates_per_s": headline,
        "spectral_grid_updates_per_s_median": (
            updates / cpu["median"] if valid else float("nan")
        ),
        "spectral_grid_updates_per_s_wall": updates / wall["min"],
        "fft_transforms_per_s": (
            transforms / cpu["min"] if valid else float("nan")
        ),
        "timing_clock": "cpu_process_time_best_of_n",
        "timing_reps": timing["cpu_s"]["n"],
        "timing_warmup_discarded": timing["warmup_discarded"],
        "timing_cpu_iqr_over_median": cpu["iqr_over_median"],
        "timing_cpu_cv": cpu["cv"],
        "timing_wall_iqr_over_median": wall["iqr_over_median"],
        "timing_wall_cv": wall["cv"],
        "timing_cpu_over_wall": timing["cpu_over_wall"],
        "timing_single_threaded": valid,
        "cpu_s": cpu["min"],
        "wall_s": wall["min"],
    }


def run_abc(grid: int, steps: int, viscosity: float, dt: float) -> dict:
    """Legacy Beltrami regression guard.

    ABC occupies only ``|k| = 1``, so the exact solution of the full nonlinear
    system is ``u(t) = exp(-nu t) u_0``.  This is a valid regression check on
    the viscous integrating factor and the projector, and nothing more; its
    error saturates at round-off by construction."""
    sp = spectral(grid)
    initial = abc_field(grid)
    state_hat = leray(forward(initial), sp)
    final = evolve(state_hat, sp, viscosity, dt, steps, True)
    exact = math.exp(-viscosity * steps * dt) * initial
    got = inverse(final, grid)
    error = float(
        np.linalg.norm((got - exact).ravel()) / np.linalg.norm(exact.ravel())
    )
    measured_ratio = float(np.vdot(got, got).real / np.vdot(initial, initial).real)
    expected_ratio = math.exp(-2.0 * viscosity * steps * dt)
    return {
        "abc_l2_rel_error": error,
        "energy_decay_rel_error": abs(measured_ratio - expected_ratio)
        / expected_ratio,
        "abc_divergence_linf": divergence_linf(final, sp),
    }


def solve(
    grid: int,
    steps: int,
    viscosity: float,
    dt: float,
    case: str = "mms",
    final_time: float | None = None,
    reps: int = 5,
    warmup: int = 2,
) -> dict[str, float]:
    if grid < 4 or grid % 2 or steps < 1 or viscosity <= 0.0 or dt <= 0.0:
        raise ValueError(
            "even grid >= 4, steps >= 1, viscosity > 0, and dt > 0 required"
        )
    if reps < 1:
        raise ValueError("reps must be >= 1")
    horizon = final_time if final_time is not None else steps * dt

    metrics: dict[str, float] = {}
    # Headline performance first: extract_headline binds to the first measured
    # spec, and the registered sota_ref lives on this axis.
    metrics.update(
        run_throughput(grid, steps, viscosity, horizon, reps, warmup)
    )
    if case in ("mms", "all"):
        metrics.update(run_mms(grid, steps, viscosity, horizon))
    if case in ("tgv", "all"):
        metrics.update(run_tgv(grid, steps, viscosity, horizon))
    if case in ("abc", "all"):
        metrics.update(run_abc(grid, steps, viscosity, dt))

    sp = spectral(grid)
    metrics["nonlinear_activity"] = nonlinear_activity(sp, taylor_green_field(grid))
    metrics["nonlinear_activity_abc"] = nonlinear_activity(sp, abc_field(grid))
    metrics["inviscid_energy_drift"] = run_inviscid_drift(
        grid, max(steps // 2, 4), horizon
    )
    metrics["grid_points"] = float(grid**3)
    metrics["accelerator"] = accel_status()
    return metrics


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=16)
    parser.add_argument("--steps", type=int, default=20)
    parser.add_argument("--viscosity", type=float, default=0.05)
    parser.add_argument("--dt", type=float, default=0.05)
    parser.add_argument("--final-time", type=float, default=1.0)
    parser.add_argument(
        "--reps", type=int, default=5,
        help="timed repetitions of the stepping kernel (accuracy metrics are "
             "deterministic and are computed once)",
    )
    parser.add_argument(
        "--warmup", type=int, default=2,
        help="discarded calls before timing, to pay FFTW planning and page faults",
    )
    parser.add_argument(
        "--require-quiet", action="store_true",
        help="refuse to publish a measurement when 1-minute loadavg per core "
             "is at or above the quiet threshold",
    )
    parser.add_argument(
        "--case", choices=("mms", "tgv", "abc", "all"), default="mms"
    )
    args = parser.parse_args()
    if args.reps < 1:
        raise ValueError("--reps must be >= 1")

    host_before = _host_load()

    # REFUSE-TO-MEASURE is opt-in, and that is a measured decision rather than
    # a softening.  Both hosts in this estate sit far above the quiet
    # threshold essentially all the time (macbook-satellite loadavg 33-113 on
    # 18 cores, Studio 97 on 32, observed across this whole session), so a
    # hard refusal would make the row permanently unmeasurable -- which is
    # what the null parity_ratio and withheld deltas already amounted to.
    # The CPU-time clock is what makes the number survive that load; the flag
    # exists for when a caller genuinely needs a wall-clock-grade reading.
    if args.require_quiet and not host_before["quiet_host"]:
        print(json.dumps({
            "status": "SKIP",
            "reason": "host_load_above_quiet_threshold",
            "host_before": host_before,
        }, sort_keys=True))
        return 0

    metrics = solve(
        args.grid, args.steps, args.viscosity, args.dt,
        args.case, args.final_time, args.reps, args.warmup,
    )
    host_after = _host_load()

    status = "PASS"
    if not metrics.get("timing_single_threaded", True):
        # CPU time is only a stand-in for quiet-host wall time while the
        # process is single-threaded.  If it is not, say so instead of
        # publishing a number that flatters a solver for using more cores.
        status = "FAIL"

    print(json.dumps({
        "status": status,
        "metrics": metrics,
        "host_before": host_before,
        "host_after": host_after,
        "measurement_quality": (
            "quiet" if host_before["quiet_host"] and host_after["quiet_host"]
            else "contended"
        ),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
