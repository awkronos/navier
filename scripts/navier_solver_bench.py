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
import time

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

    started = time.perf_counter()
    state = evolve(exact_hat(0.0), sp, viscosity, dt, steps, True, forcing, 0.0)
    elapsed = max(time.perf_counter() - started, 1e-12)

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

    # 4 RHS evaluations per IFRK4 step, 9 real transforms per evaluation.
    transforms = steps * 4 * 9
    return {
        "l2_rel_error": error,
        "l2_rel_error_half_dt": error_refined,
        "time_convergence_order": float(order),
        "divergence_linf": divergence_linf(state, sp),
        "spectral_grid_updates_per_s": float(steps * grid**3 / elapsed),
        "fft_transforms_per_s": float(transforms / elapsed),
        "wall_s": float(elapsed),
    }


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
    started = time.perf_counter()
    final = evolve(state_hat, sp, viscosity, final_time / steps, steps, True)
    elapsed = max(time.perf_counter() - started, 1e-12)
    final_energy = energy(final, sp)
    # Mean dissipation rate over the interval, -dE/dt in the bulk sense.
    return {
        "tgv_energy": float(final_energy),
        "tgv_enstrophy": float(enstrophy(final, sp)),
        "tgv_mean_dissipation": float((start_energy - final_energy) / final_time),
        "tgv_divergence_linf": divergence_linf(final, sp),
        "spectral_grid_updates_per_s": float(steps * grid**3 / elapsed),
        "wall_s": float(elapsed),
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
) -> dict[str, float]:
    if grid < 4 or grid % 2 or steps < 1 or viscosity <= 0.0 or dt <= 0.0:
        raise ValueError(
            "even grid >= 4, steps >= 1, viscosity > 0, and dt > 0 required"
        )
    horizon = final_time if final_time is not None else steps * dt

    metrics: dict[str, float] = {}
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
    return metrics


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=16)
    parser.add_argument("--steps", type=int, default=20)
    parser.add_argument("--viscosity", type=float, default=0.05)
    parser.add_argument("--dt", type=float, default=0.05)
    parser.add_argument("--final-time", type=float, default=1.0)
    parser.add_argument(
        "--case", choices=("mms", "tgv", "abc", "all"), default="mms"
    )
    args = parser.parse_args()
    metrics = solve(
        args.grid, args.steps, args.viscosity, args.dt, args.case, args.final_time
    )
    print(json.dumps({"status": "PASS", "metrics": metrics}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
