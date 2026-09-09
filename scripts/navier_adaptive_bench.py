#!/usr/bin/env python3
"""Adaptive periodic-flow refinement with an independent analytic forcing.

The manufactured force uses the continuum Taylor–Green derivatives, never
the solver's nonlinear operator. Grid/time refinement and spectral diagnostics
are numerical evidence; they do not certify a continuum singularity.
"""

from __future__ import annotations

import argparse
import json
import math
import time

import numpy as np

import navier_spectral_core as core


def analytic_taylor_green_problem(sp, viscosity: float):
    """Return exact velocity and force for p=0 and u=s(t) Taylor–Green.

    div(v)=0, Δv=-3v, and (v·∇)v equals
    (sin(x)cos(x)cos²(z), sin(y)cos(y)cos²(z), 0).
    Thus f=s'v+s²(v·∇)v+3νsv solves the continuum forced PDE.
    """
    if not math.isfinite(viscosity) or viscosity < 0:
        raise ValueError("viscosity must be finite and nonnegative")
    x, y, z = np.meshgrid(*(3 * [2 * np.pi * np.arange(sp.n) / sp.n]), indexing="ij")
    velocity = np.stack((np.sin(x) * np.cos(y) * np.cos(z),
                         -np.cos(x) * np.sin(y) * np.cos(z), np.zeros_like(x)))
    convection = np.stack((np.sin(x) * np.cos(x) * np.cos(z) ** 2,
                           np.sin(y) * np.cos(y) * np.cos(z) ** 2, np.zeros_like(x)))
    velocity_hat = core.forward(velocity)
    convection_hat = core.forward(convection)

    def amplitude(t):
        return math.exp(-0.3 * t) * math.cos(1.7 * t)

    def exact(t):
        return amplitude(t) * velocity_hat

    def forcing(t):
        s = amplitude(t)
        ds = math.exp(-0.3 * t) * (-0.3 * math.cos(1.7 * t) - 1.7 * math.sin(1.7 * t))
        return (ds + 3 * viscosity * s) * velocity_hat + s * s * convection_hat

    return exact, forcing


def run_refinement(*, grids=(12, 18, 24), case="mms", viscosity=0.05,
                   final_time=0.5, initial_dt=0.1, rtol=1e-6, atol=1e-9,
                   cfl=0.5, tail_tolerance=1e-8):
    """Compare independent runs; the finest run is a reference, not truth."""
    grids = tuple(grids)
    if case not in ("mms", "tgv"):
        raise ValueError("case must be mms or tgv")
    if not grids or any(isinstance(n, bool) or not isinstance(n, int) or n < 8 or n % 2
                        for n in grids):
        raise ValueError("grids must be even integers at least 8")
    if any(a >= b for a, b in zip(grids, grids[1:])):
        raise ValueError("grids must be strictly increasing")
    rows = []
    for n in grids:
        sp = core.spectral(n)
        exact, forcing = analytic_taylor_green_problem(sp, viscosity)
        if case == "tgv":
            forcing = None
        started = time.perf_counter()
        result = core.evolve_adaptive(exact(0.0), sp, viscosity, final_time, initial_dt,
                                     forcing=forcing, rtol=rtol, atol=atol, cfl=cfl,
                                     tail_tolerance=tail_tolerance)
        row = dict(grid=n, wall_seconds=time.perf_counter() - started,
                   final_time=result.final_time, accepted_steps=result.accepted_steps,
                   rejected_steps=result.rejected_steps, min_dt=result.min_dt,
                   max_dt=result.max_dt, max_cfl=result.max_cfl,
                   max_error_ratio=result.max_error_ratio,
                   max_velocity_linf=result.max_velocity_linf,
                   max_vorticity_linf=result.max_vorticity_linf,
                   integrated_vorticity_linf=result.integrated_vorticity_linf,
                   max_tail_energy_fraction=result.max_tail_energy_fraction,
                   underresolved=result.underresolved, diagnostics=result.diagnostics)
        if case == "mms":
            row["relative_l2_error"] = core.relative_l2(result.state, exact(final_time), sp)
        rows.append(row)
    reference = rows[-1]["diagnostics"]["energy"]
    for row in rows:
        energy = row["diagnostics"]["energy"]
        row["energy_relative_difference_from_finest"] = (
            abs(energy - reference) / abs(reference) if reference else abs(energy - reference))
    return dict(case=case, viscosity=viscosity, final_time=final_time,
                rtol=rtol, atol=atol, cfl=cfl, tail_tolerance=tail_tolerance,
                interpretation="Numerical refinement and resolution diagnostics; no blowup certificate.",
                forcing="continuum analytic Taylor–Green, pressure zero" if case == "mms" else "zero",
                runs=rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=("mms", "tgv"), default="mms")
    parser.add_argument("--grids", type=int, nargs="+", default=[12, 18, 24])
    parser.add_argument("--viscosity", type=float, default=0.05)
    parser.add_argument("--final-time", type=float, default=0.5)
    parser.add_argument("--initial-dt", type=float, default=0.1)
    parser.add_argument("--rtol", type=float, default=1e-6)
    parser.add_argument("--atol", type=float, default=1e-9)
    parser.add_argument("--cfl", type=float, default=0.5)
    parser.add_argument("--tail-tolerance", type=float, default=1e-8)
    args = vars(parser.parse_args())
    try:
        result = run_refinement(**args)
        output = json.dumps(result, indent=2, allow_nan=False)
    except (ValueError, RuntimeError) as exc:
        parser.error(str(exc))
    print(output)


if __name__ == "__main__":
    main()
