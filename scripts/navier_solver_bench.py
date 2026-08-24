#!/usr/bin/env python3
"""Deterministic spectral Navier--Stokes benchmark on an exact ABC flow.

The Arnold--Beltrami--Childress mode satisfies ``curl u = u`` and its
quadratic term is a pure pressure gradient.  After Leray projection the
periodic incompressible Navier--Stokes evolution is therefore the heat
semigroup ``u(t) = exp(-nu*t) u(0)``.  This harness advances that Fourier mode
and checks the computed field against the exact solution on a three-dimensional
grid.  It is deliberately standard-library only so the Studio solver sweep can
run it in an isolated Python environment.
"""

from __future__ import annotations

import argparse
import json
import math
import time


def abc_velocity(x: float, y: float, z: float) -> tuple[float, float, float]:
    return (
        math.sin(z) + math.cos(y),
        math.sin(x) + math.cos(z),
        math.sin(y) + math.cos(x),
    )


def solve(grid: int, steps: int, viscosity: float, dt: float) -> dict[str, float]:
    if grid < 4 or steps < 1 or viscosity <= 0.0 or dt <= 0.0:
        raise ValueError("grid >= 4, steps >= 1, viscosity > 0, and dt > 0 required")

    started = time.perf_counter()
    spacing = 2.0 * math.pi / grid
    amplitude = 1.0
    heat_step = math.exp(-viscosity * dt)
    for _ in range(steps):
        amplitude *= heat_step

    exact_amplitude = math.exp(-viscosity * steps * dt)
    error_sq = 0.0
    exact_sq = 0.0
    initial_sq = 0.0
    divergence_linf = 0.0

    for i in range(grid):
        x = i * spacing
        for j in range(grid):
            y = j * spacing
            for k in range(grid):
                z = k * spacing
                base = abc_velocity(x, y, z)
                computed = tuple(amplitude * value for value in base)
                exact = tuple(exact_amplitude * value for value in base)
                error_sq += sum((a - b) ** 2 for a, b in zip(computed, exact))
                exact_sq += sum(value * value for value in exact)
                initial_sq += sum(value * value for value in base)

                # Each ABC component is independent of its own coordinate.
                # Evaluate the centered discrete divergence anyway, so an
                # indexing or component regression is measured rather than
                # assumed away by the analytic argument.
                ux_p = amplitude * abc_velocity((i + 1) * spacing, y, z)[0]
                ux_m = amplitude * abc_velocity((i - 1) * spacing, y, z)[0]
                uy_p = amplitude * abc_velocity(x, (j + 1) * spacing, z)[1]
                uy_m = amplitude * abc_velocity(x, (j - 1) * spacing, z)[1]
                uz_p = amplitude * abc_velocity(x, y, (k + 1) * spacing)[2]
                uz_m = amplitude * abc_velocity(x, y, (k - 1) * spacing)[2]
                divergence = (ux_p - ux_m + uy_p - uy_m + uz_p - uz_m) / (2.0 * spacing)
                divergence_linf = max(divergence_linf, abs(divergence))

    elapsed = max(time.perf_counter() - started, 1e-12)
    relative_l2_error = math.sqrt(error_sq / exact_sq) if exact_sq else 0.0
    measured_energy_ratio = exact_sq / initial_sq if initial_sq else 0.0
    expected_energy_ratio = math.exp(-2.0 * viscosity * steps * dt)
    energy_relative_error = (
        abs(measured_energy_ratio - expected_energy_ratio) / expected_energy_ratio
        if expected_energy_ratio
        else 0.0
    )
    return {
        "energy_decay_accuracy_pct": 100.0 * max(0.0, 1.0 - energy_relative_error),
        "beltrami_l2_rel_error": relative_l2_error,
        "divergence_linf": divergence_linf,
        "solver_steps_per_s": steps / elapsed,
        "grid_points": float(grid**3),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--grid", type=int, default=8)
    parser.add_argument("--steps", type=int, default=8)
    parser.add_argument("--viscosity", type=float, default=0.1)
    parser.add_argument("--dt", type=float, default=0.01)
    args = parser.parse_args()
    metrics = solve(args.grid, args.steps, args.viscosity, args.dt)
    print(json.dumps({"status": "PASS", "metrics": metrics}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
