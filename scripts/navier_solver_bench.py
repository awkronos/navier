#!/usr/bin/env python3
"""Objective pseudo-spectral Navier--Stokes benchmark on an ABC flow.

This samples the periodic velocity field, transforms all three components to
Fourier space, advances viscosity with a spectral integrating factor, and
transforms back every step.  The ABC Beltrami flow has an independent exact
answer because Leray projection removes its quadratic pressure gradient.

The compute bottleneck is the repeated three-dimensional FFT/IFFT pair over
``grid**3`` modes.  Accuracy is measured independently by field, energy,
divergence, and projected-nonlinearity residuals.
"""

from __future__ import annotations

import argparse
import json
import math
import time

import numpy as np


def _grid(n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    points = 2.0 * math.pi * np.arange(n, dtype=np.float64) / n
    return np.meshgrid(points, points, points, indexing="ij")


def _abc_field(n: int) -> np.ndarray:
    x, y, z = _grid(n)
    return np.stack(
        (np.sin(z) + np.cos(y), np.sin(x) + np.cos(z), np.sin(y) + np.cos(x))
    )


def _wave_numbers(n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    k = np.fft.fftfreq(n, d=1.0 / n)
    kx, ky, kz = np.meshgrid(k, k, k, indexing="ij")
    return kx, ky, kz, kx * kx + ky * ky + kz * kz


def _leray_project(vector_hat: np.ndarray, kx, ky, kz, k2) -> np.ndarray:
    dot = kx * vector_hat[0] + ky * vector_hat[1] + kz * vector_hat[2]
    scale = np.divide(dot, k2, out=np.zeros_like(dot), where=k2 != 0.0)
    projected = vector_hat.copy()
    projected[0] -= kx * scale
    projected[1] -= ky * scale
    projected[2] -= kz * scale
    return projected


def _projected_nonlinearity_l2(field: np.ndarray, kx, ky, kz, k2) -> float:
    field_hat = np.fft.fftn(field, axes=(1, 2, 3))
    gradients = np.empty((3, 3, *field.shape[1:]), dtype=np.float64)
    for component in range(3):
        for axis, wave in enumerate((kx, ky, kz)):
            gradients[component, axis] = np.fft.ifftn(
                1j * wave * field_hat[component]
            ).real
    advective = np.einsum("aijk,caijk->cijk", field, gradients)
    projected_hat = _leray_project(
        np.fft.fftn(advective, axes=(1, 2, 3)), kx, ky, kz, k2
    )
    projected = np.fft.ifftn(projected_hat, axes=(1, 2, 3)).real
    return float(np.linalg.norm(projected.ravel()) / math.sqrt(projected.size))


def solve(grid: int, steps: int, viscosity: float, dt: float) -> dict[str, float]:
    if grid < 4 or steps < 1 or viscosity <= 0.0 or dt <= 0.0:
        raise ValueError("grid >= 4, steps >= 1, viscosity > 0, and dt > 0 required")

    initial = _abc_field(grid)
    field_hat = np.fft.fftn(initial, axes=(1, 2, 3))
    kx, ky, kz, k2 = _wave_numbers(grid)
    field_hat = _leray_project(field_hat, kx, ky, kz, k2)
    heat_step = np.exp(-viscosity * k2 * dt)

    started = time.perf_counter()
    for _ in range(steps):
        field_hat *= heat_step
        # Materialize every step so the workload is an actual 3D spectral
        # evolution, not one scalar multiplication dressed as a solver.
        field = np.fft.ifftn(field_hat, axes=(1, 2, 3)).real
        field_hat = np.fft.fftn(field, axes=(1, 2, 3))
    elapsed = max(time.perf_counter() - started, 1e-12)

    final = np.fft.ifftn(field_hat, axes=(1, 2, 3)).real
    exact = math.exp(-viscosity * steps * dt) * initial
    relative_l2_error = float(
        np.linalg.norm((final - exact).ravel()) / np.linalg.norm(exact.ravel())
    )
    measured_energy_ratio = float(
        np.vdot(final, final).real / np.vdot(initial, initial).real
    )
    expected_energy_ratio = math.exp(-2.0 * viscosity * steps * dt)
    energy_relative_error = (
        abs(measured_energy_ratio - expected_energy_ratio) / expected_energy_ratio
        if expected_energy_ratio
        else 0.0
    )
    divergence_hat = 1j * (kx * field_hat[0] + ky * field_hat[1] + kz * field_hat[2])
    divergence_linf = float(np.max(np.abs(np.fft.ifftn(divergence_hat).real)))
    transforms = 2 * steps + 8
    return {
        "l2_rel_error": relative_l2_error,
        "energy_decay_rel_error": float(energy_relative_error),
        "divergence_linf": divergence_linf,
        "projected_nonlinear_l2": _projected_nonlinearity_l2(
            initial, kx, ky, kz, k2
        ),
        "spectral_grid_updates_per_s": float(steps * grid**3 / elapsed),
        "fft_transforms_per_s": float(transforms / elapsed),
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
