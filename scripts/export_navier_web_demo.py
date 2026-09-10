#!/usr/bin/env python3
"""Export compact, reproducible Taylor--Green recordings for the web demo.

These are ordinary numerical solutions on a periodic box.  They illustrate
viscosity and resolution effects; they are not samples of the singular
whole-space construction and provide no blow-up certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import subprocess

import numpy as np

import navier_spectral_core as core


REPOSITORY_URL = "https://github.com/awkronos/navier"
CANONICAL_CORE = Path.home() / "reality/solvers/navier/navier_spectral_core.py"
CANONICAL_REPO = CANONICAL_CORE.parents[2]


def _git_head(repository: Path) -> str:
    return subprocess.run(
        ["git", "-C", str(repository), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def taylor_green_initial(sp: core.Spectral) -> np.ndarray:
    """Divergence-free Taylor--Green initial data on ``[0, 2*pi)^3``."""
    x, y, z = core.mesh(sp.n)
    velocity = np.stack(
        (
            np.sin(x) * np.cos(y) * np.cos(z),
            -np.cos(x) * np.sin(y) * np.cos(z),
            np.zeros_like(x),
        )
    )
    return core.forward(velocity)


def _sample_and_quantize(
    velocity: np.ndarray, indices: np.ndarray
) -> tuple[float, list[int], float]:
    sampled = velocity[:, indices][:, :, indices][:, :, :, indices]
    point_major = sampled.transpose(1, 2, 3, 0).reshape(-1)
    maximum = float(np.max(np.abs(point_major)))
    scale = maximum / 32760.0 if maximum else 1.0
    quantized = np.rint(point_major / scale).clip(-32760, 32760).astype(np.int16)
    reconstructed = quantized.astype(np.float64) * scale
    error = float(np.max(np.abs(reconstructed - point_major)))
    if error > scale * 0.5000001:
        raise RuntimeError("velocity quantization exceeded the half-unit error bound")
    return scale, quantized.astype(int).tolist(), error


def _frame(
    state: np.ndarray,
    sp: core.Spectral,
    viscosity: float,
    time: float,
    indices: np.ndarray,
    tail_start: float,
    tail_tolerance: float,
) -> dict:
    diagnostics = core.flow_diagnostics(
        state,
        sp,
        viscosity=viscosity,
        time=time,
        tail_start=tail_start,
        tail_tolerance=tail_tolerance,
    )
    velocity = core.inverse(state, sp.n)
    physical_energy = 0.5 * float(np.mean(np.sum(velocity * velocity, axis=0)))
    energy_gap = abs(physical_energy - float(diagnostics["energy"]))
    energy_scale = max(abs(physical_energy), 1.0)
    if energy_gap > 2.0e-12 * energy_scale:
        raise RuntimeError("physical-grid and spectral energy metrics disagree")
    quantization_scale, velocity_q, quantization_error = _sample_and_quantize(
        velocity, indices
    )
    return {
        "time": float(time),
        "diagnostics": diagnostics,
        "physical_grid_energy": physical_energy,
        "energy_crosscheck_absolute_error": energy_gap,
        "velocity_quantization_scale": quantization_scale,
        "velocity_quantization_max_error": quantization_error,
        "velocity_q": velocity_q,
    }


def _validate_run(run: dict) -> None:
    frames = run["frames"]
    times = [frame["time"] for frame in frames]
    if times[0] != 0.0 or times[-1] != run["final_time"]:
        raise RuntimeError("frame times do not include the exact time interval endpoints")
    if any(left >= right for left, right in zip(times, times[1:])):
        raise RuntimeError("frame times must be strictly increasing")
    energies = [float(frame["diagnostics"]["energy"]) for frame in frames]
    tolerance = 2.0e-8 * max(energies[0], 1.0)
    if any(right > left + tolerance for left, right in zip(energies, energies[1:])):
        raise RuntimeError("positive-viscosity unforced energy increased unexpectedly")
    divergences = [float(frame["diagnostics"]["divergence_rms"]) for frame in frames]
    if max(divergences) > 2.0e-12:
        raise RuntimeError("Leray-projected recording is not divergence-free to roundoff")
    if run["steps"]["accepted"] <= 0:
        raise RuntimeError("recording contains no accepted adaptive steps")
    encoded_length = run["sampling"]["sample_count"] ** 3 * 3
    for frame in frames:
        if len(frame["velocity_q"]) != encoded_length:
            raise RuntimeError("sample array does not match the declared layout")
        if any(abs(value) > 32760 for value in frame["velocity_q"]):
            raise RuntimeError("sample escaped the declared signed-int16 range")
        for value in frame["diagnostics"].values():
            if isinstance(value, float) and not math.isfinite(value):
                raise RuntimeError("nonfinite diagnostic cannot be serialized")


def _validate_initial_sampling(frame: dict, coordinates: list[float]) -> None:
    """Check the declared x/y/z/component flattening against analytic data."""
    x, y, z = np.meshgrid(coordinates, coordinates, coordinates, indexing="ij")
    expected = np.stack(
        (
            np.sin(x) * np.cos(y) * np.cos(z),
            -np.cos(x) * np.sin(y) * np.cos(z),
            np.zeros_like(x),
        ),
        axis=-1,
    ).reshape(-1)
    decoded = (
        np.asarray(frame["velocity_q"], dtype=np.float64)
        * frame["velocity_quantization_scale"]
    )
    error = float(np.max(np.abs(decoded - expected)))
    allowed = frame["velocity_quantization_scale"] * 0.500001 + 2.0e-14
    if error > allowed:
        raise RuntimeError("sample orientation does not reproduce Taylor--Green data")


def record_run(
    *,
    grid: int,
    viscosity: float,
    final_time: float,
    frame_count: int,
    sample_count: int,
    initial_dt: float,
    rtol: float,
    atol: float,
    cfl: float,
    tail_start: float,
    tail_tolerance: float,
) -> dict:
    if grid % sample_count:
        raise ValueError("sample_count must divide every simulation grid")
    sp = core.spectral(grid)
    state = taylor_green_initial(sp)
    indices = np.arange(sample_count, dtype=int) * (grid // sample_count)
    frame_times = np.linspace(0.0, final_time, frame_count)
    frames = [
        _frame(state, sp, viscosity, 0.0, indices, tail_start, tail_tolerance)
    ]
    accepted = rejected = 0
    min_dt = math.inf
    max_dt = max_cfl = max_error_ratio = max_tail = 0.0
    max_velocity = max_vorticity = integrated_vorticity = 0.0
    underresolved = False
    next_dt = initial_dt
    current_time = 0.0
    for target in frame_times[1:]:
        target = float(target)
        segment = core.evolve_adaptive(
            state,
            sp,
            viscosity,
            target,
            min(next_dt, target - current_time),
            t0=current_time,
            rtol=rtol,
            atol=atol,
            cfl=cfl,
            max_dt=initial_dt,
            tail_start=tail_start,
            tail_tolerance=tail_tolerance,
        )
        state = segment.state
        current_time = segment.final_time
        next_dt = max(segment.last_dt, np.finfo(float).eps)
        accepted += segment.accepted_steps
        rejected += segment.rejected_steps
        min_dt = min(min_dt, segment.min_dt)
        max_dt = max(max_dt, segment.max_dt)
        max_cfl = max(max_cfl, segment.max_cfl)
        max_error_ratio = max(max_error_ratio, segment.max_error_ratio)
        max_tail = max(max_tail, segment.max_tail_energy_fraction)
        max_velocity = max(max_velocity, segment.max_velocity_linf)
        max_vorticity = max(max_vorticity, segment.max_vorticity_linf)
        integrated_vorticity += segment.integrated_vorticity_linf
        underresolved = underresolved or segment.underresolved
        frames.append(
            _frame(
                state,
                sp,
                viscosity,
                current_time,
                indices,
                tail_start,
                tail_tolerance,
            )
        )
    coordinates = (2.0 * math.pi * indices / grid).tolist()
    run = {
        "id": f"tgv-n{grid}-nu{viscosity:g}",
        "grid": grid,
        "viscosity": viscosity,
        "final_time": final_time,
        "sampling": {
            "sample_count": sample_count,
            "source_indices": indices.tolist(),
            "coordinates_radians": coordinates,
            "array_shape": [sample_count, sample_count, sample_count, 3],
            "component_order": ["ux", "uy", "uz"],
            "flattened_layout": "x-major, then y, then z, with [ux,uy,uz] fastest",
            "decode": "velocity = velocity_q * velocity_quantization_scale",
            "interpolation": "periodic trilinear interpolation over x, y, z axes",
            "periodic_endpoint": "2*pi is excluded and identified with 0",
        },
        "steps": {
            "accepted": accepted,
            "rejected": rejected,
            "min_dt": min_dt,
            "max_dt": max_dt,
            "max_cfl": max_cfl,
            "max_error_ratio": max_error_ratio,
            "max_velocity_linf": max_velocity,
            "max_vorticity_linf": max_vorticity,
            "integrated_vorticity_linf": integrated_vorticity,
            "max_tail_energy_fraction": max_tail,
            "underresolved": underresolved,
        },
        "frames": frames,
    }
    _validate_initial_sampling(frames[0], coordinates)
    _validate_run(run)
    return run


def export_dataset(
    output: Path,
    *,
    grids: tuple[int, ...] = (12, 24, 36),
    viscosities: tuple[float, ...] = (0.02, 0.05, 0.1),
    final_time: float = 1.5,
    frame_count: int = 25,
    sample_count: int = 6,
) -> dict:
    controls = {
        "initial_dt": 0.1,
        "rtol": 1.0e-6,
        "atol": 1.0e-9,
        "cfl": 0.5,
        "tail_start": 0.75,
        "tail_tolerance": 1.0e-8,
    }
    runs = [
        record_run(
            grid=grid,
            viscosity=viscosity,
            final_time=final_time,
            frame_count=frame_count,
            sample_count=sample_count,
            **controls,
        )
        for viscosity in viscosities
        for grid in grids
    ]
    dataset = {
        "schema_version": 1,
        "title": "Adaptive periodic Taylor–Green flow recordings",
        "interpretation": (
            "Regular numerical experiments for visualization only; these are not the "
            "OpenAI whole-space blow-up candidate and do not certify singular behavior."
        ),
        "repository": REPOSITORY_URL,
        "canonical_solver": {
            "repository_commit": _git_head(CANONICAL_REPO),
            "source_path": "solvers/navier/navier_spectral_core.py",
            "source_sha256": _sha256(CANONICAL_CORE),
            "method": "dealiased Fourier pseudospectral rotational form with adaptive IFRK4",
        },
        "normalization": {
            "domain": "[0,2*pi)^3 periodic",
            "initial_velocity": "(sin(x)cos(y)cos(z), -cos(x)sin(y)cos(z), 0)",
            "forcing": "zero",
            "energy": "0.5 * spatial mean of |u|^2",
            "enstrophy": "0.5 * spatial mean of |curl u|^2",
            "time": "dimensionless solver time; every frame time is an absolute target",
        },
        "adaptive_controls": controls,
        "frame_integration": (
            "Each frame advances the preceding spectral state to the next absolute time "
            "with evolve_adaptive; the previous accepted dt seeds the next segment, and "
            "run step counts are exact sums of the segment results."
        ),
        "run_order": "viscosity-major, grid-minor",
        "runs": runs,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(dataset, separators=(",", ":"), allow_nan=False) + "\n")
    return dataset


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("/tmp/navier-web-data"))
    parser.add_argument("--smoke", action="store_true", help="export one short validation run")
    args = parser.parse_args()
    filename = "navier-web-demo-smoke.json" if args.smoke else "navier-web-demo.json"
    kwargs = (
        {"grids": (12,), "viscosities": (0.05,), "final_time": 0.25, "frame_count": 5}
        if args.smoke
        else {}
    )
    dataset = export_dataset(args.output_dir / filename, **kwargs)
    result = {
        "output": str(args.output_dir / filename),
        "runs": len(dataset["runs"]),
        "frames": sum(len(run["frames"]) for run in dataset["runs"]),
        "bytes": (args.output_dir / filename).stat().st_size,
    }
    print(json.dumps(result, allow_nan=False))


if __name__ == "__main__":
    main()
