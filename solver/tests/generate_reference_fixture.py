#!/usr/bin/env python3
"""Regenerate the checked Rust parity fixture from the canonical Python core."""

import argparse
import importlib.util
import json
import math
from pathlib import Path
import sys

import numpy as np


def load_core(path: Path):
    spec = importlib.util.spec_from_file_location("navier_spectral_core", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("core", type=Path, help="path to navier_spectral_core.py")
    parser.add_argument("--output", type=Path, default=Path("tests/fixtures/python_reference.json"))
    args = parser.parse_args()
    core = load_core(args.core.resolve())
    n, viscosity, dt = 8, 0.05, 0.01
    sp = core.spectral(n)
    initial = core.leray(core.forward(core.taylor_green_field(n)), sp)
    final = core.evolve(initial, sp, viscosity, dt, 2, True)

    def diagnostics(state, nu=0.0):
        values = core.flow_diagnostics(state, sp, viscosity=nu)
        return {key: float(values[key]) for key in ("energy", "divergence_rms", "velocity_linf", "enstrophy")}

    physical = core.inverse(final, n)
    samples = [
        float(physical[(component, *point)])
        for point in ((0, 0, 0), (1, 2, 3), (3, 4, 5), (7, 6, 2))
        for component in range(3)
    ]
    _, y, _ = core.mesh(n)
    shear = np.stack((np.sin(2.0 * y), np.zeros_like(y), np.zeros_like(y)))
    shear_initial = core.leray(core.forward(shear), sp)
    shear_final = core.evolve(shear_initial, sp, 0.2, 0.05, 4, True)
    x, y, z = core.mesh(n)
    probe = np.stack((np.sin(x) + 0.2 * np.cos(y), 0.3 * np.cos(x) + 0.1 * np.sin(z), 0.4 * np.cos(z)))
    raw = core.forward(probe)
    projected = core.leray(raw.copy(), sp)
    correction_real = core.inverse(raw - projected, n)
    projected_real = core.inverse(projected, n)
    orthogonality = abs(float(np.vdot(projected_real.ravel(), correction_real.ravel()).real)) / (
        np.linalg.norm(projected_real.ravel()) * np.linalg.norm(correction_real.ravel())
    )
    base, exact, forcing = core.mms_problem(sp, 0.05, True)
    mms = core.evolve(base, sp, 0.05, 0.05, 4, True, forcing)
    payload = {
        "grid": n,
        "mms": {"dt": 0.05, "exact_energy": core.energy(exact(0.2), sp), "final_energy": core.energy(mms, sp), "relative_l2": core.relative_l2(mms, exact(0.2), sp), "steps": 4, "viscosity": 0.05},
        "projection": {"orthogonality_relative": orthogonality, "projected_divergence_linf": core.divergence_linf(projected, sp), "projected_energy": core.energy(projected, sp), "raw_divergence_linf": core.divergence_linf(raw, sp), "raw_energy": core.energy(raw, sp)},
        "provenance": "reality/solvers/navier/navier_spectral_core.py",
        "shear": {"dt": 0.05, "expected_ratio": math.exp(-0.32), "final_energy": core.energy(shear_final, sp), "initial_energy": core.energy(shear_initial, sp), "mode": 2, "steps": 4, "viscosity": 0.2},
        "tgv": {"dt": dt, "final": diagnostics(final, viscosity), "initial": diagnostics(initial, viscosity), "samples_xyz": samples, "steps": 2, "viscosity": viscosity},
    }
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
