#!/usr/bin/env python3
"""Live demo: certify the rounding envelope of the periodic solver's
energy-budget diagnostic on a real Taylor-Green evolution.

OBSERVATION ONLY (F-012): the printed interval bounds round-off of the
diagnostic expression evaluated at the solver-reported float64 values.  The
continuum energy identity is a Lean theorem surface, not a numerical one;
nothing here closes or advances it.

Run:  python3 solver/interval_cert/energy_budget_demo.py
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

import numpy as np

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))
sys.path.insert(0, str(_HERE.parents[1] / "scripts"))  # unification shims

from float64_cert import (  # noqa: E402
    certify_cumulative_dissipation,
    certificate_record,
    enclose,
    i_add,
    i_sub,
)

import navier_spectral_core as core  # noqa: E402  (shim -> reality body)

N = 16
VISCOSITY = 0.05
DT = 0.02
OBS_STEPS = 10


def main() -> int:
    sp = core.spectral(N)
    state_hat = core.leray(core.forward(core.taylor_green_field(N)), sp)
    energies, rates = [], []
    t = 0.0
    for _ in range(OBS_STEPS + 1):
        diag = core.flow_diagnostics(state_hat, sp, viscosity=VISCOSITY, time=t)
        energies.append(float(diag["energy"]))
        rates.append(float(diag["energy_dissipation_rate"]))
        for _ in range(OBS_STEPS):
            state_hat = core.step_ifrk4(
                state_hat, sp, VISCOSITY, DT, True, None,
                t,
                np.exp(-VISCOSITY * sp.k2 * DT),
                np.exp(-VISCOSITY * sp.k2 * 0.5 * DT),
            )
            t += DT
    e0 = energies[0]
    # Observation spacing for the trapezoidal quadrature: rates are sampled
    # once per OBS_STEPS solver steps.
    obs_dt = OBS_STEPS * DT
    # 11 observation rates -> 10 trapezoid intervals over [0, t_final_minus_last_block]
    cum_iv = certify_cumulative_dissipation(rates, obs_dt)
    # Full composed envelope: defect = E_end + (trapezoidal integral of the
    # reported dissipation rates) - E_0, evaluated with intervals throughout.
    defect_iv = i_sub(i_add(enclose(energies[-1]), cum_iv), enclose(e0))
    # Point evaluation in the SAME fixed left-to-right order the interval walk
    # uses (the envelope covers this order; other orders need a separate
    # order-aware bound — see module docstring).
    acc = 0.0
    half = 0.5 * obs_dt
    for i in range(len(rates) - 1):
        acc += half * (rates[i] + rates[i + 1])
    point = energies[-1] + acc - e0
    record = certificate_record(
        {
            "point_inside": defect_iv.lo <= point <= defect_iv.hi,
            "well_ordered": defect_iv.lo <= defect_iv.hi,
            "defect_interval": defect_iv,
            "input_radius": 0.0,
        },
        backend="reality/solvers/navier/navier_spectral_core.py via navier shim",
    )
    cum_lo, cum_hi = cum_iv.lo, cum_iv.hi
    out = {
        "grid": N,
        "viscosity": VISCOSITY,
        "dt": DT,
        "final_time": t,
        "initial_energy": e0,
        "final_energy": energies[-1],
        "dissipation_integral_interval": [cum_lo, cum_hi],
        "energy_balance_defect_interval": [record["defect_interval"][0],
                                           record["defect_interval"][1]],
        "defect_envelope_width": record["defect_interval"][1] - record["defect_interval"][0],
        "certificate_record": record,
    }
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
