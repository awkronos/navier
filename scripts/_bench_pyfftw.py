import os, sys, json, time, math, numpy as np
import navier_spectral_core as core
# Reimport to clear pyfftw block
import importlib; importlib.reload(core)
from navier_solver_bench import solve
print("=== PYFFTW")
for _ in range(5):
    r = solve(16, 20, 0.05, 0.05, "mms", 1.0)
    print(json.dumps({"m": round(r["spectral_grid_updates_per_s"],1), "l2": f'{r["l2_rel_error"]:.2e}', "ord": round(r["time_convergence_order"],4)}))
