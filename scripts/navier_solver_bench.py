#!/usr/bin/env python3
"""Unification shim — canonical home: ~/reality/solvers/navier/.

2026-09-01 (Tim directive: unify all physics solvers into a single
lattice-solver codebase): the spectral solver and this bench moved into the
reality workspace (solvers/navier/). This module re-exports the unified bench
so every existing caller -- registry rows, scripts, CI, the equivalence tests
(which import the module and call run_throughput/run_tgv directly) -- binds
the one implementation without drift. Run as a script it dispatches to the
bench's own main(), so the CLI stays byte-compatible. If the reality checkout
is absent the shim fails loudly rather than silently measuring a frozen copy.
"""
import importlib.util as _ilu
import os as _os
import sys as _sys

_PATH = _os.path.expanduser("~/reality/solvers/navier/navier_solver_bench.py")
_SPEC = _ilu.spec_from_file_location("navier_solver_bench", _PATH)
_MODULE = _ilu.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)
globals().update(
    {k: v for k, v in vars(_MODULE).items() if not k.startswith("__")}
)

if __name__ == "__main__":
    _sys.exit(_MODULE.main())
