"""Unification shim — canonical home: ~/reality/solvers/navier/.

2026-09-01 (Tim directive: unify all physics solvers into a single
lattice-solver codebase): the C-accelerated kernel loader moved to the reality
workspace (solvers/navier/navier_accel.py, which compiles the sibling
navier_kernels.c copy there); this module re-exports it so existing importers
keep working unchanged. The compiled-library cache stays at
~/.cache/navier-spectral/ (host-level, shared by both paths).
"""
import importlib.util as _ilu
import os as _os

_PATH = _os.path.expanduser("~/reality/solvers/navier/navier_accel.py")
_SPEC = _ilu.spec_from_file_location("navier_accel", _PATH)
_MODULE = _ilu.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)
globals().update(
    {k: v for k, v in vars(_MODULE).items() if not k.startswith("__")}
)
