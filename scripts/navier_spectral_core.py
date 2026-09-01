"""Unification shim — canonical home: ~/reality/solvers/navier/.

2026-09-01 (Tim directive: unify all physics solvers into a single
lattice-solver codebase): the implementation moved to the reality workspace
(solvers/navier/navier_spectral_core.py) and this module re-exports it so
existing importers (tests, replay tooling) keep working unchanged. If the
reality checkout is absent the import fails loudly rather than silently
measuring a frozen copy.
"""
import importlib.util as _ilu
import os as _os

_PATH = _os.path.expanduser("~/reality/solvers/navier/navier_spectral_core.py")
_SPEC = _ilu.spec_from_file_location("navier_spectral_core", _PATH)
_MODULE = _ilu.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_MODULE)
globals().update(
    {k: v for k, v in vars(_MODULE).items() if not k.startswith("__")}
)
