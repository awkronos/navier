#!/usr/bin/env python3
"""WorldSense scientific receipt for 3D incompressible Navier-Stokes dissipation.

One run answers four questions about a *numerical* 3D Navier-Stokes evolution and
packages the answers as a machine-readable receipt Kagami's
``WorldSenseScientificFlow`` can ingest:

  1. **Leray energy dissipation** — does the discrete flow obey
     ``dE/dt = -2 nu Z <= 0`` (kinetic energy ``E = 0.5 * mean|u|^2``, enstrophy
     ``Z = 0.5 * mean|omega|^2``) to within the integrator's own truncation error?
  2. **Beale-Kato-Majda** — what is ``int_0^T ||omega(t)||_infty dt`` on this grid,
     is it finite, and where does it peak?
  3. **Triad cancellation** — is the convective term energy-neutral in the discrete
     sense, i.e. ``|<u, P((u . grad) u)>|`` at machine precision? This is the exact
     algebraic fact that makes (1) mean anything: the nonlinear transfer moves
     energy between Fourier triads without creating or destroying it, so any energy
     loss must be viscosity.
  4. **Reactor hints** — which ``(nu, t_star)`` window carries the peak enstrophy
     stretching, and is the grid resolved well enough there to be worth refining?

Scope discipline (read before citing anything below)
----------------------------------------------------
Every number here comes from a **finite grid, finite time, Fourier-Galerkin
(collocation) discretisation** of Navier-Stokes on the periodic torus. That is a
numerical observation, graded ``Probably`` — not a theorem, and specifically not a
proof, disproof or witness about the Clay millennium problem on 3D global
regularity. Concretely:

  * ``I_BKM(T) < infinity`` on a finite grid says the *discretisation* stayed
    resolved on ``[0, T]``. A truncated system always has finite
    ``||omega||_infty``; the BKM criterion's force lives in the continuum limit
    ``T -> t_breakdown``, which no grid reaches. A bounded integral here is
    evidence about resolution, never evidence about regularity.
  * ``E(T) < E(0)`` demonstrates the discrete energy inequality for THIS initial
    condition, viscosity and step count.
  * ``<u, P((u . grad) u)> = 0`` is an algebraic identity of the rotational
    (vorticity-cross-velocity) form under an orthogonal Leray projector. It is
    exact for the Galerkin truncation up to round-off and says nothing about
    existence or smoothness of continuum solutions.

``validate_navier_receipt_epistemics`` enforces this on the way out, and
``tests/test_navier_worldsense_receipt_1126.py`` pins that a receipt inflated to
``THEOREM``, ``deductive_proof=True`` or
``clay_3d_global_regularity_claimed=True`` is refused rather than emitted.

Engines
-------
The repository's solver stack, ``scripts/navier_spectral_core.py``, is an importlib
re-export shim onto the canonical unified solver in ``~/reality/solvers/navier/``
(2026-09-01 unification directive). Hosted CI holds no credential for that private
repository, so the shim raises there. This module therefore carries a
self-contained numpy Fourier-Galerkin engine and names the one it used:

  * ``engine.name = "reality_shim"`` — the canonical core, when importable;
  * ``engine.name = "builtin_ifrk4"`` — this file's engine, mirroring the canonical
    arithmetic (rotational advection, exact integrating factor, Orszag 2/3 rule) so
    a hosted-runner receipt is the same measurement rather than a silently different
    one. The test suite cross-checks the two engines wherever ``reality`` is
    present; where it is absent that leg reports itself UNMEASURED instead of
    asserting agreement it did not observe.

Usage::

    python3 scripts/navier_worldsense_receipt.py --json
    python3 scripts/navier_worldsense_receipt.py --out /tmp/navier_receipt.json
    python3 scripts/navier_worldsense_receipt.py --grid 20 --dt 0.02 --steps 40 \
        --viscosities 0.05 0.1 --ic taylor_green
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import json
import math
import os
import platform
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from collections.abc import Iterator
from typing import (
    Any,
    Callable,
    Dict,
    List,
    Optional,
    Sequence,
    Tuple,
    TYPE_CHECKING,
    cast,
)

SCRIPTS = Path(__file__).resolve().parent
REPO = SCRIPTS.parent

# FFT/BLAS thread caps before numpy is imported, matching
# scripts/ns_paired_benchmark.py: a receipt digest must not depend on how the host
# happened to partition the work, and a builder must not be starved by a probe.
for _var in (
    "OMP_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "MKL_NUM_THREADS",
    "NUMEXPR_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
):
    os.environ.setdefault(_var, "1")

import numpy as np  # noqa: E402  (thread caps above must precede this)

# scipy.fft is a faster path, never a required one. The explicit `Any` binding is
# what keeps the optional import honest for a static reader: the name is a module
# OR None, and every use site is guarded, so a host without scipy still runs.
_scipy_fft: Any = None
try:
    from scipy import fft as _scipy_fft  # type: ignore[import-not-found]
except Exception:  # noqa: BLE001 - scipy absent on a minimal runner is supported
    _scipy_fft = None

if TYPE_CHECKING:  # static-only aliases; annotations are never evaluated at runtime
    ComplexArray = np.ndarray[Any, np.dtype[np.complex128]]
    FloatArray = np.ndarray[Any, np.dtype[np.float64]]
    # Anything array-like, for the boundary functions that accept a real field or a
    # half-spectrum interchangeably and decide by shape.
    AnyArray = np.ndarray[Any, np.dtype[Any]]

# ---------------------------------------------------------------------------
# schemas, tiers, the claim boundary
# ---------------------------------------------------------------------------

RECEIPT_SCHEMA = "worldsense.scientific_receipt/1"
PROBABLY_SCHEMA = "z8.probably/1"
DOMAIN = "navier_stokes_3d"

#: ``classify_receipt`` on the ingest side reads schema-ish text out of
#: schema/kind/type/operation/receipt_type/event. Without a navier marker in one of
#: THOSE fields this receipt files as ``unattributed`` rather than in the navier
#: domain — so the marker goes where the reader looks, not only where it reads well.
RECEIPT_KIND = "navier_stokes_3d_leray_receipt"
RECEIPT_OPERATION = "navier_stokes_3d_ifrk4_leray_diagnostics"

TIER_PROBABLY = "PROBABLY"
LAYER_PROBABLY = "Probably"
EPISTEMIC_TIER = "NUMERICAL_OBSERVATION"

#: Whole-field matches only. A prose sentence explaining what a receipt does NOT
#: prove must not trip the gate that polices claims; the gate looks at tier-bearing
#: TOKENS, and `what_this_does_not_establish` rows are prose, not tiers. That
#: restriction is what makes words like ``CLOSED`` safe to include here: a field
#: whose entire value is "CLOSED" asserts a closure claim, while "closed-form
#: viscous decay" in a note asserts nothing.
#:
#: ``CLOSED`` and ``KERNEL_CLEAN`` are not stylistic additions. The ingest side
#: builds its refusal vocabulary from
#: ``kagami.core.omni.closed_loop_research_weave.THEOREM_WORDS``
#: (= {THEOREM, CLOSED, PROVED, KERNEL_CLEAN}) unioned with ``quantum.PROVABLY``,
#: and a top-level tier field holding any of those is quarantined unless a kernel
#: attestation follows it. This set is a MIRROR of that owner, deliberately not an
#: import: the flow needs Python 3.11+ (:data:`enum.StrEnum`) and this battery runs
#: on the 3.9 interpreter, so importing the owner would turn a green CI leg into an
#: ImportError. The cost of mirroring is drift, and the drift is watched --
#: tests/test_navier_worldsense_receipt_1126.py re-reads the owner's source text
#: when a kagami checkout carrying that module is reachable and fails if either
#: set grows past this copy.
PROOF_TIER_WORDS = frozenset(
    {
        "THEOREM",
        "THEOREMS",
        "PROVED",
        "PROVEN",
        "PROOF",
        "LEAN_THEOREM",
        "CONDITIONAL_THEOREM",
        "KERNEL_CHECKED",
        "KERNEL_CLEAN",
        "CLOSED",
        "PROVABLY",
    }
)

#: The fields an ingest side is allowed to treat as a tier assertion.
TIER_FIELDS = ("tier", "scientific_tier", "claim", "verdict", "status", "epistemic_tier", "layer")

#: Absolute tolerances, in the nondimensional units of the periodic box.
DIV_TOLERANCE = 1e-12
CONVECTIVE_TOLERANCE = 1e-12

DEFAULT_GRID = 16
DEFAULT_DT = 0.05
DEFAULT_STEPS = 20
DEFAULT_VISCOSITIES: Tuple[float, ...] = (0.05, 0.1, 0.2)
DEFAULT_CONVERGENCE_GRIDS: Tuple[int, int] = (12, 16)

__all__ = [
    "RECEIPT_SCHEMA",
    "PROBABLY_SCHEMA",
    "DOMAIN",
    "Grid",
    "Engine",
    "spectral",
    "resolve_engine",
    "run_once",
    "build_receipt",
    "validate_navier_receipt_epistemics",
    "canonical_json",
    "stable_view",
    "payload_sha256",
    "write_receipt",
    "main",
]


# ---------------------------------------------------------------------------
# wavenumber operators
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Grid:
    """Integer-wavenumber operators on an ``N^3`` periodic box.

    Attribute names match the canonical core's ``Spectral`` exactly (``n``, ``kx``,
    ``ky``, ``kz``, ``k2``, ``inv_k2``, ``dealias``, ``shape_hat``), which is what
    lets every diagnostic below run against either engine with no branch.
    """

    n: int
    kx: FloatArray
    ky: FloatArray
    kz: FloatArray
    k2: FloatArray
    inv_k2: FloatArray
    dealias: FloatArray

    @property
    def shape_hat(self) -> Tuple[int, int, int]:
        return (self.n, self.n, self.n // 2 + 1)


_GRID_CACHE: Dict[int, Grid] = {}


def spectral(n: int) -> Grid:
    """Wavenumber operators for an even ``N >= 4`` grid (cached per N)."""
    cached = _GRID_CACHE.get(n)
    if cached is not None:
        return cached
    if n < 4 or n % 2:
        raise ValueError("grid must be an even integer >= 4")
    kx1 = np.fft.fftfreq(n, d=1.0 / n)
    kz1 = np.fft.rfftfreq(n, d=1.0 / n)
    kx, ky, kz = np.meshgrid(kx1, kx1, kz1, indexing="ij")
    k2 = kx * kx + ky * ky + kz * kz
    inv_k2 = np.divide(1.0, k2, out=np.zeros_like(k2), where=k2 != 0.0)
    cutoff = n / 3.0  # Orszag 2/3 rule, applied per component
    mask = (np.abs(kx) < cutoff) & (np.abs(ky) < cutoff) & (np.abs(kz) < cutoff)
    grid = Grid(
        n,
        np.ascontiguousarray(kx),
        np.ascontiguousarray(ky),
        np.ascontiguousarray(kz),
        np.ascontiguousarray(k2),
        np.ascontiguousarray(inv_k2),
        np.ascontiguousarray(mask.astype(np.float64)),
    )
    _GRID_CACHE[n] = grid
    return grid


def _ks(grid: Any) -> Tuple[FloatArray, FloatArray, FloatArray]:
    """The three wavenumber arrays, read by attribute (works on either engine)."""
    return (grid.kx, grid.ky, grid.kz)


def _rfftn(field: FloatArray, axes: Tuple[int, ...]) -> ComplexArray:
    if _scipy_fft is not None:
        return _scipy_fft.rfftn(field, axes=axes)
    return np.fft.rfftn(field, axes=axes)


def _irfftn(field_hat: ComplexArray, s: Tuple[int, ...], axes: Tuple[int, ...]) -> FloatArray:
    if _scipy_fft is not None:
        return _scipy_fft.irfftn(field_hat, s=s, axes=axes)
    return np.fft.irfftn(field_hat, s=s, axes=axes)


def mesh(n: int) -> Tuple[FloatArray, FloatArray, FloatArray]:
    """The collocation points of ``[0, 2 pi)^3``."""
    points = 2.0 * math.pi * np.arange(n, dtype=np.float64) / n
    # Indexed rather than unpacked: numpy types ``meshgrid`` as a variable-length
    # ``tuple[NDArray[Any], ...]``, so a three-name unpack has no static length to
    # check against. Indexing 0/1/2 does, and returns the same three arrays.
    grids = np.meshgrid(points, points, points, indexing="ij")
    return grids[0], grids[1], grids[2]


def taylor_green_field(n: int) -> FloatArray:
    """Taylor-Green vortex: divergence-free and NOT Beltrami, so O(1) stretching."""
    x, y, z = mesh(n)
    return np.stack(
        (
            np.sin(x) * np.cos(y) * np.cos(z),
            -np.cos(x) * np.sin(y) * np.cos(z),
            np.zeros_like(x),
        )
    )


def abc_field(n: int, a: float = 1.0, b: float = 1.0, c: float = 1.0) -> FloatArray:
    """Arnold-Beltrami-Childress flow; for ``a = b = c`` it obeys ``curl u = u``.

    That Beltrami property makes it an exact Euler solution and an exact decaying
    Navier-Stokes solution, ``u(., t) = exp(-nu |k|^2 t) u(., 0)`` with ``|k|^2 = 1``
    here, hence ``E(t) = E(0) exp(-2 nu t)`` in closed form. That is the one
    configuration where the receipt's energy identity can be checked against an
    analytic target rather than against itself, which is why this file carries it.
    """
    x, y, z = mesh(n)
    return np.stack(
        (
            a * np.sin(z) + c * np.cos(y),
            b * np.sin(x) + a * np.cos(z),
            c * np.sin(y) + b * np.cos(x),
        )
    )


INITIAL_CONDITIONS: Dict[str, Callable[[int], FloatArray]] = {
    "taylor_green": taylor_green_field,
    "abc": abc_field,
}


def _as_state(value: AnyArray, grid: Any) -> ComplexArray:
    """A C-contiguous complex128 state of the grid's exact half-spectrum shape."""
    expected = (3, *grid.shape_hat)
    array = np.ascontiguousarray(np.asarray(value, dtype=np.complex128))
    if array.shape != expected:
        raise ValueError(f"vector_hat must have shape {expected}, got {array.shape}")
    return array


def _forward(field: FloatArray, _grid: Any) -> ComplexArray:
    # `_grid` is interface uniformity: every Engine callable takes (value, grid) so
    # one call site works against both backends. This transform is grid-shape
    # agnostic -- rfftn over the trailing axes needs nothing from the Grid -- and the
    # canonical core's `forward` is the same, which is why the wrapper below discards
    # it identically. Named with the leading underscore rather than dropped so the
    # arity stays visible at the call sites.
    return _rfftn(np.ascontiguousarray(np.asarray(field, dtype=np.float64)), axes=(1, 2, 3))


def _inverse(field_hat: ComplexArray, grid: Any) -> FloatArray:
    return _irfftn(field_hat, s=(grid.n, grid.n, grid.n), axes=(1, 2, 3))


def _leray(vector_hat: ComplexArray, grid: Any) -> ComplexArray:
    """Helmholtz-Leray projection onto the discrete divergence-free subspace.

    Orthogonal in the trapezoidal inner product, mode by mode onto ``k``-perp.
    Mutates ``vector_hat`` (every caller passes a fresh array), as the core does.
    """
    dot = grid.kx * vector_hat[0] + grid.ky * vector_hat[1] + grid.kz * vector_hat[2]
    scale = dot * grid.inv_k2
    vector_hat[0] -= grid.kx * scale
    vector_hat[1] -= grid.ky * scale
    vector_hat[2] -= grid.kz * scale
    return vector_hat


def _curl_hat(vector_hat: ComplexArray, grid: Any) -> ComplexArray:
    out = np.empty_like(vector_hat)
    out[0] = 1j * (grid.ky * vector_hat[2] - grid.kz * vector_hat[1])
    out[1] = 1j * (grid.kz * vector_hat[0] - grid.kx * vector_hat[2])
    out[2] = 1j * (grid.kx * vector_hat[1] - grid.ky * vector_hat[0])
    return out


def _parseval_weight(grid: Any) -> FloatArray:
    """Mode multiplicities of a half spectrum: interior ``kz`` bins carry their
    conjugate partner, the ``kz = 0`` and Nyquist bins do not."""
    weight = np.ones(grid.shape_hat[2], dtype=np.float64)
    weight[1 : (grid.n + 1) // 2] = 2.0
    return weight


def _norm_sq(vector_hat: ComplexArray, grid: Any, weight: FloatArray) -> float:
    """``mean|v|^2`` straight from the half spectrum (Parseval, no inverse transform)."""
    total = float(np.sum(np.abs(vector_hat) ** 2 * weight))
    return total / float(grid.n ** 6)


def _energy(vector_hat: ComplexArray, grid: Any, weight: FloatArray) -> float:
    return 0.5 * _norm_sq(vector_hat, grid, weight)


def _enstrophy(vector_hat: ComplexArray, grid: Any, weight: FloatArray) -> float:
    return _energy(_curl_hat(vector_hat, grid), grid, weight)


def _mean_grad_sq(vector_hat: ComplexArray, grid: Any, weight: FloatArray) -> float:
    """``mean|grad v|^2``, i.e. ``sum_ij mean (d_j v_i)^2``."""
    total = float(np.sum(grid.k2 * np.abs(vector_hat) ** 2 * weight))
    return total / float(grid.n ** 6)


def _linf(vector_hat: ComplexArray, grid: Any) -> float:
    """``max_x |v(x)|`` over the collocation grid, vector magnitude."""
    real = _inverse(vector_hat, grid)
    return float(np.sqrt(np.max(np.sum(real * real, axis=0))))


def _divergence_linf(vector_hat: ComplexArray, grid: Any) -> float:
    div_hat = 1j * (grid.kx * vector_hat[0] + grid.ky * vector_hat[1] + grid.kz * vector_hat[2])
    return float(np.max(np.abs(_irfftn(div_hat, s=(grid.n, grid.n, grid.n), axes=(0, 1, 2)))))


def _nonlinear_hat(vector_hat: ComplexArray, grid: Any, dealias: bool) -> ComplexArray:
    """``P_L[(omega x u)_hat]`` — the rotational form of the convective term.

    For divergence-free ``u``, ``P_L((u . grad) u) = P_L(omega x u)`` exactly,
    because the two differ by ``P_L grad(|u|^2 / 2) = 0``. The rotational form is the
    one worth evaluating: ``u . (omega x u) = 0`` holds POINTWISE (a scalar triple
    product with a repeated factor), so the discrete energy neutrality is round-off
    rather than a residual of aliasing.
    """
    work = vector_hat * grid.dealias if dealias else vector_hat
    curl_buf = _curl_hat(work, grid)
    # One 6-component buffer, so velocity and vorticity transform to physical
    # space in a single batched inverse FFT (the core stacks the same way); a
    # newaxis here would concatenate along the batch axis and yield a 5-D array.
    combo = np.concatenate((work, curl_buf), axis=0)
    real = _inverse(combo, grid)
    u = real[0:3]
    w = real[3:6]
    cross = np.stack(
        (
            w[1] * u[2] - w[2] * u[1],
            w[2] * u[0] - w[0] * u[2],
            w[0] * u[1] - w[1] * u[0],
        )
    )
    cross_hat = _forward(cross, grid)
    if dealias:
        cross_hat = cross_hat * grid.dealias
    return _leray(cross_hat, grid)


def _step_ifrk4(
    vector_hat: ComplexArray,
    grid: Any,
    viscosity: float,
    dt: float,
    dealias: bool,
    e_full: Optional[FloatArray] = None,
    e_half: Optional[FloatArray] = None,
) -> ComplexArray:
    """One integrating-factor RK4 step: Stokes exactly, advection by RK4.

    ``e_full = exp(-nu |k|^2 dt)`` and ``e_half = exp(-nu |k|^2 dt / 2)`` may be
    passed in to skip recomputing the largest array in the problem every call;
    :func:`run_once` does. The arithmetic is the canonical core's.
    """
    if not math.isfinite(viscosity) or viscosity < 0.0:
        raise ValueError("viscosity must be finite and nonnegative")
    if not math.isfinite(dt) or dt <= 0.0:
        raise ValueError("dt must be finite and positive")
    # Narrowed once, into non-optional locals: `np.exp` over an `Any` grid array
    # would otherwise leave the parameter typed Optional after an in-place
    # reassignment, and every product below would be a `* None` for a static reader.
    full: FloatArray = np.exp(-viscosity * grid.k2 * dt) if e_full is None else e_full
    half: FloatArray = np.exp(-viscosity * grid.k2 * 0.5 * dt) if e_half is None else e_half

    def rhs(state: ComplexArray) -> ComplexArray:
        return -_nonlinear_hat(state, grid, dealias)

    a = dt * rhs(vector_hat)
    b = dt * rhs(half * (vector_hat + 0.5 * a))
    c = dt * rhs(half * vector_hat + 0.5 * b)
    d = dt * rhs(full * vector_hat + half * c)
    return full * vector_hat + (full * a + 2.0 * half * (b + c) + d) / 6.0


# ---------------------------------------------------------------------------
# engine resolution
# ---------------------------------------------------------------------------


@dataclass
class Engine:
    """A solver backend, named. Every measurement in this file goes through it."""

    name: str
    note: str
    spectral: Callable[[int], Any]
    forward: Callable[..., ComplexArray]
    inverse: Callable[..., FloatArray]
    leray: Callable[..., ComplexArray]
    curl_hat: Callable[..., ComplexArray]
    energy: Callable[..., float]
    enstrophy: Callable[..., float]
    divergence_linf: Callable[..., float]
    nonlinear_hat: Callable[..., ComplexArray]
    step_ifrk4: Callable[..., ComplexArray]
    initial_field: Dict[str, Callable[[int], FloatArray]]
    transform_backend: str

    def as_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "note": self.note,
            "transform_backend": self.transform_backend,
            "numpy_version": np.__version__,
            "scipy_fft_available": _scipy_fft is not None,
            "initial_conditions": sorted(self.initial_field),
        }


def _builtin_engine() -> Engine:
    # Named functions, not lambdas: the Engine fields are Callable[..., float] and a
    # bare lambda leaves its parameters unannotated for a strict reader, so the
    # weight lookup happens in a signature that says what it takes.
    def energy(v: ComplexArray, g: Any) -> float:
        return _energy(v, g, _parseval_weight(g))

    def enstrophy(v: ComplexArray, g: Any) -> float:
        return _enstrophy(v, g, _parseval_weight(g))

    return Engine(
        name="builtin_ifrk4",
        note="self-contained numpy Fourier-Galerkin engine in scripts/navier_worldsense_receipt.py",
        spectral=spectral,
        forward=_forward,
        inverse=_inverse,
        leray=_leray,
        curl_hat=_curl_hat,
        energy=energy,
        enstrophy=enstrophy,
        divergence_linf=_divergence_linf,
        nonlinear_hat=_nonlinear_hat,
        step_ifrk4=_step_ifrk4,
        initial_field=dict(INITIAL_CONDITIONS),
        transform_backend="scipy.fft" if _scipy_fft is not None else "numpy.fft",
    )


_CORE_MODULE = "navier_spectral_core"

_CORE_NAMES = (
    "spectral",
    "forward",
    "inverse",
    "leray",
    "curl_hat",
    "energy",
    "enstrophy",
    "divergence_linf",
    "nonlinear_hat",
    "step_ifrk4",
)


def _canonical_core() -> Any:
    """Import ``scripts/navier_spectral_core.py`` (the reality unification shim).

    Returns ``None`` on any failure. On a hosted runner ``~/reality`` is not checked
    out and the shim raises by design ("fails loudly rather than silently measuring a
    frozen copy"); that is the supported degraded path here, not a defect in this
    script, and :func:`resolve_engine` records which engine actually answered.

    The load route is the repository's own — ``scripts`` on ``sys.path``, then a
    normal ``importlib.import_module`` — the way
    ``tests/test_navier_solver_equivalence.py``, ``scripts/navier_adaptive_bench.py``
    and ``scripts/ns_paired_benchmark.py`` all reach the shim. It is not a style
    choice: loading the shim through ``spec_from_file_location`` + ``exec_module``
    under a private name measured here as
    ``AttributeError: 'NoneType' object has no attribute '__dict__'`` inside
    ``dataclasses._is_type``. The reality body declares ``class Spectral`` with
    string (PEP 563) annotations and no ``from __future__ import annotations`` of its
    own resolution table, so dataclasses looks the defining module up by name in
    ``sys.modules``; the shim re-exports by copying globals, which leaves the REALITY
    module's name bound to nothing unless the ordinary import machinery did the
    binding. An ad-hoc loader silently disabled the canonical engine on the one host
    that has it — the failure was invisible because the builtin fallback is designed
    to be quiet.
    """
    if not (SCRIPTS / f"{_CORE_MODULE}.py").is_file():
        return None
    entry = str(SCRIPTS)
    if entry not in sys.path:
        sys.path.insert(0, entry)
    try:
        module = importlib.import_module(_CORE_MODULE)
    except Exception:  # noqa: BLE001 - absent reality is normal on CI
        return None
    if not all(hasattr(module, attribute) for attribute in _CORE_NAMES):
        return None
    return module


def _wrap_core(core: Any) -> Engine:
    """Adapt the canonical core's signatures to this module's ``(value, grid)`` form."""

    def forward(field: FloatArray, _grid: Any) -> ComplexArray:
        # The core's forward takes the real field alone; `_grid` keeps the adapter's
        # arity aligned with the builtin engine's (see _builtin_engine._forward).
        return core.forward(np.ascontiguousarray(np.asarray(field, dtype=np.float64)))

    def inverse(field_hat: ComplexArray, grid: Any) -> FloatArray:
        return core.inverse(field_hat, grid.n)

    def step_ifrk4(
        vector_hat: ComplexArray,
        grid: Any,
        viscosity: float,
        dt: float,
        dealias: bool,
        e_full: Optional[FloatArray] = None,
        e_half: Optional[FloatArray] = None,
    ) -> ComplexArray:
        # core: step_ifrk4(v, sp, nu, dt, dealias, forcing=None, time=0.0, e_full, e_half)
        return core.step_ifrk4(
            vector_hat, grid, viscosity, dt, dealias, None, 0.0, e_full, e_half
        )

    fields: Dict[str, Callable[[int], FloatArray]] = dict(INITIAL_CONDITIONS)
    for attribute in ("taylor_green_field", "abc_field"):
        if hasattr(core, attribute):
            fields[attribute.replace("_field", "")] = getattr(core, attribute)
    return Engine(
        name="reality_shim",
        note="canonical unified solver via scripts/navier_spectral_core.py (~/reality/solvers/navier)",
        spectral=core.spectral,
        forward=forward,
        inverse=inverse,
        leray=core.leray,
        curl_hat=core.curl_hat,
        energy=core.energy,
        enstrophy=core.enstrophy,
        divergence_linf=core.divergence_linf,
        nonlinear_hat=core.nonlinear_hat,
        step_ifrk4=step_ifrk4,
        initial_field=fields,
        transform_backend="core",
    )


def resolve_engine(preference: str = "auto") -> Engine:
    """``auto`` prefers the canonical core and falls back to the builtin engine."""
    core = _canonical_core()
    if preference == "canonical":
        if core is None:
            raise RuntimeError(
                "--engine canonical requested but scripts/navier_spectral_core.py did "
                "not import on this host (no ~/reality/solvers/navier checkout)"
            )
        return _wrap_core(core)
    if preference == "builtin":
        return _builtin_engine()
    if core is not None:
        return _wrap_core(core)
    return _builtin_engine()


# ---------------------------------------------------------------------------
# invariants
# ---------------------------------------------------------------------------


def _inner_product(a_real: FloatArray, b_real: FloatArray) -> float:
    """Discrete (trapezoidal) ``mean(a . b)`` over the collocation grid."""
    # cast to Any: numpy types the reduction of a float64 array as an unbound
    # generic, so `float(...)` below would hand a statically Unknown object to
    # the interpreter even though it is a numpy scalar by construction.
    return float(cast(Any, np.mean(np.sum(a_real * b_real, axis=0))))


def convective_skew_residual(
    engine: Engine,
    grid: Any,
    vector_hat: ComplexArray,
    dealias: bool,
) -> Dict[str, float]:
    """How exactly energy-neutral the convective term is on this grid.

    Three instruments, reported together because they fail for different reasons:

      * ``triple_product_pointwise`` — ``mean(u . (omega x u))``: zero because the
        scalar triple product repeats a factor, so round-off only, at any resolution;
      * ``projected_convective`` — ``mean(u . P_L(omega x u))``, what the energy
        identity actually needs. It equals the pointwise value because ``P_L`` is an
        orthogonal projector and the state is already divergence-free, so a gap
        between the two means the projector or the state is wrong, not the algebra;
      * ``projected_convective_relative`` — the same divided by
        ``||u|| * ||P_L(omega x u)||``, the only version comparable across grids and
        viscosities (an absolute residual shrinks simply because the flow decayed).
    """
    weight = _parseval_weight(grid)
    nonlinear = engine.nonlinear_hat(vector_hat, grid, dealias)
    u_real = engine.inverse(vector_hat, grid)
    n_real = engine.inverse(nonlinear, grid)
    w_real = engine.inverse(engine.curl_hat(vector_hat, grid), grid)
    cross = np.stack(
        (
            w_real[1] * u_real[2] - w_real[2] * u_real[1],
            w_real[2] * u_real[0] - w_real[0] * u_real[2],
            w_real[0] * u_real[1] - w_real[1] * u_real[0],
        )
    )
    pointwise = _inner_product(u_real, cross)
    projected = _inner_product(u_real, n_real)
    u_norm = math.sqrt(max(_norm_sq(vector_hat, grid, weight), 0.0))
    n_norm = math.sqrt(max(_norm_sq(nonlinear, grid, weight), 0.0))
    scale = u_norm * n_norm
    return {
        "triple_product_pointwise": pointwise,
        "projected_convective": projected,
        "projected_convective_relative": (abs(projected) / scale) if scale > 0.0 else 0.0,
        "velocity_l2": u_norm,
        "nonlinear_l2": n_norm,
    }


def enstrophy_production(engine: Engine, grid: Any, vector_hat: ComplexArray) -> float:
    """``mean(omega . (omega . grad) u)`` — the vortex-stretching source of ``Z``.

    This is the only term in the 3D enstrophy budget that can make ``Z`` grow, so it
    is the term the Beale-Kato-Majda integral is really about. Evaluated
    pseudospectrally (derivatives in Fourier, products in physical space), which
    makes it a statement about this discretisation: with the 2/3 rule the triple
    product carries its own aliasing error, so this number is a refinement TARGET
    for the reactor hint, not an invariant, and it is never gated.
    """
    w_hat = engine.curl_hat(vector_hat, grid)
    w_real = engine.inverse(w_hat, grid)
    box = (grid.n, grid.n, grid.n)
    total = np.zeros(box, dtype=np.float64)
    for component in range(3):
        advected = np.zeros(box, dtype=np.float64)
        for direction, k in enumerate(_ks(grid)):
            deriv_hat = vector_hat[component] * (1j * k)
            advected += w_real[direction] * _irfftn(deriv_hat, s=box, axes=(0, 1, 2))
        total += advected * w_real[component]
    return float(np.mean(total))


def _simpson(values: Sequence[float], h: float) -> Optional[float]:
    """Composite Simpson over an even number of intervals (so an odd sample count)."""
    count = len(values)
    if count < 3 or count % 2 == 0:
        return None
    interior = sum(values[i] * (4.0 if i % 2 else 2.0) for i in range(1, count - 1))
    return h / 3.0 * (values[0] + values[-1] + interior)


def _trapezoid(values: Sequence[float], h: float) -> float:
    if len(values) < 2:
        return 0.0
    return h * (0.5 * values[0] + math.fsum(values[1:-1]) + 0.5 * values[-1])


# ---------------------------------------------------------------------------
# one run
# ---------------------------------------------------------------------------


def run_once(
    engine: Engine,
    grid_n: int,
    viscosity: float,
    dt: float,
    steps: int,
    initial: str = "taylor_green",
    dealias: bool = True,
    include_series: bool = False,
) -> Dict[str, Any]:
    """Integrate one ``(N, nu, dt, steps)`` configuration and instrument it.

    The state advances at ``h = dt / 2`` and the energy balance is checked across a
    full ``dt`` against the enstrophy at the genuine midpoint between them. That is
    a quadrature choice, not a second solver: ``dE/dt = -2 nu Z`` sampled
    symmetrically about ``t + dt/2`` is second-order accurate in ``dt``, so the
    residual that comes back is the integrator's, not the estimator's. Doubling the
    step count also buys the Simpson rule an even interval count for the BKM
    integral at no extra bookkeeping.
    """
    if grid_n < 4 or grid_n % 2:
        raise ValueError("grid must be an even integer >= 4")
    if steps < 1:
        raise ValueError("steps must be >= 1")
    if not math.isfinite(viscosity) or viscosity < 0.0:
        raise ValueError("viscosity must be finite and nonnegative")
    if not math.isfinite(dt) or dt <= 0.0:
        raise ValueError("dt must be finite and positive")
    if initial not in engine.initial_field:
        raise KeyError(f"unknown initial condition {initial!r}")

    grid = engine.spectral(grid_n)
    h = 0.5 * dt
    t_final = steps * dt
    substeps = 2 * steps
    e_full = np.exp(-viscosity * grid.k2 * h)
    e_half = np.exp(-viscosity * grid.k2 * 0.5 * h)

    state = _as_state(engine.leray(engine.forward(engine.initial_field[initial](grid_n), grid), grid), grid)

    times: List[float] = []
    energies: List[float] = []
    enstrophies: List[float] = []
    vorticity_linf: List[float] = []
    productions: List[float] = []
    divergences: List[float] = []
    skews: List[Dict[str, float]] = []
    grad_u_sq: List[float] = []

    for index in range(substeps + 1):
        if index:
            state = engine.step_ifrk4(state, grid, viscosity, h, dealias, e_full, e_half)
        # `state` now holds the field at t = index * h.
        energies.append(float(engine.energy(state, grid)))
        enstrophies.append(float(engine.enstrophy(state, grid)))
        vorticity_linf.append(_linf(engine.curl_hat(state, grid), grid))
        times.append(index * h)
        if index % 2 == 0:
            divergences.append(_divergence_linf(state, grid))
            skews.append(convective_skew_residual(engine, grid, state, dealias))
            weight = _parseval_weight(grid)
            # mean|grad u|^2 == mean|omega|^2 == 2 Z exactly for a periodic
            # divergence-free Galerkin field; the pair is reported so a future
            # projector bug shows up as a split rather than as a silent drift.
            grad_u_sq.append(_mean_grad_sq(state, grid, weight))
            productions.append(enstrophy_production(engine, grid, state))

    max_energy_increase = 0.0
    for previous, current in zip(energies, energies[1:]):
        max_energy_increase = max(max_energy_increase, current - previous)

    stepwise_residual = 0.0
    for j in range(steps):
        observed = (energies[2 * j + 2] - energies[2 * j]) / dt
        stepwise_residual = max(
            stepwise_residual, abs(observed + 2.0 * viscosity * enstrophies[2 * j + 1])
        )

    integral_z = _simpson(enstrophies, h)
    cumulative_residual = (
        abs((energies[-1] - energies[0]) + 2.0 * viscosity * integral_z)
        if integral_z is not None
        else 0.0
    )
    integral_bkm = _simpson(vorticity_linf, h)
    peak_index = int(np.argmax(np.asarray(vorticity_linf)))
    production_index = int(np.argmax(np.asarray(productions))) if productions else 0
    dissipation_rate = 2.0 * viscosity * (integral_z / t_final) if integral_z is not None else 0.0
    kolmogorov_eta = (viscosity ** 3 / dissipation_rate) ** 0.25 if dissipation_rate > 0.0 else None
    k_max = math.sqrt(3.0) * (grid_n / 2.0)
    # Beltrami check: ABC has |k|^2 = 1, so E(T) = E(0) exp(-2 nu T) is analytic.
    exact_ratio = math.exp(-2.0 * viscosity * t_final) if initial == "abc" else None

    receipt_run: Dict[str, Any] = {
        "grid": grid_n,
        "viscosity": viscosity,
        "dt": dt,
        "steps": steps,
        "substeps_per_report": 2,
        "t_final": t_final,
        "initial_condition": initial,
        "dealias": dealias,
        "energy_initial": energies[0],
        "energy_final": energies[-1],
        "energy_ratio": (energies[-1] / energies[0]) if energies[0] > 0.0 else None,
        "energy_exact_ratio_beltrami": exact_ratio,
        "energy_exact_error_beltrami": (
            abs(energies[-1] / energies[0] - exact_ratio)
            if exact_ratio is not None and energies[0] > 0.0
            else None
        ),
        "max_energy_increase": max_energy_increase,
        "dissipation_rate_mean": dissipation_rate,
        "enstrophy_initial": enstrophies[0],
        "enstrophy_final": enstrophies[-1],
        "enstrophy_peak": max(enstrophies),
        "enstrophy_peak_t": times[int(np.argmax(np.asarray(enstrophies)))],
        "integral_enstrophy_simpson": integral_z,
        "integral_enstrophy_trapezoid": _trapezoid(enstrophies, h),
        "energy_balance_stepwise_residual": stepwise_residual,
        "energy_balance_cumulative_residual": cumulative_residual,
        "energy_balance_cumulative_residual_relative": (
            cumulative_residual / energies[0] if energies[0] > 0.0 else None
        ),
        "mean_grad_u_sq_minus_2z_max": max(
            abs(value - 2.0 * z) for value, z in zip(grad_u_sq, enstrophies[::2])
        ),
        "divergence_linf_max": max(divergences) if divergences else None,
        "convective_skew": {
            "projected_convective_max": max(abs(s["projected_convective"]) for s in skews),
            "triple_product_pointwise_max": max(abs(s["triple_product_pointwise"]) for s in skews),
            "projected_convective_relative_max": max(s["projected_convective_relative"] for s in skews),
            "samples": len(skews),
        },
        "vorticity_linf_initial": vorticity_linf[0],
        "vorticity_linf_final": vorticity_linf[-1],
        "vorticity_linf_peak": vorticity_linf[peak_index],
        "vorticity_linf_peak_t": times[peak_index],
        "bkm_integral_simpson": integral_bkm,
        "bkm_integral_trapezoid": _trapezoid(vorticity_linf, h),
        "enstrophy_production_peak": productions[production_index] if productions else None,
        "enstrophy_production_peak_t": times[2 * production_index] if productions else None,
        "kolmogorov_length": kolmogorov_eta,
        "grid_spacing": 2.0 * math.pi / grid_n,
        "resolution_ratio": (k_max * kolmogorov_eta) if kolmogorov_eta is not None else None,
        "underresolved": (
            None if kolmogorov_eta is None else bool(k_max * kolmogorov_eta < 1.0)
        ),
    }
    if include_series:
        receipt_run["time_series"] = {
            "t": times,
            "energy": energies,
            "enstrophy": enstrophies,
            "vorticity_linf": vorticity_linf,
            # These are sampled at the REPORT steps only (every second half step),
            # so their axis is ``times[0::2]`` — 0, dt, 2 dt, ... The production
            # series is what names the refinement window, so it travels with the
            # series rather than only as a max.
            "t_report": times[0::2],
            "production": productions,
            "divergence_linf": divergences,
            "mean_grad_u_sq": grad_u_sq,
            "convective_skew_abs": [s["projected_convective"] for s in skews],
            "triple_product_pointwise": [s["triple_product_pointwise"] for s in skews],
        }
    return receipt_run


def temporal_refinement(
    engine: Engine, grid_n: int, viscosity: float, dt: float, steps: int, initial: str
) -> Dict[str, Any]:
    """Richardson gap between ``dt`` and ``dt / 2`` at one fixed grid.

    IFRK4 is fourth order on the advective term (the Stokes part is integrated
    exactly, so it contributes no temporal error). What is quoted here is the
    OBSERVED coarse-fine gap; a clean order estimate needs a third refinement, and
    claiming ``p = 4`` from two runs would be a claim about the scheme rather than
    about this data. Where the configuration admits an analytic target (Beltrami
    ABC), that target is reported next to the gap.
    """
    coarse = run_once(engine, grid_n, viscosity, dt, steps, initial)
    fine = run_once(engine, grid_n, viscosity, 0.5 * dt, 2 * steps, initial)
    difference = coarse["energy_final"] - fine["energy_final"]
    return {
        "quantity": "energy_final",
        "dt_coarse": dt,
        "dt_fine": 0.5 * dt,
        "steps_coarse": steps,
        "steps_fine": 2 * steps,
        "energy_final_coarse": coarse["energy_final"],
        "energy_final_fine": fine["energy_final"],
        "abs_difference": abs(difference),
        "relative_difference": (
            abs(difference) / abs(fine["energy_final"]) if fine["energy_final"] else None
        ),
        "bkm_abs_difference": abs(
            (coarse["bkm_integral_simpson"] or 0.0) - (fine["bkm_integral_simpson"] or 0.0)
        ),
        "coarse_balance_residual": coarse["energy_balance_stepwise_residual"],
        "fine_balance_residual": fine["energy_balance_stepwise_residual"],
        "note": "an observation about this integrator on this data, not an order proof",
    }


def spatial_refinement(
    engine: Engine,
    grids: Sequence[int],
    viscosity: float,
    dt: float,
    steps: int,
    initial: str,
) -> Dict[str, Any]:
    """Grid-refinement sensitivity of ``E(T)`` and of the BKM integral."""
    runs = [run_once(engine, int(n), viscosity, dt, steps, initial) for n in grids]
    energies = [r["energy_final"] for r in runs]
    bkms = [(r["bkm_integral_simpson"] or 0.0) for r in runs]
    return {
        "grids": [int(n) for n in grids],
        "energy_final": energies,
        "bkm_integral": bkms,
        "energy_spread": (max(energies) - min(energies)) if energies else None,
        "bkm_spread": (max(bkms) - min(bkms)) if bkms else None,
        "note": "difference between resolved fields on these grids for the same "
        "initial data; it bounds the spatial part of this receipt's error bar",
    }


# ---------------------------------------------------------------------------
# receipt assembly
# ---------------------------------------------------------------------------


def _utc_stamp() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _git_head() -> Optional[str]:
    """This repository's HEAD commit, read from the filesystem (no subprocess)."""
    try:
        git = REPO / ".git"
        if git.is_dir():
            return _resolve_head(git)
        if git.is_file():
            # A linked worktree stores `gitdir:` into the main checkout.
            pointer = git.read_text(encoding="utf-8").strip()
            if pointer.startswith("gitdir:"):
                target = Path(pointer.split(":", 1)[1].strip())
                if not target.is_absolute():
                    target = (REPO / target).resolve()
                return _resolve_head(target)
    except OSError:
        return None
    return None


def _resolve_head(gitdir: Path) -> Optional[str]:
    try:
        head = (gitdir / "HEAD").read_text(encoding="utf-8").strip()
    except OSError:
        return None
    if not head.startswith("ref:"):
        return head or None
    ref_path = gitdir / head.split(" ", 1)[1].strip()
    if not ref_path.is_file():
        common = gitdir / "commondir"
        try:
            base = (gitdir / common.read_text(encoding="utf-8").strip()).resolve()
            ref_path = base / head.split(" ", 1)[1].strip()
        except OSError:
            return None
    try:
        return ref_path.read_text(encoding="utf-8").strip() or None
    except OSError:
        return None


def build_receipt(
    grids: Sequence[int] = (DEFAULT_GRID,),
    viscosities: Sequence[float] = DEFAULT_VISCOSITIES,
    dt: float = DEFAULT_DT,
    steps: int = DEFAULT_STEPS,
    initial: str = "taylor_green",
    dealias: bool = True,
    engine: Optional[Engine] = None,
    convergence_grids: Sequence[int] = DEFAULT_CONVERGENCE_GRIDS,
    include_series: bool = False,
) -> Dict[str, Any]:
    """Run the schedule and emit one ``worldsense.scientific_receipt/1`` payload."""
    if not grids or not viscosities:
        raise ValueError("grids and viscosities must both be non-empty")
    started = time.perf_counter()
    engine = engine if engine is not None else resolve_engine("auto")

    runs: List[Dict[str, Any]] = []
    solver_steps = 0
    for grid_n in grids:
        for viscosity in viscosities:
            runs.append(run_once(engine, int(grid_n), float(viscosity), dt, steps, initial, dealias, include_series))
            solver_steps += 2 * steps

    temporal = temporal_refinement(engine, int(grids[0]), float(viscosities[0]), dt, steps, initial)
    spatial = spatial_refinement(engine, convergence_grids, float(viscosities[0]), dt, steps, initial)
    solver_steps += 2 * steps + 2 * (2 * steps) + 2 * 2 * steps

    best = max(runs, key=lambda r: (r["enstrophy_production_peak"] or 0.0))
    skew_abs_max = max(r["convective_skew"]["projected_convective_max"] for r in runs)
    skew_rel_max = max(r["convective_skew"]["projected_convective_relative_max"] for r in runs)
    divergence_max = max((r["divergence_linf_max"] or 0.0) for r in runs)
    balance_max = max(r["energy_balance_stepwise_residual"] for r in runs)
    cumulative_max = max((r["energy_balance_cumulative_residual_relative"] or 0.0) for r in runs)
    monotone_worst = max(r["max_energy_increase"] for r in runs)
    bkm_values = [r["bkm_integral_simpson"] for r in runs]
    wall_ms = (time.perf_counter() - started) * 1000.0

    payload: Dict[str, Any] = {
        "receipt_schema": RECEIPT_SCHEMA,
        "schema": RECEIPT_SCHEMA,
        "kind": RECEIPT_KIND,
        "operation": RECEIPT_OPERATION,
        "domain": DOMAIN,
        "title": "3D incompressible Navier-Stokes Leray energy dissipation, "
        "Beale-Kato-Majda integral and triad cancellation on a periodic torus",
        "tier": TIER_PROBABLY,
        "layer": LAYER_PROBABLY,
        "epistemic_tier": EPISTEMIC_TIER,
        "deductive_proof": False,
        "clay_3d_global_regularity_claimed": False,
        "generated_utc": _utc_stamp(),
        "provenance": {
            "repository": REPO.name,
            "head": _git_head(),
            "python": platform.python_version(),
            "platform": platform.platform(),
            "script": Path(__file__).name,
            "engine": engine.as_dict(),
            "canonical_home": str(Path.home() / "reality" / "solvers" / "navier"),
        },
        "configuration": {
            "grids": [int(n) for n in grids],
            "viscosities": [float(nu) for nu in viscosities],
            "dt": dt,
            "steps": steps,
            "t_final": dt * steps,
            "initial_condition": initial,
            "dealias": dealias,
            "equation": "du/dt = -P_L((u . grad) u) + nu * laplacian(u),  div u = 0",
            "domain_geometry": "periodic box [0, 2 pi)^3, nondimensional units",
            "integrator": "integrating-factor RK4 (Stokes exact, advection RK4)",
        },
        "invariants": {
            "leray_energy_dissipation": {
                "identity": "dE/dt = -2 nu Z,  E = 0.5 mean|u|^2,  Z = 0.5 mean|omega|^2",
                "energy_initial_mean": math.fsum(r["energy_initial"] for r in runs) / len(runs),
                "energy_final_mean": math.fsum(r["energy_final"] for r in runs) / len(runs),
                "energy_decayed": bool(all(r["energy_final"] < r["energy_initial"] for r in runs)),
                "max_stepwise_energy_increase": monotone_worst,
                "stepwise_residual_max": balance_max,
                "cumulative_residual_relative_max": cumulative_max,
                "sign": "nonpositive up to the integrator's truncation error",
            },
            "beale_kato_majda": {
                "definition": "int_0^T ||omega(t)||_infty dt, collocation-grid sup norm",
                "integral_min": min(bkm_values) if bkm_values else None,
                "integral_max": max(bkm_values) if bkm_values else None,
                "all_positive_finite": bool(
                    all(v is not None and math.isfinite(v) and v > 0.0 for v in bkm_values)
                ),
                "quadrature": "composite Simpson over 2*steps half-steps; trapezoid reported per run",
                "scope_note": "finite on a truncated system by construction; it bounds "
                "resolution over [0, T] and says nothing about continuum regularity",
            },
            "triad_cancellation": {
                "identity": "<u, P_L((u . grad) u)> = 0 for divergence-free periodic u",
                "abs_max": skew_abs_max,
                "relative_max": skew_rel_max,
                "gated_on": "abs_max",
                "conditioning_note": "the gate is the ABSOLUTE residual, as the identity is "
                "an assertion about <u, P_L(...)> itself. relative_max divides by "
                "||u|| * ||P_L(...)||, which vanishes for a Beltrami field, so on ABC data "
                "an O(1) relative reading accompanies an O(1e-18) absolute one: it is the "
                "denominator going to zero, not the cancellation failing.",
                "pointwise_triple_product_max": max(
                    r["convective_skew"]["triple_product_pointwise_max"] for r in runs
                ),
                "mechanism": "u . (omega x u) = 0 pointwise (repeated factor in the scalar "
                "triple product) and P_L is an orthogonal projector, so the projected "
                "convective term inherits the cancellation",
                "tolerance": CONVECTIVE_TOLERANCE,
                "holds": bool(skew_abs_max < CONVECTIVE_TOLERANCE),
            },
            "solenoidal_constraint": {
                "definition": "max over sampled times of the grid sup norm of div u",
                "max_abs_divergence_linf": divergence_max,
                "tolerance": DIV_TOLERANCE,
                "holds": bool(divergence_max < DIV_TOLERANCE),
            },
            "enstrophy_budget": {
                "identity": "dZ/dt = mean(omega . (omega . grad) u) - nu mean|grad omega|^2",
                "mean_grad_u_sq_minus_2z_max": max(r["mean_grad_u_sq_minus_2z_max"] for r in runs),
                "note": "the identity is checked on the DISCRETE fields; production is "
                "reported per run as a refinement target and is not gated",
            },
        },
        "runs": runs,
        "refinement": {"temporal": temporal, "spatial": spatial},
        # note: the two claim flags appear ONCE at the top level (with tier, layer and
        # epistemic_tier above) and once inside `probably`. This literal used to declare
        # them twice at the top level -- harmless while both copies said False, and a
        # silent last-wins divergence the moment they did not. The epistemic gate reads
        # `payload.get(key)`, so a duplicated key is a gate that can be satisfied by the
        # copy nobody edited.
        "probably": {
            "schema": PROBABLY_SCHEMA,
            "layer": LAYER_PROBABLY,
            "epistemic_tier": EPISTEMIC_TIER,
            "deductive_proof": False,
            "clay_3d_global_regularity_claimed": False,
            "confidence": {
                "temporal_richardson_relative_gap": temporal["relative_difference"],
                "spatial_energy_spread": spatial["energy_spread"],
                "spatial_bkm_spread": spatial["bkm_spread"],
                "energy_balance_cumulative_residual_relative": cumulative_max,
            },
            "what_this_establishes": [
                "this Fourier-Galerkin discretisation loses kinetic energy at the viscous "
                "rate 2 nu Z to within its own truncation error",
                "the convective transfer is energy-neutral to machine precision on the "
                "discrete divergence-free subspace",
                "the computed ||omega||_infty time integral is finite over [0, T] for "
                "these parameters",
            ],
            "what_this_does_not_establish": [
                "global smoothness of 3D Navier-Stokes (Clay problem A/B)",
                "finite-time breakdown, nor that its possibility was tested",
                "any bound on a continuum solution at any time",
                "that refining the grid would keep the BKM integral bounded",
            ],
        },
        "reactor_optimization_hint": {
            "kind": "adaptive_refinement",
            "driver": "enstrophy_stretching",
            "nu_star": best["viscosity"],
            "grid_star": best["grid"],
            "t_star": best["enstrophy_production_peak_t"],
            "window": [
                max(0.0, (best["enstrophy_production_peak_t"] or 0.0) - dt),
                (best["enstrophy_production_peak_t"] or 0.0) + dt,
            ],
            "peak_enstrophy_production": best["enstrophy_production_peak"],
            "peak_vorticity_linf": best["vorticity_linf_peak"],
            "peak_vorticity_linf_t": best["vorticity_linf_peak_t"],
            "peak_enstrophy": best["enstrophy_peak"],
            # The peak sits at the end of the interval: the window is clipped
            # there, so the hint names a boundary of the measured interval
            # rather than an interior event.
            "peak_at_window_edge": bool(
                (best["enstrophy_production_peak_t"] or 0.0)
                >= float(best["t_final"]) - dt
            ),
            "kolmogorov_length": best["kolmogorov_length"],
            "grid_spacing": best["grid_spacing"],
            "resolution_ratio_kmax_eta": best["resolution_ratio"],
            "underresolved": best["underresolved"],
            "action": "refine time-stepping and/or raise N inside this window; a fixed dt "
            "spends its error where the stretching peaks",
            "expected_effect": "a smaller energy-balance residual and a larger, "
            "better-resolved BKM integral",
            "epistemic_note": "refinement raises the fidelity of a numerical observation; "
            "it never raises its tier",
        },
        "z8_meter": {
            "digest_sha256": None,
            "digest_over": "stable view of the measurement: excludes generated_utc, "
            "provenance, wall_ms and the digest itself, so a replay reproduces it",
            "wall_ms": wall_ms,
            "solver_steps": solver_steps,
            "runs": len(runs) + 4,
            "grid_points_per_run": [int(r["grid"]) ** 3 for r in runs],
            "deterministic": True,
            # These are the fields the stable view drops. They name the whole
            # `provenance` subtree rather than one key inside it, because that is
            # what _VOLATILE_KEYS actually excludes: an earlier draft listed
            # `provenance.host`, a field this payload never emits, so the receipt
            # documented a volatility it does not have while hiding the platform,
            # head and engine strings it does.
            "nondeterministic_fields": [
                "generated_utc",
                "z8_meter.wall_ms",
                "provenance.platform",
                "provenance.python",
                "provenance.head",
                "provenance.engine",
            ],
        },
    }
    payload["z8_meter"]["digest_sha256"] = payload_sha256(payload)
    validate_navier_receipt_epistemics(payload)
    return payload


# ---------------------------------------------------------------------------
# epistemic gate
# ---------------------------------------------------------------------------


def _walk_strings(value: Any, path: str = "$") -> Iterator[Tuple[str, str]]:
    """Every string in a nested structure, with its JSON path, for refusal messages."""
    if isinstance(value, str):
        yield path, value
    elif isinstance(value, dict):
        # Annotated view of the narrowed mapping: isinstance against bare `dict`
        # leaves the key and value types unbound, and an unbound key would make
        # the path string below statically unknown. JSON object keys are strings.
        mapping = cast(Dict[str, Any], value)
        for key, item in mapping.items():
            yield from _walk_strings(item, f"{path}.{key}")
    elif isinstance(value, (list, tuple)):
        for index, item in enumerate(cast(Sequence[Any], value)):
            yield from _walk_strings(item, f"{path}[{index}]")


def _looks_like_schema_id(value: str) -> bool:
    """Does this string read as a ``family/name/version`` identifier?

    Written without ``re`` to keep the module's dependency surface at numpy plus the
    standard library. The shape the ingest side recognises is a dotted lowercase
    namespace ending in ``/N`` — ``worldsense.scientific_receipt/1``,
    ``z8.probably/1``. Prose ("closed-form solution", "navier_stokes_3d") never has a
    trailing ``/digit``, so this does not fire on ordinary descriptive text.
    """
    head, slash, tail = value.rpartition("/")
    if not slash or not head or not tail:
        return False
    return tail.isdigit() and head == head.lower() and " " not in head


def validate_navier_receipt_epistemics(receipt: Any) -> Dict[str, Any]:
    """Refuse a navier receipt that claims more than a finite-grid run can support.

    Raises :class:`ValueError` on the first violation. This is a gate, not a
    rewriter: it never downgrades a claim quietly, because a receipt that edits its
    own tier is indistinguishable from one that never overstated.

    The parameter is ``Any``, not ``Dict[str, Any]``, on purpose: the consumer's
    first act is to check the payload is a mapping at all, and it runs on JSON read
    off disk (or off the wire) whose shape nothing has proven. Typing it as a dict
    would make that check statically redundant while leaving it exactly as load-
    bearing at runtime.

    Checks, most severe first:

      1. ``deductive_proof`` and ``clay_3d_global_regularity_claimed`` must be
         present and exactly ``False``, at the top level and in the ``probably``
         block — an ABSENT flag is not a false one;
      2. no string anywhere may stand alone as a theorem-grade word, and no
         tier-bearing field may hold one;
      3. ``epistemic_tier`` must be ``NUMERICAL_OBSERVATION`` and ``layer``
         ``Probably`` in both places;
      4. the schema strings must be the ones the ingest side recognises, and every
         schema-ish field that is present must say the same thing — the reader
         concatenates them, so one correct field cannot vouch for a second,
         different one; the empty string counts as absent, since that is exactly
         what the reader's own `.get(key, "")` sees. The three free-text fields the
         reader concatenates likewise (`kind`, `operation`, `event`) may not hold a
         foreign schema identifier: they cannot be pinned to one value, but they can
         be refused as a second family name;
      5. ``axioms`` may not appear at all. It is the ingest side's kernel-attestation
         channel: ``_kernel_notary`` reads ``row["axioms"]`` and decides whether a
         theorem-grade word is notarised by walking that set against
         ``STRICT_AXIOMS``. Publishing one here — empty, full, or anything between —
         is a numerical receipt signing up as a Lean verdict. The consumer refuses
         both an absent and an empty list (``no_axioms_field``,
         ``axioms_empty_or_unreadable``), so this rule costs the receipt nothing
         today: it is here for the day a producer starts copying tier words in, and
         for every consumer that reads the field more loosely than that one does.
    """
    if not isinstance(receipt, dict):
        raise ValueError("receipt must be a mapping")
    payload = cast(Dict[str, Any], receipt)

    probably = payload.get("probably")
    if not isinstance(probably, dict):
        raise ValueError("receipt carries no `probably` block")
    probably_block = cast(Dict[str, Any], probably)

    for key in ("deductive_proof", "clay_3d_global_regularity_claimed"):
        locations: List[Tuple[str, Any]] = [
            ("receipt", payload.get(key)),
            ("probably", probably_block.get(key)),
        ]
        for where, value in locations:
            if value is None:
                raise ValueError(
                    f"epistemic field {key!r} is missing from {where}; an absent claim "
                    f"is not a false claim"
                )
            if value is not False:
                raise ValueError(
                    f"epistemic inflation refused: {where}.{key} = {value!r} — a "
                    "finite-grid numerical run proves nothing deductively"
                )

    for path, text in _walk_strings(payload):
        if text.strip().upper() in PROOF_TIER_WORDS:
            raise ValueError(
                f"theorem-grade word {text!r} at {path}; this receipt is a numerical "
                "observation and may not carry one"
            )

    for field in TIER_FIELDS:
        for where, holder in (("receipt", payload), ("probably", probably_block)):
            value = holder.get(field)
            if isinstance(value, str) and value.strip().upper() in PROOF_TIER_WORDS:
                raise ValueError(f"tier field {where}.{field} = {value!r} asserts a proof")

    if payload.get("epistemic_tier") != EPISTEMIC_TIER:
        raise ValueError(f"receipt epistemic_tier must be {EPISTEMIC_TIER!r}")
    if probably_block.get("epistemic_tier") != EPISTEMIC_TIER:
        raise ValueError(f"probably.epistemic_tier must be {EPISTEMIC_TIER!r}")
    if payload.get("layer") != LAYER_PROBABLY or probably_block.get("layer") != LAYER_PROBABLY:
        raise ValueError(f"layer must be {LAYER_PROBABLY!r} in both the receipt and its probably block")
    if probably_block.get("schema") != PROBABLY_SCHEMA:
        raise ValueError(f"probably.schema must be {PROBABLY_SCHEMA!r}")
    # Every schema-ish field the ingest side concatenates must AGREE, not merely
    # one of them satisfy the check. The reader joins schema/kind/type/operation/
    # receipt_type/event into one string, so a payload carrying the true schema in
    # `receipt_schema` and a different one in `schema` reaches the classifier as a
    # hybrid and files by whichever substring lands first — a receipt can be
    # attributed to a domain its own `schema` field denies. Measured refusal:
    # schema="worldsense.proven_receipt/1" with a correct receipt_schema passed the
    # single-witness version of this check.
    #
    # An empty string counts as absent, not as disagreement: the reader's own read is
    # `payload.get(key, "")`, so `type=""` and no `type` key concatenate to identical
    # text and neither can add a matchable token. Refusing it would make the honest
    # tier unemittable by a producer that blanks optional fields, which is the same
    # failure mode as a gate that refuses PROBABLY. Any other non-matching value —
    # including a whitespace-only one, which is garbage rather than absence — is a
    # second, different schema claim and goes.
    for field in ("schema", "receipt_schema", "type", "receipt_type"):
        value = payload.get(field)
        if value is None or value == "":
            continue
        if value != RECEIPT_SCHEMA:
            raise ValueError(
                f"receipt {field} = {value!r}; a numerical navier receipt declares "
                f"{RECEIPT_SCHEMA!r} and every schema field must say the same thing"
            )
    if payload.get("schema") != RECEIPT_SCHEMA and payload.get("receipt_schema") != RECEIPT_SCHEMA:
        raise ValueError(
            f"receipt carries no {RECEIPT_SCHEMA!r} in schema or receipt_schema"
        )
    # The reader concatenates six fields, not four: `kind`, `operation` and `event`
    # join the same string that decides which receipt family this is filed under. They
    # are free text, so they cannot be pinned to one value, but a free-text field that
    # reads as a schema identifier is a second family name riding into the classifier
    # through a field this gate would otherwise never look at. Ordinary prose has no
    # trailing `/digit`, which is what makes the shape test safe to apply.
    for field in ("kind", "operation", "event"):
        value = payload.get(field)
        if (
            isinstance(value, str)
            and _looks_like_schema_id(value)
            and value not in (RECEIPT_SCHEMA, PROBABLY_SCHEMA)
        ):
            raise ValueError(
                f"receipt {field} = {value!r} names a schema this receipt does not "
                f"declare; the ingest side concatenates {field} with schema/type/"
                "receipt_type when it files a receipt, so a foreign identifier here "
                "re-attributes the run"
            )
    if payload.get("domain") != DOMAIN:
        raise ValueError(f"domain must be {DOMAIN!r}")
    if "axioms" in payload or "axioms" in probably_block:
        raise ValueError(
            "a numerical receipt may not carry an `axioms` field: it is the ingest "
            "side's kernel-attestation channel, and no Lean kernel walked any part "
            "of this run"
        )
    return {
        "ok": True,
        "tier": payload.get("tier"),
        "epistemic_tier": payload.get("epistemic_tier"),
    }


# ---------------------------------------------------------------------------
# digests and IO
# ---------------------------------------------------------------------------

#: Excluded from the measurement digest so a replay reproduces it on any host.
#: ``digest_sha256`` is excluded for self-reference: the digest of a receipt that
#: already carries one must equal the one it carries.
_VOLATILE_KEYS = frozenset({"generated_utc", "provenance", "wall_ms", "digest_sha256"})


def stable_view(payload: Any) -> Any:
    """The receipt with its volatile fields dropped and its floats exactified.

    Public because it is the digest's domain: a consumer that wants to know WHY two
    receipts differ, or to re-verify a stored digest without the writer's code, needs
    this projection and nothing else. It is not the payload's canonical text (that is
    :func:`canonical_json`); it is the smaller thing the digest is taken over.
    """
    if isinstance(payload, dict):
        mapping = cast(Dict[str, Any], payload)
        return {
            key: stable_view(value)
            for key, value in sorted(mapping.items())
            if key not in _VOLATILE_KEYS
        }
    if isinstance(payload, (list, tuple)):
        return [stable_view(item) for item in cast(Sequence[Any], payload)]
    if isinstance(payload, float):
        # repr() round-trips a double exactly, independent of locale or field width.
        return repr(payload)
    return payload


def canonical_json(payload: Any) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def payload_sha256(payload: Any) -> str:
    """The measurement digest: SHA-256 over the stable canonical view."""
    return hashlib.sha256(canonical_json(stable_view(payload)).encode("utf-8")).hexdigest()


def write_receipt(receipt: Dict[str, Any], output: Path) -> Dict[str, Any]:
    """Write ``{payload_sha256, payload}`` and return the write receipt."""
    body = canonical_json(receipt)
    digest = hashlib.sha256(body.encode("utf-8")).hexdigest()
    output.parent.mkdir(parents=True, exist_ok=True)
    wrapped = {"payload_sha256": digest, "payload": json.loads(body)}
    output.write_text(json.dumps(wrapped, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {"output": str(output), "payload_sha256": digest, "bytes": output.stat().st_size}


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _even_grid(value: str) -> int:
    number = int(value)
    if number < 4 or number % 2:
        raise argparse.ArgumentTypeError("must be an even integer >= 4")
    return number


def _positive_int(value: str) -> int:
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be >= 1")
    return number


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Emit a WorldSense scientific receipt for 3D Navier-Stokes dissipation."
    )
    parser.add_argument("--grid", type=_even_grid, nargs="+", default=[DEFAULT_GRID],
                        help="collocation grid(s), even and >= 4 (default: %(default)s)")
    parser.add_argument("--viscosities", type=float, nargs="+", default=list(DEFAULT_VISCOSITIES),
                        help="kinematic viscosity schedule (default: %(default)s)")
    parser.add_argument("--dt", type=float, default=DEFAULT_DT,
                        help="reported step, integrated with dt/2 (default: %(default)s)")
    parser.add_argument("--steps", type=_positive_int, default=DEFAULT_STEPS,
                        help="reported steps (default: %(default)s)")
    parser.add_argument("--ic", choices=sorted(INITIAL_CONDITIONS), default="taylor_green",
                        help="initial condition (default: %(default)s)")
    parser.add_argument("--no-dealias", action="store_true", help="disable the Orszag 2/3 rule")
    parser.add_argument("--engine", choices=("auto", "canonical", "builtin"), default="auto",
                        help="solver backend (default: %(default)s)")
    parser.add_argument("--convergence-grids", type=_even_grid, nargs=2,
                        default=list(DEFAULT_CONVERGENCE_GRIDS), metavar=("COARSE", "FINE"),
                        help="grids for the spatial refinement leg (default: %(default)s)")
    parser.add_argument("--include-series", action="store_true",
                        help="keep the per-step time series inside each run")
    parser.add_argument("--json", action="store_true", help="print the receipt as JSON on stdout")
    parser.add_argument("--out", type=Path, default=None,
                        help="write {payload_sha256, payload} to this path")
    parser.add_argument("--summary", action="store_true", help="print one line, not the payload")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    if args.dt <= 0.0 or not math.isfinite(args.dt):
        print("dt must be finite and positive", file=sys.stderr)
        return 2
    engine = resolve_engine(args.engine)
    receipt = build_receipt(
        grids=tuple(args.grid),
        viscosities=tuple(args.viscosities),
        dt=args.dt,
        steps=args.steps,
        initial=args.ic,
        dealias=not args.no_dealias,
        engine=engine,
        convergence_grids=tuple(args.convergence_grids),
        include_series=bool(args.include_series),
    )
    if args.out is not None:
        print(json.dumps(write_receipt(receipt, args.out.resolve()), indent=2))
    elif args.json:
        print(canonical_json(receipt))
    elif args.summary:
        invariants = receipt["invariants"]
        print(
            f"navier worldsense receipt engine={engine.name} grids={list(args.grid)} "
            f"nu={list(args.viscosities)} dt={args.dt} steps={args.steps} ic={args.ic} "
            f"E0={invariants['leray_energy_dissipation']['energy_initial_mean']:.12g} "
            f"ET={invariants['leray_energy_dissipation']['energy_final_mean']:.12g} "
            f"div={invariants['solenoidal_constraint']['max_abs_divergence_linf']:.3g} "
            f"skew={invariants['triad_cancellation']['relative_max']:.3g} "
            f"BKM={invariants['beale_kato_majda']['integral_max']:.6g} "
            f"digest={receipt['z8_meter']['digest_sha256'][:16]}"
        )
    else:
        print(
            canonical_json(
                {
                    "digest": receipt["z8_meter"]["digest_sha256"],
                    "engine": engine.name,
                    "tier": receipt["tier"],
                    "epistemic_tier": receipt["epistemic_tier"],
                    "invariants": receipt["invariants"],
                    "reactor_optimization_hint": receipt["reactor_optimization_hint"],
                    "hint": "pass --json for the full payload, or --out to write it",
                }
            )
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
