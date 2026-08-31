#!/usr/bin/env python3
"""Pseudo-spectral incompressible Navier--Stokes core on the periodic box.

Solves the rotational-form momentum equation on ``[0, 2*pi)^3``::

    du/dt + omega x u = -grad(P) + nu * laplacian(u) + f,      div(u) = 0

with ``omega = curl(u)`` and ``P = p + |u|^2 / 2``.  Working in Fourier space and
applying the Helmholtz--Leray projector ``P_L = I - k k^T / |k|^2`` annihilates
the pressure gradient exactly, leaving a closed evolution for the solenoidal
velocity::

    d(u_hat)/dt = -P_L[(omega x u)_hat] - nu * |k|^2 * u_hat + P_L[f_hat]

Three properties of this discretization are used as correctness diagnostics.

1.  ``P_L`` is an orthogonal projector onto the divergence-free subspace:
    ``k . (P_L v)_hat = k . v_hat - |k|^2 (k . v_hat) / |k|^2 = 0`` identically,
    so divergence is zero to round-off at every step by construction.

2.  The rotational form is energy-neutral pointwise, because ``omega x u`` is
    orthogonal to ``u``.  Hence ``d/dt (|u|^2 / 2) = -nu |grad u|^2`` in the
    semi-discrete system, and with ``nu = 0`` the only energy drift is the time
    integrator's truncation error.  This makes inviscid energy drift a clean,
    independent measurement of temporal accuracy.

3.  The quadratic nonlinearity moves energy to wavenumber ``2 k_max``, which a
    grid of ``N`` modes cannot represent.  The Orszag 2/3 rule zeroes every mode
    with ``|k_i| >= N / 3`` before and after the product so that the retained
    band is alias-free.

Time advance is integrating-factor RK4 (Trefethen, *Spectral Methods in
MATLAB*, ch. 10): the stiff viscous operator is integrated exactly by
``exp(-nu |k|^2 h)`` and the nonlinear remainder by classical RK4, giving fourth
order in ``h`` with no viscous stability restriction.

Real fields are carried as half-spectrum ``rfftn`` coefficients, which halves
both the transform cost and the memory traffic relative to a complex ``fftn``.
"""

from __future__ import annotations

import ctypes
import math
from dataclasses import dataclass

import multiprocessing as _mp

import numpy as np

# FFT backend: pyFFTW (fastest, pre-planned) > scipy.fft > numpy.fft.
_HAS_PYFFTW = False
_HAS_SCIPY_FFT = False
try:
    import pyfftw
    from pyfftw.interfaces import scipy_fft as _fft

    pyfftw.config.NUM_THREADS = 1  # N=16 arrays too small for multi-threading
    from pyfftw.interfaces.cache import enable as _fftw_enable_cache

    _fftw_enable_cache()
    _HAS_SCIPY_FFT = _HAS_PYFFTW = True
except ImportError:
    try:
        import scipy.fft as _fft

        _HAS_SCIPY_FFT = True
    except ImportError:
        pass  # fall through to numpy.fft below


# Aligned array allocator — avoids the ~37% pyfftw penalty on numpy arrays.
def _alloc_hat(sp: Spectral, batch: int = 3) -> np.ndarray:
    """Return a spectral-domain (batch, n, n, n//2+1) complex array, aligned
    for pyFFTW when available, otherwise plain numpy."""
    if _HAS_PYFFTW:
        return pyfftw.empty_aligned(
            (batch, sp.n, sp.n, sp.n // 2 + 1), dtype="complex128"
        )
    return np.empty((batch, sp.n, sp.n, sp.n // 2 + 1), dtype=np.complex128)


def _alloc_real(sp: Spectral, batch: int = 3) -> np.ndarray:
    """Return a real (batch, n, n, n) array, aligned for pyFFTW when
    available."""
    if _HAS_PYFFTW:
        return pyfftw.empty_aligned((batch, sp.n, sp.n, sp.n), dtype="float64")
    return np.empty((batch, sp.n, sp.n, sp.n), dtype=np.float64)


# --------------------------------------------------------------------------
# grid, wavenumbers, projector
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Spectral:
    """Wavenumber operators for a real scalar/vector field on an N^3 box."""

    n: int
    kx: np.ndarray
    ky: np.ndarray
    kz: np.ndarray
    k2: np.ndarray
    inv_k2: np.ndarray
    dealias: np.ndarray

    @property
    def shape_hat(self) -> tuple[int, int, int]:
        return (self.n, self.n, self.n // 2 + 1)


_SPECTRAL_CACHE: dict[int, Spectral] = {}


def spectral(n: int) -> Spectral:
    cached = _SPECTRAL_CACHE.get(n)
    if cached is not None:
        return cached
    if n < 4 or n % 2:
        raise ValueError("grid must be an even integer >= 4")
    kf = np.fft.fftfreq(n, d=1.0 / n)
    kr = np.fft.rfftfreq(n, d=1.0 / n)
    kx, ky, kz = np.meshgrid(kf, kf, kr, indexing="ij")
    k2 = kx * kx + ky * ky + kz * kz
    inv_k2 = np.divide(1.0, k2, out=np.zeros_like(k2), where=k2 != 0.0)
    cutoff = n / 3.0
    mask = (np.abs(kx) < cutoff) & (np.abs(ky) < cutoff) & (np.abs(kz) < cutoff)
    # ascontiguousarray: meshgrid output is not guaranteed C-contiguous, and
    # the C kernels index these as flat double arrays.
    sp = Spectral(
        n,
        np.ascontiguousarray(kx),
        np.ascontiguousarray(ky),
        np.ascontiguousarray(kz),
        np.ascontiguousarray(k2),
        np.ascontiguousarray(inv_k2),
        np.ascontiguousarray(mask.astype(np.float64)),
    )
    _SPECTRAL_CACHE[n] = sp
    return sp


def mesh(n: int) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    points = 2.0 * math.pi * np.arange(n, dtype=np.float64) / n
    return np.meshgrid(points, points, points, indexing="ij")


def forward(field: np.ndarray, overwrite: bool = False) -> np.ndarray:
    if _HAS_SCIPY_FFT:
        return _fft.rfftn(field, axes=(1, 2, 3), overwrite_x=overwrite)
    return np.fft.rfftn(field, axes=(1, 2, 3))


def inverse(field_hat: np.ndarray, n: int, overwrite: bool = False) -> np.ndarray:
    if _HAS_SCIPY_FFT:
        return _fft.irfftn(field_hat, s=(n, n, n), axes=(1, 2, 3), overwrite_x=overwrite)
    return np.fft.irfftn(field_hat, s=(n, n, n), axes=(1, 2, 3))


def leray(vector_hat: np.ndarray, sp: Spectral) -> np.ndarray:
    """Orthogonal projection onto the divergence-free subspace.

    MUTATES vector_hat in place (all callers pass a fresh array)."""
    dot = sp.kx * vector_hat[0] + sp.ky * vector_hat[1] + sp.kz * vector_hat[2]
    scale = dot * sp.inv_k2
    vector_hat[0] -= sp.kx * scale
    vector_hat[1] -= sp.ky * scale
    vector_hat[2] -= sp.kz * scale
    return vector_hat


def curl_hat(
    vector_hat: np.ndarray, sp: Spectral, out: np.ndarray | None = None
) -> np.ndarray:
    if out is None:
        out = np.empty_like(vector_hat)
    out[0] = 1j * (sp.ky * vector_hat[2] - sp.kz * vector_hat[1])
    out[1] = 1j * (sp.kz * vector_hat[0] - sp.kx * vector_hat[2])
    out[2] = 1j * (sp.kx * vector_hat[1] - sp.ky * vector_hat[0])
    return out


def divergence_linf(vector_hat: np.ndarray, sp: Spectral) -> float:
    div_hat = 1j * (
        sp.kx * vector_hat[0] + sp.ky * vector_hat[1] + sp.kz * vector_hat[2]
    )
    return float(np.max(np.abs(np.fft.irfftn(div_hat, s=(sp.n,) * 3))))


def energy(vector_hat: np.ndarray, sp: Spectral) -> float:
    """Mean kinetic energy 1/(2|D|) * integral |u|^2, from the half spectrum."""
    weight = np.ones(sp.shape_hat[2])
    weight[1 : (sp.n + 1) // 2] = 2.0
    total = float(np.sum(np.abs(vector_hat) ** 2 * weight))
    return 0.5 * total / float(sp.n**6)


def enstrophy(vector_hat: np.ndarray, sp: Spectral) -> float:
    return energy(curl_hat(vector_hat, sp), sp)


# --------------------------------------------------------------------------
# right-hand side and time advance
# --------------------------------------------------------------------------


# Per-grid scratch buffers for nonlinear_hat, allocated once and reused across
# every IFRK4 stage instead of malloc'd fresh on each of the 4 RHS calls per
# step.  Safe because each call fully overwrites and fully consumes every
# buffer before returning a *new* array (leray()/forward() output is never
# aliased to a scratch buffer) -- evolve() drives stages strictly
# sequentially, so there is never a live reader of a stale buffer.
#
# ``combo`` stacks the dealiased velocity (components 0:3) and its curl
# (components 3:6) into ONE (6, n, n, n//2+1) array so the two inverse
# transforms the original code issued separately collapse into a single
# batched ``irfftn`` call -- same total FLOPs (rfftn/irfftn already batch
# over the leading axis independently per slice), but one fewer Python/FFT
# dispatch per RHS evaluation.
_SCRATCH_CACHE: dict[int, tuple[np.ndarray, np.ndarray]] = {}


def _scratch(sp: Spectral) -> tuple[np.ndarray, np.ndarray]:
    """Return ``(combo_hat[6], cross_real[3])`` scratch buffers for grid
    ``sp.n``, aligned for pyFFTW when available."""
    cached = _SCRATCH_CACHE.get(sp.n)
    if cached is not None:
        return cached
    bufs = (_alloc_hat(sp, batch=6), _alloc_real(sp, batch=3))
    _SCRATCH_CACHE[sp.n] = bufs
    return bufs


# --------------------------------------------------------------------------
# accelerated path: pre-planned FFTW transforms + fused C pointwise kernels
# --------------------------------------------------------------------------
#
# Both accelerations are optional and independently verified.  ``navier_accel``
# refuses to enable the C library unless every kernel reproduces its numpy
# reference under ``np.array_equal``; ``_Plans`` is only built when pyFFTW is
# importable.  With neither available this module runs exactly as before.
#
# Arithmetic is bit-preserving by construction, not by tolerance.  Two places
# needed care to keep it that way and both are load-bearing:
#
#   * ``dt * (-nl)`` is replaced by folding ``scale = -dt`` into the projector
#     kernel.  IEEE multiplication is exactly sign-symmetric, so ``(-dt)*v``
#     and ``dt*(-v)`` are the same double.
#   * with forcing present the reference computes ``dt * (-nl + P_L f)``, i.e.
#     ONE multiply after the sum.  Distributing dt would re-round.  So the
#     forced path uses ``scale = -1`` and keeps the ``dt *`` outside, and only
#     the unforced path (which is what the headline TGV and inviscid-drift
#     instances use) gets the fully folded kernel.

try:
    import navier_accel as _accel
except ImportError:  # invoked from outside scripts/
    import os as _os
    import sys as _sys

    _sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
    try:
        import navier_accel as _accel  # type: ignore[no-redef]
    except ImportError:
        _accel = None  # type: ignore[assignment]

_LIB = getattr(_accel, "LIB", None) if _accel is not None else None


class _Plans:
    """Pre-planned FFTW transforms and stage buffers for one grid size.

    ``pyfftw.interfaces.scipy_fft`` rebuilds a cache key and normalises
    arguments on every call.  Measured at N=16 (best-of-200): 83 us vs 58 us
    for the batched 6-component inverse and 39 us vs 25 us for the
    3-component forward -- i.e. the wrapper cost as much as ~40% of the
    transform.  Holding the plan objects removes it.

    NOT reentrant: the buffers are shared per grid size.  ``evolve`` drives
    stages strictly sequentially and nothing else holds a reference across a
    call, which is the only invariant required.
    """

    __slots__ = (
        "hat6", "real6", "real3", "hat3", "inv", "fwd",
        "a", "b", "c", "d", "stage", "ping", "pong", "ones",
        "m", "p3", "_ptrs", "_efac", "sp",
    )

    def __init__(self, sp: Spectral) -> None:
        n = sp.n
        self.sp = sp
        self.hat6 = _alloc_hat(sp, batch=6)
        self.real6 = _alloc_real(sp, batch=6)
        self.real3 = _alloc_real(sp, batch=3)
        self.hat3 = _alloc_hat(sp, batch=3)
        # FFTW_MEASURE, not FFTW_PATIENT: patient planning costs seconds at
        # N=48 and the benchmark's whole smoke budget is ~1 s.  Wisdom is not
        # persisted across processes, so planning happens once per run.
        self.inv = pyfftw.FFTW(
            self.hat6, self.real6, axes=(1, 2, 3),
            direction="FFTW_BACKWARD",
            flags=("FFTW_MEASURE", "FFTW_DESTROY_INPUT"), threads=1,
        )
        self.fwd = pyfftw.FFTW(
            self.real3, self.hat3, axes=(1, 2, 3),
            direction="FFTW_FORWARD", flags=("FFTW_MEASURE",), threads=1,
        )
        self.a = _alloc_hat(sp)
        self.b = _alloc_hat(sp)
        self.c = _alloc_hat(sp)
        self.d = _alloc_hat(sp)
        self.stage = _alloc_hat(sp)
        self.ping = _alloc_hat(sp)
        self.pong = _alloc_hat(sp)
        self.ones = np.ones(sp.shape_hat, dtype=np.float64)
        self.m = n * n * (n // 2 + 1)
        self.p3 = n * n * n
        # ``ndarray.ctypes.data_as`` builds a fresh ctypes object on every
        # call -- measured 7.7 us each, and one RHS evaluation needs sixteen
        # of them, which is more than the transforms it wraps.  Every buffer
        # here is long-lived, so the pointers are made once.  The cache keys
        # on the buffer address and RETAINS the array, which is what keeps
        # that address valid; it is bounded and cleared if a caller streams
        # short-lived arrays through it.
        self._ptrs: dict[int, tuple[np.ndarray, object]] = {}
        self._efac: dict[tuple[float, float], tuple[np.ndarray, np.ndarray]] = {}
        for buf in (
            sp.kx, sp.ky, sp.kz, sp.k2, sp.inv_k2, sp.dealias, self.ones,
            self.hat6, self.real6, self.real3, self.hat3,
            self.a, self.b, self.c, self.d, self.stage, self.ping, self.pong,
        ):
            self.ptr(buf)
        del n

    def ptr(self, array: np.ndarray):
        """Cached ``double *`` for ``array``."""
        key = array.ctypes.data
        hit = self._ptrs.get(key)
        if hit is not None and hit[0] is array:
            return hit[1]
        if len(self._ptrs) > 128:
            self._ptrs.clear()
        made = _accel.ptr(array)
        self._ptrs[key] = (array, made)
        return made

    def factors(self, viscosity: float, dt: float) -> tuple[np.ndarray, np.ndarray]:
        """Cached ``(exp(-nu k^2 dt), exp(-nu k^2 dt/2))`` for this grid.

        ``evolve`` is called repeatedly at the same (nu, dt) by the
        convergence study, and these are also pointer-cache entries, so
        recomputing them each time would both cost two ``np.exp`` passes and
        churn the pointer cache."""
        key = (viscosity, dt)
        hit = self._efac.get(key)
        if hit is None:
            k2 = self.sp.k2
            full = np.ascontiguousarray(np.exp(-viscosity * k2 * dt))
            half = np.ascontiguousarray(np.exp(-viscosity * k2 * 0.5 * dt))
            self.ptr(full)
            self.ptr(half)
            hit = self._efac[key] = (full, half)
        return hit


_PLAN_CACHE: dict[int, "_Plans"] = {}


def _plans(sp: Spectral) -> "_Plans":
    cached = _PLAN_CACHE.get(sp.n)
    if cached is None:
        cached = _Plans(sp)
        _PLAN_CACHE[sp.n] = cached
    return cached


def _fast_available() -> bool:
    return _LIB is not None and _HAS_PYFFTW


def _p(array: np.ndarray):
    return _accel.ptr(array)


def _nl_into(
    vector_hat: np.ndarray,
    sp: Spectral,
    dealias: bool,
    scale: float,
    out: np.ndarray,
) -> np.ndarray:
    """``out = scale * P_L[(omega x u)_hat]`` with no Python-level temporaries.

    Identical arithmetic to :func:`nonlinear_hat` followed by a scalar
    multiply; see the module note above for why the scale is folded in.
    """
    pl = _plans(sp)
    q = pl.ptr
    mask = sp.dealias if dealias else pl.ones
    _LIB.navier_pre_transform(
        q(vector_hat), q(sp.kx), q(sp.ky), q(sp.kz), q(mask), q(pl.hat6), pl.m,
    )
    pl.inv()
    _LIB.navier_cross(q(pl.real6), q(pl.real3), pl.p3)
    pl.fwd()
    _LIB.navier_post_leray(
        q(pl.hat3), q(sp.kx), q(sp.ky), q(sp.kz), q(sp.inv_k2), q(sp.dealias),
        scale, 1 if dealias else 0, q(out), pl.m,
    )
    return out


def nonlinear_hat(vector_hat: np.ndarray, sp: Spectral, dealias: bool) -> np.ndarray:
    """Projected rotational nonlinearity ``P_L[(omega x u)_hat]``.

    Uses preallocated, aligned scratch buffers so the four RHS evaluations
    per IFRK4 step reuse the same memory instead of allocating fresh arrays
    every call, and stacks the dealiased velocity and its curl into one
    6-component buffer so they transform to physical space in a SINGLE
    batched inverse FFT rather than two separate calls (the forward/inverse
    wrappers already batch over the leading axis per-slice, so stacking is
    numerically identical to two independent transforms -- it only removes
    a redundant Python/FFT dispatch). Components are written in-place to
    skip ``np.stack``.
    """
    combo, cross = _scratch(sp)
    work = combo[:3]
    curl_buf = combo[3:]
    if dealias:
        np.multiply(vector_hat, sp.dealias, out=work)
    else:
        work[...] = vector_hat
    curl_hat(work, sp, out=curl_buf)
    uw = inverse(combo, sp.n, overwrite=True)  # combo is scratch, safe to consume
    u = uw[:3]
    w = uw[3:]
    cross[0] = w[1] * u[2] - w[2] * u[1]
    cross[1] = w[2] * u[0] - w[0] * u[2]
    cross[2] = w[0] * u[1] - w[1] * u[0]
    cross_hat = forward(cross, overwrite=True)  # cross is scratch, safe to consume
    if dealias:
        cross_hat *= sp.dealias
    return leray(cross_hat, sp)


def step_ifrk4(
    vector_hat: np.ndarray,
    sp: Spectral,
    viscosity: float,
    dt: float,
    dealias: bool,
    forcing=None,
    time: float = 0.0,
    e_full: np.ndarray | None = None,
    e_half: np.ndarray | None = None,
    out: np.ndarray | None = None,
) -> np.ndarray:
    """One integrating-factor RK4 step of the projected momentum equation.

    Precomputed ``e_full = exp(-viscosity * k2 * dt)`` and
    ``e_half = exp(-viscosity * k2 * 0.5 * dt)`` can be passed to avoid
    recomputing the exponentials on every call (the ``evolve`` loop does this).
    """
    if e_full is None:
        e_full = np.exp(-viscosity * sp.k2 * dt)
    if e_half is None:
        e_half = np.exp(-viscosity * sp.k2 * 0.5 * dt)

    if _fast_available() and vector_hat.flags["C_CONTIGUOUS"]:
        return _step_ifrk4_fast(
            vector_hat, sp, dt, dealias, forcing, time, e_full, e_half, out
        )

    def rhs(v_hat: np.ndarray, t: float) -> np.ndarray:
        result = -nonlinear_hat(v_hat, sp, dealias)
        if forcing is not None:
            result = result + leray(forcing(t), sp)
        return result

    a = dt * rhs(vector_hat, time)
    b = dt * rhs(e_half * (vector_hat + 0.5 * a), time + 0.5 * dt)
    c = dt * rhs(e_half * vector_hat + 0.5 * b, time + 0.5 * dt)
    d = dt * rhs(e_full * vector_hat + e_half * c, time + dt)
    result = e_full * vector_hat + (e_full * a + 2.0 * e_half * (b + c) + d) / 6.0
    if out is not None:
        out[...] = result
        return out
    return result


def _step_ifrk4_fast(
    vector_hat: np.ndarray,
    sp: Spectral,
    dt: float,
    dealias: bool,
    forcing,
    time: float,
    e_full: np.ndarray,
    e_half: np.ndarray,
    out: np.ndarray | None,
) -> np.ndarray:
    """IFRK4 step with the fused kernels.  Bit-identical to the numpy branch.

    Six C calls and four planned transforms per step replace ~150 numpy
    dispatches.  Every stage writes into a preallocated per-grid buffer, so a
    whole ``evolve`` loop allocates nothing after the first step.
    """
    pl = _plans(sp)
    q = pl.ptr
    m = pl.m
    half = 0.5 * dt

    # scale folded into the projector when unforced; see module note.
    scale = -1.0 if forcing is not None else -dt

    def stage(v_hat: np.ndarray, t: float, dest: np.ndarray) -> np.ndarray:
        _nl_into(v_hat, sp, dealias, scale, dest)
        if forcing is not None:
            # reference order: dt * (-nl + P_L f), one multiply after the sum
            np.add(dest, leray(forcing(t), sp), out=dest)
            np.multiply(dest, dt, out=dest)
        return dest

    pv, pef, peh = q(vector_hat), q(e_full), q(e_half)
    a = stage(vector_hat, time, pl.a)
    _LIB.navier_stage2(pv, q(a), peh, q(pl.stage), m)
    b = stage(pl.stage, time + half, pl.b)
    _LIB.navier_stage3(pv, q(b), peh, q(pl.stage), m)
    c = stage(pl.stage, time + half, pl.c)
    _LIB.navier_stage4(pv, q(c), pef, peh, q(pl.stage), m)
    d = stage(pl.stage, time + dt, pl.d)

    if out is None:
        out = np.empty_like(vector_hat)
    _LIB.navier_combine(
        pv, q(a), q(b), q(c), q(d), pef, peh, q(out), m,
    )
    return out


def evolve(
    vector_hat: np.ndarray,
    sp: Spectral,
    viscosity: float,
    dt: float,
    steps: int,
    dealias: bool = True,
    forcing=None,
    t0: float = 0.0,
) -> np.ndarray:
    state = np.ascontiguousarray(vector_hat)

    if _fast_available():
        # Ping-pong between two preallocated buffers so the whole time loop
        # allocates nothing; only the escaping final state is copied out.
        pl = _plans(sp)
        e_full, e_half = pl.factors(viscosity, dt)
        pl.ping[...] = state
        src, dst = pl.ping, pl.pong
        for index in range(steps):
            step_ifrk4(
                src, sp, viscosity, dt, dealias, forcing, t0 + index * dt,
                e_full, e_half, out=dst,
            )
            src, dst = dst, src
        return src.copy()

    e_full = np.exp(-viscosity * sp.k2 * dt)
    e_half = np.exp(-viscosity * sp.k2 * 0.5 * dt)
    state = state.copy()
    for index in range(steps):
        state = step_ifrk4(
            state, sp, viscosity, dt, dealias, forcing, t0 + index * dt,
            e_full, e_half,
        )
    return state


# --------------------------------------------------------------------------
# initial conditions
# --------------------------------------------------------------------------


def abc_field(n: int, a: float = 1.0, b: float = 1.0, c: float = 1.0) -> np.ndarray:
    """Arnold--Beltrami--Childress flow.  For a=b=c this satisfies curl u = u."""
    x, y, z = mesh(n)
    return np.stack(
        (
            a * np.sin(z) + c * np.cos(y),
            b * np.sin(x) + a * np.cos(z),
            c * np.sin(y) + b * np.cos(x),
        )
    )


def taylor_green_field(n: int) -> np.ndarray:
    """Taylor--Green vortex.  Divergence-free, and NOT a Beltrami field, so its
    projected nonlinearity is O(1) rather than zero."""
    x, y, z = mesh(n)
    return np.stack(
        (
            np.sin(x) * np.cos(y) * np.cos(z),
            -np.cos(x) * np.sin(y) * np.cos(z),
            np.zeros_like(x),
        )
    )


# --------------------------------------------------------------------------
# manufactured solution with live nonlinearity
# --------------------------------------------------------------------------


def mms_amplitude(t: float) -> float:
    return math.exp(-0.3 * t) * math.cos(1.7 * t)


def mms_amplitude_dot(t: float) -> float:
    return math.exp(-0.3 * t) * (
        -0.3 * math.cos(1.7 * t) - 1.7 * math.sin(1.7 * t)
    )


def mms_problem(sp: Spectral, viscosity: float, dealias: bool = True):
    """Method of manufactured solutions on a live-nonlinearity carrier.

    The target ``u*(x, t) = s(t) v(x)`` uses the Taylor--Green field ``v``, whose
    projected nonlinearity is O(1).  Substituting ``u*`` into the projected
    momentum equation defines the forcing that makes it an exact solution::

        f_hat(t) = s'(t) v_hat + s(t)^2 * P_L[(curl v x v)_hat]
                   + nu |k|^2 s(t) v_hat

    Because ``P_L[(curl v x v)]`` is evaluated with the same discrete operator
    the solver uses, the spatial discretization is exact and the residual error
    is purely temporal.  That isolates the time integrator's convergence order.
    """
    base = taylor_green_field(sp.n)
    base_hat = leray(forward(base), sp)
    nl_hat = nonlinear_hat(base_hat, sp, dealias)
    visc_hat = viscosity * sp.k2 * base_hat

    def exact_hat(t: float) -> np.ndarray:
        return mms_amplitude(t) * base_hat

    def forcing(t: float) -> np.ndarray:
        s = mms_amplitude(t)
        return mms_amplitude_dot(t) * base_hat + s * s * nl_hat + s * visc_hat

    return base_hat, exact_hat, forcing


def relative_l2(state_hat: np.ndarray, reference_hat: np.ndarray, sp: Spectral) -> float:
    numerator = inverse(state_hat - reference_hat, sp.n)
    denominator = inverse(reference_hat, sp.n)
    denom = float(np.linalg.norm(denominator.ravel()))
    if denom == 0.0:
        return float("nan")
    return float(np.linalg.norm(numerator.ravel()) / denom)
