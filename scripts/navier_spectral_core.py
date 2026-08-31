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
    sp = Spectral(n, kx, ky, kz, k2, inv_k2, mask.astype(np.float64))
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

    def rhs(v_hat: np.ndarray, t: float) -> np.ndarray:
        out = -nonlinear_hat(v_hat, sp, dealias)
        if forcing is not None:
            out = out + leray(forcing(t), sp)
        return out

    a = dt * rhs(vector_hat, time)
    b = dt * rhs(e_half * (vector_hat + 0.5 * a), time + 0.5 * dt)
    c = dt * rhs(e_half * vector_hat + 0.5 * b, time + 0.5 * dt)
    d = dt * rhs(e_full * vector_hat + e_half * c, time + dt)
    return e_full * vector_hat + (e_full * a + 2.0 * e_half * (b + c) + d) / 6.0


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
    e_full = np.exp(-viscosity * sp.k2 * dt)
    e_half = np.exp(-viscosity * sp.k2 * 0.5 * dt)
    state = vector_hat.copy()
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
