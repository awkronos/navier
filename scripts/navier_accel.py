#!/usr/bin/env python3
"""Optional acceleration layer for the pseudo-spectral Navier--Stokes core.

Two independent accelerations, each of which degrades to the plain numpy /
``scipy.fft`` path without changing a single reported number:

1.  **Fused C pointwise kernels** (``navier_kernels.c``).  At N = 16..48 one
    spectral component is 2.3k-56k complex entries, so the solver is
    interpreter-dispatch bound, not flop bound: one IFRK4 step issued ~150
    numpy calls for ~50k flops of pointwise work.  The C loops collapse the
    dealias / curl / cross-product / Leray / RK4-assembly chain into six
    calls per step.

2.  **Pre-planned pyFFTW transforms.**  ``pyfftw.interfaces.scipy_fft``
    rebuilds a cache key and normalises arguments on every call, which at
    these transform sizes costs as much as the transform: measured 83 us vs
    58 us for a batched 6-component N=16 inverse, and 39 us vs 25 us for a
    3-component forward.  Holding ``pyfftw.FFTW`` plan objects on fixed
    aligned buffers removes that.

Both are verified against the reference numpy implementation at import time
(:func:`self_check`) and disabled on any disagreement, so a wrong or
unbuildable accelerator can only cost speed, never correctness.

The shared object is built into a per-user cache directory keyed by the
hash of the C source -- never into the repository -- so the solver's working
tree stays clean under the registry's ``dirty_tree_policy: refuse``.
"""

from __future__ import annotations

import ctypes
import hashlib
import os
import subprocess
import sys
import tempfile

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
_CSOURCE = os.path.join(_HERE, "navier_kernels.c")

# Set to "0" to force the pure-numpy reference path (used by the equivalence
# test and available as an escape hatch if a toolchain ever miscompiles).
_ENABLED = os.environ.get("NAVIER_ACCEL", "1") != "0"

LIB = None
BUILD_STATUS = "disabled"


def _cache_dir() -> str:
    root = os.environ.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache")
    return os.path.join(root, "navier-spectral")


def _build() -> tuple[object | None, str]:
    """Compile ``navier_kernels.c`` into a cached shared object and load it.

    Returns ``(handle_or_None, status_string)``.  Never raises: every failure
    path falls back to numpy.
    """
    if not _ENABLED:
        return None, "disabled_by_env"
    try:
        with open(_CSOURCE, "rb") as handle:
            source = handle.read()
    except OSError as exc:
        return None, f"source_missing:{exc.__class__.__name__}"

    cc = os.environ.get("CC") or "cc"
    digest = hashlib.sha256(
        source + cc.encode() + sys.platform.encode()
    ).hexdigest()[:16]
    suffix = ".dylib" if sys.platform == "darwin" else ".so"
    outdir = _cache_dir()
    target = os.path.join(outdir, f"navier_kernels-{digest}{suffix}")

    if not os.path.exists(target):
        try:
            os.makedirs(outdir, exist_ok=True)
            # -O3 -ffp-contract=off: full optimisation, but NO fused
            # multiply-add contraction and no fast-math, so every expression
            # keeps the exact IEEE-754 rounding the numpy path produces.
            flags = [
                "-O3",
                "-fPIC",
                "-shared",
                "-std=c11",
                "-ffp-contract=off",
                "-fno-fast-math",
            ]
            # Build to a temporary name in the same directory, then rename, so
            # two concurrent bench processes can never load a half-written file.
            fd, tmp = tempfile.mkstemp(dir=outdir, suffix=suffix)
            os.close(fd)
            proc = subprocess.run(
                [cc, *flags, _CSOURCE, "-o", tmp],
                capture_output=True,
                timeout=120,
            )
            if proc.returncode != 0:
                os.unlink(tmp)
                return None, "compile_failed"
            os.replace(tmp, target)
        except Exception as exc:  # noqa: BLE001 - any failure means fallback
            return None, f"build_error:{exc.__class__.__name__}"

    try:
        lib = ctypes.CDLL(target)
    except OSError:
        return None, "load_failed"

    d = ctypes.POINTER(ctypes.c_double)
    z = ctypes.c_size_t
    f = ctypes.c_double
    lib.navier_pre_transform.argtypes = [d, d, d, d, d, d, z]
    lib.navier_pre_transform.restype = None
    lib.navier_cross.argtypes = [d, d, z]
    lib.navier_cross.restype = None
    lib.navier_post_leray.argtypes = [d, d, d, d, d, d, f, ctypes.c_int, d, z]
    lib.navier_post_leray.restype = None
    lib.navier_stage2.argtypes = [d, d, d, d, z]
    lib.navier_stage2.restype = None
    lib.navier_stage3.argtypes = [d, d, d, d, z]
    lib.navier_stage3.restype = None
    lib.navier_stage4.argtypes = [d, d, d, d, d, z]
    lib.navier_stage4.restype = None
    lib.navier_combine.argtypes = [d, d, d, d, d, d, d, d, z]
    lib.navier_combine.restype = None
    lib.navier_axpy.argtypes = [d, d, f, d, z]
    lib.navier_axpy.restype = None
    for name in (
        "navier_pre_transform",
        "navier_cross",
        "navier_post_leray",
        "navier_stage2",
        "navier_stage3",
        "navier_stage4",
        "navier_combine",
        "navier_axpy",
    ):
        getattr(lib, name)  # raises AttributeError if a symbol is missing
    return lib, "ok"


def ptr(array: np.ndarray):
    """C ``double *`` view of a C-contiguous float64/complex128 array."""
    return array.ctypes.data_as(ctypes.POINTER(ctypes.c_double))


def self_check() -> tuple[bool, str]:
    """Verify every C kernel against its numpy reference on random data.

    Uses ``array_equal`` -- BIT equality, not a tolerance.  The C code is a
    reformulation with identical operation order, so anything short of exact
    agreement means the accelerator changed the arithmetic and must not run.
    """
    if LIB is None:
        return False, BUILD_STATUS
    rng = np.random.default_rng(20260831)
    n, mz = 8, 5
    m = n * n * mz
    p = n * n * n

    def rc(shape):
        return np.ascontiguousarray(
            rng.standard_normal(shape) + 1j * rng.standard_normal(shape)
        )

    def rr(shape):
        return np.ascontiguousarray(rng.standard_normal(shape))

    kx, ky, kz = rr((n, n, mz)), rr((n, n, mz)), rr((n, n, mz))
    inv_k2, deal = rr((n, n, mz)) ** 2, rng.integers(0, 2, (n, n, mz)).astype(float)
    deal = np.ascontiguousarray(deal)
    inv_k2 = np.ascontiguousarray(inv_k2)
    vhat = rc((3, n, n, mz))

    # 1. pre_transform
    got = np.empty((6, n, n, mz), dtype=np.complex128)
    LIB.navier_pre_transform(
        ptr(vhat), ptr(kx), ptr(ky), ptr(kz), ptr(deal), ptr(got), m
    )
    w = vhat * deal
    ref = np.concatenate(
        [
            w,
            np.stack(
                [
                    1j * (ky * w[2] - kz * w[1]),
                    1j * (kz * w[0] - kx * w[2]),
                    1j * (kx * w[1] - ky * w[0]),
                ]
            ),
        ]
    )
    if not np.array_equal(got, ref):
        return False, "mismatch:pre_transform"

    # 2. cross
    uw = rr((6, n, n, n))
    gotc = np.empty((3, n, n, n))
    LIB.navier_cross(ptr(uw), ptr(gotc), p)
    u, g = uw[:3], uw[3:]
    refc = np.stack(
        [
            g[1] * u[2] - g[2] * u[1],
            g[2] * u[0] - g[0] * u[2],
            g[0] * u[1] - g[1] * u[0],
        ]
    )
    if not np.array_equal(gotc, refc):
        return False, "mismatch:cross"

    # 3. post_leray (with and without dealiasing, and with a scale)
    chat = rc((3, n, n, mz))
    for apply_d, scale in ((1, -0.25), (0, 1.0)):
        gotp = np.empty((3, n, n, mz), dtype=np.complex128)
        LIB.navier_post_leray(
            ptr(chat), ptr(kx), ptr(ky), ptr(kz), ptr(inv_k2), ptr(deal),
            ctypes.c_double(scale), ctypes.c_int(apply_d), ptr(gotp), m,
        )
        x = chat * deal if apply_d else chat.copy()
        s = (kx * x[0] + ky * x[1] + kz * x[2]) * inv_k2
        refp = scale * np.stack([x[0] - kx * s, x[1] - ky * s, x[2] - kz * s])
        if not np.array_equal(gotp, refp):
            return False, f"mismatch:post_leray:d={apply_d}"

    # 4. RK4 stage assembly
    a, b, c, dd = rc((3, n, n, mz)), rc((3, n, n, mz)), rc((3, n, n, mz)), rc((3, n, n, mz))
    ef, eh = rr((n, n, mz)), rr((n, n, mz))
    out = np.empty((3, n, n, mz), dtype=np.complex128)

    LIB.navier_stage2(ptr(vhat), ptr(a), ptr(eh), ptr(out), m)
    if not np.array_equal(out, eh * (vhat + 0.5 * a)):
        return False, "mismatch:stage2"
    LIB.navier_stage3(ptr(vhat), ptr(b), ptr(eh), ptr(out), m)
    if not np.array_equal(out, eh * vhat + 0.5 * b):
        return False, "mismatch:stage3"
    LIB.navier_stage4(ptr(vhat), ptr(c), ptr(ef), ptr(eh), ptr(out), m)
    if not np.array_equal(out, ef * vhat + eh * c):
        return False, "mismatch:stage4"
    LIB.navier_combine(
        ptr(vhat), ptr(a), ptr(b), ptr(c), ptr(dd), ptr(ef), ptr(eh), ptr(out), m
    )
    ref4 = ef * vhat + (ef * a + 2.0 * eh * (b + c) + dd) / 6.0
    if not np.array_equal(out, ref4):
        return False, "mismatch:combine"

    LIB.navier_axpy(ptr(a), ptr(b), ctypes.c_double(0.125), ptr(out), 6 * m)
    if not np.array_equal(out, a + 0.125 * b):
        return False, "mismatch:axpy"

    return True, "ok"


LIB, BUILD_STATUS = _build()
if LIB is not None:
    _passed, _why = self_check()
    if not _passed:
        LIB, BUILD_STATUS = None, _why


def status() -> str:
    return BUILD_STATUS


if __name__ == "__main__":
    print(f"navier_accel: {BUILD_STATUS}")
    raise SystemExit(0 if LIB is not None else 1)
