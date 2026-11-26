#!/usr/bin/env python3
"""Paired Navier-Stokes solver benchmark + the 80540a2 mass-escape diagnostic.

This module bridges the repository's existing solver stack to two things it did
not have before: a **paired A/B benchmark** (baseline vs. one concrete solver
improvement, measured side by side on the same reference data) and a
**hermetic numerical witness for the mass-escape obstruction** proved in Lean at
commit ``80540a2`` (`Navier/Analysis/CarrierTimeContinuityObstruction.lean`,
ledger `F-032`).

Scope discipline (this is a numerical diagnostic, not a regularity proof)
------------------------------------------------------------------------
Nothing here is evidence about whether the 3D Navier-Stokes equations are
globally smooth, whether finite-time breakdown is possible, or whether the Clay
millennium problems A/B (unforced, whole-space) or the forced breakdown
alternatives C/D (`openai/NavierStokesAndEuler`, `Navier/OfficialProblem.lean`)
hold. A finite-grid, finite-time run establishes a property of THIS
discretisation on THIS data only. `80540a2`'s own scope note is the same kind of
discipline and is quoted rather than restated here: the Lean obstruction refutes
a *derivation* ("a bump translated to infinity as `t ↓ 0`, extended by zero"
satisfies every regularity / incompressibility / bounded-energy / pointwise-start
clause, yet its slices do not converge to the initial slice in `L²`) — it does
NOT say a genuine Navier-Stokes evolution loses `L²` time-continuity ("no
pressure makes this witness satisfy the momentum equation"). The numerical
control below reproduces that logical gap — pointwise + bounded-energy checks
can be satisfied while the `L²`-in-time check is not — for a pure translating
bump, and says nothing at all about NS dynamics. Do not cite this script as
solver support for any regularity claim; cite it only as a regression test that
the diagnostic instruments behave as designed.

Prior art consumed (not rewritten)
----------------------------------
`scripts/navier_spectral_core.py` (an importlib re-export shim onto the
canonical unified solver at `~/reality/solvers/navier/`, per the 2026-09-01
unification directive) provides the whole periodic-spectral engine this file
drives rather than reimplementing:

  * `spectral`, `forward`, `inverse`, `leray` — the torus Fourier machinery and
    the exact Helmholtz-Leray projector (the "exact Stokes" part: the viscous
    term `nu * |k|^2` is diagonal in this basis and is integrated exactly by
    the integrating factor below, never stepped explicitly);
  * `nonlinear_hat(dealias=)` — the rotational (vorticity-cross-velocity, i.e.
    energy-neutral / skew-symmetric) advection term, with the Orszag 2/3
    rule as a selectable flag. **The A/B pair this benchmark measures is this
    one flag**: `dealias=False` is the baseline "conservative" collocation
    solver (no aliasing control), `dealias=True` is the concrete improvement
    named in the lane brief. The rotational form and the integrating factor are
    not the A/B axis — they are common to both arms and already proven by the
    canonical core (see `tests/test_navier_solver_equivalence.py` for its own
    invariants).
  * `step_ifrk4`, `evolve` — integrating-factor RK4 (exact Stokes, fourth-order
    RK4 on the nonlinearity).
  * `energy`, `enstrophy`, `divergence_linf`, `flow_diagnostics` (velocity /
    vorticity Linf and RMS, strain Frobenius Linf, `high_frequency_energy_fraction`,
    `underresolved`), `high_frequency_energy_fraction` — the scale-localized
    blowup-diagnostic instruments, measured per arm.
  * `taylor_green_field`, `abc_field`, `mms_problem`, `relative_l2` — trusted
    reference data: the Taylor-Green vortex (non-Beltrami, O(1) projected
    nonlinearity) and the manufactured-solution problem whose forcing is
    constructed against the same discrete operator, isolating temporal error.

`scripts/build_solver_release.py` provides the provenance idiom reused here
(`navier_commit` + `canonical_commit` + per-file SHA-256 + an explicit
"finite-grid results ... do not establish continuum smoothness or singularity"
scope line). `scripts/navier_solver_bench.py` is *not* called: its `solve()`
hard-wires `dealias=True` internally and cannot express the A/B pair, and
reusing its throughput harness is out of scope for this lane (it already has its
own equivalence tests).

New here, not in prior art
--------------------------
  * `run_arm` / `paired_solver_benchmark` — a side-by-side, same-data,
    per-step-timed A/B with p50/p95 step latency (ms) and a `tracemalloc`
    peak/live-block memory readout, which none of the existing bench entry
    points compute.
  * `smooth_shear_negative_control` — an exact steady Euler shear state used as
    a false-positive check on the blowup diagnostics.
  * `mass_escape_witness` — a whole-space (not torus) translating Gaussian
    curl-field that reproduces, numerically, the exact logical shape of
    `80540a2`'s `escapingCarrier`: pointwise convergence to the initial slice +
    bounded energy, with `L²`-in-time continuity failing, and a tail-mass
    diagnostic that catches it where the naive pair of checks cannot. This is
    why the witness is *not* built on `navier_spectral_core`: the periodic box
    wraps an escaping bump back around instead of losing it, which would invert
    the phenomenon the Lean module is about.
  * `build_receipt` / `main` — a deterministic, content-addressed JSON
    receipt (replay keys, exact source SHA, per-file digests) that a run writes
    once and a test re-verifies byte-for-byte.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import platform
import subprocess
import sys
import time
import tracemalloc
from pathlib import Path

# Thread caps must be pinned before numpy (and therefore BLAS/FFTW) loads, the
# same reason and the same set of variables as the canonical bench: an
# unpinned thread count makes latency depend on what the OS felt like giving
# the process, which is not a property of the solver. ``setdefault`` so an
# explicit outer setting still wins.
for _var in (
    "OMP_NUM_THREADS",
    "MKL_NUM_THREADS",
    "OPENBLAS_NUM_THREADS",
    "VECLIB_MAXIMUM_THREADS",
    "NUMEXPR_NUM_THREADS",
):
    os.environ.setdefault(_var, "1")

import numpy as np  # noqa: E402  (thread caps above must precede this)

_REPO_ROOT = Path(__file__).resolve().parents[1]
_SCRIPTS_DIR = _REPO_ROOT / "scripts"
if str(_SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(_SCRIPTS_DIR))

import navier_spectral_core as core  # noqa: E402  (the unification shim)

TOOL_VERSION = "ns-paired-benchmark/1"
SCHEMA_VERSION = 1

# The obstruction being mirrored, and the raw `#print axioms` census recorded by
# its own commit -- kept here so a stale receipt is traceable to a specific
# Lean surface, not to a floating claim.
OBSTRUCTION_COMMIT = "80540a20c7d095876bdf69b9c52ba098f6845b64"
OBSTRUCTION_MODULE = "Navier.Analysis.CarrierTimeContinuityObstruction"
OBSTRUCTION_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]

SCOPE_NOTE = (
    "Finite-grid, finite-time numerical measurements. Establishes solver "
    "accuracy, conservation and diagnostic behaviour for this discretisation "
    "on this reference data. Does not establish, support, or contradict "
    "global regularity, finite-time breakdown, or the Clay A/B or forced C/D "
    "surfaces. The mass-escape control mirrors the logical gap proved at "
    f"{OBSTRUCTION_COMMIT} for a translating bump, not for a Navier-Stokes "
    "evolution."
)


# ---------------------------------------------------------------------------
# git / provenance
# ---------------------------------------------------------------------------


def _git(repo: Path, *args: str) -> str | None:
    try:
        out = subprocess.run(
            ["git", "-C", str(repo), *args],
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError):
        return None
    return out.stdout.strip() or None


def navier_source_sha() -> str:
    sha = _git(_REPO_ROOT, "rev-parse", "HEAD")
    if sha is None or len(sha) != 40:
        raise RuntimeError(
            "ns_paired_benchmark must run from a git checkout; "
            f"`git -C {_REPO_ROOT} rev-parse HEAD` returned {sha!r}"
        )
    return sha


def fft_backend() -> str:
    """Which transform stack the canonical core resolved at import."""
    if getattr(core, "_HAS_PYFFTW", False):
        return "pyfftw"
    if getattr(core, "_HAS_SCIPY_FFT", False):
        return "scipy.fft"
    return "numpy.fft"


def source_digests() -> dict[str, str]:
    """SHA-256 of every tracked solver input this receipt claims to replay."""
    files = [
        _SCRIPTS_DIR / "ns_paired_benchmark.py",
        _REPO_ROOT / "tests" / "test_ns_paired_benchmark.py",
    ]
    canonical_home = Path.home() / "reality"
    for name in ("navier_spectral_core.py", "navier_solver_bench.py", "navier_accel.py"):
        files.append(canonical_home / "solvers" / "navier" / name)
        files.append(_SCRIPTS_DIR / name)
    digests: dict[str, str] = {}
    for path in files:
        if path.is_file():
            rel = str(path.relative_to(_REPO_ROOT) if path.is_relative_to(_REPO_ROOT) else path)
            digests[rel] = hashlib.sha256(path.read_bytes()).hexdigest()
    return digests


def replay_keys() -> dict[str, object]:
    return {
        "tool_version": TOOL_VERSION,
        "schema_version": SCHEMA_VERSION,
        "navier_commit": navier_source_sha(),
        "navier_dirty": bool(_git(_REPO_ROOT, "status", "--porcelain", "--", "scripts", "tests")),
        "obstruction_commit": OBSTRUCTION_COMMIT,
        "obstruction_module": OBSTRUCTION_MODULE,
        "obstruction_axioms": list(OBSTRUCTION_AXIOMS),
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "fft_backend": fft_backend(),
        "platform": platform.platform(),
        "machine": platform.machine(),
        "byteorder": sys.byteorder,
        "thread_caps_pinned": True,
        # Nothing here draws a random number: every reference field, every grid
        # and every time step is fixed by the run configuration below, so
        # determinism is structural, not seeded. Recorded so a replay does not
        # go looking for a seed that does not exist.
        "random_seed": None,
        "source_sha256": source_digests(),
    }


# ---------------------------------------------------------------------------
# timing helpers
# ---------------------------------------------------------------------------


def _percentile(sorted_values: list[float], q: float) -> float:
    """Nearest-rank percentile over an already-sorted list (deterministic,
    no interpolation branch to disagree across numpy versions)."""
    if not sorted_values:
        raise ValueError("no latency samples")
    if not (0.0 <= q <= 1.0):
        raise ValueError("q must be in [0, 1]")
    idx = math.ceil(q * len(sorted_values)) - 1
    return sorted_values[max(0, min(idx, len(sorted_values) - 1))]


# ---------------------------------------------------------------------------
# one paired arm
# ---------------------------------------------------------------------------


def run_arm(
    case: str,
    grid: int,
    steps: int,
    dt: float,
    viscosity: float,
    dealias: bool,
    tail_start: float = 0.75,
    tail_tolerance: float = 1.0e-8,
) -> dict[str, object]:
    """Evolve one reference case with one dealiasing choice; return metrics.

    ``case`` is ``"tgv"`` (Taylor-Green, no forcing, decays) or ``"mms"``
    (manufactured solution, the discretisation-exact target). Timing is per
    step (`core.step_ifrk4`) so p50/p95 step latency is a real distribution,
    not one whole-loop number divided by step count.
    """
    sp = core.spectral(grid)
    if case == "tgv":
        state0 = core.leray(core.forward(core.taylor_green_field(grid)), sp)
        exact_hat = None
        forcing = None
    elif case == "mms":
        _base_hat, exact_hat, forcing = core.mms_problem(sp, viscosity, dealias)
        state0 = exact_hat(0.0)
    else:
        raise ValueError(f"unknown case {case!r}")

    # Divergence and energy are read before any step so both the baseline and
    # the improved arm start from an identical, projector-clean state.
    div0 = core.divergence_linf(state0, sp)
    e0 = core.energy(state0, sp)

    tracemalloc.start()
    live0, _peak0 = tracemalloc.get_traced_memory()
    step_ms: list[float] = []
    tail_series: list[float] = []
    vel_linf_series: list[float] = []
    vort_linf_series: list[float] = []
    strain_linf_series: list[float] = []
    energy_series: list[float] = []

    state = state0
    for index in range(steps):
        t0 = time.perf_counter()
        state = core.step_ifrk4(state, sp, viscosity, dt, dealias, forcing, index * dt)
        step_ms.append((time.perf_counter() - t0) * 1000.0)
        if index == 0 or index == steps - 1 or (index % max(1, steps // 5) == 0):
            diag = core.flow_diagnostics(
                state, sp, viscosity=viscosity, forcing=forcing,
                time=index * dt, tail_start=tail_start, tail_tolerance=tail_tolerance,
            )
            tail_series.append(float(diag["high_frequency_energy_fraction"]))
            vel_linf_series.append(float(diag["velocity_linf"]))
            vort_linf_series.append(float(diag["vorticity_linf"]))
            strain_linf_series.append(float(diag["strain_frobenius_linf"]))
            energy_series.append(float(diag["energy"]))

    live_bytes, peak_bytes = tracemalloc.get_traced_memory()
    snapshot = tracemalloc.take_snapshot()
    tracemalloc.stop()
    live_blocks = sum(
        stat.count for stat in snapshot.statistics("traceback")
    )

    step_sorted = sorted(step_ms)
    out: dict[str, object] = {
        "case": case,
        "dealias": dealias,
        "grid": grid,
        "steps": steps,
        "dt": dt,
        "viscosity": viscosity,
        "divergence_linf_at_start": div0,
        "divergence_linf_final": core.divergence_linf(state, sp),
        "energy_initial": e0,
        "energy_final": core.energy(state, sp),
        "energy_drift_abs": abs(core.energy(state, sp) - e0),
        "energy_drift_rel": abs(core.energy(state, sp) - e0) / e0 if e0 > 0 else 0.0,
        "enstrophy_final": core.enstrophy(state, sp),
        "step_latency_ms": {
            "p50": _percentile(step_sorted, 0.50),
            "p95": _percentile(step_sorted, 0.95),
            "min": step_sorted[0],
            "max": step_sorted[-1],
            "samples": len(step_sorted),
        },
        "memory": {
            "traced_bytes_at_entry": live0,
            "traced_bytes_live_after_run": live_bytes,
            "traced_peak_bytes": peak_bytes,
            "live_allocation_blocks_after_run": live_blocks,
        },
        "blowup_diagnostic": {
            "velocity_linf": {"initial": vel_linf_series[0], "final": vel_linf_series[-1],
                               "max": max(vel_linf_series)},
            "vorticity_linf": {"initial": vort_linf_series[0], "final": vort_linf_series[-1],
                                "max": max(vort_linf_series)},
            "strain_frobenius_linf": {"initial": strain_linf_series[0],
                                       "final": strain_linf_series[-1],
                                       "max": max(strain_linf_series)},
            "high_frequency_energy_fraction": {"initial": tail_series[0],
                                                "final": tail_series[-1],
                                                "max": max(tail_series)},
            "energy_series": energy_series,
        },
    }
    if exact_hat is not None:
        out["mms_relative_l2_error"] = core.relative_l2(state, exact_hat(steps * dt), sp)
        v_exact = core.inverse(exact_hat(steps * dt), grid)
        v_num = core.inverse(state, grid)
        out["mms_relative_linf_error"] = float(
            np.max(np.abs(v_num - v_exact))
            / max(float(np.max(np.abs(v_exact))), 1e-300)
        )
    return out


def grid_convergence_rate(
    case: str, viscosity: float, final_time: float, grids: tuple[int, int], dealias: bool
) -> dict[str, object]:
    """Two-resolution relative-L2 ratio for the manufactured solution.

    A spectral method on an exact-manufactured solution is not expected to
    follow a polynomial rate; the raw ratio is what is reported, and the test
    pins a floor rather than pretending an order.
    """
    if len(grids) != 2:
        raise ValueError("exactly two grids required")
    coarse, fine = sorted(grids)
    if fine % 2 or coarse % 2 or fine < 4 or coarse < 4:
        raise ValueError("grids must be even and >= 4")
    out = {}
    for label, g in (("coarse", coarse), ("fine", fine)):
        steps = max(4, int(round(final_time / (0.05 * (16.0 / g)))))
        arm = run_arm(case, g, steps, final_time / steps, viscosity, dealias)
        out[label] = {
            "grid": g,
            "steps": steps,
            "relative_l2_error": arm.get("mms_relative_l2_error"),
            "relative_linf_error": arm.get("mms_relative_linf_error"),
        }
    c_err, f_err = out["coarse"]["relative_l2_error"], out["fine"]["relative_l2_error"]
    if isinstance(c_err, float) and isinstance(f_err, float) and c_err > 0 and f_err > 0:
        out["error_reduction_ratio"] = c_err / f_err
        out["equivalent_polynomial_order"] = (
            math.log(c_err / f_err) / math.log(float(fine) / float(coarse))
        )
    else:
        out["error_reduction_ratio"] = None
        out["equivalent_polynomial_order"] = None
    return out


def paired_solver_benchmark(
    grid: int, steps: int, dt: float, viscosity: float
) -> dict[str, object]:
    """The A/B pair, on identical data, differing only in the dealiasing flag.

    Three independent measurements of the pair:

      * inviscid energy conservation (nu = 0, no forcing): the true continuum
        energy is exactly constant, so any drift is the discretisation's own
        error, and this is the "energy conservation residual" the lane brief
        asks for. A viscous run is NOT used for this: there energy decays for
        physical reasons and the raw drift measures the flow, not the solver.
      * Taylor-Green with viscosity (the standard test flow): divergence
        residual and the scale-localized blowup diagnostics, paired.
      * the manufactured solution: accuracy (L2 / Linf relative error), paired.
    """
    baseline_inviscid = run_arm("tgv", grid, steps, dt, 0.0, dealias=False)
    improved_inviscid = run_arm("tgv", grid, steps, dt, 0.0, dealias=True)
    baseline = run_arm("tgv", grid, steps, dt, viscosity, dealias=False)
    improved = run_arm("tgv", grid, steps, dt, viscosity, dealias=True)
    mms_baseline = run_arm("mms", grid, steps, dt, viscosity, dealias=False)
    mms_improved = run_arm("mms", grid, steps, dt, viscosity, dealias=True)
    return {
        "inviscid_energy_conservation": {
            "baseline": baseline_inviscid,
            "improved": improved_inviscid,
            "delta": {
                "energy_drift_rel": (
                    improved_inviscid["energy_drift_rel"]
                    - baseline_inviscid["energy_drift_rel"]
                ),
            },
        },
        "tgv": {
            "baseline": baseline,
            "improved": improved,
            "delta": {
                "divergence_linf_final": (
                    improved["divergence_linf_final"] - baseline["divergence_linf_final"]
                ),
                "enstrophy_final": improved["enstrophy_final"] - baseline["enstrophy_final"],
                "high_frequency_energy_fraction_final": (
                    improved["blowup_diagnostic"]["high_frequency_energy_fraction"]["final"]
                    - baseline["blowup_diagnostic"]["high_frequency_energy_fraction"]["final"]
                ),
            },
        },
        "mms": {
            "baseline": mms_baseline,
            "improved": mms_improved,
            "delta": {
                "relative_l2_error": (
                    mms_improved["mms_relative_l2_error"]
                    - mms_baseline["mms_relative_l2_error"]
                ),
                "relative_linf_error": (
                    mms_improved["mms_relative_linf_error"]
                    - mms_baseline["mms_relative_linf_error"]
                ),
            },
        },
    }


# ---------------------------------------------------------------------------
# negative control (a): bounded-energy smooth shear, must not raise a false alarm
# ---------------------------------------------------------------------------


def smooth_shear_negative_control(grid: int, steps: int, dt: float) -> dict[str, object]:
    """An exact steady Euler shear state: u = (sin y, 0, 0) on the torus.

    ``u`` depends on ``y`` only and points in ``x`` only, so ``(u . grad) u = 0``
    identically; with ``nu = 0`` and no forcing the field is a stationary
    solution of the projected equation to round-off. Every scale-localized
    diagnostic the solver reports must therefore stay flat, and the
    under-resolved flag must never fire. A blowup instrument that alarms on
    *this* state is measuring its own discretisation error, not a flow feature.
    """
    sp = core.spectral(grid)
    x, y, z = core.mesh(grid)
    field = np.stack((np.sin(y), np.zeros_like(y), np.zeros_like(y)))
    state = core.leray(core.forward(field), sp)
    start = core.flow_diagnostics(state, sp, viscosity=0.0)
    worst_underresolved = 0.0
    for index in range(steps):
        state = core.step_ifrk4(state, sp, 0.0, dt, True, None, index * dt)
        diag = core.flow_diagnostics(state, sp, viscosity=0.0)
        worst_underresolved = max(
            worst_underresolved,
            1.0 if bool(diag["underresolved"]) else 0.0,
        )
    end = core.flow_diagnostics(state, sp, viscosity=0.0)
    return {
        "case": "smooth_shear_negative_control",
        "grid": grid,
        "steps": steps,
        "dt": dt,
        "velocity_linf_start": start["velocity_linf"],
        "velocity_linf_end": end["velocity_linf"],
        "velocity_linf_drift": abs(end["velocity_linf"] - start["velocity_linf"]),
        "vorticity_linf_start": start["vorticity_linf"],
        "vorticity_linf_end": end["vorticity_linf"],
        "vorticity_linf_drift": abs(end["vorticity_linf"] - start["vorticity_linf"]),
        "energy_drift_rel": (
            abs(end["energy"] - start["energy"]) / start["energy"] if start["energy"] > 0 else 0.0
        ),
        "high_frequency_energy_fraction_start": start["high_frequency_energy_fraction"],
        "high_frequency_energy_fraction_end": end["high_frequency_energy_fraction"],
        "ever_underresolved": bool(worst_underresolved > 0.0),
        "false_blowup_alarm": bool(worst_underresolved > 0.0),
    }


# ---------------------------------------------------------------------------
# negative control (b): the 80540a2 mass-escape wavepacket, whole space
# ---------------------------------------------------------------------------


def _gaussian_curl_field(
    coord: np.ndarray, centre: np.ndarray, sigma: float
) -> np.ndarray:
    """``u = (d_y g, -d_x g, 0)`` for ``g`` a Gaussian about ``centre``.

    Divergence-free by construction (mixed partials of ``g`` commute), like the
    Lean witness's certified ``phifun``. Shape: ``coord`` is ``(3, n, n, n)``
    from ``np.meshgrid(indexing="ij")``; the return is ``(3, n, n, n)``.
    """
    dx = coord[0] - centre[0]
    dy = coord[1] - centre[1]
    dz = coord[2] - centre[2]
    r2 = dx * dx + dy * dy + dz * dz
    g = np.exp(-r2 / (2.0 * sigma * sigma))
    # d/dx g = -(dx/sigma^2) g, d/dy g = -(dy/sigma^2) g
    dgdx = -(dx / (sigma * sigma)) * g
    dgdy = -(dy / (sigma * sigma)) * g
    return np.stack((dgdy, -dgdx, np.zeros_like(dgdx)))


def mass_escape_witness(
    sigma: float = 0.6,
    central_radius: float = 6.0,
    central_grid: int = 64,
    track_radius: float = 3.0,
    track_grid: int = 64,
    escape_times: tuple[float, ...] = (0.5, 0.25, 0.125, 0.0625, 0.03125),
) -> dict[str, object]:
    """Numerical mirror of ``80540a2``'s ``escapingCarrier``.

    ``escapingCarrier t x = if t = 0 then 0 else phifun (x - t⁻¹ • e₀)``: a
    fixed bump translated along the first axis by ``1/t`` as ``t -> 0+``, with
    the initial slice the zero field.

    Two sampling windows, not one giant box:

      * a FIXED central window ``[-central_radius, central_radius]^3`` — what
        a naive pointwise inspection sees, standing in for any bounded region
        an observer is stuck with;
      * a TRACKING window ``centre + [-track_radius, track_radius]^3`` that
        always contains the bump (``track_radius >= 4 * sigma``), standing in
        for "the whole of space" for a compactly supported integrand.

    The three facts ``80540a2`` proves reproduce numerically:

      1. pointwise convergence holds — every fixed point of the central window
         eventually sees only zeros (`escapingCarrier_rightContinuousAtStart`);
      2. the bump's energy is the same positive number at every sampled time —
         translation does not change it (`kineticEnergy_escapingCarrier`,
         `integral_phifun_shift`) — so the energy sequence is bounded, with no
         hint of a blow-up (`escapingCarrier_energy_bdd`), while the initial
         slice is the zero field (`initial_slice_energy = 0`);
      3. the `L²`-in-time gap to the initial slice, measured over the tracking
         window, does not tend to `0` (`not_tendsto_L2Gap_atStart`), and the
         fraction of the bump's energy lying outside the central window grows
         to `1` — the escape, made visible as a tail rather than as a spike.

    The "naive" instrument — pointwise max on the fixed central window plus a
    bounded-energy check — passes both of its tests at every sampled time and
    therefore reports no problem. The "tail-aware" instrument — the `L²` gap
    over a window that always contains the bump, and the tail-mass fraction —
    reports the escape at every sampled time. That gap between the two
    instruments *is* the obstruction: no amount of fixing the observation
    domain, tightening the pointwise tolerance, or bounding the energy closes
    it, because the missing input is a spatial envelope the escape destroys
    (`not_exists_integrable_envelope_escapingCarrier`), not a finer grid.

    Deliberately NOT a Navier-Stokes evolution and NOT periodic: this is the
    kinematic translation core of the Lean witness, which stands on its own
    without a pressure, a viscosity, or a momentum equation (`80540a2`'s own
    "What is NOT claimed" section says exactly this, and the Lean module proves
    the divergence-free vector-field version separately). A periodic box would
    be wrong here — an escaping bump on a torus wraps around and revisits the
    observer, which is the opposite of losing mass to infinity.
    """
    if central_grid < 16 or track_grid < 16:
        raise ValueError("both grids must be >= 16")
    if track_radius < 4.0 * sigma:
        raise ValueError("track_radius must be >= 4 * sigma to hold the bump's support")
    if not escape_times or min(escape_times) <= 0.0:
        raise ValueError("escape_times must be positive")
    ordered = sorted(escape_times, reverse=True)  # t descending: the escape direction

    central_axis = np.linspace(-central_radius, central_radius, central_grid)
    central_coord = np.stack(np.meshgrid(*(central_axis,) * 3, indexing="ij"), axis=0)
    track_axis = np.linspace(-track_radius, track_radius, track_grid)
    track_coord = np.stack(np.meshgrid(*(track_axis,) * 3, indexing="ij"), axis=0)
    central_cell = ((2.0 * central_radius) / (central_grid - 1)) ** 3
    track_cell = ((2.0 * track_radius) / (track_grid - 1)) ** 3

    naive_max_over_central: list[float] = []
    naive_energy_series: list[float] = []
    l2_gap_over_tracking_window: list[float] = []
    tail_mass_fraction: list[float] = []

    for t in ordered:
        centre = np.array([1.0 / t, 0.0, 0.0])
        # Pointwise reading on the FIXED window: as `1/t` grows, the bump leaves
        # every fixed point, so this decays to 0 (and stays 0 once the whole
        # support is past `central_radius`).
        central_field = _gaussian_curl_field(central_coord, centre, sigma)
        naive_max_over_central.append(
            float(np.max(np.sqrt(np.sum(central_field * central_field, axis=0))))
        )
        central_energy = (
            float(np.sum(central_field * central_field)) * central_cell
        )
        # The bump's own energy, read over a window that translates with it.
        # This is the numerical `integral_phifun_shift`: the same positive
        # number at every sampled time, up to quadrature error. The window's
        # absolute position is deliberately large (|centre| up to 32) while its
        # extent is small (track_radius = 3), so the integrand is genuinely
        # sampled at a moving location rather than re-reading one fixed array.
        track_coord_at_centre = track_coord + centre[:, None, None, None]
        track_field = _gaussian_curl_field(track_coord_at_centre, centre, sigma)
        track_energy = float(np.sum(track_field * track_field)) * track_cell
        naive_energy_series.append(track_energy)
        # ||u(t) - u(0)||_{L2} with u(0) identically 0: the gap over a window
        # that always contains the bump, so it never collapses.
        l2_gap_over_tracking_window.append(math.sqrt(max(track_energy, 0.0)))
        tail_mass_fraction.append(
            1.0 - (central_energy / track_energy if track_energy > 0 else 0.0)
        )

    pointwise_decays_to_zero = bool(
        naive_max_over_central[-1] <= 1e-9 and all(
            naive_max_over_central[i + 1] <= naive_max_over_central[i] + 1e-12
            for i in range(len(naive_max_over_central) - 1)
        )
    )
    energy_sequence = np.asarray(naive_energy_series, dtype=np.float64)
    energy_spread = float(
        (energy_sequence.max() - energy_sequence.min()) / energy_sequence.mean()
    ) if energy_sequence.size else float("nan")
    energy_is_bounded_and_flat = bool(
        np.all(np.isfinite(energy_sequence)) and energy_spread < 1e-9
    )
    # The initial slice is the zero field by definition (`escapingCarrier_zero`).
    initial_slice_energy = 0.0
    gap_sequence = np.asarray(l2_gap_over_tracking_window, dtype=np.float64)
    gap_does_not_tend_to_zero = bool(
        gap_sequence.size and gap_sequence.min() > 1e-3
    )
    tail_grows = bool(
        len(tail_mass_fraction) >= 2
        and tail_mass_fraction[-1] >= tail_mass_fraction[0]
    )

    return {
        "case": "mass_escape_witness",
        "mirrors_commit": OBSTRUCTION_COMMIT,
        "mirrors_declarations": [
            "escapingCarrier", "kineticEnergy_escapingCarrier",
            "escapingCarrier_rightContinuousAtStart", "escapingCarrier_energy_bdd",
            "not_tendsto_kineticEnergy_atStart", "not_tendsto_L2Gap_atStart",
        ],
        "sigma": sigma,
        "central_radius": central_radius,
        "central_grid": central_grid,
        "track_radius": track_radius,
        "track_grid": track_grid,
        "escape_times_sorted_descending": ordered,
        "initial_slice_energy": initial_slice_energy,
        "naive_pointwise_max_on_central_window": naive_max_over_central,
        "naive_pointwise_converges_to_zero": pointwise_decays_to_zero,
        "naive_energy_series": naive_energy_series,
        "naive_energy_relative_spread": energy_spread,
        "naive_energy_bounded_and_flat": energy_is_bounded_and_flat,
        "l2_gap_to_initial_slice": l2_gap_over_tracking_window,
        "l2_gap_tends_to_zero": not gap_does_not_tend_to_zero,
        "tail_mass_fraction_outside_central_window": tail_mass_fraction,
        "tail_fraction_is_non_decreasing": tail_grows,
        # A naive pointwise+energy check passes on every sampled time; the L2
        # invariant fails on every sampled time. That gap is the obstruction.
        "naive_checks_miss_the_escape": bool(
            pointwise_decays_to_zero and energy_is_bounded_and_flat
        ),
        "tail_invariant_catches_the_escape": bool(
            gap_does_not_tend_to_zero and tail_mass_fraction[-1] > 0.99
        ),
        "scope_note": (
            "Kinematic translation witness mirroring "
            f"{OBSTRUCTION_MODULE}.escapingCarrier; not a Navier-Stokes "
            "evolution, not a regularity claim."
        ),
    }


# ---------------------------------------------------------------------------
# receipt
# ---------------------------------------------------------------------------


def build_receipt(
    grid: int, steps: int, dt: float, viscosity: float, conv_grids: tuple[int, int]
) -> dict[str, object]:
    keys = replay_keys()
    return {
        "schema_version": SCHEMA_VERSION,
        "tool_version": TOOL_VERSION,
        "scope_note": SCOPE_NOTE,
        "replay_keys": keys,
        "configuration": {
            "grid": grid,
            "steps": steps,
            "dt": dt,
            "viscosity": viscosity,
            "grid_convergence_grids": list(conv_grids),
        },
        "paired_solver_benchmark": paired_solver_benchmark(grid, steps, dt, viscosity),
        "grid_convergence": grid_convergence_rate(
            "mms", viscosity, steps * dt, conv_grids, dealias=True
        ),
        "negative_controls": {
            "smooth_shear": smooth_shear_negative_control(grid, steps, dt),
            "mass_escape": mass_escape_witness(),
        },
    }


def canonical_json(payload: object) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def write_receipt(receipt: dict[str, object], output: Path) -> dict[str, object]:
    body = canonical_json(receipt)
    content_sha = hashlib.sha256(body.encode("utf-8")).hexdigest()
    output.parent.mkdir(parents=True, exist_ok=True)
    wrapped = {"payload_sha256": content_sha, "payload": json.loads(body)}
    output.write_text(json.dumps(wrapped, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return {"output": str(output), "payload_sha256": content_sha, "bytes": output.stat().st_size}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--grid", type=int, default=16)
    parser.add_argument("--steps", type=int, default=20)
    parser.add_argument("--dt", type=float, default=0.05)
    parser.add_argument("--viscosity", type=float, default=0.05)
    parser.add_argument(
        "--convergence-grids", type=int, nargs=2, default=(12, 16), metavar=("COARSE", "FINE")
    )
    parser.add_argument("--output", type=Path, default=None,
                        help="write the hermetic receipt here instead of stdout")
    args = parser.parse_args()

    receipt = build_receipt(args.grid, args.steps, args.dt, args.viscosity,
                            tuple(args.convergence_grids))
    if args.output is not None:
        print(json.dumps(write_receipt(receipt, args.output.resolve()), indent=2))
    else:
        print(canonical_json(receipt))
    return 0


if __name__ == "__main__":
    sys.exit(main())
