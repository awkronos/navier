#!/usr/bin/env python3
"""Engine-level benchmark comparing FFT backends across grid sizes.

Times ``forward → inverse → nonlinear_hat → leray`` (the inner-loop
operations of one IFRK4 sub-step) for pyFFTW and scipy.fft at multiple
resolutions.  Reports speed ratio and wall time per call for each grid,
and writes an HTML comparison chart.
"""

from __future__ import annotations

import argparse
import json
import math
import time

import numpy as np

try:
    from navier_spectral_core import (
        forward,
        inverse,
        leray,
        nonlinear_hat,
        set_fft_backend,
        spectral,
        taylor_green_field,
        _HAS_PYFFTW,
        _HAS_SCIPY_FFT,
    )
except ImportError:
    import os, sys

    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from navier_spectral_core import (  # type: ignore[no-redef]
        forward,
        inverse,
        leray,
        nonlinear_hat,
        set_fft_backend,
        spectral,
        taylor_green_field,
        _HAS_PYFFTW,
        _HAS_SCIPY_FFT,
    )


def time_ops(
    grid: int, num_calls: int, backend: str, passes: int = 3
) -> dict[str, float]:
    """Measure aggregate wall time for a full engine operation bundle.

    Each call: ``forward → inverse → nonlinear_hat → leray``, which is the
    inner-loop work of one IFRK4 sub-step.  Runs ``passes`` repetitions and
    returns the median timing for stability on noisy hosts.
    """
    set_fft_backend(backend)
    sp = spectral(grid)
    field = taylor_green_field(grid)
    field_hat = forward(field)

    # warm-up with a few passes in the target backend
    for _ in range(5):
        fwd = forward(field, overwrite=True)
        inv = inverse(fwd, grid)
        nl = nonlinear_hat(fwd, sp, True)
        leray(nl, sp)

    timings: list[float] = []
    for _ in range(passes):
        started = time.perf_counter()
        for _ in range(num_calls):
            fwd = forward(field, overwrite=True)
            inv = inverse(fwd, grid)
            nl = nonlinear_hat(fwd, sp, True)
            leray(nl, sp)
        timings.append(max(time.perf_counter() - started, 1e-12))

    timings.sort()
    median = timings[len(timings) // 2]

    xfrm_per_call = 4  # forward + inverse (in nonlinear_hat) + forward (cross) + inverse
    xfrm_total = xfrm_per_call * num_calls
    return {
        "backend": backend,
        "grid": grid,
        "num_calls": num_calls,
        "wall_s": median,
        "ops_per_s": num_calls / median,
        "xfrm_per_s": xfrm_total / median,
        "us_per_op": median / num_calls * 1e6,
    }


def run_bench(
    grids: tuple[int, ...] = (16, 24, 32, 48),
    num_calls: int = 80,
    output_html: str | None = None,
    passes: int = 3,
) -> list[dict]:
    backends = ["pyfftw"] if _HAS_PYFFTW else []
    if _HAS_SCIPY_FFT:
        backends.append("scipy")
    if not backends:
        raise RuntimeError("no FFT backend available — install scipy or pyfftw")

    results: list[dict] = []
    for grid in grids:
        for backend in backends:
            r = time_ops(grid, num_calls, backend, passes=passes)
            results.append(r)
            ratio_info = ""
            if len(backends) == 2:
                py_result = next(
                    (rr for rr in results if rr["backend"] == "pyfftw" and rr["grid"] == grid), None
                )
                sc_result = next(
                    (rr for rr in results if rr["backend"] == "scipy" and rr["grid"] == grid), None
                )
                if py_result and sc_result:
                    ratio_info = f"  pyFFTW/scipy ×{py_result['ops_per_s'] / sc_result['ops_per_s']:.2f}"
            print(
                f"  grid={grid:3d}  backend={backend:8s}  "
                f"{r['ops_per_s']:>8.0f} ops/s  "
                f"{r['us_per_op']:>8.1f} µs/op"
                f"{ratio_info}"
            )

    if output_html and len(backends) == 2:
        _write_html(results, output_html)

    return results


def _write_html(results: list[dict], path: str) -> None:
    import html as htmlmod

    py_results = [r for r in results if r["backend"] == "pyfftw"]
    sc_results = [r for r in results if r["backend"] == "scipy"]

    rows = []
    for pyr, scr in zip(py_results, sc_results):
        assert pyr["grid"] == scr["grid"]
        g = pyr["grid"]
        ratio = pyr["ops_per_s"] / scr["ops_per_s"] if scr["ops_per_s"] else 0
        rows.append(
            f"""
        <tr>
          <td>{g}</td>
          <td class="num">{scr['ops_per_s']:,.0f}</td>
          <td class="num">{scr['us_per_op']:.1f}</td>
          <td class="num">{pyr['ops_per_s']:,.0f}</td>
          <td class="num">{pyr['us_per_op']:.1f}</td>
          <td class="num {'' if ratio >= 1 else 'slow'}">{ratio:.2f}×</td>
        </tr>"""
        )

    html_content = f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <title>FFT Backend Comparison — navier-spectral-smoke</title>
  <style>
    body {{ font-family: Inter, system-ui, sans-serif; max-width: 720px; margin: 2rem auto; padding: 0 1rem; }}
    h1 {{ font-size: 1.3rem; margin-bottom: .2rem; }}
    .subtitle {{ color: #666; font-size: .85rem; margin-bottom: 1.5rem; }}
    table {{ border-collapse: collapse; width: 100%; }}
    th {{ text-align: left; padding: 6px 10px; background: #f5f5f5; font-size: .8rem; border-bottom: 2px solid #ddd; }}
    td {{ padding: 6px 10px; border-bottom: 1px solid #eee; font-size: .85rem; }}
    .num {{ text-align: right; font-variant-numeric: tabular-nums; }}
    .slow {{ color: #c33; }}
    .sep {{ border-top: 1px dashed #ccc; }}
    code {{ background: #f0f0f0; padding: 1px 4px; border-radius: 3px; font-size: .8rem; }}
  </style>
</head>
<body>
<h1>FFT Backend Comparison</h1>
<p class="subtitle">navier-spectral-smoke — engine ops/s (forward+inverse+nl+leray) across grid sizes</p>
<table>
<thead>
<tr>
  <th>Grid</th>
  <th class="num" colspan="2">scipy.fft</th>
  <th class="num" colspan="2">pyFFTW</th>
  <th class="num">ratio</th>
</tr>
<tr>
  <th></th>
  <th class="num">ops/s</th>
  <th class="num">µs/op</th>
  <th class="num">ops/s</th>
  <th class="num">µs/op</th>
  <th class="num">py/sc</th>
</tr>
</thead>
<tbody>
{''.join(rows)}
</tbody>
</table>
<p style="margin-top:1rem; font-size:.75rem; color:#888;">
  Each op = forward → inverse → nonlinear_hat → leray, repeated 100×.
</p>
</body>
</html>"""
    with open(path, "w") as f:
        f.write(html_content)
    print(f"  Wrote {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description="FFT backend benchmark")
    parser.add_argument(
        "--grids",
        type=int,
        nargs="+",
        default=[16, 24, 32, 48, 64],
        help="grid sizes to benchmark (default: 16 24 32 48 64)",
    )
    parser.add_argument(
        "--num-calls", type=int, default=100, help="iterations per backend"
    )
    parser.add_argument(
        "--output-html",
        type=str,
        default=None,
        help="write HTML comparison to this path",
    )
    args = parser.parse_args()

    backends_available = []
    if _HAS_PYFFTW:
        backends_available.append("pyFFTW")
    if _HAS_SCIPY_FFT:
        backends_available.append("scipy.fft")

    print(f"Backends available: {' + '.join(backends_available)}")
    print(f"Grid sizes: {args.grids}")
    print(f"Iterations: {args.num_calls}")
    print()

    t0 = time.perf_counter()
    results = run_bench(
        grids=tuple(args.grids),
        num_calls=args.num_calls,
        output_html=args.output_html,
    )
    elapsed = time.perf_counter() - t0

    print(f"\nBenchmark complete in {elapsed:.2f}s")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())