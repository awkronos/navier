#!/usr/bin/env python3
"""Build a deterministic standalone distribution from the canonical solver.

This exports a release snapshot; it does not establish another maintained
implementation. No upload or publication occurs.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile


def git(repo: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(repo), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def build(output: Path, canonical: Path) -> dict:
    repo = Path(__file__).resolve().parents[1]
    names = (
        "navier_spectral_core.py", "navier_accel.py", "navier_kernels.c",
        "navier_solver_bench.py", "test_navier_spectral_core.py",
    )
    sources = {name: canonical / "solvers/navier" / name for name in names}
    sources["LICENSE"] = canonical / "LICENSE"
    sources["navier_adaptive_bench.py"] = repo / "scripts/navier_adaptive_bench.py"
    sources["export_navier_web_demo.py"] = repo / "scripts/export_navier_web_demo.py"
    # Refuse to stamp a clean upstream commit on modified canonical source.
    paths = [str(path.relative_to(canonical)) for path in sources.values()
             if path.is_relative_to(canonical)]
    if git(canonical, "status", "--porcelain", "--", *paths):
        raise RuntimeError("canonical solver source is modified; commit and verify it first")
    files = {name: path.read_bytes() for name, path in sources.items()}
    manifest = {
        "schema_version": 1,
        "canonical_repository": "https://github.com/awktavian/reality",
        "canonical_commit": git(canonical, "rev-parse", "HEAD"),
        "navier_repository": "https://github.com/awkronos/navier",
        "navier_base_commit": git(repo, "rev-parse", "HEAD"),
        "scope": "Periodic numerical solver; no continuum regularity certificate.",
        "sha256": {name: hashlib.sha256(data).hexdigest()
                   for name, data in sorted(files.items())},
    }
    files["PROVENANCE.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    files["requirements.txt"] = b"numpy>=1.26,<3\npytest>=8,<10\n"
    files["README.md"] = b"""# Standalone Navier solver

This deterministic release snapshot exports the canonical Awkronos solver.
The canonical repository remains the maintenance source; this directory is
independent of that checkout and needs no OpenAI package or Lean installation.

Create a Python 3.11+ environment, then run:

    python -m pip install -r requirements.txt
    python -m pytest -q test_navier_spectral_core.py
    python navier_adaptive_bench.py --help
    python navier_adaptive_bench.py
    python export_navier_web_demo.py --help

NumPy is sufficient. SciPy/pyFFTW and a C compiler are optional acceleration;
the solver checks accelerators against its reference operations. Record the
Python/NumPy versions and selected FFT backend with any reported benchmark.

Adaptive IFRK4 uses step doubling, a CFL guard and spectral-tail diagnostics.
The benchmark includes independent analytic manufactured forcing. Finite-grid
results and sampled vorticity integrals do not establish continuum smoothness
or singularity. Source hashes and the canonical commit are in PROVENANCE.json.
The original implementation's license accompanies the source.
"""
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in sorted(files.items()):
            info = zipfile.ZipInfo("navier-solver/" + name, (2026, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, data)
    return {"output": str(output), "sha256": hashlib.sha256(output.read_bytes()).hexdigest(),
            "canonical_commit": manifest["canonical_commit"], "files": len(files)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--canonical", type=Path, default=Path.home() / "reality")
    args = parser.parse_args()
    print(json.dumps(build(args.output.resolve(), args.canonical.resolve()), indent=2))
