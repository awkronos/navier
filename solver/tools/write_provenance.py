#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from pathlib import Path

from provenance import (
    BUILD_INPUTS,
    COMPILED_SOURCES,
    CRATE_DIR,
    WEB_ARTIFACTS,
    build_pipeline_digest,
    sha256,
    source_digest,
)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument("--rustc", required=True)
    parser.add_argument("--wasm-bindgen", required=True)
    args = parser.parse_args()
    output = args.output_dir.resolve()
    payload = {
        "schemaVersion": 1,
        "crate": "navier-web",
        "compiledSources": list(COMPILED_SOURCES),
        "sourceDigest": source_digest(),
        "buildInputs": list(BUILD_INPUTS),
        "buildPipelineDigest": build_pipeline_digest(),
        "cargoLockSha256": sha256(CRATE_DIR / "Cargo.lock"),
        "rustc": args.rustc,
        "wasmBindgen": args.wasm_bindgen,
        "artifacts": {name: sha256(output / name) for name in WEB_ARTIFACTS},
        "method": {
            "equation": "3D periodic incompressible Navier-Stokes",
            "spatial": "dealiased rotational Fourier pseudo-spectral with Leray projection",
            "time": "fixed-step integrating-factor RK4",
            "dealiasing": "componentwise Orszag 2/3 rule",
        },
        "backends": {
            "cpuWasm": {"label": "cpu-wasm-spectral-ifrk4", "computePrecision": "f64"},
            "webGpu": {"label": "webgpu-spectral-ifrk4", "computePrecision": "f32"},
        },
        "continuumCertificate": False,
        "adaptiveRecording": False,
        "reproducibility": {
            "rustPathRemapping": True,
            "localAbsolutePathGuard": True,
        },
    }
    (output / "provenance.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
