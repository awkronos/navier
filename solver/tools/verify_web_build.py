#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
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


LOCAL_PATH_MARKERS = (b"/Users/", b"/home/", b"\\Users\\")


def local_path_marker_count(wasm: bytes) -> int:
    """Count common user-home path markers without exposing matched paths."""
    return sum(wasm.count(marker) for marker in LOCAL_PATH_MARKERS)


def verify_manifest(output: Path, manifest: dict) -> list[str]:
    failures = []
    if manifest.get("schemaVersion") != 1 or manifest.get("crate") != "navier-web":
        failures.append("unsupported provenance schema or crate")
    if manifest.get("compiledSources") != list(COMPILED_SOURCES):
        failures.append("compiled source inventory does not match this checkout")
    if manifest.get("sourceDigest") != source_digest():
        failures.append("compiled source digest does not match this checkout")
    if manifest.get("buildInputs") != list(BUILD_INPUTS):
        failures.append("build input inventory does not match this checkout")
    if manifest.get("buildPipelineDigest") != build_pipeline_digest():
        failures.append("build pipeline digest does not match this checkout")
    if manifest.get("cargoLockSha256") != sha256(CRATE_DIR / "Cargo.lock"):
        failures.append("Cargo.lock hash does not match this checkout")
    if manifest.get("continuumCertificate") is not False or manifest.get("adaptiveRecording") is not False:
        failures.append("unsupported numerical certification claim")
    if manifest.get("reproducibility") != {
        "rustPathRemapping": True,
        "localAbsolutePathGuard": True,
    }:
        failures.append("reproducible path-remapping policy is missing")
    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, dict) or set(artifacts) != set(WEB_ARTIFACTS):
        failures.append("artifact inventory must contain the complete browser build")
        return failures
    for name in WEB_ARTIFACTS:
        path = output / name
        if not path.resolve().is_relative_to(output.resolve()) or not path.is_file() or sha256(path) != artifacts[name]:
            failures.append(f"artifact hash mismatch: {name}")
    wasm_path = output / "navier_web_bg.wasm"
    if wasm_path.is_file():
        marker_count = local_path_marker_count(wasm_path.read_bytes())
        if marker_count:
            failures.append(
                f"browser WASM contains {marker_count} local absolute path marker(s)"
            )
    return failures


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} OUTPUT_DIRECTORY")
    output = Path(sys.argv[1]).resolve()
    manifest = json.loads((output / "provenance.json").read_text(encoding="utf-8"))
    failures = verify_manifest(output, manifest)
    if failures:
        raise SystemExit("stale Navier web build: " + "; ".join(failures))
    print(f"verified Navier web build {manifest['sourceDigest']}")


if __name__ == "__main__":
    main()
