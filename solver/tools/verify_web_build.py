#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from pathlib import Path

from provenance import COMPILED_SOURCES, CRATE_DIR, WEB_ARTIFACTS, sha256, source_digest


def verify_manifest(output: Path, manifest: dict) -> list[str]:
    failures = []
    if manifest.get("schemaVersion") != 1 or manifest.get("crate") != "navier-web":
        failures.append("unsupported provenance schema or crate")
    if manifest.get("compiledSources") != list(COMPILED_SOURCES):
        failures.append("compiled source inventory does not match this checkout")
    if manifest.get("sourceDigest") != source_digest():
        failures.append("compiled source digest does not match this checkout")
    if manifest.get("cargoLockSha256") != sha256(CRATE_DIR / "Cargo.lock"):
        failures.append("Cargo.lock hash does not match this checkout")
    if manifest.get("continuumCertificate") is not False or manifest.get("adaptiveRecording") is not False:
        failures.append("unsupported numerical certification claim")
    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, dict) or set(artifacts) != set(WEB_ARTIFACTS):
        failures.append("artifact inventory must contain the complete browser build")
        return failures
    for name in WEB_ARTIFACTS:
        path = output / name
        if not path.resolve().is_relative_to(output.resolve()) or not path.is_file() or sha256(path) != artifacts[name]:
            failures.append(f"artifact hash mismatch: {name}")
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
