#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
from pathlib import Path

from provenance import CRATE_DIR, sha256, source_digest


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} OUTPUT_DIRECTORY")
    output = Path(sys.argv[1]).resolve()
    manifest = json.loads((output / "provenance.json").read_text(encoding="utf-8"))
    failures = []
    if manifest.get("sourceDigest") != source_digest():
        failures.append("compiled source digest does not match this checkout")
    if manifest.get("cargoLockSha256") != sha256(CRATE_DIR / "Cargo.lock"):
        failures.append("Cargo.lock hash does not match this checkout")
    for name, expected in manifest.get("artifacts", {}).items():
        path = output / name
        if not path.is_file() or sha256(path) != expected:
            failures.append(f"artifact hash mismatch: {name}")
    if failures:
        raise SystemExit("stale Navier web build: " + "; ".join(failures))
    print(f"verified Navier web build {manifest['sourceDigest']}")


if __name__ == "__main__":
    main()
