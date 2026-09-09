from __future__ import annotations

import hashlib
from pathlib import Path


CRATE_DIR = Path(__file__).resolve().parent.parent
COMPILED_SOURCES = (
    "Cargo.lock",
    "Cargo.toml",
    "src/core.rs",
    "src/gpu.rs",
    "src/lib.rs",
    "src/shaders/spectral.wgsl",
)


def sha256(path: Path) -> str:
    return "sha256-" + hashlib.sha256(path.read_bytes()).hexdigest()


def source_digest() -> str:
    digest = hashlib.sha256()
    for relative in COMPILED_SOURCES:
        digest.update(relative.encode())
        digest.update(b"\0")
        digest.update((CRATE_DIR / relative).read_bytes())
        digest.update(b"\0")
    return "sha256-" + digest.hexdigest()
