from __future__ import annotations

import hashlib
from pathlib import Path


CRATE_DIR = Path(__file__).resolve().parent.parent

BUILD_INPUTS = (
    "build-web.sh",
    "tools/provenance.py",
    "tools/verify_web_build.py",
    "tools/write_provenance.py",
)

def compiled_sources() -> tuple[str, ...]:
    """Bind every source/shader input, including future include_str! assets."""
    inputs = ["Cargo.lock", "Cargo.toml"]
    if (CRATE_DIR / "build.rs").is_file():
        inputs.append("build.rs")
    inputs.extend(
        path.relative_to(CRATE_DIR).as_posix()
        for path in (CRATE_DIR / "src").rglob("*") if path.is_file()
    )
    return tuple(sorted(inputs))


COMPILED_SOURCES = compiled_sources()
WEB_ARTIFACTS = (
    "navier_web.d.ts", "navier_web.js", "navier_web_bg.wasm", "navier_web_bg.wasm.d.ts",
)


def sha256(path: Path) -> str:
    return "sha256-" + hashlib.sha256(path.read_bytes()).hexdigest()


def digest_files(relative_paths: tuple[str, ...]) -> str:
    digest = hashlib.sha256()
    for relative in relative_paths:
        digest.update(relative.encode())
        digest.update(b"\0")
        digest.update((CRATE_DIR / relative).read_bytes())
        digest.update(b"\0")
    return "sha256-" + digest.hexdigest()


def source_digest() -> str:
    return digest_files(COMPILED_SOURCES)


def build_pipeline_digest() -> str:
    return digest_files(BUILD_INPUTS)
