# Release recheck — 2026-09-09

The original C consumer and its 615-module local source closure were rechecked
with `python3 -u scripts/verify_construction.py --jobs 2`, exit 0. The verifier
accepted 332 current receipts, rebuilt 283 invalidated compiled objects, and
then compiled the exact-type/raw-axiom audit. No Lean source changed in this
release-artifact cleanup; the preceding native main is `4e4aab7`.

`module-manifest.json` binds all 615 current source files and compiled objects
to their checked SHA-256 values and environment fingerprints, without embedding
machine-local paths. `construction.txt` preserves the complete verifier output.
`axioms.txt` preserves the fresh raw compiler output for all eleven named
endpoints. Every transitive axiom list is exactly
`[propext, Classical.choice, Quot.sound]`.

The original endpoint remains
`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown :
Navier.ProblemStatements.WholeSpaceBreakdown`.
The [result map](../../../docs/RESULT_MAP.md) states the exact scope and remaining
unforced/periodic/weak-continuation questions. The concentration and Madelung
notes are analytical explanations, not additional Lean endpoints.

`gpu.txt` records six passing strict GPU correctness tests on Apple M5 Max/Metal
(`NAVIER_REQUIRE_GPU=1 cargo test --locked gpu::tests -- --nocapture`). Two
benchmarks are intentionally ignored. `python-tests.txt` records eleven passing
provenance and proof-verifier tests. `relocation.txt` records byte-identical
WASM, JS, declarations, and provenance after rebuilding from a relocated checkout,
with zero user-home path markers.

The browser WASM SHA-256 is
`4e23d4e64689143ea9383ae500f749cce76d88b07d4bde15eb898e036676749e`.
Compiled source digest remains
`sha256-0e1821db4a7bb0a52adbda940128aa5e0dd1f50deac13feeca834b763c7c07ac`.
These numerical checks do not constitute a continuum theorem.
