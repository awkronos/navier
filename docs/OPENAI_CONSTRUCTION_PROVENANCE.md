# OpenAI construction provenance

The native construction under `Navier/Construction` is adapted from OpenAI's
`NavierStokesAndEuler` repository at revision
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`. The source snapshot accompanies
the September 8, 2026 paper *Finite time blowup for Navier–Stokes*.

The adaptation vendors source rather than taking a Lake dependency. Its 577
Lean modules comprise the 511-module candidate construction and the 66-module
whole-space finite-energy comparison closure. Each adapted file names the
upstream source, pinned revision, and applicable license in its header.

## Upstream boundary (2026-09-13)

Upstream `openai/NavierStokesAndEuler` has advanced from the pinned
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` to head `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`
(+188 files, +25,143 lines). The delta is paper-appendix machinery only — the
`GenericRealization`/`ClosedIntervalCk`/`WholeDomainPhysicalStageTheorem`/
`FlatPrimitivePaper` family — and `formalization.yaml`'s main-results set is
unchanged, so the C/D crown set adapted here remains crown-complete against
upstream. The port of the appendix layer is named as the next construction
target rather than silently merged. The repository also carries the unforced
Euler breakdown (`Euler.euler_breakdown_R3`,
`Euler.exists_compact_smooth_euler_singularity`), which this repo does not yet
adapt; see the Euler rows of `OPEN_FRONTIER_MAP.md` and
`references/manifest.json`.

## Adaptation boundary

The port changes module paths from `NavierStokes` to `Navier.Construction` and
uses the APIs available in the Lean 4.31.0 toolchain it was authored against;
the repository now compiles it on `v4.34.0-rc2` (migrated in `ad12c3d`).
Compatibility edits include renamed conditional simplification lemmas,
`Continuous`/`ContDiff` method names, extended-natural coercion lemmas, and
direct `Finsupp.single` coefficient identities where former Laurent-polynomial
simp lemmas are unavailable. These edits preserve theorem statements and the
mathematical carriers.

Repository-native glue is intentionally outside the adapted namespace:

- `Navier/Analysis/EuclideanPDETransport.lean` proves the coordinate isometry,
  PDE derivative identities, energy transport, and force admissibility.
- `Navier/Analysis/ForceRecursivePartials.lean` defines literal successive
  coordinate differentiation by recursively applying `fderivWithin`. It proves
  equality with the Taylor jet evaluation for every ordered direction family,
  including the boundary at time zero, and derives all weighted force bounds.
- `Navier/Breakdown/NativeConstructionEndpoint.lean` consumes an actual compact
  candidate and excludes native global solutions.
- `Navier/Breakdown/ConstructedBreakdown.lean` supplies the selected candidate
  and proves `Navier.ProblemStatements.WholeSpaceBreakdown`.

No additional axiom, generated proof oracle, or external compiled object supplies
the result. The selected candidate and its transitive construction closure were
compiled from the vendored source.

## 2026-09-13 re-verification receipts (Lean v4.34.0-rc2)

Native repository at `6e9c2ec`, verified in an isolated clone with the shared
Mathlib cache (`85e3a25e006c35636f0e53b0e9296caca2685bc0`):

- `lake build Navier.Breakdown.ConstructedBreakdown
  Navier.Analysis.PeriodicConstructedBreakdown` —
  **Build completed successfully (9379 jobs)**, plus the
  `DeadlineParameterizedWholeSpaceBreakdown` module.
- Raw `#print axioms` for the four crown theorems — every one reports exactly
  `[propext, Classical.choice, Quot.sound]`:
  `wholeSpaceBreakdown`, `wholeSpaceBreakdown_with_successivePartials`,
  `wholeSpaceBreakdown_deadlineT`,
  `Navier.Analysis.PeriodicConstructedBreakdown.periodicBreakdown`.

Upstream `openai/NavierStokesAndEuler` at head `f9e8bc5b38b6e212696e8a30e3e91517af887bbd`,
built from scratch on a 32-core host (this repository's separate checkout, not
a Lake dependency):

- Full `lake build` — **Build completed successfully (11424 jobs)**; all 2,659
  modules; zero errors.
- Raw `#print axioms` for the four upstream crown declarations — every one
  reports exactly `[propext, Classical.choice, Quot.sound]`:
  `NavierStokes.Comparator.navier_stokes_breakdown_R3`,
  `NavierStokes.Comparator.navier_stokes_breakdown_periodic`,
  `Euler.euler_breakdown_R3`,
  `Euler.exists_compact_smooth_euler_singularity`.
  (The Euler pair is additionally emitted by the project's own
  `Euler/Solution.lean` during the build.)
- Structural audit of the graph: 0 import cycles, max depth 96, no import
  path between the Euler and NavierStokes libraries, and the
  `formalization.yaml` main-results set unchanged since the pinned `8937a8f`.
- Per-file compiler-derived census: every module recompiled individually via
  `lake env lean` — zero `uses sorry` warnings across NavierStokes, Euler, and
  ComparatorChallenges. A full no-op re-run of `lake build` at current source
  completed successfully (11424 jobs).

These receipts establish kernel-clean compilation of both repositories' crown
endpoints on the current toolchain. They do not promote any upstream model
result to a statement about unforced Navier–Stokes; see `BARRIERS.md` §5.

## License

The adapted `Navier/Construction` sources are distributed under the Apache
License 2.0 from the upstream project. A copy is retained at
[`references/licenses/OpenAI-Apache-2.0.txt`](../references/licenses/OpenAI-Apache-2.0.txt).
`CompactFutureForce.lean` also adapts the upstream compact-jet argument and
carries the same Apache notice. `EuclideanPDETransport.lean`,
`ForceRecursivePartials.lean`, `NativeConstructionEndpoint.lean`, and
`ConstructedBreakdown.lean` are original repository glue and remain under the
repository's MIT license.

## Verification boundary

The dependency-ordered source check compiled all 511 construction modules and
all 66 finite-energy comparison modules with Lean 4.31.0. Fresh raw
`#print axioms` checks for the selected compact candidate, comparison theorem,
coordinate endpoint, and final whole-space breakdown theorem report only:

```text
propext
Classical.choice
Quot.sound
```

This proves forced whole-space alternative C in the repository's formal
statement. It does not prove the separate zero-force global-regularity
alternative A, and the numerical solver is not part of the proof.

### Reproduce from a clean checkout

Install Lake and the Lean toolchain selected by `lean-toolchain`. Then fetch the
pinned Mathlib revision recorded by Lake:

```bash
lake update
```

On the project machines, the shared Mathlib cache can instead be repaired with
the workspace cache tool before verification. The verifier itself does not
download dependencies or invoke a remote proof service.

```bash
python3 scripts/verify_construction.py --check-plan
python3 scripts/verify_construction.py --jobs 2
```

The first command parses only the local import closure rooted at
`Navier.Breakdown.ConstructedBreakdown` and reports which modules have current
receipts. The second invokes the pinned compiler through `lake env lean`, once
per stale source, and writes outputs into `.lake/build/lib/lean`. Receipts and
logs live under `.lake/verify-construction`. A source hash, the environment
hash, any transitive local dependency fingerprint, a failed recorded exit, or
a mismatch in the compiled `.olean` SHA-256 invalidates the affected receipt.
Replacing or corrupting one compiled object therefore invalidates its
transitive consumers as well. Independent ready modules are compiled with
bounded parallelism; the default is two workers.

For a shared workspace that requires serialized compiler materialization, pass
its operator explicitly. The verifier does not hardcode a user or machine path:

```bash
python3 scripts/verify_construction.py \
  --lock-wrapper /path/to/lean-build-lock.sh --lock-timeout 600
```

After the closure compiles, the verifier imports the final module and runs raw,
fully qualified `#check`, `#print`, and `#print axioms` commands for
`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown`, its strengthened
successive-partials form, and the recursive-partial bound it consumes. It exits
nonzero if the compiler fails, source changes during a compile, the graph is
cyclic, the axiom output cannot be parsed, or any axiom lies outside the
three-name allowlist above.
