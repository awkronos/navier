# OpenAI construction provenance

The native construction under `Navier/Construction` is adapted from OpenAI's
`NavierStokesAndEuler` repository at revision
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`. The source snapshot accompanies
the September 8, 2026 paper *Finite time blowup for Navier–Stokes*.

The adaptation vendors source rather than taking a Lake dependency. Its 577
Lean modules comprise the 511-module candidate construction and the 66-module
whole-space finite-energy comparison closure. Each adapted file names the
upstream source, pinned revision, and applicable license in its header.

## Adaptation boundary

The port changes module paths from `NavierStokes` to `Navier.Construction` and
uses the APIs available in this repository's pinned Lean 4.31.0 toolchain.
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
