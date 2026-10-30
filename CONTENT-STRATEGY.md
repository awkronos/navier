# Content strategy

This repository has two public faces, and this document is the map between
them so a future edit does not create drift, a dead link, or a privacy leak.

## 1. The two faces

| Face | What it is | Who maintains its SEO surface |
| --- | --- | --- |
| **This GitHub repository** | The proof source, the solver, and the written record (`README.md` + `docs/`). GitHub renders `README.md` as the repo's landing page and generates the repo's link-preview (Open Graph) card from repository metadata. | This repository, via `README.md` structure and `gh repo edit` metadata (description, homepage, topics). |
| **`navier.awkronos.com`** | The interactive companion: explains the construction and runs the Rust solver in-browser. | `awkronos-waddle` (`packages/waddle-manifests/src/navier/manifest.ts`), a separate repository. Its hreflang, sitemap, and robots entries are that repository's concern, not this one's. |

`README.md` already links the live companion
(`[navier.awkronos.com](https://navier.awkronos.com/)`); nothing in this
repository should duplicate that app's metadata or try to drive its SEO from
here.

## 2. GitHub repo metadata (the repo's own "SEO")

Set via `gh repo edit awkronos/navier`, read by GitHub's own social-card
generator and search indexing — kept here as a single source so a future
edit doesn't silently drift from what the repo actually states:

- **Description**: a one-line, accurate summary of the proved result and the
  solver, not a marketing line. Named theorems over hedging, matching the
  brand-voice rule the sibling `awkronos-waddle` repository states explicitly
  (`AGENTS.md`: "Specific numbers, named theorems, named files. No hedging, no
  marketing words.").
- **Homepage**: `https://navier.awkronos.com/` — the live companion, never a
  second canonical claim competing with it.
- **Topics**: the terms a researcher or engineer would actually search —
  the formal-verification stack (`lean4`, `formal-verification`,
  `theorem-proving`, `mathlib`), the subject (`navier-stokes`,
  `partial-differential-equations`, `fluid-dynamics`), and the numerical
  companion (`rust`, `spectral-methods`, `cfd`). Topics are discovery
  metadata; they do not assert a result the README and the theorem types do
  not already assert.

## 3. `README.md` → `docs/` link discipline

`README.md` is the entry point; every document it links lives under `docs/`
or at the repository root and is reachable with a plain relative path (no
redirector, no shortlink). `docs/README.md` is the actual documentation
index — `README.md` links it once ("Documentation index") rather than
re-deriving the full table, so the index has exactly one place to grow.

Rule for adding a new `docs/*.md` file:

1. It is linked from `docs/README.md` under the correct section (current
   evidence, open frontier, or historical record) — an unlinked doc file is
   an orphan a reader cannot discover from the index.
2. If it is also load-bearing enough to belong in the root `README.md`
   (a result, a reproducibility step, or a construction boundary), link it
   there too, using the exact relative path a `make check`-style link audit
   can resolve.
3. Never link a path that does not exist yet "for later" — every link in
   this repository's markdown resolves today, checked by walking every
   `](...)` target in every tracked `.md` file and confirming the relative
   path exists (`https://`/`mailto:` targets are out of scope for that
   check; they are not this repository's to keep live).

## 4. The Polya relationship stays internal

[`docs/POLYA_MAP.md`](docs/POLYA_MAP.md) cross-references Polya Lean theorem
*names* (`Polya.Strategies.FixedPointBanach.apply`, and so on) against Navier
bridges. Those are Lean identifiers, not URLs — the document contains no
hyperlink to `polya.awkronos.com`.

That is deliberate, not an oversight: Polya is a single-owner, Clerk-gated
surface (`WADDLE_RELEASE_STATE.polya === "off"` in
`awkronos-waddle/packages/waddle-ids/src/public-switches.ts`), excluded from
every sitemap and disallowed in `robots.txt` on that host. A public
Navier document naming a theorem by its Lean identifier costs nothing and
asserts nothing about discoverability; a public document *linking* to
`polya.awkronos.com` would be the wrong direction for a surface that is
intentionally not indexed. If a future doc needs to cite Polya work, cite the
Lean name or the strategy file path, not a URL on that host.

## 5. CFSG

This repository has no content relationship with the `cfsg` (finite simple
group classification) proof project — the two are unrelated Lean
formalizations and no document here should imply a dependency between them.
Any `polya ↔ navier ↔ cfsg` cross-reference lives in `awkronos-waddle`
(where all three are waddle manifests, e.g. `apps/hub/app/cfsg-periodic-table/`),
not in this repository.
