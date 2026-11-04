# Citations — awkronos/navier

Structured, per-result citations for this repository: one entry per citable unit, in
the Awkronos citation carrier shape `{id, title, kind, authors, year, venue_or_status,
stable_link, cites, cited_by}` (schema `contracts/citation-schema.json`,
`schema_version: awkronos.citation-document.v1`).

Use `CITATION.cff` to cite the repository as a whole. Use a specific entry from the
block below to cite a *specific* result, and cite exactly what that entry's
`venue_or_status` says it is — no more.

## Conventions

**Identifier policy.** An id is stable content, not a moving pointer: ids are lowercase
(`^[a-z0-9][a-z0-9._:/+-]{2,}$`), never a line number, never a branch. Internal ids are
prefixed `navier.`; external ids are the literature identifier itself (`doi:…`,
`arxiv:…`), and manifest-derived external ids are prefixed `navier.manifest.` to show
that the repository's own `references/manifest.json` is what carries them.

**Stable links.** Every `stable_link` is either a commit-pinned permalink of a *tracked*
blob or tree (`/blob/<40-hex>/…`, `/tree/<40-hex>/…`), a DOI (`https://doi.org/…`), or an
arXiv abstract page (`https://arxiv.org/abs/…`). Branch-anchored URLs are not used: a
branch moves. Every internal link in this file is pinned to
`a4b066c6d26742a36e4f914b1ea56e2a6c88f12b` — the `origin/main` tip this document was
written against. Re-pin on fold; a rename adds an alias row rather than silently moving an id.

**Verbatim marks.** A straight double quote in this file means *repository text, verbatim*, with
only two normalisations: markdown link markup `[text](url)` is reduced to its text, and backticks,
`*` emphasis markers and runs of whitespace are stripped — the same normalisation the checker applies
to the blob, on both sides of the test. A quotation is always introduced by the `path:line` or
`path:line-line` range it was cut from, and a *sub-span* of a line is marked `span verbatim` when the
line around it (JSON, a ledger row) contains double quotes of its own that cannot be nested.
Single quotes and *italics* mark this document's own emphasis and are never a claim about repo text;
backticks mark a literal name — a path, a section, a field, a command — and are likewise not a
quotation. Two shapes are deliberately *not* read as single-quoted quotations by the delimiter leg,
because they are ordinary English rather than citation: a genitive apostrophe after a code span
(`RESULT_MAP.md`'s premise column) and a plural genitive (`entries' authors`). The leg excludes an
apostrophe opener that follows a letter or a backtick, and one followed by a bare `s`; a run of text
actually wrapped in single quotes still fails.
Every double-quoted span is re-found in the pinned blob by an independent checker (`Q`), and every
`path:line` claim is confirmed by locating the quoted span's line rather than by trusting the number
(`N`), so a right quotation at a wrong line number fails the gate. `Q` and `N` run over the whole
document — this header and the receipt included — and a negative control (`C`) mutates real spans to
prove the leg rejects them instead of accepting everything.

**Kinds.** `kind` is the carrier's enum, not the repository's. Internal units are graded from the
table cell that carries them; register sources are mapped by a fixed rule stated here once —
`journal_article → theorem`, `preprint → theorem`, `official_problem_statement → artifact` — and each
such entry names the register's own `type` value beside the mapped kind, so the mapping is auditable
rather than hidden.

**Epistemic vocabulary, and where it comes from.** `venue_or_status` states an epistemic
status, not a marketing status. The words are `proven`, `computed`, `open` and
`maintained artifact`, and each is sourced to this repository's own authorities rather
than to this document's judgement:

- `proven` — the repository's kernel-accepted theorem. The authority for the claim, and
  for the premises a theorem actually carries, is [`RESULT_MAP.md`](RESULT_MAP.md) (the
  authoritative claim-to-declaration map; its table header row `docs/RESULT_MAP.md:67` is
  "Claim | Proof-bearing declaration | Premise carried by its type | Fresh verification
  surface"); the authority for the raw axiom closure is
  `Navier/AxiomAudit.lean` (`#print axioms` receipts) and `Navier/ConditionalAudit.lean`,
  with the whole-tree `collectAxioms` sweep in `scripts/AuditAllAxioms.lean`.
- `proven as a CONDITIONAL theorem` — the statement is checked, and its premise is named
  verbatim from `RESULT_MAP.md`'s premise column. A conditional entry is never cited as an
  unconditional result, and this repository does not claim its antecedent is inhabited.
- `computed` — numerical evidence produced by a solver or a profile iteration, explicitly
  *not* the continuum proof.
- `open` — a formalised problem statement (the Clay alternatives A and B). An `open` entry
  is an **artifact**, never a theorem: what is checked there is the encoding, not the
  proposition.
- `maintained artifact` — a tooling or ledger object the repository keeps.

Axiom closures are quoted from the audit files; **nothing in this file was re-elaborated,
rebuilt or re-proved by the citation lane** (no Lean build seat was consumed). Where an
entry says a premise is carried by the statement type, that is a quotation of the
repository's own table, not an inference.

**Authorship.** Per-result entries carry `Awkronos` as author and `CITATION.cff` carries
the project-level `authors:` — `[A-CONFIRM]`, owner ruling **R-H** open, because a lane
must not synthesize a person-per-theorem attribution from commit metadata. The measured
basis is stated inside each entry (`venue_or_status`) rather than assumed. Every entry whose
author set is an organization alone repeats that reason in its own `venue_or_status`, marked
`org-only`, which is what the carrier's rule 3 requires: an org-alone list is refused unless
the entry says why.

**Zero self-citation of literature.** No entry in this file cites a work this repository
did not itself record. Where an entry has a `cites` edge, the target is either another
entry here or a source this repository carries in `references/manifest.json` or in its own
`docs/`, with the file and line named in the target's `venue_or_status`.

**Typed absences are recorded, not papered over.** Several works appear in this
repository's prose with an identifier only (surnames plus an arXiv id or DOI, with no
title, no given names, no venue pages). Those entries say so, and the ones with *no*
identifier at all in repo text are listed as prose-only gaps under
`Unresolved attributions` below, with no stable link invented. A plausible-looking wrong
identifier is worse than an absent one.

## Provenance and upstream attribution

The analytical construction adapted here is **OpenAI's**, not Awkronos's. The adapted
Lean modules under `Navier/Construction` come from `openai/NavierStokesAndEuler` at pinned
revision `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` (Apache-2.0; each adapted file names
the upstream source, pinned revision and license in its header) and accompany the OpenAI
release *Finite time blowup for Navier–Stokes*. The count is disclosed rather than smoothed:
this repository's provenance note prints docs/OPENAI_CONSTRUCTION_PROVENANCE.md:8, span verbatim — "577".  The same figure is repeated at
`docs/NATIVE_BREAKDOWN_AND_SOLVER.md:12` and `docs/PREPUBLICATION_REVIEW.md:35`, while
`git ls-tree` at this pin measures **579** tracked `.lean` files under
`Navier/Construction/`. Both numbers are printed because they differ; reconciling them is a
repository-owner act, not something a citation lane quietly picks a favourite of. Full boundary and verification detail:
[`OPENAI_CONSTRUCTION_PROVENANCE.md`](OPENAI_CONSTRUCTION_PROVENANCE.md). The
`license:` field of `CITATION.cff` is `[A-CONFIRM]` (owner ruling **R-I**): GitHub detects
`MIT`, while the adapted modules preserve `Apache-2.0` notices, so `MIT AND Apache-2.0` is
the measured-accurate SPDX expression if the repository prefers an expression over a
single id.

Awkronos's own contribution is the transport into the native PDE carrier, the additional
force-derivative comparisons, the solver work, and the interactive explanation.

## Reading the graph

`cites` lists the units/works an entry stands on; `cited_by` is its exact reverse, so the
two directions cannot disagree. An entry with `cites: []` and `cited_by: []` is either a
bibliography carrier (the manifest, which carries other entries' identifiers rather than
standing on them) or a work this repository's prose cites without any unit of its own
depending on it yet; `venue_or_status` names which.

The block below is machine-readable: it validates against `contracts/citation-schema.json`
as a `citation_document` (root entry, `how_to_cite` block, and every `citation_entry`).

```yaml
schema_version: awkronos.citation-document.v1
project: awkronos/navier
how_to_cite:
  title: >-
    Navier: Lean formalization of forced Navier–Stokes breakdown, unforced regularity frontiers, and a
    Rust spectral fluid solver
  authors:
  - name: Tim Jacoby
    role: person
  - name: Awkronos
    role: organization
  repository-code: https://github.com/awkronos/navier
  cff-mirror: >-
    CITATION.cff at the default branch, cff-version 1.2.0, is the machine-readable mirror of this block;
    per-result citations are the entries in docs/CITATIONS.md, and the prior-work bibliography is references/manifest.json.
  structured-list: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/docs/CITATIONS.md
citations:
- id: navier.candidate.r3-compact-candidate-exists
  title: A compact Euclidean candidate exists
  kind: theorem
  authors:
  - name: OpenAI
    role: organization
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:69, row of the "Completed forced path" table, cells verbatim: Claim "A compact
    Euclidean candidate exists" | Premise carried by its type "None" | Fresh verification surface "ConditionalAudit.lean;
    raw axioms". Declaration line Navier/Construction/R3ActualCandidate.lean:25-25 — "theorem selected_compact_candidate
    :" Namespace and file name differ and this entry pins the file: the declaration is Navier.Construction.R3CompactCandidate.selected_compact_candidate.
    Authorship measured from the carrier's own header, which carries an upstream attribution: "Adapted
    from OpenAI/NavierStokesAndEuler, revision" Typed absence, recorded rather than papered over: no #print
    axioms receipt at the pin names selected_compact_candidate in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean,
    and this lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Construction/R3ActualCandidate.lean
  cites:
  - navier.manifest.openai2026_forced_breakdown
  cited_by:
  - navier.candidate.compact-candidate-excludes-global-solution
  - navier.candidate.compact-candidate-unique-on-icc
  - navier.candidate.native-endpoint-transfer
- id: navier.candidate.compact-candidate-excludes-global-solution
  title: Every admissible global competitor contradicts that candidate
  kind: theorem
  authors:
  - name: OpenAI
    role: organization
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:70, row of the "Completed forced path" table, cells verbatim: Claim "Every admissible
    global competitor contradicts that candidate" | Premise carried by its type "An actual candidate and
    an actual GlobalSolutionRn competitor" | Fresh verification surface "ConditionalAudit.lean; raw axioms".
    Declaration line Navier/Construction/R3FiniteEnergyComparison.lean:84-84 — "theorem compact_candidate_excludes_global_solution"
    The contradiction this row records is the shape of the conditional statement, not a refutation of
    an unconditionally existing competitor. Authorship measured from the carrier's own header, which carries
    an upstream attribution: "Adapted from OpenAI/NavierStokesAndEuler, revision" Typed absence, recorded
    rather than papered over: no #print axioms receipt at the pin names compact_candidate_excludes_global_solution
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Construction/R3FiniteEnergyComparison.lean
  cites:
  - navier.candidate.r3-compact-candidate-exists
  cited_by: []
- id: navier.candidate.native-endpoint-transfer
  title: Euclidean construction data inhabit the native whole-space C carrier
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:71, row of the "Completed forced path" table, cells verbatim: Claim "Euclidean
    construction data inhabit the native whole-space C carrier" | Premise carried by its type "An actual
    compact candidate" | Fresh verification surface "ConditionalAudit.lean; raw axioms". Declaration line
    Navier/Breakdown/NativeConstructionEndpoint.lean:27-27 — "theorem wholeSpaceBreakdown_of_compactCandidate"
    Authorship measured, not synthesised: the first 16 lines of the pinned carrier carry neither an upstream-attribution
    line nor an original-work line, so this entry names only the organization whose repository holds the
    artifact; project-scope attribution is carried by CITATION.cff, and owner ruling R-H is still open.
    Typed absence, recorded rather than papered over: no #print axioms receipt at the pin names wholeSpaceBreakdown_of_compactCandidate
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Breakdown/NativeConstructionEndpoint.lean
  cites:
  - navier.candidate.r3-compact-candidate-exists
  cited_by: []
- id: navier.forced.whole-space-breakdown-c
  title: The selected construction proves C for every positive viscosity
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:72, row of the "Completed forced path" table, cells verbatim: Claim "The selected
    construction proves C for every positive viscosity" | Premise carried by its type "None" | Fresh verification
    surface "Direct single-file source compile plus raw axioms". Declaration line Navier/Breakdown/ConstructedBreakdown.lean:25-25
    — "theorem wholeSpaceBreakdown : Navier.ProblemStatements.WholeSpaceBreakdown := by"docs/OPEN_FRONTIER_MAP.md:10,
    row of the "Current boundary" table, cells verbatim: Surface "Forced whole-space alternative C" |
    Current status "THEOREM: ConstructedBreakdown.wholeSpaceBreakdown". Its Live edge cell opens "Optional
    follow-ups: sharper mechanism, force semantics, finite-time localization"; the cell continues on that
    line, so this is a quoted prefix and not the whole cell. The proposition it inhabits is this repository's
    own encoding, whose doc-comment reads Navier/OfficialProblem.lean:126-128 — "/-- Fefferman alternative
    C: for every positive viscosity, some admissible whole-space datum and admissible force admit no global
    smooth bounded-energy classical solution pair. -/" The same file states the reading boundary this
    entry must not be crossed past docs/OPEN_FRONTIER_MAP.md:43-46 — "The globally smooth object in the
    completed strengthened C result is the force. The selected velocity is classical before its singular
    deadline and cannot be continued as a global smooth bounded-energy solution. “Global smooth velocity”
    would describe A or B and must not be inferred from C." Upstream: the analytical construction is OpenAI's
    (docs/OPENAI_CONSTRUCTION_PROVENANCE.md, pinned revision 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538,
    Apache-2.0); Awkronos's contribution is the transport into the native PDE carrier. Authorship measured,
    not synthesised: the first 16 lines of the pinned carrier carry neither an upstream-attribution line
    nor an original-work line, so this entry names only the organization whose repository holds the artifact;
    project-scope attribution is carried by CITATION.cff, and owner ruling R-H is still open. Typed absence,
    recorded rather than papered over: no #print axioms receipt at the pin names wholeSpaceBreakdown in
    Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Breakdown/ConstructedBreakdown.lean
  cites:
  - navier.manifest.fefferman2000
  - navier.manifest.openai2026_forced_breakdown
  - navier.manifest.leray1934
  - navier.force.coordinate-partial-equivalence
  cited_by:
  - navier.bkm.sharp-pair
  - navier.force.globally-smooth-extension
  - navier.forced.deadline-parameterised-c
  - navier.forced.scaled-deadline-t-profile
  - navier.forced.selected-finite-energy-candidate
  - navier.forced.successive-partials-form
  - navier.obstruction.excludes-locally-finite-energy-continuation
  - navier.obstruction.force-compact-physical-support
  - navier.obstruction.force-nonzero-before-one
  - navier.obstruction.speed-blowup-in-every-competitor
- id: navier.force.globally-smooth-extension
  title: The chosen force is smooth on all real spacetime and has an explicit half-space extension
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:73, row of the "Completed forced path" table, cells verbatim: Claim "The chosen
    force is smooth on all real spacetime and has an explicit half-space extension" | Premise carried
    by its type "None" | Fresh verification surface "ConditionalAudit.lean; raw axioms". Declaration line
    Navier/Analysis/ConstructedForceExtension.lean:109-109 — "theorem constructedWholeSpaceBreakdownWithGloballySmoothForce
    :" Authorship measured, not synthesised: the first 16 lines of the pinned carrier carry neither an
    upstream-attribution line nor an original-work line, so this entry names only the organization whose
    repository holds the artifact; project-scope attribution is carried by CITATION.cff, and owner ruling
    R-H is still open. Typed absence, recorded rather than papered over: no #print axioms receipt at the
    pin names constructedWholeSpaceBreakdownWithGloballySmoothForce in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean,
    and this lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/ConstructedForceExtension.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by:
  - navier.obstruction.selected-finite-time-profile
- id: navier.forced.successive-partials-form
  title: >-
    Every ordered successive coordinate derivative of the chosen force obeys the required weighted bound
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:74, row of the "Completed forced path" table, cells verbatim: Claim "Every ordered
    successive coordinate derivative of the chosen force obeys the required weighted bound" | Premise
    carried by its type "nu > 0" | Fresh verification surface "ConditionalAudit.lean; raw axioms". Declaration
    line Navier/Breakdown/ConstructedBreakdown.lean:43-43 — "theorem wholeSpaceBreakdown_with_successivePartials
    (ν : ℝ) (hν : 0 < ν) :" Reading of that premise cell: `nu > 0` names the theorem's own bound variable
    — the viscosity is universally quantified in the source — so the row records no consumed external
    assumption. Authorship measured, not synthesised: the first 16 lines of the pinned carrier carry neither
    an upstream-attribution line nor an original-work line, so this entry names only the organization
    whose repository holds the artifact; project-scope attribution is carried by CITATION.cff, and owner
    ruling R-H is still open. Typed absence, recorded rather than papered over: no #print axioms receipt
    at the pin names wholeSpaceBreakdown_with_successivePartials in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean,
    and this lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Breakdown/ConstructedBreakdown.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by: []
- id: navier.force.coordinate-partial-equivalence
  title: >-
    The formal Fréchet-bundle force condition is equivalent to smoothness plus decay of every genuine
    ordered coordinate partial
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:75, row of the "Completed forced path" table, cells verbatim: Claim "The formal
    Fréchet-bundle force condition is equivalent to smoothness plus decay of every genuine ordered coordinate
    partial" | Premise carried by its type "A concrete force f; smoothness is explicit on the coordinate-partial
    side" | Fresh verification surface "Direct single-file compile plus raw axioms". Declaration line
    Navier/Analysis/ForceCoordinateEquivalence.lean:147-147 — "theorem forcedDataRapidDecay_iff_successivePartials
    (f : ForceField) :" Authorship measured, not synthesised: the first 16 lines of the pinned carrier
    carry neither an upstream-attribution line nor an original-work line, so this entry names only the
    organization whose repository holds the artifact; project-scope attribution is carried by CITATION.cff,
    and owner ruling R-H is still open. Typed absence, recorded rather than papered over: no #print axioms
    receipt at the pin names forcedDataRapidDecay_iff_successivePartials in Navier/AxiomAudit.lean or
    Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat, so this entry quotes no axiom
    closure for it. org-only author set: this repository's carriers record no per-result attribution (the
    file headers name the project, and CITATION.cff carries the project-level authors), and owner ruling
    R-H on that person list is still open — so naming an individual for this result would be invented,
    not measured. Per-result entries therefore carry the organization, and the mapping is the repository
    owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/ForceCoordinateEquivalence.lean
  cites:
  - navier.manifest.openai2026_forced_breakdown
  cited_by:
  - navier.forced.whole-space-breakdown-c
- id: navier.obstruction.force-compact-physical-support
  title: >-
    The selected globally smooth force has compact support on physical spacetime and vanishes after a
    finite time
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:76, row of the "Completed forced path" table, cells verbatim: Claim "The selected
    globally smooth force has compact support on physical spacetime and vanishes after a finite time"
    | Premise carried by its type "None; spatial support is asserted for t ≥ 0, with a finite future cutoff"
    | Fresh verification surface "Direct single-file source compile plus raw axioms". Declaration line
    Navier/Analysis/ConstructedFiniteTimeObstruction.lean:272-272 — "theorem selected_force_has_compact_physical_support
    :" Reading of that premise cell: the word 'asserted' qualifies which half of the claim is bounded
    (the spatial clause is stated on t ≥ 0), not whether the row is proved — the row's grading is its
    Claim cell, quoted above. Authorship measured, not synthesised: the first 16 lines of the pinned carrier
    carry neither an upstream-attribution line nor an original-work line, so this entry names only the
    organization whose repository holds the artifact; project-scope attribution is carried by CITATION.cff,
    and owner ruling R-H is still open. Typed absence, recorded rather than papered over: no #print axioms
    receipt at the pin names selected_force_has_compact_physical_support in Navier/AxiomAudit.lean or
    Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat, so this entry quotes no axiom
    closure for it. org-only author set: this repository's carriers record no per-result attribution (the
    file headers name the project, and CITATION.cff carries the project-level authors), and owner ruling
    R-H on that person list is still open — so naming an individual for this result would be invented,
    not measured. Per-result entries therefore carry the organization, and the mapping is the repository
    owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/ConstructedFiniteTimeObstruction.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by: []
- id: navier.obstruction.force-nonzero-before-one
  title: The selected force is nonzero somewhere strictly before the unit-viscosity deadline
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:77, row of the "Completed forced path" table, cells verbatim: Claim "The selected
    force is nonzero somewhere strictly before the unit-viscosity deadline" | Premise carried by its type
    "None; ∃ t ∈ (0,1), ∃ x, f(t,x) ≠ 0" | Fresh verification surface "Direct single-file source compile
    plus raw axioms". Declaration line Navier/Analysis/ConstructedFiniteTimeObstruction.lean:426-426 —
    "theorem selected_force_nonzero_before_one :" Authorship measured, not synthesised: the first 16 lines
    of the pinned carrier carry neither an upstream-attribution line nor an original-work line, so this
    entry names only the organization whose repository holds the artifact; project-scope attribution is
    carried by CITATION.cff, and owner ruling R-H is still open. Typed absence, recorded rather than papered
    over: no #print axioms receipt at the pin names selected_force_nonzero_before_one in Navier/AxiomAudit.lean
    or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat, so this entry quotes no
    axiom closure for it. org-only author set: this repository's carriers record no per-result attribution
    (the file headers name the project, and CITATION.cff carries the project-level authors), and owner
    ruling R-H on that person list is still open — so naming an individual for this result would be invented,
    not measured. Per-result entries therefore carry the organization, and the mapping is the repository
    owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/ConstructedFiniteTimeObstruction.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by: []
- id: navier.forced.selected-finite-energy-candidate
  title: The selected unit-viscosity candidate has uniformly finite energy before its deadline
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:78, row of the "Completed forced path" table, cells verbatim: Claim "The selected
    unit-viscosity candidate has uniformly finite energy before its deadline" | Premise carried by its
    type "None; interval is Set.Ico 0 1" | Fresh verification surface "ConditionalAudit.lean; raw axioms".
    Declaration line Navier/Breakdown/ConstructedBreakdown.lean:30-30 — "theorem selectedFiniteEnergyCandidate
    :" Authorship measured, not synthesised: the first 16 lines of the pinned carrier carry neither an
    upstream-attribution line nor an original-work line, so this entry names only the organization whose
    repository holds the artifact; project-scope attribution is carried by CITATION.cff, and owner ruling
    R-H is still open. Typed absence, recorded rather than papered over: no #print axioms receipt at the
    pin names selectedFiniteEnergyCandidate in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean,
    and this lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Breakdown/ConstructedBreakdown.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by: []
- id: navier.obstruction.selected-finite-time-profile
  title: >-
    One selected witness simultaneously has a globally smooth force, pre-singular finite energy, compact
    spatial support, no continuous terminal extension on its support, and slab uniqueness
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:79, row of the "Completed forced path" table, cells verbatim: Claim "One selected
    witness simultaneously has a globally smooth force, pre-singular finite energy, compact spatial support,
    no continuous terminal extension on its support, and slab uniqueness" | Premise carried by its type
    "None" | Fresh verification surface "Dependency-ordered source rebuild plus raw axioms". Declaration
    line Navier/Analysis/ConstructedFiniteTimeObstruction.lean:290-290 — "theorem selected_candidate_finite_time_profile
    :" Authorship measured, not synthesised: the first 16 lines of the pinned carrier carry neither an
    upstream-attribution line nor an original-work line, so this entry names only the organization whose
    repository holds the artifact; project-scope attribution is carried by CITATION.cff, and owner ruling
    R-H is still open. Typed absence, recorded rather than papered over: no #print axioms receipt at the
    pin names selected_candidate_finite_time_profile in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean,
    and this lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/ConstructedFiniteTimeObstruction.lean
  cites:
  - navier.force.globally-smooth-extension
  - navier.obstruction.speed-blowup-in-every-competitor
  cited_by: []
- id: navier.candidate.compact-candidate-unique-on-icc
  title: >-
    Every compact candidate is unique against a smooth finite-energy competitor on a closed pre-singular
    slab
  kind: theorem
  authors:
  - name: OpenAI
    role: organization
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:80, row of the "Completed forced path" table, cells verbatim: Claim "Every compact
    candidate is unique against a smooth finite-energy competitor on a closed pre-singular slab" | Premise
    carried by its type "Candidate properties and the competitor's local smoothness, energy, divergence,
    PDE and zero initial data on that slab" | Fresh verification surface "Dependency-ordered source rebuild
    plus raw axioms". Declaration line Navier/Construction/R3FiniteEnergyComparison.lean:46-46 — "theorem
    compact_candidate_unique_on_Icc" Cite this entry as the conditional it is: the premise cell names
    what the statement carries, and this repository claims no unconditional uniqueness theorem. Authorship
    measured from the carrier's own header, which carries an upstream attribution: "Adapted from OpenAI/NavierStokesAndEuler,
    revision" Typed absence, recorded rather than papered over: no #print axioms receipt at the pin names
    compact_candidate_unique_on_Icc in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this
    lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only author set:
    this repository's carriers record no per-result attribution (the file headers name the project, and
    CITATION.cff carries the project-level authors), and owner ruling R-H on that person list is still
    open — so naming an individual for this result would be invented, not measured. Per-result entries
    therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Construction/R3FiniteEnergyComparison.lean
  cites:
  - navier.candidate.r3-compact-candidate-exists
  cited_by: []
- id: navier.obstruction.speed-blowup-in-every-competitor
  title: >-
    Every same-force competitor smooth before time one and finite-energy on each closed earlier slab develops
    unbounded speed at that deadline
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:81, row of the "Completed forced path" table, cells verbatim: Claim "Every same-force
    competitor smooth before time one and finite-energy on each closed earlier slab develops unbounded
    speed at that deadline" | Premise carried by its type "None for the selected witness; the competitor
    class is explicit and no terminal trace is assumed" | Fresh verification surface "Direct single-file
    source compile plus raw axioms". Declaration line Navier/Analysis/ConstructedFiniteTimeObstruction.lean:402-402
    — "theorem selected_candidate_forces_speed_blowup_in_every_smooth_competitor :" Authorship measured,
    not synthesised: the first 16 lines of the pinned carrier carry neither an upstream-attribution line
    nor an original-work line, so this entry names only the organization whose repository holds the artifact;
    project-scope attribution is carried by CITATION.cff, and owner ruling R-H is still open. Typed absence,
    recorded rather than papered over: no #print axioms receipt at the pin names selected_candidate_forces_speed_blowup_in_every_smooth_competitor
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/ConstructedFiniteTimeObstruction.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by:
  - navier.bkm.no-control-in-every-competitor
  - navier.bkm.selected-candidate-admits-no-control
  - navier.obstruction.selected-finite-time-profile
- id: navier.obstruction.excludes-locally-finite-energy-continuation
  title: >-
    The selected witness excludes a same-force continuation smooth before the deadline and continuous
    through it, even when energy is assumed only separately on each closed pre-singular slab
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:82, row of the "Completed forced path" table, cells verbatim: Claim "The selected
    witness excludes a same-force continuation smooth before the deadline and continuous through it, even
    when energy is assumed only separately on each closed pre-singular slab" | Premise carried by its
    type "None" | Fresh verification surface "Direct single-file source compile plus raw axioms". Declaration
    line Navier/Analysis/ConstructedFiniteTimeObstruction.lean:440-440 — "theorem selected_candidate_excludes_locally_finite_energy_continuation
    :" Authorship measured, not synthesised: the first 16 lines of the pinned carrier carry neither an
    upstream-attribution line nor an original-work line, so this entry names only the organization whose
    repository holds the artifact; project-scope attribution is carried by CITATION.cff, and owner ruling
    R-H is still open. Typed absence, recorded rather than papered over: no #print axioms receipt at the
    pin names selected_candidate_excludes_locally_finite_energy_continuation in Navier/AxiomAudit.lean
    or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat, so this entry quotes no
    axiom closure for it. org-only author set: this repository's carriers record no per-result attribution
    (the file headers name the project, and CITATION.cff carries the project-level authors), and owner
    ruling R-H on that person list is still open — so naming an individual for this result would be invented,
    not measured. Per-result entries therefore carry the organization, and the mapping is the repository
    owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/ConstructedFiniteTimeObstruction.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by: []
- id: navier.bkm.selected-candidate-admits-no-control
  title: The selected candidate admits no Beale–Kato–Majda control bundle on [0,1)
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:83, row of the "Completed forced path" table, cells verbatim: Claim "The selected
    candidate admits no Beale–Kato–Majda control bundle on [0,1)" | Premise carried by its type "None;
    the refutation consumes the candidate's own speed_unbounded field" | Fresh verification surface "Direct
    single-file source compile plus raw axioms". Declaration line Navier/Analysis/BKMForcedBreakdownNecessity.lean:187-187
    — "theorem selected_candidate_admits_no_BKM_control :" Authorship measured, not synthesised: the first
    16 lines of the pinned carrier carry neither an upstream-attribution line nor an original-work line,
    so this entry names only the organization whose repository holds the artifact; project-scope attribution
    is carried by CITATION.cff, and owner ruling R-H is still open. Typed absence, recorded rather than
    papered over: no #print axioms receipt at the pin names selected_candidate_admits_no_BKM_control in
    Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/BKMForcedBreakdownNecessity.lean
  cites:
  - navier.bkm.sharp-pair
  - navier.obstruction.speed-blowup-in-every-competitor
  cited_by:
  - navier.bkm.no-control-in-every-competitor
- id: navier.bkm.no-control-in-every-competitor
  title: >-
    Every same-force competitor smooth before time one and finite-energy on each closed earlier slab admits
    no Beale–Kato–Majda control bundle on [0,1)
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:84, row of the "Completed forced path" table, cells verbatim: Claim "Every same-force
    competitor smooth before time one and finite-energy on each closed earlier slab admits no Beale–Kato–Majda
    control bundle on [0,1)" | Premise carried by its type "None for the selected witness; the competitor
    class is identical to the speed-blowup row's" | Fresh verification surface "Direct single-file source
    compile plus raw axioms". The file's own scope section, headed Navier/Analysis/BKMForcedBreakdownNecessity.lean:30-38
    — "## Pattern-A scope, stated once What is proved: ¬ Nonempty (BKMControl (uncurry v) 1) for every
    competitor v in the class, and for the candidate itself. What is not claimed: the divergence ∫₀¹ ‖ω(t)‖∞
    dt = ∞ of the constructed field. Residual (OPEN, named): constructing any BKMControl rate/gronwall
    pair for the selected candidate would need Sobolev–Grönwall control inputs the repository does not
    supply for this profile; this file refutes the control bundle, which is the exact hypothesis the criterion
    consumes, and nothing stronger."docs/OPEN_FRONTIER_MAP.md:12, row of the "Current boundary" table,
    cells verbatim: Surface "BKM criterion at the constructed breakdown" | Current status "THEOREM: BKMForcedBreakdownNecessity.selected_candidate_forces_no_BKM_control_in_every_smooth_competitor".
    Its Live edge cell opens "The criterion's hypothesis is refuted for every admissible profile of the
    proved blow-up mechanism, so it cannot be weakened and remain consumable at this endpoint"; the cell
    continues on that line, so this is a quoted prefix and not the whole cell. Authorship measured, not
    synthesised: the first 16 lines of the pinned carrier carry neither an upstream-attribution line nor
    an original-work line, so this entry names only the organization whose repository holds the artifact;
    project-scope attribution is carried by CITATION.cff, and owner ruling R-H is still open. Typed absence,
    recorded rather than papered over: no #print axioms receipt at the pin names selected_candidate_forces_no_BKM_control_in_every_smooth_competitor
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/BKMForcedBreakdownNecessity.lean
  cites:
  - navier.bkm.sharp-pair
  - navier.bkm.selected-candidate-admits-no-control
  - navier.obstruction.speed-blowup-in-every-competitor
  cited_by:
  - navier.bkm.vorticity-integral-divergence-conditional
- id: navier.forced.scaled-deadline-t-profile
  title: >-
    For every viscosity and every prescribed deadline there is a parabolically rescaled candidate whose
    classical evolution has uniformly finite energy before the deadline and unbounded speed at it
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:85, row of the "Completed forced path" table, cells verbatim: Claim "For every
    viscosity and every prescribed deadline there is a parabolically rescaled candidate whose classical
    evolution has uniformly finite energy before the deadline and unbounded speed at it" | Premise carried
    by its type "None; the deadline enters through λ = T^(−1/2) with proved endpoint law deadlineOf λ
    = T" | Fresh verification surface "Direct single-file source compile plus raw axioms". Declaration
    line Navier/Analysis/ScaledConstructedBreakdown.lean:585-585 — "theorem exists_deadlineT_profile (T
    : ℝ) (hT : 0 < T) :" Authorship measured, not synthesised: the first 16 lines of the pinned carrier
    carry neither an upstream-attribution line nor an original-work line, so this entry names only the
    organization whose repository holds the artifact; project-scope attribution is carried by CITATION.cff,
    and owner ruling R-H is still open. Typed absence, recorded rather than papered over: no #print axioms
    receipt at the pin names exists_deadlineT_profile in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean,
    and this lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/ScaledConstructedBreakdown.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by:
  - navier.forced.deadline-parameterised-c
- id: navier.forced.deadline-parameterised-c
  title: >-
    Alternative C holds at every prescribed positive deadline: for every ν > 0 and T > 0 there is a rapidly
    decaying smooth force, vanishing for t ≥ T₀·T and nonzero at some t ∈ (0,T), admitting no global classical
    solution
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/RESULT_MAP.md:86, row of the "Completed forced path" table, cells verbatim: Claim "Alternative
    C holds at every prescribed positive deadline: for every ν > 0 and T > 0 there is a rapidly decaying
    smooth force, vanishing for t ≥ T₀·T and nonzero at some t ∈ (0,T), admitting no global classical
    solution" | Premise carried by its type "None; T₀ is the existential raw-candidate endpoint from CompactFutureTimeSupport,
    so the support endpoint is the proved law T₀·T, not the asserted bound T" | Fresh verification surface
    "Direct single-file source compile plus raw axioms". Declaration line Navier/Breakdown/DeadlineParameterizedWholeSpaceBreakdown.lean:538-538
    — "theorem wholeSpaceBreakdown_deadlineT (nu T : ℝ)"docs/OPEN_FRONTIER_MAP.md:11, row of the "Current
    boundary" table, cells verbatim: Surface "Deadline-parameterized forced alternative C" | Current status
    "THEOREM: DeadlineParameterizedWholeSpaceBreakdown.wholeSpaceBreakdown_deadlineT". Its Live edge cell
    opens "Proved for every ν > 0 and every prescribed T > 0"; the cell continues on that line, so this
    is a quoted prefix and not the whole cell. Authorship measured, not synthesised: the first 16 lines
    of the pinned carrier carry neither an upstream-attribution line nor an original-work line, so this
    entry names only the organization whose repository holds the artifact; project-scope attribution is
    carried by CITATION.cff, and owner ruling R-H is still open. Typed absence, recorded rather than papered
    over: no #print axioms receipt at the pin names wholeSpaceBreakdown_deadlineT in Navier/AxiomAudit.lean
    or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat, so this entry quotes no
    axiom closure for it. org-only author set: this repository's carriers record no per-result attribution
    (the file headers name the project, and CITATION.cff carries the project-level authors), and owner
    ruling R-H on that person list is still open — so naming an individual for this result would be invented,
    not measured. Per-result entries therefore carry the organization, and the mapping is the repository
    owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Breakdown/DeadlineParameterizedWholeSpaceBreakdown.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  - navier.forced.scaled-deadline-t-profile
  cited_by: []
- id: navier.forced.periodic-breakdown-d
  title: Periodic breakdown D
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/OPEN_FRONTIER_MAP.md:40, row of the "Current boundary" table, cells verbatim: Surface "Periodic
    breakdown D" | Current status "THEOREM: PeriodicConstructedBreakdown.periodicBreakdown". Its Live
    edge cell opens "The native periodic forced endpoint has no remaining premise"; the cell continues
    on that line, so this is a quoted prefix and not the whole cell. Checked bearer Navier/Analysis/PeriodicConstructedBreakdown.lean:203-203
    — "theorem periodicBreakdown : ProblemStatements.PeriodicBreakdown := by" The proposition it inhabits,
    whose doc-comment reads Navier/OfficialProblem.lean:136-138 — "/-- Fefferman alternative D: for every
    positive viscosity, some admissible periodic datum and periodic time-decaying force admit no global
    smooth periodic solution pair. No whole-space energy condition occurs. -/" Definition Navier/OfficialProblem.lean:139-139
    — "def PeriodicBreakdown : Prop :="See navier.problem.periodic-global-regularity-b for the unforced
    alternative this endpoint does not settle. Authorship measured, not synthesised: the first 16 lines
    of the pinned carrier carry neither an upstream-attribution line nor an original-work line, so this
    entry names only the organization whose repository holds the artifact; project-scope attribution is
    carried by CITATION.cff, and owner ruling R-H is still open. Typed absence, recorded rather than papered
    over: no #print axioms receipt at the pin names periodicBreakdown in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean,
    and this lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/PeriodicConstructedBreakdown.lean
  cites:
  - navier.manifest.openai2026_forced_breakdown
  - navier.manifest.fefferman2000
  cited_by: []
- id: navier.madelung.scalar-lift-falsified
  title: Scalar Madelung route for the lift
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/OPEN_FRONTIER_MAP.md:39, row of the "Current boundary" table, cells verbatim: Surface "Scalar
    Madelung route for the lift" | Current status "FALSIFIED (kernel, decoder level): Analysis.MadelungDecoderCurlObstruction.no_scalar_madelung_initial_lift_of_rotational_data".
    Its Live edge cell opens "No C^∞ scalar wavefunction nonzero at the origin decodes any rotational
    datum λ > 0 — including the compactly supported, divergence-free rotationalDatum λ with |u| ≤ λ <
    ν₀/16 (2026-09-11)"; the cell continues on that line, so this is a quoted prefix and not the whole
    cell. Declaration Navier/Analysis/MadelungDecoderCurlObstruction.lean:516-518 — "theorem no_scalar_madelung_initial_lift_of_rotational_data
    (lam : ℝ) (hlam : 0 < lam) : ¬ ∃ (κ : ℝ) (ψ : Space → ℂ), ContDiff ℝ ∞ ψ ∧ ψ 0 ≠ 0 ∧ MadelungInitialDecoder
    κ ψ ⇑(rotationalDatum lam) := by" docs/RESULT_MAP.md records the same counterexample in prose docs/RESULT_MAP.md:352-359
    — "Navier/Analysis/MadelungDecoderCurlObstruction.lean proves, on the crown SchwartzVelocity carrier
    and under strict axioms, that no C^∞ scalar wavefunction nonzero at the origin decodes any rotational
    datum λ > 0 — the compactly supported, divergence-free rotationalDatum λ with |u| ≤ λ < ν₀/16 is the
    counterexample — so the scalar route cannot carry the small-data lift. The remaining transport obligations
    {PDE, forcing, energy class} are located in the whole-space ScaledCutoff family." Cite it only as
    the decoder-level obstruction it is: it falsifies one route and settles neither alternative A nor
    B. The empty cites array claims independence of the other entries in this document, which is true
    in that narrow sense; it does not claim the work stood on nothing, and its carrier's prior art is
    recorded in navier.madelung.regularity-comparison. Authorship measured, not synthesised: the first
    16 lines of the pinned carrier carry neither an upstream-attribution line nor an original-work line,
    so this entry names only the organization whose repository holds the artifact; project-scope attribution
    is carried by CITATION.cff, and owner ruling R-H is still open. Typed absence, recorded rather than
    papered over: no #print axioms receipt at the pin names no_scalar_madelung_initial_lift_of_rotational_data
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/MadelungDecoderCurlObstruction.lean
  cites: []
  cited_by:
  - navier.madelung.regularity-comparison
- id: navier.upstream.euler-breakdown
  title: Unforced 3-D Euler blowup (upstream, not adapted here)
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    docs/OPEN_FRONTIER_MAP.md:41, row of the "Current boundary" table, cells verbatim: Surface "Unforced
    3-D Euler blowup (upstream, not adapted here)" | Current status "THEOREM (upstream): Euler.euler_breakdown_R3,
    Euler.exists_compact_smooth_euler_singularity [OPENAI2026_EULER]; this repository re-verified the
    upstream build clean on 2026-09-13". Its Live edge cell opens "Different carrier: the Euler model
    is quarantined for A/B (BARRIERS.md §5) and no transfer theorem exists"; the cell continues on that
    line, so this is a quoted prefix and not the whole cell. Upstream, not adapted here: the declarations
    that row names, Euler.euler_breakdown_R3 and Euler.exists_compact_smooth_euler_singularity, belong
    to the pinned upstream release and are NOT declarations of this repository (no Navier/Euler.lean is
    tracked at the pin — measured by git cat-file, and recorded as a typed absence rather than cited as
    an in-repo carrier). The provenance note pins the upstream head it was checked against docs/OPENAI_CONSTRUCTION_PROVENANCE.md:36-36
    — "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538 to head f9e8bc5b38b6e212696e8a30e3e91517af887bbd" Authorship
    measured, not synthesised: the first 16 lines of the pinned carrier carry neither an upstream-attribution
    line nor an original-work line, so this entry names only the organization whose repository holds the
    artifact; project-scope attribution is carried by CITATION.cff, and owner ruling R-H is still open.
    Typed absence, recorded rather than papered over: no #print axioms receipt at the pin names euler_breakdown_R3
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/docs/OPEN_FRONTIER_MAP.md
  cites:
  - navier.manifest.openai2026_euler
  cited_by: []
- id: navier.bkm.sharp-pair
  title: >-
    The Beale–Kato–Majda criterion as one sharp pair: sufficiency, non-vacuity and endpoint necessity
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    proven — kernel-accepted, as named legs in one carrier file. Sufficiency, from the file's own doc-comment
    Navier/Analysis/BealeKatoMajda.lean:215-216 — "/-- BKM continuation: finite vorticity integral ⟹ the
    velocity stays uniformly bounded on [0,T). No pointwise blow-up occurs before T. -/" The engine it
    runs on Navier/Analysis/BealeKatoMajda.lean:26-27 — "PDE quantity. This is a fully unconditional real-analysis
    theorem (propext, Classical.choice, Quot.sound only)." Non-vacuity, in the file's own words Navier/Analysis/BealeKatoMajda.lean:36-37
    — "converges — a genuine restriction, not forced by continuity, so the criterion is non-vacuous even
    though blow-up of ω at T is permitted). From it," Declarations: velocity_bounded Navier/Analysis/BealeKatoMajda.lean:217-217
    — "theorem velocity_bounded (c : BKMControl u T) (hT : 0 < T) :"; excludes_pointEvaluationBreakdown
    Navier/Analysis/BealeKatoMajda.lean:252-252 — "theorem excludes_pointEvaluationBreakdown"; controlZero
    Navier/Analysis/BealeKatoMajda.lean:266-266 — "def controlZero (T : ℝ) : BKMControl (fun _ _ => 0)
    T where". Authorship measured, not synthesised: the first 16 lines of the pinned carrier carry neither
    an upstream-attribution line nor an original-work line, so this entry names only the organization
    whose repository holds the artifact; project-scope attribution is carried by CITATION.cff, and owner
    ruling R-H is still open. Endpoint necessity at the constructed breakdown is carried by navier.bkm.selected-candidate-admits-no-control
    and navier.bkm.no-control-in-every-competitor, not by this entry. Typed absence, recorded rather than
    papered over: no #print axioms receipt at the pin names Navier.Analysis.BKMControl.velocity_bounded
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/BealeKatoMajda.lean
  cites:
  - navier.forced.whole-space-breakdown-c
  cited_by:
  - navier.bkm.no-control-in-every-competitor
  - navier.bkm.selected-candidate-admits-no-control
- id: navier.bkm.vorticity-integral-divergence-conditional
  title: >-
    Vorticity-integral divergence for the selected profile, conditional on a Grönwall control pair
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    proven as a conditional theorem, and the file states its own limit. Line 2 Navier/Analysis/BKMVorticityIntegralDivergence.lean:2-2
    — "Original work, lane L6b, 2026-09-13. Adapted carriers are imported, not copied." The module's own
    scope limit Navier/Analysis/BKMVorticityIntegralDivergence.lean:37-41 — "WHAT THIS MODULE DOES NOT
    PROVE: it does not construct the Grönwall control pair (Y, Y') — positive continuous Y with derivative
    Y' on Ioo 0 1 satisfying Y' ≤ V u · Y and ‖uncurry u t x‖ ≤ Y t. That pair is the named missing primitive
    (the row's residual); every divergence theorem above is conditional on it. The carrier equivalences
    ofReal (V u t) = vorticityRate" Declarations: vorticity_integral_divergence Navier/Analysis/BKMVorticityIntegralDivergence.lean:472-472
    — "theorem vorticity_integral_divergence {u p f : _} (h : Properties u p f)"; lintegral_vorticity_integral_divergence
    Navier/Analysis/BKMVorticityIntegralDivergence.lean:490-490 — "theorem lintegral_vorticity_integral_divergence
    {u p f : _} (h : Properties u p f)"; bkmVorticityControl_eq_top Navier/Analysis/BKMVorticityIntegralDivergence.lean:579-579
    — "theorem bkmVorticityControl_eq_top {u p f : _} (h : Properties u p f)" Authorship measured from
    the carrier's own header, which claims original work: "Original work, lane L6b, 2026-09-13. Adapted
    carriers are imported, not copied." The decomposition the frontier table records for this residual
    — module by module, with declaration counts — is quoted in navier.bkm.no-control-in-every-competitor.
    Typed absence, recorded rather than papered over: no #print axioms receipt at the pin names Navier.Analysis.vorticity_integral_divergence
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/BKMVorticityIntegralDivergence.lean
  cites:
  - navier.bkm.no-control-in-every-competitor
  cited_by: []
- id: navier.periodic.classical-uniqueness
  title: >-
    Periodic classical uniqueness: equality of velocities at every positive viscosity under the native
    classical contract
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    proven, and the repository states the scope it does not reach. docs/RESULT_MAP.md docs/RESULT_MAP.md:31-36
    — "open. A new periodic classical uniqueness theorem proves equality of velocities at every positive
    viscosity under the native classical contract, including periodic velocity and periodic pressure.
    It consumes an assumed B witness to attach this proved uniqueness conclusion; it does not discharge
    B's existence premise. No equality of pressures is claimed, since a spatially constant pressure gauge
    remains free." The file's own closing note Navier/Analysis/PeriodicClassicalUniqueness.lean:15-16
    — "This closes the uniqueness consequence of alternative B. It does not supply the existence assertion
    in ProblemStatements.PeriodicGlobalRegularity." Declarations: velocity_unique_at_viscosity_one Navier/Analysis/PeriodicClassicalUniqueness.lean:106-106
    — "theorem velocity_unique_at_viscosity_one"; velocity_unique Navier/Analysis/PeriodicClassicalUniqueness.lean:139-139
    — "theorem velocity_unique"; periodicGlobalRegularity_uniqueVelocity Navier/Analysis/PeriodicClassicalUniqueness.lean:172-172
    — "theorem periodicGlobalRegularity_uniqueVelocity". Authorship measured, not synthesised: the first
    16 lines of the pinned carrier carry neither an upstream-attribution line nor an original-work line,
    so this entry names only the organization whose repository holds the artifact; project-scope attribution
    is carried by CITATION.cff, and owner ruling R-H is still open. No equality of pressures is claimed.
    This is a uniqueness consequence of alternative B and consumes an assumed B witness, which is why
    its cites edge lands on the problem statement rather than on a result. Typed absence, recorded rather
    than papered over: no #print axioms receipt at the pin names Navier.Analysis.PeriodicClassicalUniqueness.velocity_unique
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/PeriodicClassicalUniqueness.lean
  cites:
  - navier.problem.periodic-global-regularity-b
  cited_by: []
- id: navier.madelung.regularity-comparison
  title: A smooth wavefunction can have singular decoded phase velocity
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    proven — kernel-accepted. Declaration: norm_le_of_madelung_pairing Navier/Analysis/QuantumVortexRegularity.lean:35-35
    — "theorem norm_le_of_madelung_pairing". Authorship measured, not synthesised: the first 16 lines
    of the pinned carrier carry neither an upstream-attribution line nor an original-work line, so this
    entry names only the organization whose repository holds the artifact; project-scope attribution is
    carried by CITATION.cff, and owner ruling R-H is still open. Scope, as the repository records it:
    this comparison inhabits neither alternative A nor B, and the quantization material says the same
    of itself (see navier.madelung.winding-quantization). The scalar Madelung route's own falsification
    is a separate unit, navier.madelung.scalar-lift-falsified. The 1926 Madelung attribution that this
    correspondence rests on appears in repo prose with NO identifier, so it is recorded as a typed absence
    under 'Unresolved attributions' below rather than given a link here. Typed absence, recorded rather
    than papered over: no #print axioms receipt at the pin names norm_le_of_madelung_pairing in Navier/AxiomAudit.lean
    or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat, so this entry quotes no
    axiom closure for it. org-only author set: this repository's carriers record no per-result attribution
    (the file headers name the project, and CITATION.cff carries the project-level authors), and owner
    ruling R-H on that person list is still open — so naming an individual for this result would be invented,
    not measured. Per-result entries therefore carry the organization, and the mapping is the repository
    owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/QuantumVortexRegularity.lean
  cites:
  - arxiv:1111.4670
  - doi:10.1103/physreva.49.1613
  - doi:10.1103/physrevresearch.6.043130
  - navier.madelung.scalar-lift-falsified
  cited_by: []
- id: navier.madelung.winding-quantization
  title: Integer circulation and the phase-lift obstruction
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    proven — kernel-accepted. Declaration: realChargePhase_closes_iff_integer Navier/Analysis/QuantumVortexWinding.lean:30-30
    — "theorem realChargePhase_closes_iff_integer (kappa : ℝ) :". Authorship measured, not synthesised:
    the first 16 lines of the pinned carrier carry neither an upstream-attribution line nor an original-work
    line, so this entry names only the organization whose repository holds the artifact; project-scope
    attribution is carried by CITATION.cff, and owner ruling R-H is still open. Scope, in the repository's
    own words: docs/QUANTIZATION_REGULARITY_WICK.md docs/QUANTIZATION_REGULARITY_WICK.md:57-60 — "The
    native proof covers these explicit phase loops and the differentiable periodic-lift obstruction. A
    general winding-degree theorem, homotopy invariance, and the nonvanishing continuous disk-extension
    obstruction are not claimed as formalized here." and the same file on the geometric works this entry
    cites docs/QUANTIZATION_REGULARITY_WICK.md:62-66 — "For geometric treatments and their hypotheses,
    see Khesin–Misiołek–Modin and the Khesin–Modin preprint, which discusses noncritical zeros, the Madelung
    momentum map, and circulation quantization. These cited results are not claimed as formalized in this
    repository." — which is why those works sit in cites as prior literature and are not claimed as formalized
    here. Typed absence, recorded rather than papered over: no #print axioms receipt at the pin names
    realChargePhase_closes_iff_integer in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and
    this lane consumed no Lean build seat, so this entry quotes no axiom closure for it. org-only author
    set: this repository's carriers record no per-result attribution (the file headers name the project,
    and CITATION.cff carries the project-level authors), and owner ruling R-H on that person list is still
    open — so naming an individual for this result would be invented, not measured. Per-result entries
    therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/QuantumVortexWinding.lean
  cites:
  - arxiv:1711.00321
  - arxiv:2607.01024
  - arxiv:1905.02467
  cited_by: []
- id: navier.wick.mode-comparison
  title: Wick rotation preserves an analytic formula, not its damping estimate
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    proven — kernel-accepted. Declarations: differentiable_entireHeatMode Navier/Analysis/WickRotationModes.lean:41-41
    — "theorem differentiable_entireHeatMode (a : ℝ) :"; entireHeatMode_real_eq_modeDecay Navier/Analysis/WickRotationModes.lean:48-48
    — "theorem entireHeatMode_real_eq_modeDecay (a t : ℝ) :". Authorship measured, not synthesised: the
    first 16 lines of the pinned carrier carry neither an upstream-attribution line nor an original-work
    line, so this entry names only the organization whose repository holds the artifact; project-scope
    attribution is carried by CITATION.cff, and owner ruling R-H is still open. This entry's title is
    the repository's own section heading for the material, verbatim: docs/QUANTIZATION_REGULARITY_WICK.md:94
    docs/QUANTIZATION_REGULARITY_WICK.md:94-94 — "## Wick rotation preserves an analytic formula, not
    its damping estimate" Scope: the comparison inhabits neither alternative A nor B. Typed absence, recorded
    rather than papered over: no #print axioms receipt at the pin names differentiable_entireHeatMode
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/WickRotationModes.lean
  cites:
  - navier.manifest.foias_temam1989
  cited_by: []
- id: navier.frontier.scalar-budget-obstruction
  title: >-
    Typed no-go: no scalar heat/Duhamel majorant supplies a fixed positive invariant restart radius
  kind: theorem
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    proven — kernel-accepted, and it is an OBSTRUCTION, not a regularity result: it rules out one majorant
    class and does not advance alternative A. docs/RESULT_MAP.md states the obstruction and its bearer
    docs/RESULT_MAP.md:185-188 — "velocity, pressure, smoothness, PDE and energy carrier. The existing
    scalar heat/Duhamel majorant cannot supply a fixed positive invariant radius; GlobalRegularityCrownCore.not_restart_scalar_budget_le_fixed_radius
    proves that obstruction at its exact type." not_restart_scalar_budget_le_fixed_radius Navier/Analysis/GlobalRegularityCrownCore.lean:50-50
    — "theorem not_restart_scalar_budget_le_fixed_radius". Authorship measured, not synthesised: the first
    16 lines of the pinned carrier carry neither an upstream-attribution line nor an original-work line,
    so this entry names only the organization whose repository holds the artifact; project-scope attribution
    is carried by CITATION.cff, and owner ruling R-H is still open. Typed absence, recorded rather than
    papered over: no #print axioms receipt at the pin names not_restart_scalar_budget_le_fixed_radius
    in Navier/AxiomAudit.lean or Navier/ConditionalAudit.lean, and this lane consumed no Lean build seat,
    so this entry quotes no axiom closure for it. org-only author set: this repository's carriers record
    no per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Analysis/GlobalRegularityCrownCore.lean
  cites:
  - navier.problem.whole-space-global-regularity-a
  cited_by: []
- id: navier.problem.whole-space-global-regularity-a
  title: Unforced whole-space global regularity (Fefferman alternative A)
  kind: artifact
  authors:
  - name: Charles L. Fefferman
    role: person
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    OPEN in this repository — a formalised problem statement, not a result; cite it only as the exact
    encoding of the target proposition. Navier/Problem.lean, doc-comment together with definition Navier/Problem.lean:250-259
    — "/-- The canonical formal encoding of Fefferman whole-space statement A. For every nu > 0 and every
    divergence-free Schwartz velocity u0 on R^3, there exist velocity and pressure fields that are smooth
    on nonnegative time, solve the actual unforced Navier--Stokes equation pointwise, attain u0, remain
    incompressible, and have uniformly bounded finite kinetic energy. This definition states the target
    proposition. Establishing it requires a proof of this exact type; refuting it requires a proof of
    its negation. -/ def WholeSpaceGlobalRegularity : Prop :=" The audit file states what its own receipt
    does not mean Navier/AxiomAudit.lean:93-99 — "Each command below asks Lean for the transitive axioms
    of a named declaration. The audit of ProblemStatements.WholeSpaceGlobalRegularity concerns only the
    canonical proposition's definition and its imported foundations; it does not construct an inhabitant
    and is not evidence that alternative A is proved. In contrast, ConstructedBreakdown.wholeSpaceBreakdown
    is a proof of the distinct forced alternative C. The remaining commands audit the named analytic,
    algebraic," docs/OPEN_FRONTIER_MAP.md:13, row of the "Current boundary" table, cells verbatim: Surface
    "Unforced whole-space alternative A" | Current status "OPEN: ProblemStatements.WholeSpaceGlobalRegularity".
    Its Live edge cell opens "Local existence, normalized continuation and arbitrary-large-data critical
    control must meet in one faithful whole-space consumer"; the cell continues on that line, so this
    is a quoted prefix and not the whole cell. Authors: Fefferman states the problem (references/manifest.json
    id FEFFERMAN2000); Awkronos carries the formalisation.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/Problem.lean
  cites:
  - navier.manifest.fefferman2000
  - navier.manifest.tao2016
  cited_by:
  - navier.frontier.scalar-budget-obstruction
- id: navier.problem.periodic-global-regularity-b
  title: Unforced periodic global regularity (Fefferman alternative B)
  kind: artifact
  authors:
  - name: Charles L. Fefferman
    role: person
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    OPEN in this repository — a formalised problem statement, not a result. Navier/OfficialProblem.lean,
    doc-comment and definition Navier/OfficialProblem.lean:118-120 — "/-- Fefferman alternative B: unforced
    global smooth periodic solutions for every positive viscosity and every admissible periodic initial
    datum. -/ def PeriodicGlobalRegularity : Prop :=" docs/OPEN_FRONTIER_MAP.md:14, row of the "Current
    boundary" table, cells verbatim: Surface "Unforced periodic alternative B" | Current status "OPEN
    (arbitrary data): ProblemStatements.PeriodicGlobalRegularity". Its Live edge cell opens "Constructed
    physical local evolution and all spatial moments must feed joint classical reconstruction and arbitrary-data,
    horizon-uniform continuation control"; the cell continues on that line, so this is a quoted prefix
    and not the whole cell. docs/RESULT_MAP.md records it open docs/RESULT_MAP.md:29-31 — "The periodic
    unforced existence proposition Navier.ProblemStatements.PeriodicGlobalRegularity (alternative B) also
    remains open. A new periodic classical uniqueness theorem" The uniqueness consequence of this statement
    IS proved and is its own unit, navier.periodic.classical-uniqueness; existence is not. Authors: Fefferman
    states the problem (references/manifest.json id FEFFERMAN2000); Awkronos carries the formalisation.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/OfficialProblem.lean
  cites:
  - navier.manifest.fefferman2000
  cited_by:
  - navier.periodic.classical-uniqueness
- id: navier.algorithm.rust-spectral-solver
  title: >-
    Periodic spectral solver: rotational nonlinearity, Fourier-space Leray projection, componentwise Orszag
    2/3 dealiasing, integrating-factor RK4
  kind: algorithm
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    computed — numerical evidence, not the continuum proof. The crate is tracked at the pinned commit
    (solver/Cargo.toml, solver/src, solver/tests, solver/build-web.sh) and its README names the method
    set this entry's title expands: solver/README.md solver/README.md:8-10 — "2. SpectralSolver advances
    unforced incompressible Navier–Stokes benchmark flows on [0, 2π)^3 using the rotational nonlinearity,
    Fourier-space Leray projection, componentwise Orszag 2/3 dealiasing, and integrating-factor RK4."
    docs/RESULT_MAP.md's own numerical-boundary section states what no numerical surface establishes docs/RESULT_MAP.md:334-340
    — "The axis evaluator does not implement the annular matching, Borel background, covariance waves,
    correction cycles, or final spacetime localization that make the selected force globally smooth. Its
    displayed momentum residual is the force required by the finite reconstructed field, not the selected
    force of ConstructedBreakdown.wholeSpaceBreakdown. Tests can validate implementation identities and
    finite-resolution behavior. No finite grid, residual sample, or visual trajectory establishes a continuum
    regularity or breakdown theorem." Authorship measured, not synthesised: the first 16 lines of the
    pinned carrier carry neither an upstream-attribution line nor an original-work line, so this entry
    names only the organization whose repository holds the artifact; project-scope attribution is carried
    by CITATION.cff, and owner ruling R-H is still open. Prior art: the Leray weak-solution context is
    navier.manifest.leray1934. The 2/3-dealiasing attribution in solver/README.md carries no identifier
    in repo text, so no cites edge is asserted for it; the gap is recorded under 'Unresolved attributions'
    rather than filled with a plausible link. org-only author set: this repository's carriers record no
    per-result attribution (the file headers name the project, and CITATION.cff carries the project-level
    authors), and owner ruling R-H on that person list is still open — so naming an individual for this
    result would be invented, not measured. Per-result entries therefore carry the organization, and the
    mapping is the repository owner's act, not the citation lane's.
  stable_link: https://github.com/awkronos/navier/tree/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/solver
  cites:
  - navier.manifest.leray1934
  cited_by: []
- id: navier.algorithm.analytic-axis-stage
  title: >-
    Finite analytic-axis profile iteration reconstructing one computable stage of the construction
  kind: algorithm
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    computed — numerical evidence, not the continuum proof. Carrier: docs/COMPUTED_AXIS_CONSTRUCTION.md,
    pinned by this entry; the scope is stated by the result map: docs/RESULT_MAP.md docs/RESULT_MAP.md:325-332
    — "The Rust crate has two separate numerical surfaces. AxisConstruction evaluates a finite radial-series
    approximation to the analytic-axis profile, reconstructs velocity and pressure in its bounded similarity
    chart, and measures the profile-equation defects, divergence defect, and momentum residual. The CPU/WASM/WebGPU
    spectral solver separately evolves ordinary periodic flows. The computed-construction note records
    the exact equations, defaults, sampled domain, and omitted correction layers." Authorship measured,
    not synthesised: the first 16 lines of the pinned carrier carry neither an upstream-attribution line
    nor an original-work line, so this entry names only the organization whose repository holds the artifact;
    project-scope attribution is carried by CITATION.cff, and owner ruling R-H is still open. The axis
    evaluator's own limits, including which force its residual belongs to, are quoted in navier.algorithm.rust-spectral-solver.
    org-only author set: this repository's carriers record no per-result attribution (the file headers
    name the project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that
    person list is still open — so naming an individual for this result would be invented, not measured.
    Per-result entries therefore carry the organization, and the mapping is the repository owner's act,
    not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/docs/COMPUTED_AXIS_CONSTRUCTION.md
  cites:
  - navier.manifest.openai2026_forced_breakdown
  cited_by: []
- id: navier.artifact.references-manifest
  title: 'Structured prior-work manifest: 17 sources with ids, years, venues, URLs and DOIs'
  kind: artifact
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    maintained artifact. Measured from the pinned blob: references/manifest.json parses to schema_version
    1, file checked_at 2026-07-14, and a sources array of exactly 17 objects — no duplicate ids. Each
    navier.manifest.* entry above is a field dump of one of those objects, read from the parsed JSON rather
    than transcribed, and every cites edge in this document that ends in navier.manifest.* resolves here.
    The register describes itself, verbatim: references/manifest.json:4, span verbatim — "Primary and
    official sources supporting the Navier-Stokes attack blueprint, its known bridges, and its barrier
    tests.". and sources is the array this entry counts. org-only author set: this repository's carriers
    record no per-result attribution (the file headers name the project, and CITATION.cff carries the
    project-level authors), and owner ruling R-H on that person list is still open — so naming an individual
    for this result would be invented, not measured. Per-result entries therefore carry the organization,
    and the mapping is the repository owner's act, not the citation lane's. An empty cites array is a
    claim of independence under the carrier, so the claim here is scoped: this repository records no dependency
    edge for this entry — it does not assert that the work stood on nothing.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/references/manifest.json
  cites: []
  cited_by: []
- id: navier.artifact.falsification-ledger
  title: 'Ledger of rejected claim classes and their repair conditions: entries are never deleted'
  kind: artifact
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    maintained artifact; cite it to record that a claim class was rejected, never as a result. The repository's
    own non-deletion law, in its words: docs/FALSIFICATION_LEDGER.md docs/FALSIFICATION_LEDGER.md:3-10
    — "Ledger initialized: 2026-07-14 Research program baseline (initial contract commit): 81448ed3e488b8b7d357ce430d52df4434f0c9cd
    This ledger records failed claim classes and boundary mistakes, not failed people or papers. A published
    theorem remains valid in its stated scope even when a stronger use of it is killed. Entries are never
    deleted; a repaired, strictly narrower successor links back to the original ID." Row F-027 is the
    case this document is honest about — it attributes two class-decay facts docs/FALSIFICATION_LEDGER.md:82,
    span verbatim — "primary sources: Dobrokhotov–Shafarevich 1994 (Math. Notes 55): if u(t) decays faster
    than |x|^{-4} then ∫ uᵢuⱼ dx = c(t) δᵢⱼ; Brandolese 2004 (Math. Ann. 329, arXiv 2003-04-28): the |x|^{-4}
    rate is attained at positive times for generic data". That span carries no DOI and no arXiv id: the
    string 'arXiv 2003-04-28' inside it is a date-shaped non-identifier, not an identifier. Per the register
    law those rows stay typed absences under `Prose-only attributions to upgrade`, and the citation lane
    did not substitute a web-resolved identifier for a register row the repository never measured. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/docs/FALSIFICATION_LEDGER.md
  cites:
  - navier.manifest.tao2016
  cited_by: []
- id: navier.artifact.mathlib-pin
  title: >-
    Mathlib pin consumed by the build: v4.35.0-rc4 at rev 1f414401f69059aa7eead47b53ee40bd38455eeb
  kind: artifact
  authors:
  - name: leanprover-community
    role: organization
  year: 2026
  venue_or_status: >-
    org-only author: this repository's register names the organization leanprover-community and records
    no person list for mathlib, so naming individuals would be an invention; org-only is stated per the
    carrier, not assumed. Pinned dependency, measured from the tracked blobs at the pin: The mathlib row
    records lake-manifest.json:10, span verbatim — "1f414401f69059aa7eead47b53ee40bd38455eeb". and its
    inputRev lake-manifest.json:13, span verbatim — "v4.35.0-rc4". lean-toolchain:1 lean-toolchain:1-1
    — "leanprover/lean4:v4.35.0-rc4" Cite the pin, never a moving branch. This repository does not claim
    mathlib's own proofs. An empty cites array is a claim of independence under the carrier, and it is
    TRUE here in the narrow sense: the pin is a measured build input, not a result standing on this document's
    other entries.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/lake-manifest.json
  cites: []
  cited_by: []
- id: navier.artifact.audit-axioms
  title: 'Navier/AxiomAudit.lean: the repository''s own raw-axiom receipt sheet'
  kind: artifact
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    maintained artifact and IN-REPO AUTHORITY: every axiom closure quoted in this document is extracted
    from this file or Navier/ConditionalAudit.lean by line number, never re-elaborated. Its own description
    of what it does Navier/AxiomAudit.lean:93-94 — "Each command below asks Lean for the transitive axioms
    of a named declaration. The audit of" The aggregate finding, as RESULT_MAP records it docs/RESULT_MAP.md:96-97
    — "All named completed declarations above currently report only propext, Classical.choice, and Quot.sound.
    The source attribution and adaptation" The per-receipt subset claim, in the file's own words Navier/AxiomAudit.lean:682-683
    — "research program — each #print axioms receipt is a strict subset of {propext, Classical.choice,
    Quot.sound} (verified 2026-07-16). The two" And the whole-tree sweep Navier/AxiomAudit.lean:693-695
    — "Navier.Analysis.SingularIntegralPrelims.bkm_shape_absorption. The whole-tree runtime collectAxioms
    sweep (scripts/AuditAllAxioms.lean, exit 0) finds zero sorryAx in the transitive closure of every
    imported Navier declaration." This entry is deliberately given no cites edge to each unit it receipts:
    a pointer to an evidence file is not an intellectual dependency, and inflating the graph with receipt
    edges would hide the real ones. org-only author set: this repository's carriers record no per-result
    attribution (the file headers name the project, and CITATION.cff carries the project-level authors),
    and owner ruling R-H on that person list is still open — so naming an individual for this result would
    be invented, not measured. Per-result entries therefore carry the organization, and the mapping is
    the repository owner's act, not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/AxiomAudit.lean
  cites: []
  cited_by: []
- id: navier.artifact.audit-conditional
  title: 'Navier/ConditionalAudit.lean: build-time conditional-audit carrier'
  kind: artifact
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    maintained artifact and IN-REPO AUTHORITY for the ConditionalAudit.lean verification surface that
    many RESULT_MAP rows name. docs/OPEN_FRONTIER_MAP.md docs/OPEN_FRONTIER_MAP.md:68-70 — "Every lake
    build now emits raw #print axioms receipts for all four crowns from Navier/ConditionalAudit.lean (build
    log = receipt pipeline), and scripts/check_construction_drift.py pins the vendored slice to upstream"
    Same no-receipt-edge convention as navier.artifact.audit-axioms: the independence this entry's empty
    cites array claims is a property of a build-time audit carrier, not of the theorems it audits. org-only
    author set: this repository's carriers record no per-result attribution (the file headers name the
    project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that person
    list is still open — so naming an individual for this result would be invented, not measured. Per-result
    entries therefore carry the organization, and the mapping is the repository owner's act, not the citation
    lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/Navier/ConditionalAudit.lean
  cites: []
  cited_by: []
- id: navier.artifact.open-frontier-map
  title: >-
    docs/OPEN_FRONTIER_MAP.md: the repository's current mathematical boundary, surface by surface
  kind: artifact
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    maintained artifact and IN-REPO AUTHORITY for the THEOREM / OPEN / FALSIFIED / DECOMPOSED grading
    of each surface; this document quotes its cells by line rather than restating them. Its header states
    its own law: docs/OPEN_FRONTIER_MAP.md:3-4 docs/OPEN_FRONTIER_MAP.md:3-4 — "Use current theorem types
    and compiler evidence to select work. This file does not assign fixed outcomes or prescribe a proof
    route." and it marks two other artifacts historical: docs/OPEN_FRONTIER_MAP.md:106-108 docs/OPEN_FRONTIER_MAP.md:106-108
    — "The dated residual ledger and research blueprint are historical records. Their counts, line numbers,
    and proposed routes are not current verification evidence or constraints on new proofs." The whole-tree
    sweep's limits are recorded in the same file: docs/OPEN_FRONTIER_MAP.md:99-104 docs/OPEN_FRONTIER_MAP.md:99-104
    — "scripts/AuditAllAxioms.lean checks every declaration imported from a Navier module, including private
    helpers and declarations in other namespaces, for disallowed transitive axioms. Refresh changed modules
    before running it. This detects admitted dependencies omitted by a handpicked public audit. It does
    not decide whether the definitions faithfully encode a scientific claim, or whether the hypotheses
    of a conditional theorem can be proved." Independence here is a property of a navigation artifact
    that quotes other carriers rather than standing on them. org-only author set: this repository's carriers
    record no per-result attribution (the file headers name the project, and CITATION.cff carries the
    project-level authors), and owner ruling R-H on that person list is still open — so naming an individual
    for this result would be invented, not measured. Per-result entries therefore carry the organization,
    and the mapping is the repository owner's act, not the citation lane's. An empty cites array is a
    claim of independence under the carrier, so the claim here is scoped: this repository records no dependency
    edge for this entry — it does not assert that the work stood on nothing.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/docs/OPEN_FRONTIER_MAP.md
  cites: []
  cited_by:
  - navier.artifact.formalization-yaml
- id: navier.artifact.formalization-yaml
  title: 'formalization.yaml: machine-readable mirror of the frontier table'
  kind: artifact
  authors:
  - name: Awkronos
    role: organization
  year: 2026
  venue_or_status: >-
    maintained artifact. docs/OPEN_FRONTIER_MAP.md:65-67 docs/OPEN_FRONTIER_MAP.md:65-67 — "formalization.yaml
    is the machine-readable mirror of the table above; scripts/check_formalization.py --check validates
    it fail-closed and --probe prints the raw-axiom command sequence without asserting results." A fold
    that changes a grading must change this file and pass that check; this citation document does not
    duplicate its rows, it points here — which is why its one cites edge is the mirror relation itself.
    org-only author set: this repository's carriers record no per-result attribution (the file headers
    name the project, and CITATION.cff carries the project-level authors), and owner ruling R-H on that
    person list is still open — so naming an individual for this result would be invented, not measured.
    Per-result entries therefore carry the organization, and the mapping is the repository owner's act,
    not the citation lane's.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/formalization.yaml
  cites:
  - navier.artifact.open-frontier-map
  cited_by: []
- id: navier.manifest.openai2026_forced_breakdown
  title: Finite time blowup for Navier–Stokes
  kind: theorem
  authors:
  - name: OpenAI
    role: organization
  year: 2026
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id OPENAI2026_FORCED_BREAKDOWN;
    registry_id ref.forced_breakdown.openai2026; title Finite time blowup for Navier–Stokes; authors OpenAI;
    year 2026; venue OpenAI research release; type preprint; primary True; checked_at 2026-09-13; doi
    null in source; url https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf;
    roles native source adaptation proving smooth forced whole-space breakdown alternative C || compact
    force admissibility, singular candidate, and finite-energy comparison || concentration-aware numerical
    diagnostics; no Lake dependency. org-only author: the register carries this authoring organization
    and records no person list for this source, so naming individuals here would be an invention — org-only
    is stated per the carrier, not assumed. Carrier kind theorem mapped from the register's own type field
    by the rule *journal_article → theorem, preprint → theorem, official_problem_statement → artifact*,
    stated in the Conventions section. no DOI and no arXiv id exists in the register row, so stable_link
    is the commit-pinned permalink of the manifest that carries the publisher URL — a publisher URL is
    not sha-anchored and is therefore not used as the stable_link. No identifier in this document was
    resolved on the web by the citation lane: this repository's own register and its own markdown links
    are the only literature authority used here. An empty cites array is a claim of independence under
    the carrier, so the claim here is scoped: this repository records no dependency edge for this entry
    — it does not assert that the work stood on nothing.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/references/manifest.json
  cites: []
  cited_by:
  - navier.algorithm.analytic-axis-stage
  - navier.candidate.r3-compact-candidate-exists
  - navier.force.coordinate-partial-equivalence
  - navier.forced.periodic-breakdown-d
  - navier.forced.whole-space-breakdown-c
- id: navier.manifest.openai2026_euler
  title: Finite time blowup for the Euler equation
  kind: theorem
  authors:
  - name: OpenAI
    role: organization
  year: 2026
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id OPENAI2026_EULER;
    registry_id ref.euler_breakdown.openai2026; title Finite time blowup for the Euler equation; authors
    OpenAI; year 2026; venue OpenAI research release; type preprint; primary True; checked_at 2026-09-13;
    doi null in source; url https://cdn.openai.com/pdf/315b36cd-ec98-4023-8342-93345194ece1/euler.pdf;
    roles upstream unforced 3-D Euler finite-time breakdown with smooth compactly supported divergence-free
    data || formalized at openai/NavierStokesAndEuler@f9e8bc5 (Euler/ tree); not yet adapted in this repository
    || quarantined carrier for Fefferman A/B pending a transfer theorem; source of the packet-induction
    frozen-scale-record method. org-only author: the register carries this authoring organization and
    records no person list for this source, so naming individuals here would be an invention — org-only
    is stated per the carrier, not assumed. Carrier kind theorem mapped from the register's own type field
    by the rule *journal_article → theorem, preprint → theorem, official_problem_statement → artifact*,
    stated in the Conventions section. no DOI and no arXiv id exists in the register row, so stable_link
    is the commit-pinned permalink of the manifest that carries the publisher URL — a publisher URL is
    not sha-anchored and is therefore not used as the stable_link. No identifier in this document was
    resolved on the web by the citation lane: this repository's own register and its own markdown links
    are the only literature authority used here. An empty cites array is a claim of independence under
    the carrier, so the claim here is scoped: this repository records no dependency edge for this entry
    — it does not assert that the work stood on nothing.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/references/manifest.json
  cites: []
  cited_by:
  - navier.upstream.euler-breakdown
- id: navier.manifest.fefferman2000
  title: Existence and Smoothness of the Navier-Stokes Equation
  kind: artifact
  authors:
  - name: Charles L. Fefferman
    role: person
  year: 2000
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id FEFFERMAN2000; registry_id
    ref.problem_statement.fefferman2000; title Existence and Smoothness of the Navier-Stokes Equation;
    authors Charles L. Fefferman; year 2000; venue Clay Mathematics Institute Millennium Prize Problems;
    type official_problem_statement; primary True; checked_at 2026-07-14; doi null in source; url https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf;
    roles exact equations and admissibility clauses || exact alternatives A-D || whole-space primary formal
    target. Carrier kind artifact mapped from the register's own type field by the rule *journal_article
    → theorem, preprint → theorem, official_problem_statement → artifact*, stated in the Conventions section.
    no DOI and no arXiv id exists in the register row, so stable_link is the commit-pinned permalink of
    the manifest that carries the publisher URL — a publisher URL is not sha-anchored and is therefore
    not used as the stable_link. No identifier in this document was resolved on the web by the citation
    lane: this repository's own register and its own markdown links are the only literature authority
    used here. An empty cites array is a claim of independence under the carrier, so the claim here is
    scoped: this repository records no dependency edge for this entry — it does not assert that the work
    stood on nothing.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/references/manifest.json
  cites: []
  cited_by:
  - navier.forced.periodic-breakdown-d
  - navier.forced.whole-space-breakdown-c
  - navier.problem.periodic-global-regularity-b
  - navier.problem.whole-space-global-regularity-a
- id: navier.manifest.leray1934
  title: Sur le mouvement d'un liquide visqueux emplissant l'espace
  kind: theorem
  authors:
  - name: Jean Leray
    role: person
  year: 1934
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id LERAY1934; registry_id
    ref.leray.1934; title Sur le mouvement d'un liquide visqueux emplissant l'espace; authors Jean Leray;
    year 1934; venue Acta Mathematica 63, 193-248; type journal_article; primary True; checked_at 2026-07-14;
    doi 10.1007/BF02547354; url https://doi.org/10.1007/BF02547354; roles global finite-energy weak-solution
    boundary || weak versus smooth solution distinction. Carrier kind theorem mapped from the register's
    own type field by the rule *journal_article → theorem, preprint → theorem, official_problem_statement
    → artifact*, stated in the Conventions section. stable_link is the DOI resolver form of the DOI printed
    in this repository's own register row (doi 10.1007/BF02547354). No identifier in this document was
    resolved on the web by the citation lane: this repository's own register and its own markdown links
    are the only literature authority used here. An empty cites array is a claim of independence under
    the carrier, so the claim here is scoped: this repository records no dependency edge for this entry
    — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1007/BF02547354
  cites: []
  cited_by:
  - navier.algorithm.rust-spectral-solver
  - navier.forced.whole-space-breakdown-c
- id: navier.manifest.prodi1959
  title: Un teorema di unicità per le equazioni di Navier-Stokes
  kind: theorem
  authors:
  - name: Giovanni Prodi
    role: person
  year: 1959
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id PRODI1959; registry_id
    ref.prodi.1959; title Un teorema di unicità per le equazioni di Navier-Stokes; authors Giovanni Prodi;
    year 1959; venue Annali di Matematica Pura ed Applicata 48(1), 173-182; type journal_article; primary
    True; checked_at 2026-07-14; doi 10.1007/BF02410664; url https://doi.org/10.1007/BF02410664; roles
    Prodi integrability and uniqueness criterion || critical mixed-norm continuation boundary || R1 boundary.
    Carrier kind theorem mapped from the register's own type field by the rule *journal_article → theorem,
    preprint → theorem, official_problem_statement → artifact*, stated in the Conventions section. stable_link
    is the DOI resolver form of the DOI printed in this repository's own register row (doi 10.1007/BF02410664).
    No identifier in this document was resolved on the web by the citation lane: this repository's own
    register and its own markdown links are the only literature authority used here. An empty cites array
    is a claim of independence under the carrier, so the claim here is scoped: this repository records
    no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1007/BF02410664
  cites: []
  cited_by: []
- id: navier.manifest.serrin1962
  title: On the Interior Regularity of Weak Solutions of the Navier-Stokes Equations
  kind: theorem
  authors:
  - name: James Serrin
    role: person
  year: 1962
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id SERRIN1962; registry_id
    ref.serrin.1962; title On the Interior Regularity of Weak Solutions of the Navier-Stokes Equations;
    authors James Serrin; year 1962; venue Archive for Rational Mechanics and Analysis 9, 187-195; type
    journal_article; primary True; checked_at 2026-07-14; doi 10.1007/BF00253344; url https://doi.org/10.1007/BF00253344;
    roles mixed-norm regularity criterion || conditional continuation bridge. Carrier kind theorem mapped
    from the register's own type field by the rule *journal_article → theorem, preprint → theorem, official_problem_statement
    → artifact*, stated in the Conventions section. stable_link is the DOI resolver form of the DOI printed
    in this repository's own register row (doi 10.1007/BF00253344). No identifier in this document was
    resolved on the web by the citation lane: this repository's own register and its own markdown links
    are the only literature authority used here. An empty cites array is a claim of independence under
    the carrier, so the claim here is scoped: this repository records no dependency edge for this entry
    — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1007/BF00253344
  cites: []
  cited_by: []
- id: navier.manifest.kato1984
  title: >-
    Strong L^p-Solutions of the Navier-Stokes Equation in R^m, with Applications to Weak Solutions
  kind: theorem
  authors:
  - name: Tosio Kato
    role: person
  year: 1984
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id KATO1984; registry_id
    ref.kato.1984; title Strong L^p-Solutions of the Navier-Stokes Equation in R^m, with Applications
    to Weak Solutions; authors Tosio Kato; year 1984; venue Mathematische Zeitschrift 187, 471-480; type
    journal_article; primary True; checked_at 2026-07-14; doi 10.1007/BF01174182; url https://doi.org/10.1007/BF01174182;
    roles strong local solution theory || critical-space mild-solution precedent || R2 boundary. Carrier
    kind theorem mapped from the register's own type field by the rule *journal_article → theorem, preprint
    → theorem, official_problem_statement → artifact*, stated in the Conventions section. stable_link
    is the DOI resolver form of the DOI printed in this repository's own register row (doi 10.1007/BF01174182).
    No identifier in this document was resolved on the web by the citation lane: this repository's own
    register and its own markdown links are the only literature authority used here. An empty cites array
    is a claim of independence under the carrier, so the claim here is scoped: this repository records
    no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1007/BF01174182
  cites: []
  cited_by: []
- id: navier.manifest.ckn1982
  title: Partial Regularity of Suitable Weak Solutions of the Navier-Stokes Equations
  kind: theorem
  authors:
  - name: Luis Caffarelli
    role: person
  - name: Robert V. Kohn
    role: person
  - name: Louis Nirenberg
    role: person
  year: 1982
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id CKN1982; registry_id
    ref.ckn.1982; title Partial Regularity of Suitable Weak Solutions of the Navier-Stokes Equations;
    authors Luis Caffarelli; Robert V. Kohn; Louis Nirenberg; year 1982; venue Communications on Pure
    and Applied Mathematics 35, 771-831; type journal_article; primary True; checked_at 2026-07-14; doi
    10.1002/cpa.3160350604; url https://onlinelibrary.wiley.com/doi/pdf/10.1002/cpa.3160350604; roles
    suitable weak solutions || epsilon and partial regularity || R4 and R9 boundary. Carrier kind theorem
    mapped from the register's own type field by the rule *journal_article → theorem, preprint → theorem,
    official_problem_statement → artifact*, stated in the Conventions section. stable_link is the DOI
    resolver form of the DOI printed in this repository's own register row (doi 10.1002/cpa.3160350604).
    No identifier in this document was resolved on the web by the citation lane: this repository's own
    register and its own markdown links are the only literature authority used here. An empty cites array
    is a claim of independence under the carrier, so the claim here is scoped: this repository records
    no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1002/cpa.3160350604
  cites: []
  cited_by: []
- id: navier.manifest.constantin_fefferman1993
  title: >-
    Direction of Vorticity and the Problem of Global Regularity for the Navier-Stokes Equations
  kind: theorem
  authors:
  - name: Peter Constantin
    role: person
  - name: Charles Fefferman
    role: person
  year: 1993
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id CONSTANTIN_FEFFERMAN1993;
    registry_id ref.constantin.fefferman1993; title Direction of Vorticity and the Problem of Global Regularity
    for the Navier-Stokes Equations; authors Peter Constantin; Charles Fefferman; year 1993; venue Indiana
    University Mathematics Journal 42(3), 775-789; type journal_article; primary True; checked_at 2026-07-14;
    doi null in source; url https://iumj.org/article/3627/; roles vorticity-direction regularity criterion
    || R3 conditional boundary. Carrier kind theorem mapped from the register's own type field by the
    rule *journal_article → theorem, preprint → theorem, official_problem_statement → artifact*, stated
    in the Conventions section. no DOI and no arXiv id exists in the register row, so stable_link is the
    commit-pinned permalink of the manifest that carries the publisher URL — a publisher URL is not sha-anchored
    and is therefore not used as the stable_link. No identifier in this document was resolved on the web
    by the citation lane: this repository's own register and its own markdown links are the only literature
    authority used here. An empty cites array is a claim of independence under the carrier, so the claim
    here is scoped: this repository records no dependency edge for this entry — it does not assert that
    the work stood on nothing.
  stable_link: >-
    https://github.com/awkronos/navier/blob/a4b066c6d26742a36e4f914b1ea56e2a6c88f12b/references/manifest.json
  cites: []
  cited_by: []
- id: navier.manifest.koch_tataru2001
  title: Well-Posedness for the Navier-Stokes Equations
  kind: theorem
  authors:
  - name: Herbert Koch
    role: person
  - name: Daniel Tataru
    role: person
  year: 2001
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id KOCH_TATARU2001;
    registry_id ref.koch.tataru2001; title Well-Posedness for the Navier-Stokes Equations; authors Herbert
    Koch; Daniel Tataru; year 2001; venue Advances in Mathematics 157(1), 22-35; type journal_article;
    primary True; checked_at 2026-07-14; doi 10.1006/aima.2000.1937; url https://doi.org/10.1006/aima.2000.1937;
    roles BMO-minus-one well-posedness || critical mild fixed-point route || small-data versus arbitrary-data
    boundary. Carrier kind theorem mapped from the register's own type field by the rule *journal_article
    → theorem, preprint → theorem, official_problem_statement → artifact*, stated in the Conventions section.
    stable_link is the DOI resolver form of the DOI printed in this repository's own register row (doi
    10.1006/aima.2000.1937). No identifier in this document was resolved on the web by the citation lane:
    this repository's own register and its own markdown links are the only literature authority used here.
    An empty cites array is a claim of independence under the carrier, so the claim here is scoped: this
    repository records no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1006/aima.2000.1937
  cites: []
  cited_by: []
- id: navier.manifest.ess2003
  title: L_{3,∞}-Solutions of the Navier-Stokes Equations and Backward Uniqueness
  kind: theorem
  authors:
  - name: Luis Escauriaza
    role: person
  - name: Gregory A. Seregin
    role: person
  - name: Vladimir Šverák
    role: person
  year: 2003
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id ESS2003; registry_id
    ref.ess.2003; title L_{3,∞}-Solutions of the Navier-Stokes Equations and Backward Uniqueness; authors
    Luis Escauriaza; Gregory A. Seregin; Vladimir Šverák; year 2003; venue Russian Mathematical Surveys
    58(2), 211-250; type journal_article; primary True; checked_at 2026-07-14; doi 10.1070/RM2003v058n02ABEH000609;
    url https://www.mathnet.ru/eng/rm609; roles endpoint L-infinity-time L3-space regularity || backward
    uniqueness || R1 and R4 conditional bridge. Carrier kind theorem mapped from the register's own type
    field by the rule *journal_article → theorem, preprint → theorem, official_problem_statement → artifact*,
    stated in the Conventions section. stable_link is the DOI resolver form of the DOI printed in this
    repository's own register row (doi 10.1070/RM2003v058n02ABEH000609). No identifier in this document
    was resolved on the web by the citation lane: this repository's own register and its own markdown
    links are the only literature authority used here. An empty cites array is a claim of independence
    under the carrier, so the claim here is scoped: this repository records no dependency edge for this
    entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1070/RM2003v058n02ABEH000609
  cites: []
  cited_by: []
- id: navier.manifest.gallagher_koch_planchon2013
  title: A profile decomposition approach to the L^∞_t(L^3_x) Navier–Stokes regularity criterion
  kind: theorem
  authors:
  - name: Isabelle Gallagher
    role: person
  - name: Gabriel S. Koch
    role: person
  - name: Fabrice Planchon
    role: person
  year: 2013
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id GALLAGHER_KOCH_PLANCHON2013;
    registry_id ref.gallagher.koch.planchon2013; title A profile decomposition approach to the L^∞_t(L^3_x)
    Navier–Stokes regularity criterion; authors Isabelle Gallagher; Gabriel S. Koch; Fabrice Planchon;
    year 2013; venue Mathematische Annalen 355(4), 1527-1559; type journal_article; primary True; checked_at
    2026-07-14; doi 10.1007/s00208-012-0830-0; url https://doi.org/10.1007/s00208-012-0830-0; roles critical
    profile decomposition || critical-element regularity machinery || R4 compactness boundary. Carrier
    kind theorem mapped from the register's own type field by the rule *journal_article → theorem, preprint
    → theorem, official_problem_statement → artifact*, stated in the Conventions section. stable_link
    is the DOI resolver form of the DOI printed in this repository's own register row (doi 10.1007/s00208-012-0830-0).
    No identifier in this document was resolved on the web by the citation lane: this repository's own
    register and its own markdown links are the only literature authority used here. An empty cites array
    is a claim of independence under the carrier, so the claim here is scoped: this repository records
    no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1007/s00208-012-0830-0
  cites: []
  cited_by: []
- id: navier.manifest.foias_temam1989
  title: Gevrey Class Regularity for the Solutions of the Navier-Stokes Equations
  kind: theorem
  authors:
  - name: Ciprian Foias
    role: person
  - name: Roger Temam
    role: person
  year: 1989
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id FOIAS_TEMAM1989;
    registry_id ref.foias.temam1989; title Gevrey Class Regularity for the Solutions of the Navier-Stokes
    Equations; authors Ciprian Foias; Roger Temam; year 1989; venue Journal of Functional Analysis 87(2),
    359-369; type journal_article; primary True; checked_at 2026-07-14; doi 10.1016/0022-1236(89)90015-3;
    url https://doi.org/10.1016/0022-1236(89)90015-3; roles Gevrey regularity precedent || analyticity-radius
    route boundary. Carrier kind theorem mapped from the register's own type field by the rule *journal_article
    → theorem, preprint → theorem, official_problem_statement → artifact*, stated in the Conventions section.
    stable_link is the DOI resolver form of the DOI printed in this repository's own register row (doi
    10.1016/0022-1236(89)90015-3). No identifier in this document was resolved on the web by the citation
    lane: this repository's own register and its own markdown links are the only literature authority
    used here. An empty cites array is a claim of independence under the carrier, so the claim here is
    scoped: this repository records no dependency edge for this entry — it does not assert that the work
    stood on nothing.
  stable_link: https://doi.org/10.1016/0022-1236(89)90015-3
  cites: []
  cited_by:
  - navier.wick.mode-comparison
- id: navier.manifest.tao2016
  title: Finite Time Blowup for an Averaged Three-Dimensional Navier-Stokes Equation
  kind: theorem
  authors:
  - name: Terence Tao
    role: person
  year: 2016
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id TAO2016; registry_id
    ref.tao.averaged2016; title Finite Time Blowup for an Averaged Three-Dimensional Navier-Stokes Equation;
    authors Terence Tao; year 2016; venue Journal of the American Mathematical Society 29(3), 601-674;
    type journal_article; primary True; checked_at 2026-07-14; doi 10.1090/jams/838; url https://www.ams.org/jams/2016-29-03/S0894-0347-2015-00838-4/S0894-0347-2015-00838-4.pdf;
    roles averaged-operator blowup obstruction || energy-plus-generic-harmonic-analysis kill test || exact-bilinear-structure
    discriminator. Carrier kind theorem mapped from the register's own type field by the rule *journal_article
    → theorem, preprint → theorem, official_problem_statement → artifact*, stated in the Conventions section.
    stable_link is the DOI resolver form of the DOI printed in this repository's own register row (doi
    10.1090/jams/838). No identifier in this document was resolved on the web by the citation lane: this
    repository's own register and its own markdown links are the only literature authority used here.
    An empty cites array is a claim of independence under the carrier, so the claim here is scoped: this
    repository records no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1090/jams/838
  cites: []
  cited_by:
  - navier.artifact.falsification-ledger
  - navier.problem.whole-space-global-regularity-a
- id: navier.manifest.tao2019
  title: Quantitative Bounds for Critically Bounded Solutions to the Navier-Stokes Equations
  kind: theorem
  authors:
  - name: Terence Tao
    role: person
  year: 2019
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id TAO2019; registry_id
    ref.tao.2019; title Quantitative Bounds for Critically Bounded Solutions to the Navier-Stokes Equations;
    authors Terence Tao; year 2019; venue arXiv:1908.04958v2; type preprint; primary True; checked_at
    2026-07-14; doi null in source; url https://arxiv.org/abs/1908.04958v2; roles quantitative critical-norm
    regularity bounds || frequency-localized cascade constraints || R5 conditional boundary. Carrier kind
    theorem mapped from the register's own type field by the rule *journal_article → theorem, preprint
    → theorem, official_problem_statement → artifact*, stated in the Conventions section. stable_link
    is the arXiv abstract page parsed out of the URL in this repository's own register row. No identifier
    in this document was resolved on the web by the citation lane: this repository's own register and
    its own markdown links are the only literature authority used here. An empty cites array is a claim
    of independence under the carrier, so the claim here is scoped: this repository records no dependency
    edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://arxiv.org/abs/1908.04958
  cites: []
  cited_by: []
- id: navier.manifest.buckmaster_vicol2019
  title: Nonuniqueness of Weak Solutions to the Navier-Stokes Equation
  kind: theorem
  authors:
  - name: Tristan Buckmaster
    role: person
  - name: Vlad Vicol
    role: person
  year: 2019
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id BUCKMASTER_VICOL2019;
    registry_id ref.buckmaster.vicol2019; title Nonuniqueness of Weak Solutions to the Navier-Stokes Equation;
    authors Tristan Buckmaster; Vlad Vicol; year 2019; venue Annals of Mathematics 189(1), 101-144; type
    journal_article; primary True; checked_at 2026-07-14; doi 10.4007/annals.2019.189.1.3; url https://annals.math.princeton.edu/2019/189-1/p03;
    roles finite-energy weak nonuniqueness boundary || weak versus smooth category audit. Carrier kind
    theorem mapped from the register's own type field by the rule *journal_article → theorem, preprint
    → theorem, official_problem_statement → artifact*, stated in the Conventions section. stable_link
    is the DOI resolver form of the DOI printed in this repository's own register row (doi 10.4007/annals.2019.189.1.3).
    No identifier in this document was resolved on the web by the citation lane: this repository's own
    register and its own markdown links are the only literature authority used here. An empty cites array
    is a claim of independence under the carrier, so the claim here is scoped: this repository records
    no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.4007/annals.2019.189.1.3
  cites: []
  cited_by: []
- id: navier.manifest.albritton_brue_colombo2022
  title: Non-Uniqueness of Leray Solutions of the Forced Navier-Stokes Equations
  kind: theorem
  authors:
  - name: Dallas Albritton
    role: person
  - name: Elia Brué
    role: person
  - name: Maria Colombo
    role: person
  year: 2022
  venue_or_status: >-
    Prior work, read field by field from this repository's verified register (no web resolution). Fields
    read from the pinned blob references/manifest.json (parsed, not transcribed): id ALBRITTON_BRUE_COLOMBO2022;
    registry_id ref.albritton.brue.colombo2022; title Non-Uniqueness of Leray Solutions of the Forced
    Navier-Stokes Equations; authors Dallas Albritton; Elia Brué; Maria Colombo; year 2022; venue Annals
    of Mathematics 196(1), 415-455; type journal_article; primary True; checked_at 2026-07-14; doi 10.4007/annals.2022.196.1.3;
    url https://projecteuclid.org/journals/annals-of-mathematics/volume-196/issue-1/Non-uniqueness-of-Leray-solutions-of-the-forced-Navier-Stokes/10.4007/annals.2022.196.1.3.full;
    roles forced Leray nonuniqueness boundary || force and solution-class quarantine || R9 and R11 boundary.
    Carrier kind theorem mapped from the register's own type field by the rule *journal_article → theorem,
    preprint → theorem, official_problem_statement → artifact*, stated in the Conventions section. stable_link
    is the DOI resolver form of the DOI printed in this repository's own register row (doi 10.4007/annals.2022.196.1.3).
    No identifier in this document was resolved on the web by the citation lane: this repository's own
    register and its own markdown links are the only literature authority used here. An empty cites array
    is a claim of independence under the carrier, so the claim here is scoped: this repository records
    no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.4007/annals.2022.196.1.3
  cites: []
  cited_by: []
- id: arxiv:1711.00321
  title: '[title not recorded in repo text] — and their hypotheses'
  kind: theorem
  authors:
  - name: Khesin
    role: person
  - name: Misiołek
    role: person
  - name: Modin
    role: person
  year: 2017
  venue_or_status: >-
    Cited by this repository at docs/QUANTIZATION_REGULARITY_WICK.md:62-66 — "For geometric treatments
    and their hypotheses, see Khesin–Misiołek–Modin and the Khesin–Modin preprint, which discusses noncritical
    zeros, the Madelung momentum map, and circulation quantization. These cited results are not claimed
    as formalized in this repository." That citation is a markdown link whose label this lane parses for
    author names and whose URL this lane parses for the identifier: the URL carries the arXiv identifier
    1711.00321, and stable_link is the canonical resolver form of the SAME identifier (https://arxiv.org/abs/1711.00321)
    — the id is measured from repo text, the URL form is canonicalised, not invented. year DERIVED from
    the arXiv identifier's submission prefix (1711 = 2017-11); the repository prints no year for this
    work. Title provenance: the repository prints no title for this work, so the title field carries the
    repository's own descriptive phrase, cut out of the citing sentence, and marks the absence. The repository's
    descriptive phrase, verbatim: docs/QUANTIZATION_REGULARITY_WICK.md:62-66, span verbatim — "and their
    hypotheses" And the repository's own scope statement on this work: docs/QUANTIZATION_REGULARITY_WICK.md:66-66
    — "These cited results are not claimed as formalized in this repository." Typed absences: title, given
    names, venue pages. No identifier in this document was resolved on the web by the citation lane: this
    repository's own register and its own markdown links are the only literature authority used here.
    Graded theorem because the repository calls these *cited results* while stating they are not formalized
    here. An empty cites array is a claim of independence under the carrier, so the claim here is scoped:
    this repository records no dependency edge for this entry — it does not assert that the work stood
    on nothing.
  stable_link: https://arxiv.org/abs/1711.00321
  cites: []
  cited_by:
  - navier.madelung.winding-quantization
- id: arxiv:2607.01024
  title: >-
    [title not recorded in repo text] — noncritical zeros, the Madelung momentum map, and circulation
    quantization
  kind: artifact
  authors:
  - name: Khesin
    role: person
  year: 2026
  venue_or_status: >-
    Cited by this repository at docs/QUANTIZATION_REGULARITY_WICK.md:62-66 — "For geometric treatments
    and their hypotheses, see Khesin–Misiołek–Modin and the Khesin–Modin preprint, which discusses noncritical
    zeros, the Madelung momentum map, and circulation quantization. These cited results are not claimed
    as formalized in this repository." That citation is a markdown link whose label this lane parses for
    author names and whose URL this lane parses for the identifier: the URL carries the arXiv identifier
    2607.01024, and stable_link is the canonical resolver form of the SAME identifier (https://arxiv.org/abs/2607.01024)
    — the id is measured from repo text, the URL form is canonicalised, not invented. year DERIVED from
    the arXiv identifier's submission prefix (2607 = 2026-07); the repository prints no year for this
    work. Title provenance: the repository prints no title for this work, so the title field carries the
    repository's own descriptive phrase, cut out of the citing sentence, and marks the absence. The repository's
    descriptive phrase, verbatim: docs/QUANTIZATION_REGULARITY_WICK.md:62-66, span verbatim — "noncritical
    zeros, the Madelung momentum map, and circulation quantization" Typed absences: title, given names,
    venue pages. No identifier in this document was resolved on the web by the citation lane: this repository's
    own register and its own markdown links are the only literature authority used here. Graded artifact
    rather than theorem because the repository states a topic for this preprint, not a result. An empty
    cites array is a claim of independence under the carrier, so the claim here is scoped: this repository
    records no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://arxiv.org/abs/2607.01024
  cites: []
  cited_by:
  - navier.madelung.winding-quantization
- id: arxiv:1905.02467
  title: quantum vortex reconnections in smooth Gross–Pitaevskii solutions
  kind: theorem
  authors:
  - name: Enciso
    role: person
  - name: Peralta-Salas
    role: person
  year: 2019
  venue_or_status: >-
    Cited by this repository at docs/QUANTIZATION_REGULARITY_WICK.md:89-92 — "Navier–Stokes. For a genuine
    PDE result, Enciso and Peralta-Salas prove quantum vortex reconnections in smooth Gross–Pitaevskii
    solutions. That external theorem establishes that reconnection and smooth wavefunction evolution can
    coexist; it is not part of our Lean proof closure." That citation is a markdown link whose label this
    lane parses for author names and whose URL this lane parses for the identifier: the URL carries the
    arXiv identifier 1905.02467, and stable_link is the canonical resolver form of the SAME identifier
    (https://arxiv.org/abs/1905.02467) — the id is measured from repo text, the URL form is canonicalised,
    not invented. year DERIVED from the arXiv identifier's submission prefix (1905 = 2019-05); the repository
    prints no year for this work. Title provenance: the link TEXT this repository prints is a descriptive
    phrase, not a publisher title, so the title field above reproduces it and marks it as such. And the
    repository's own scope statement on this work: docs/QUANTIZATION_REGULARITY_WICK.md:91-92 — "That
    external theorem establishes that reconnection and smooth wavefunction evolution can coexist; it is
    not part of our Lean proof closure." Typed absences: none for title — the repository prints the phrase
    as the link text, given names, venue pages. No identifier in this document was resolved on the web
    by the citation lane: this repository's own register and its own markdown links are the only literature
    authority used here. This is the one literature link in repo prose whose link TEXT is a result description
    rather than an author list; the author names are therefore parsed out of the sentence that precedes
    the link. An empty cites array is a claim of independence under the carrier, so the claim here is
    scoped: this repository records no dependency edge for this entry — it does not assert that the work
    stood on nothing.
  stable_link: https://arxiv.org/abs/1905.02467
  cites: []
  cited_by:
  - navier.madelung.winding-quantization
- id: arxiv:1111.4670
  title: '[title not recorded in repo text] — does not reconstruct a single-valued wavefunction'
  kind: theorem
  authors:
  - name: Carles
    role: person
  - name: Danchin
    role: person
  - name: Saut
    role: person
  year: 2012
  venue_or_status: >-
    Cited by this repository at docs/MADELUNG_CORRESPONDENCE.md:28-31 — "the resulting velocity has zero
    curl. Nonzero density and the topology of the phase matter; a fluid formulation does not reconstruct
    a single-valued wavefunction. See Carles, Danchin and Saut (2012) and Wallstrom (1994)." That citation
    is a markdown link whose label this lane parses for author names and whose URL this lane parses for
    the identifier: the URL carries the arXiv identifier 1111.4670, and stable_link is the canonical resolver
    form of the SAME identifier (https://arxiv.org/abs/1111.4670) — the id is measured from repo text,
    the URL form is canonicalised, not invented. year 2012 read out of the label this repository prints.
    Title provenance: the repository prints no title for this work, so the title field carries the repository's
    own descriptive phrase, cut out of the citing sentence, and marks the absence. The repository's descriptive
    phrase, verbatim: docs/MADELUNG_CORRESPONDENCE.md:28-31, span verbatim — "does not reconstruct a single-valued
    wavefunction" Typed absences: title, given names, venue pages. No identifier in this document was
    resolved on the web by the citation lane: this repository's own register and its own markdown links
    are the only literature authority used here. The repository's URL points at the /html/ v1 render;
    the stable link here is the /abs/ resolver form of the same identifier. An empty cites array is a
    claim of independence under the carrier, so the claim here is scoped: this repository records no dependency
    edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://arxiv.org/abs/1111.4670
  cites: []
  cited_by:
  - navier.madelung.regularity-comparison
- id: doi:10.1103/physreva.49.1613
  title: >-
    [title not recorded in repo text] — and the topology of the phase matter; a fluid formulation does
    not reconstruct a single-valued wavefunction
  kind: theorem
  authors:
  - name: Wallstrom
    role: person
  year: 1994
  venue_or_status: >-
    Cited by this repository at docs/MADELUNG_CORRESPONDENCE.md:28-31 — "the resulting velocity has zero
    curl. Nonzero density and the topology of the phase matter; a fluid formulation does not reconstruct
    a single-valued wavefunction. See Carles, Danchin and Saut (2012) and Wallstrom (1994)." That citation
    is a markdown link whose label this lane parses for author names and whose URL this lane parses for
    the identifier: the URL carries the DOI identifier 10.1103/PhysRevA.49.1613, and stable_link is the
    canonical resolver form of the SAME identifier (https://doi.org/10.1103/PhysRevA.49.1613) — the id
    is measured from repo text, the URL form is canonicalised, not invented. year 1994 read out of the
    label this repository prints. Title provenance: the repository prints no title for this work, so the
    title field carries the repository's own descriptive phrase, cut out of the citing sentence, and marks
    the absence. The repository's descriptive phrase, verbatim: docs/MADELUNG_CORRESPONDENCE.md:28-31,
    span verbatim — "and the topology of the phase matter; a fluid formulation does not reconstruct a
    single-valued wavefunction" Typed absences: title, given names, venue pages. No identifier in this
    document was resolved on the web by the citation lane: this repository's own register and its own
    markdown links are the only literature authority used here. The repository's URL is the publisher
    landing page; the DOI parsed out of it is used as the canonical resolver link. An empty cites array
    is a claim of independence under the carrier, so the claim here is scoped: this repository records
    no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1103/PhysRevA.49.1613
  cites: []
  cited_by:
  - navier.madelung.regularity-comparison
- id: doi:10.1103/physrevresearch.6.043130
  title: >-
    [title not recorded in repo text] — a Navier–Stokes representation using a two-component wavefunction
    and a nonlinear Schrödinger–Pauli equation with imaginary diffusion
  kind: theorem
  authors:
  - name: Meng
    role: person
  - name: Yang
    role: person
  year: 2024
  venue_or_status: >-
    Cited by this repository at docs/MADELUNG_CORRESPONDENCE.md:168-172 — "Meng and Yang (2024) develop
    a Navier–Stokes representation using a two-component wavefunction and a nonlinear Schrödinger–Pauli
    equation with imaginary diffusion. Their effective spin system is non-Hermitian. This is a closer
    research connection than the ordinary scalar Madelung transform." That citation is a markdown link
    whose label this lane parses for author names and whose URL this lane parses for the identifier: the
    URL carries the DOI identifier 10.1103/PhysRevResearch.6.043130, and stable_link is the canonical
    resolver form of the SAME identifier (https://doi.org/10.1103/PhysRevResearch.6.043130) — the id is
    measured from repo text, the URL form is canonicalised, not invented. year 2024 read out of the label
    this repository prints. Title provenance: the repository prints no title for this work, so the title
    field carries the repository's own descriptive phrase, cut out of the citing sentence, and marks the
    absence. The repository's descriptive phrase, verbatim: docs/MADELUNG_CORRESPONDENCE.md:168-172, span
    verbatim — "a Navier–Stokes representation using a two-component wavefunction and a nonlinear Schrödinger–Pauli
    equation with imaginary diffusion" Typed absences: title, given names, venue pages. No identifier
    in this document was resolved on the web by the citation lane: this repository's own register and
    its own markdown links are the only literature authority used here. The citing paragraph is this repository's
    own summary of the work, not a verified abstract; the quote above is that summary. An empty cites
    array is a claim of independence under the carrier, so the claim here is scoped: this repository records
    no dependency edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1103/PhysRevResearch.6.043130
  cites: []
  cited_by:
  - navier.madelung.regularity-comparison
- id: doi:10.1017/jfm.2024.1193
  title: '[title not recorded in repo text] — of mode-to-mode transfers'
  kind: artifact
  authors:
  - name: Ding
    role: person
  - name: Chung
    role: person
  - name: Illingworth
    role: person
  year: 2024
  venue_or_status: >-
    Cited by this repository at docs/TRIADS_AND_SYMMETRY.md:81-82 — "For the fluid interpretation of mode-to-mode
    transfers, see Ding, Chung and Illingworth, Journal of Fluid Mechanics." That citation is a markdown
    link whose label this lane parses for author names and whose URL this lane parses for the identifier:
    the URL carries the DOI identifier 10.1017/jfm.2024.1193, and stable_link is the canonical resolver
    form of the SAME identifier (https://doi.org/10.1017/jfm.2024.1193) — the id is measured from repo
    text, the URL form is canonicalised, not invented. year DERIVED from the year token inside the DOI
    this repository prints (2024); the repository prints no year for this work. Title provenance: the
    repository prints no title for this work, so the title field carries the repository's own descriptive
    phrase, cut out of the citing sentence, and marks the absence. The repository's descriptive phrase,
    verbatim: docs/TRIADS_AND_SYMMETRY.md:81-82, span verbatim — "of mode-to-mode transfers" Typed absences:
    title, given names, venue pages. No identifier in this document was resolved on the web by the citation
    lane: this repository's own register and its own markdown links are the only literature authority
    used here. Graded artifact: the repository names no result for this work, only the topic it is a reference
    for, so it is an orphan in this graph — no unit entry depends on it. An empty cites array is a claim
    of independence under the carrier, so the claim here is scoped: this repository records no dependency
    edge for this entry — it does not assert that the work stood on nothing.
  stable_link: https://doi.org/10.1017/jfm.2024.1193
  cites: []
  cited_by: []
```

## How this block was checked

Written by lane `Q50-NAVIER-CITE-EXEC-1103` on 2026-11-03 (host `Tims-MBP-2.localdomain`) as
additive files only — `CITATION.cff`, this file, a README `## How to cite` section and a
`docs/README.md` index row; no deletion, no retraction, no change to any Lean source.

**It is generated, not typed.** This block is emitted by a generator that reads the repository at
`a4b066c6d267…` through `git show <pin>:<path>`: RESULT_MAP and OPEN_FRONTIER_MAP table cells are
parsed out of their rows, declaration lines and axiom receipts are pulled out of the source files,
authorship lines are read out of each carrier file's own header, and every literature field is read
out of `references/manifest.json` or out of the citing markdown link. Hand-typing a repository
sentence is what makes a citation drift when the sentence changes; here a changed upstream sentence
changes this file instead of silently falsifying it.

Denominators measured at generation time: **63 entries**
(39 internal units, 17 register sources, 7 works cited in `docs/` prose),
**48 `cites` edges**, each mirrored exactly once into the target's `cited_by`,
kinds = theorem 49
/ algorithm 2 / dataset 0
/ artifact 12; 26 independence claims scoped in-file;
39 entries carry an org-only author set and every one states the reason in-file
(36 of them by this generator pass, the rest inside their own extraction), as the carrier's
rule 3 requires.

Three validators run over this file and `CITATION.cff` on the lane branch before it is offered for
fold; their per-leg counts and exit codes are recorded in the lane's RESULT.json receipts, not
asserted here:

1. `cff_validate.py` — `CITATION.cff` against the CFF **1.2.0** schema
   (`schema.json` at tag 1.2.0 of citation-file-format/citation-file-format, vendored by
   `Q50-NAVIER-CITE-PREP-1103`), which has a root `pattern: ^1\.2\.0$` and
   `additionalProperties: false`; it also asserts the reference-type enum and the
   `required: [authors, title, type]` of `definitions.reference`.
2. The Awkronos carrier `contracts/citation-schema.json`, read from the carrier commit
   `b2ec1cc2c270c7293b86b58a8da4b4e354668372` by `git -C ~/.claude show
   b2ec1cc2c…:contracts/citation-schema.json` — **that path is not on the spine's `main`**, so the
   carrier-sha read is the sanctioned one and this receipt names the sha. Validated with
   `jsonschema.Draft202012Validator` + `FormatChecker` in three legs: this document against
   `$defs.citation_document`, the `how_to_cite` block against `$defs.how_to_cite_block`, and every
   entry against the root `citation_entry` schema.
3. `cite_validate.py` — the carrier's `x-cross-field` rules that JSON Schema cannot state: unique
   ids, the `citation_id` pattern (lowercase; uppercase ids are rejected), the
   `x-stable-link-shapes` test on every `stable_link` (branch-anchored URLs are rejected),
   referential integrity of `cites`/`cited_by` in both directions, the org-author explanation
   requirement, and rule 6 agreement between `CITATION.cff`, this `how_to_cite` block and the
   README BibTeX on title, authors and `repository-code`. A harness crash exits 2, never 0, so an
   instrument fault cannot read as a green leg.

A fourth, read-only probe (`verify_claims.py`) re-checks this document against the repository,
independently of the generator, in eight legs: **P** every `stable_link` path exists at the pin with
the claimed blob/tree type (`git cat-file`); **D** every named Lean declaration is an actual
declaration line in a tracked source — the leg probes dotted names in this document's claim text and
states which names resolve to a declaration line and which are present-but-not-a-declaration-line,
and it skips JSON-Schema pointers and Python class names, which the validator legs are the authority
for; **Q** every double-quoted span of 25+ characters is found verbatim in a tracked blob at the pin,
after the same delimiter normalisation the generator applies; **N** every `path:line` claim is checked
by *locating the quoted span and comparing its line*, so right text at a wrong line number fails;
**S** no long quotation survives in single quotes (single quotes mark this document's own emphasis),
with genitive apostrophes excluded because they are English, not citation; **H** every 40-hex token
is accounted for as either a revision quoted out of repo text or a commit that actually resolves in
the repository the document names (navier, or the substrate repository carrying
`contracts/citation-schema.json`) — never a plausible-looking sha that exists nowhere; **V** every
name introduced in the form references/manifest.json id <ID> resolves to a real source id; **C** a
negative control, which
mutates real spans (one character, an inserted space, deleted characters) and requires the **Q** leg
to reject them, so a leg that would accept anything is exposed rather than trusted. **Q**, **N**,
**S**, **H**, **V** and **D** run over the whole file — this header and the receipt included, with
the YAML fence replaced by its decoded content so PyYAML's own quoting is not mistaken for a
quotation. Where a claim could not be checked that way it is marked as derived, inferred or a typed
absence inside `venue_or_status` itself.

No Lean build or re-elaboration was run by this lane: axiom closures are quoted from
`Navier/AxiomAudit.lean`, `Navier/ConditionalAudit.lean` and `scripts/AuditAllAxioms.lean` as the
repository recorded them, not re-measured here, and an entry whose declaration no receipt names says
so as a typed absence instead of quoting a closure.

## Unresolved attributions — typed absences

These works are cited by this repository's prose, but the identifier is **not** present
anywhere in repo text, so no entry exists for them above and no stable link is invented
here. Fill each from its own landing page before promoting it; a wrong-but-plausible
identifier is worse than an absent one.

| work, as repo prose names it | where repo text says it | what repo text actually carries |
|-|-|-|
| Madelung (1926) | `docs/MADELUNG_CORRESPONDENCE.md` | prose-only attribution: no DOI, no arXiv id, no title in repo text |
| Orszag 2/3 dealiasing | `solver/README.md:10` | "componentwise Orszag 2/3 dealiasing" — a method name and a fraction; no identifier in repo text |

Both are named inside the entries that depend on them
(`navier.madelung.regularity-comparison`, `navier.algorithm.rust-spectral-solver`) so the
gap is visible at the point of use rather than hidden in a footnote.

## Prose-only attributions to upgrade — blocked, not skipped

`docs/FALSIFICATION_LEDGER.md` row **F-027** attributes two class-decay facts in prose only:

- **Dobrokhotov–Shafarevich 1994** (Math. Notes 55) — faster-than-`|x|^{-4}` decay forces
  `∫ uᵢuⱼ dx = c(t) δᵢⱼ`.
- **Brandolese 2004** (Math. Ann. 329) — the `|x|^{-4}` rate is attained at positive times
  for generic data. The ledger row also carries the string "arXiv 2003-04-28", which is a
  **date-shaped non-identifier**, not an arXiv id; do not promote it into one.

Neither has an identifier in repo text. Per the register law these rows stay typed
absences; the citation lane did not substitute a web-resolved identifier for a register
row the repository never measured.

## Owner rulings still open (blocking nothing above, changing two fields)

- **R-H — `authors:`.** `CITATION.cff` carries `Tim Jacoby` + `Awkronos` marked
  `[A-CONFIRM]`; per-result entries carry `Awkronos` with the measured basis quoted in
  `venue_or_status`. A person-per-theorem mapping is not synthesized from commit metadata.
  Ruling changes `CITATION.cff authors:` and each entry's `authors`, nothing else.
- **R-I — `license:`.** `MIT` (GitHub-detected SPDX) vs `MIT AND Apache-2.0` (mixed:
  adapted modules preserve upstream notices). Ruling changes one `license:` field.

## What a fold must re-check

This document pins `a4b066c6d26742a36e4f914b1ea56e2a6c88f12b`. On fold to a newer tip,
re-pin every internal `stable_link` to the new commit sha, re-run the three validators named
in the `How this block was checked` receipt above, re-run `verify_claims.py` over this file,
and re-check the declaration names against
`docs/RESULT_MAP.md` — a theorem renamed without an alias row silently breaks every entry
that cites it.
