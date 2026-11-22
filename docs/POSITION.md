# The Awkronos position on the Navier–Stokes problem

This document is the standing position statement of
[awkronos/navier](https://github.com/awkronos/navier). It is maintained, not
published-and-forgotten: every claim here mirrors a row of
[`formalization.yaml`](../formalization.yaml), the claim manifest, and the
scope gate recomputes the manifest at each head. When a claim changes, the
manifest row changes first and this page follows. Dated measurement prose
does not belong here; dated records live under
[`history/`](history/).

## What we claim

**Forced whole-space alternative C is proved.** The Lean theorem
`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown` inhabits
Fefferman's whole-space breakdown alternative: for every positive viscosity
there are admissible initial data and a smooth rapidly decaying force for
which no global smooth bounded-energy classical solution exists. Its
transitive axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`. The strengthening with successive-partial regularity and the
deadline-parameterized variant carry the same axiom set as manifest rows
`crown_C_whole_space_successive_partials` and `crown_C_deadline_parameterized`.

**Forced periodic alternative D is proved.** `PeriodicConstructedBreakdown.periodicBreakdown`
supplies, for every positive viscosity, admissible periodic forcing that
excludes every global smooth periodic velocity-pressure pair
(`crown_D_periodic_forced`).

Two scope facts are part of the theorem types, not prose caveats. "Globally
smooth" applies to the **force**; the constructed velocity is smooth on every
pre-singular interval and is proved not to admit a global classical
continuation satisfying the official energy contract. The excluded competitor
may choose a different finite energy bound on each closed pre-singular slab,
so the obstruction is stronger than the official endpoint needs.

**The provenance boundary.** The analytical construction is OpenAI's,
adapted from `openai/NavierStokesAndEuler` at pinned revision
`8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538` with Apache-2.0 notices preserved
([provenance note](OPENAI_CONSTRUCTION_PROVENANCE.md)). Awkronos's native
contribution is the transport into the original native PDE carrier, the
additional force-derivative comparisons, the periodic construction, the
solvers, and the interactive explanation. The claim of this repository is
its own checked theorem at its own pinned head, compiled on the toolchain
the repository pins.

## What we do not claim

**The Clay Millennium problem is `OPEN`.** Unforced three-dimensional
Navier–Stokes existence and smoothness, alternatives A and B at zero force,
is neither proved nor claimed here, in the manifest, or on any surface of
this project. The forced construction does not touch it: a counterexample
with force says nothing about every datum without force. Comparison before
the singular time does not assert uniqueness of a weak continuation after
it.

The manifest's four `OPEN` rows name the boundary exactly:

| Row | Surface | Bearing on the Clay problem |
| --- | --- | --- |
| `open_A_whole_space_unforced` | `ProblemStatements.WholeSpaceGlobalRegularity` | direct |
| `open_B_periodic_unforced` | `ProblemStatements.PeriodicGlobalRegularity` | direct |
| `open_bkm_vorticity_integral_divergence_residual` | scalar vorticity-rate estimate for the selected profile of the constructed forced field | inside the forced route; everything from this leaf to the crown is proved |
| `open_mild_assembly_leaves_instantiation` | non-degenerate discharge of the mild-assembly time leaves | live construction target, not an assumption of the crown |

The five `CONDITIONAL_THEOREM` rows keep their hypotheses in their types:
a conditional theorem is not a theorem until its premise is supplied, and
the manifest names the premise of each. None of them is an assumption of
`wholeSpaceBreakdown`.

## Standing method: barriers

A barrier is a test that prevents a familiar conditional, weak, numerical,
or altered-model result from being promoted past its scope. The full
[kill matrix](BARRIERS.md) is current method, not history; its load-bearing
rows as they bear on this position:

- **Scaling/criticality.** Energy and supercritical norms shrink under the
  Navier–Stokes scaling while critical norms stay fixed; no scale-uniform
  critical control follows from energy size alone. The obstruction is
  kernel-certified in Lean (`Navier.EnergyObstruction.energy_not_scale_coercive`).
- **Energy-only.** Any argument using only properties of the bilinear form
  preserved under Tao-admissible averaging settles nothing: the averaged
  equation blows up ([TAO2016]). A decisive positive estimate must
  distinguish the exact Navier–Stokes symbol.
- **Endpoint-as-assumption.** Serrin, `L^∞_t L^3_x`, BKM-type, and strain
  criteria assumed outright are the conclusion restated. Assumed bounds
  move into the open-residual field, they do not close routes.
- **Weak/smooth category.** Weak existence and weak non-uniqueness
  (Leray; Buckmaster–Vicol; Albritton–Brué–Colombo) are not alternative A,
  C, or D witnesses. The forced C and D constructions were inhabited
  independently, and the ledger bars citing the non-uniqueness papers as
  their witnesses.
- **Model/domain drift.** 2D, Euler, dyadic, hyperdissipative, bounded-domain,
  and periodic results do not transfer to whole-space A without an explicit
  transfer theorem.
- **Statement-paraphrase drift.** The working target is diffed against
  Fefferman's clause verbatim; a narrower paraphrase (zero-force reading,
  velocity-only periodicity) never counts as the official target.
- **Numerics-as-proof and text-as-proof.** Solver output is numerical
  evidence about a truncated model, never a theorem; and a status claim is
  bound to a compiler receipt at a named revision, never to a grep or a
  prose line.

## Standing method: the falsification ledger

The [ledger](FALSIFICATION_LEDGER.md) is append-only: entries record killed
claim classes, the witness class (M: the mathematics; I: an inference or
misreading of scope; T: a missing model transfer), the consequence, and the
permitted successor. A published theorem remains valid in its stated scope
even when a stronger use of it is killed. This position is the ledger's
current balance, and the ledger is what makes the position revisable without
being unstable.

## What would change this position

This section is the falsifier list. Each entry names the observation and the
exact effect on the claim set.

1. **A compiler event at the pinned head.** If `lake build` at a head fails
   on the endpoint's dependency chain, or the raw `#print axioms` census of
   `wholeSpaceBreakdown` prints anything outside `propext`,
   `Classical.choice`, `Quot.sound`, the `THEOREM` row is demoted to an
   explicit UNMEASURED-at-this-head state until a fresh receipt exists. The
   manifest row and the README headline change together; the gate refuses a
   README that outruns the manifest.
2. **A semantic-drift finding against our carrier.** The adapted C carrier
   is compared clause by clause with Fefferman's official wording in
   [CONSTRUCTION_REVIEW.md](CONSTRUCTION_REVIEW.md), and the force predicate
   has an exact equivalence with ordered-coordinate rapid decay
   ([ForceCoordinateEquivalence.lean](../Navier/Analysis/ForceCoordinateEquivalence.lean)).
   The residual the repository records is the total-Frechet versus
   coordinatewise multi-index half of the general force-clause bridge: if it
   were shown that our carrier is not the official alternative C, the claim
   narrows to its working paraphrase (ledger class I); it does not vanish.
3. **A soundness event below us.** A contradiction in the pinned Mathlib
   revision or the Lean kernel would put every formal claim in the estate in
   question at once; the position would then read as conditional on the
   repaired base. This is not a Navier-specific risk and no local edit
   addresses it.
4. **An external resolution of A or B, either direction.** A proof or a
   counterexample of unforced global regularity changes the
   `open_A`/`open_B` rows and the Clay paragraph of this position, with a
   named declaration if it is formalized and compiler-checked. It does not
   touch the C or D rows.
5. **Reconciliation with the Alpöge–Buckmaster formalization.** See the next
   section. Their rebuild, certificate release, or interval-verification
   release moves the *external context* paragraph and, if their formal
   artifact proves an official-surface breakdown, joins the standing
   literature in the `OPEN` rows' context; it cannot move our manifest rows,
   which are receipts about our bytes.

## Position relative to external formalizations

The repository's only proved objects are its own manifest rows. External
formalizations are context, cited with their own conditionality spelled out.

**OpenAI's construction** is the analytical basis of the adapted modules
(`Navier/Construction`, pinned revision above). Its paper, *Finite time
blowup for Navier–Stokes*, motivates the construction; this repository's
claim is the checked Lean theorem, not the paper.

**The Alpöge–Buckmaster package** (*Finite-time blow-up for the
Navier–Stokes equations*, L. Alpöge and T. Buckmaster; Lean 4 package with
the paper of 20 November 2026) is an independent formalization effort. On
their own README and NOTICE: it is a Lean v4.33.1 package depending on
Mathlib; the top-level statement files state theorems with `sorry` in place
of proofs and `Solution.lean` proves them from the `Breakdown/` library; the
comparator files permit exactly `propext`, `Quot.sound`, and
`Classical.choice`.

Their architecture is conditional at the point where a claim meets data.
`breakdown_on_space` and `breakdown_on_torus` assume the existence of a
nonzero smooth self-similar solution (periodic in time up to a fixed linear
isometry, with stated decay). Three further theorems derive from the
existence of a certificate, and their NOTICE states plainly: "No certificate
is given in this package." The cell-system theorems assume data of seven
kinds, and again: "No such data are given in this package." The certificate
whose hash their paper gives is not in their repository, and the interval
verification that the certificate satisfies the Appendix B conditions "is
not part of the formalization and is not in this repository either." Their
README states that "the patched package was not rebuilt when this repository
was assembled."

So at their current head, their published formal artifact is the one whose
final rebuild is outstanding. That is their record to finish, and nothing
here reaches it in either direction. The symmetry we insist on is this: the
object proved in this repository, `wholeSpaceBreakdown`, was compiler-checked
at its pinned head with transitive axioms exactly `propext`,
`Classical.choice`, and `Quot.sound`; an upstream patch, ours or theirs,
cannot un-check these bytes. Whether the rebuilt Alpöge–Buckmaster program
covers the same official surface as our whole-space alternative C is a live
identity question, under separate measurement.

<!-- BACKFOAM slot: measured integration numbers (file census of their
package, rebuild/verification receipts if and when published, the identity
diff of their statements against Navier/Problem.lean clause surfaces) land
here as a follow-up commit. Until then this section quotes only their own
README and NOTICE text. -->

## Maintenance law

- Claims live in [`formalization.yaml`](../formalization.yaml). Prose mirrors
  rows. No claim is added, strengthened, or imported by a sentence.
- The scope gate
  [`scripts/test_readme_scope_truth.py`](../scripts/test_readme_scope_truth.py)
  recomputes counts and headline claims at each run; the structure checker
  validates every row's declaration, file, and axiom allowlist.
- Theorem names from external repositories never become manifest rows.
- Dated measurements are moved to [`history/`](history/), with a one-line
  header, when they stop bearing on the current position.
