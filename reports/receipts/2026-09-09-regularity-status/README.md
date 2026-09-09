# Regularity status — fresh LSP and compiler examination

2026-09-09. This is an endpoint audit, not a repository-wide proof census.
The A/B global-control research and visual redesign remain in progress.

| Original endpoint | Status at this audit | What the current proof actually supplies |
| --- | --- | --- |
| A: `WholeSpaceGlobalRegularity` | Open | The native composition theorem consumes local classical existence, pressure-normalized continuation, and a horizon-independent a priori bound for the same quantity. Those remain explicit premises. |
| B: `PeriodicGlobalRegularity` | Open | Native periodic velocity uniqueness; faithful Fourier initialization and exact reconstruction of the initial datum. Time-dependent classical realization and arbitrary-data global control remain required. |
| C: `WholeSpaceBreakdown` | Proved | `ConstructedBreakdown.wholeSpaceBreakdown` has the exact original type and no analytic premise. |
| D: `PeriodicBreakdown` | No accepted endpoint witness in this audit | The native definition exists; viscosity and convention transports are conditional and are not an inhabitant of D. The use of periodic intermediate fields in C does not itself close native D. |

A and B fix force to zero. C and D allow a selected force. Thus C does not
refute A or B. The exact official alternatives are specified in `Navier/Problem.lean`
and `Navier/OfficialProblem.lean`.

## Evidence

The canonical CLI LSP returned zero error diagnostics for `Problem.lean`,
`OfficialProblem.lean`, `ConstructedBreakdown.lean`, and
`PeriodicDatumFourierConstraints.lean`. At the C proof body it displayed the
actual goal `ProblemStatements.WholeSpaceBreakdown`. LSP hover resolved
`CriticalMildOffZeroTerminalBound` as a proposition with viscosity, datum and
bound parameters, not as a proved bound.

The obstruction module returned zero errors, one tactic-style suggestion and
raw axiom information. Its LSP client emitted an EOF exception during shutdown
on both the initial call and the single retry. These diagnostics are advisory;
the direct compiler completed successfully and carries acceptance.

Fresh single-file source compilation, with exact `#check` and raw qualified
`#print axioms`, exited 0 for:

- C and its finite-energy/successive-coordinate-partial consequences;
- the conditional whole-space composition theorem;
- periodic classical velocity uniqueness and its conditional B consumer;
- canonical Fourier-carrier divergence freedom and Hermitian reality;
- selected-force support, nonzero forcing, slab uniqueness, speed transfer and
  the locally finite-energy continuation obstruction;
- exact periodic initial reconstruction, independently checked in its frozen
  reconstruction worktree before integration.

The audited declarations print only `propext`, `Classical.choice`, `Quot.sound`.
The checked conditional theorems still carry the explicit premises printed in
their types. A clean axiom list does not discharge them.

Compiler command: `~/.claude/hooks/lean-build-lock.sh 300 lake env lean <source>`.
Source copies appended the named diagnostic commands; no proof term was changed.
The raw outputs are preserved alongside this note. The frozen reconstruction
artifact was SHA-256
`946158217b238334b10cf59dc07e280edf8c408c9a084812e04648bbbcd0a5e9`;
main subsequently moves its trailing diagnostics to the evolution receipt.

## Exact construction class

At unit viscosity the selected fields satisfy:

- zero initial velocity;
- velocity and pressure smooth on `[0,1) × R³`;
- divergence-free velocity and the pointwise forced equation on `0<t<1`;
- one compact spatial support for the velocity on the entire presingular interval;
- one uniform finite kinetic-energy bound on `[0,1)`;
- a force smooth on all real spacetime, compactly supported on physical
  spacetime, and identically zero after a finite future cutoff;
- a force nonzero somewhere at a time strictly between zero and one;
- for every `M>0` and `delta>0`, some `1-delta<t<1`, `t>0`, and some `x`
  satisfy `norm(u(t,x))>M`.

Every same-force, zero-initial-data competitor with smooth velocity and pressure,
the pointwise equation, incompressibility, and a finite energy bound on each
closed slab `[0,T]`, `T<1`, agrees with the candidate. The competitor's bounds
may depend on T. It requires neither compact spatial support nor pressure-gauge
normalization. Hence it cannot continue continuously through time one on the
candidate's compact support.

This excludes the official global classical bounded-energy class. It does not
prove existence, uniqueness or nonexistence of weak continuations, nor specify
an optimal Sobolev or Hölder regularity threshold for such continuations.

The force is the residual of the constructed velocity and pressure, completed
by convergent correction series and a smooth cutoff. For each ordered mixed
partial and each polynomial weight K, a finite bound exists on nonnegative
time. The proof does not provide one uniform constant across all derivative
orders, analyticity, genericity, stability under perturbation, or a small-force
bound. The final witness uses classical choice and an infinite diagonal schedule;
it is not the finite Rust field displayed by the simulator.

The checked viscosity transport uses `u_nu(t,x)=nu*u(nu*t,x)`,
`p_nu(t,x)=nu²*p(nu*t,x)`, `f_nu(t,x)=nu²*f(nu*t,x)`.
The native C endpoint is quantified over every positive viscosity. Refined
speed-transfer declarations are currently normalized to unit viscosity/time one.

## Exact global-control obligation

For each physically phase-encoded initialized lattice datum a and positive raw
viscosity mu, prove
there is a finite K depending on a and nu but not the chart horizon T or radius R,
such that every actual original-data mild chart obeys
`offZeroMixedCriticalQty nu (u T) <= K`.
Here the displayed declaration's viscosity argument `nu` denotes the raw
coefficient `mu=(2*pi)^2*nu_physical`. The initializer is
`A=-2*pi*I*u_hat`; its reality law is anti-Hermitian. The unrestricted complex
version of this bound is under a separate counterexample audit. It cannot be
silently identified with the physical-data obligation.
The zero mode is conserved and is removed from this obligation. The bound feeds
the existing terminal-norm and cofinal global-mild consumers. It is not, by
itself, the native classical B theorem: smooth space-time reconstruction, the
pressure/PDE bridge and initial trace must also be consumed. Whole-space A
additionally needs the physical whole-space transport, not a periodic surrogate.

The new dynamic Dini estimate and interior time-modulus artifacts are useful
local inputs. Constants depending on an assumed chart radius do not constitute
this horizon-independent arbitrary-data bound.

LSP shutdown trace paths are redacted to `<home>`; diagnostics and all theorem/axiom messages are unchanged.

## Exact endpoint verifier refresh

`endpoint-audit.txt` records a fresh source/type/axiom audit: C's dependency
receipts are 615/615 and its exact endpoint consumer passes. A, B, and D have
no unconditional witness in this audit. This is the audit's scope, not a
prohibition on constructing those proofs. `rejected-pressure-as-B.txt` records
the exact Lean type mismatch when a coefficient-level pressure prerequisite
is deliberately offered as a B witness.

Run `python3 scripts/verify_construction.py --audit-regularity-endpoints`.
Register a proposed proof with `--endpoint-witness B=Module:Declaration`;
the verifier compiles its current source, checks the exact original consumer,
prints transitive axioms, and checks dependency freshness. Use
`--endpoint-prerequisite B=Module:Declaration` for a supporting result.
