# Navier

An evidence-gated, parallel mathematical research and formalization research_program
for the three-dimensional incompressible Navier–Stokes problem.

This repository does not claim a solution. Live repository proof status exists
only in `/tmp/proof-report.json`. Refresh the central report with
`~/.claude/scripts/proof-report-refresh.sh --oneline` and select the `navier`
row before making any build or closure claim.

The repository separates kernel-checked infrastructure, conditional regularity
routes, open analytic payloads, computational observations, and falsified
approaches. Lean source and fresh compiler output determine formal status.

The primary formal surface is Fefferman's whole-space
existence-and-smoothness statement (A): for every positive viscosity and every
rapidly decaying smooth divergence-free initial velocity on `ℝ³`, with zero
forcing, there is a smooth global solution with uniformly bounded energy.
The Lean source also states official breakdown alternative (C) as a distinct
forced endpoint; it does not confuse zero-force singularity, weak-solution
nonuniqueness, or averaged-model blowup with C.

## What is here

- [`docs/ATTACK.md`](docs/ATTACK.md): 11 parallel positive, rigidity,
  computational, and breakdown routes, each with a lower residual, kill test,
  and pivot.
- [`docs/OPEN_FRONTIER_MAP.md`](docs/OPEN_FRONTIER_MAP.md): the checked support
  layer, the twelve-lane open-obligation map, and the endpoint dependency
  picture.
- [`Navier/Problem.lean`](Navier/Problem.lean): concrete derivatives,
  equation, solution predicate, and the direct statement-A encoding.
- [`Navier/Scaling.lean`](Navier/Scaling.lean): axiom-audited algebraic
  critical-line facts, without pretending the analytic norm theory exists.
- [`docs/BARRIERS.md`](docs/BARRIERS.md) and
  [`docs/FALSIFICATION_LEDGER.md`](docs/FALSIFICATION_LEDGER.md): scaling,
  energy-only, weak/smooth, model-drift, compactness, and numerical-proof
  gates with preserved failures.
- [`references/manifest.json`](references/manifest.json): checked primary and
  official source locators.

The formal encoding has comparison theorems for Schwartz decay, half-space
smoothness, coordinate derivatives, and the energy clause; see
[`docs/FORMALIZATION.md`](docs/FORMALIZATION.md) for the exact declarations.
They establish representation comparisons. The global regularity target
requires a proof of the full existence proposition in `Navier/Problem.lean`.

## Verify

The focused check is serial by design:

```bash
make check
```

Individual commands and pinned versions are documented in
[`REPRODUCIBILITY.md`](REPRODUCIBILITY.md). Successful checks establish artifact
integrity and the stated support lemmas; they do not prove the problem endpoint.

## Lineage

The research_program borrows proof-bearing status discipline from `~/reality`,
frontier/bridge separation from `~/reimann`, and a single fail-closed parallel
portfolio from `~/npnep`. It imports no mathematical conclusion from those
projects. Exact snapshots, transplanted patterns, and rejected anti-patterns
are recorded in the blueprint.
