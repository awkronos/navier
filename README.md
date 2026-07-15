# Navier

An evidence-gated, parallel mathematical research and formalization campaign
for the three-dimensional incompressible Navier–Stokes Clay problem.

**Current status: SCAFFOLDED / SCIENTIFIC FRONTIER.** This repository does not
claim a solution. It separates kernel-checked infrastructure, conditional
regularity routes, open analytic payloads, computational observations, and
falsified approaches so none can be promoted by wording alone.

The primary formal surface is Fefferman's whole-space
existence-and-smoothness statement (A): for every positive viscosity and every
rapidly decaying smooth divergence-free initial velocity on `ℝ³`, with zero
forcing, there is a smooth global solution with uniformly bounded energy.
The machine registry also tracks official breakdown alternative (C) as a
distinct forced endpoint; it does not confuse zero-force singularity,
weak-solution nonuniqueness, or averaged-model blowup with C.

## What is here

- [`docs/ATTACK.md`](docs/ATTACK.md): 11 parallel positive, rigidity,
  computational, and breakdown routes, each with a lower residual, kill test,
  and pivot.
- [`data/attack_registry.json`](data/attack_registry.json): the sole
  machine-readable status/dependency/evidence registry, checked fail-closed.
- [`Navier/Problem.lean`](Navier/Problem.lean): concrete derivatives,
  equation, solution predicate, and the direct statement-A encoding.
- [`Navier/OfficialProblem.lean`](Navier/OfficialProblem.lean): typed sibling
  surfaces for official alternatives B, C, and D, including force decay,
  periodic velocity and pressure, and the deliberate absence of a whole-space
  energy clause from B/D.
- [`Navier/Analysis/VectorCalculus.lean`](Navier/Analysis/VectorCalculus.lean)
  and [`Navier/Analysis/Covariance.lean`](Navier/Analysis/Covariance.lean):
  checked product/coordinate identities and full covariance of the forced
  pointwise momentum equation under positive parabolic scaling.
- [`Navier/Analysis/CriticalL3.lean`](Navier/Analysis/CriticalL3.lean) and
  [`Navier/Analysis/CriticalL3Integrable.lean`](Navier/Analysis/CriticalL3Integrable.lean):
  raw critical-mass transport plus a repaired contract that explicitly
  requires every selected slice to have integrable cubic norm density. The
  repaired finite-time bound is exactly scaling covariant; it does not produce
  an unconditional bound. The `ViscosityTransport`,
  `ViscosityAdmissibility`, `ViscosityForceDecay`, and `ViscosityEndpoints`
  modules exactly transport the full official solution/admissibility contracts
  and prove equivalences between every A--D surface and its viscosity-one form.
  None of those equivalences inhabits an endpoint.
- [`Navier/Breakdown/MaximalNonextension.lean`](Navier/Breakdown/MaximalNonextension.lean):
  a conditional point-evaluation consumer that converts a genuine local
  blowup witness plus agreement into official whole-space or periodic
  nonexistence. It does not construct the local solution or blowup.
- [`Navier/Scaling.lean`](Navier/Scaling.lean): axiom-audited algebraic
  critical-line facts, without pretending the analytic norm theory exists.
- [`Navier/Routes/R7/ExactSymbol.lean`](Navier/Routes/R7/ExactSymbol.lean):
  a Leray-numerator leaf plus a checked countermodel showing why energy
  cancellation alone is too weak. Its companion
  [`Navier/Routes/R7/Triad.lean`](Navier/Routes/R7/Triad.lean) proves collective
  cancellation of six real symbol coefficients and a nonzero coefficient.
  [`Navier/Routes/R7/ScaledTriad.lean`](Navier/Routes/R7/ScaledTriad.lean)
  proves linear frequency growth for that algebraic coefficient.
  [`Navier/Routes/R7/PhaseSymbol.lean`](Navier/Routes/R7/PhaseSymbol.lean)
  restores a normalized Leray symbol, Fourier `i`, complex phases, and receiver
  conjugation. The `SymmetrizedPhase`, `SymmetrizedWitness`,
  `WeightedShellTransfer`, `FieldLeakage`, and `FullFieldLeakage` modules then
  expose one cancellation regression, one surviving conjugate-symmetric
  six-mode witness, unequal-shell weighted transfer, and an exhaustive
  36-pair off-support coefficient equal to the scale. This finite table is
  not an invariant Fourier network or a PDE solution.
- [`artifacts/runs/experiment.json`](artifacts/runs/experiment.json): a pinned,
  exact-integer/rational replay of the symmetrized triad scan. It is explicitly
  falsification evidence, never theorem or endpoint evidence.
- [`docs/BARRIERS.md`](docs/BARRIERS.md) and
  [`docs/FALSIFICATION_LEDGER.md`](docs/FALSIFICATION_LEDGER.md): scaling,
  energy-only, weak/smooth, model-drift, compactness, and numerical-proof
  gates with preserved failures.
- [`references/manifest.json`](references/manifest.json): checked primary and
  official source locators.

The formal encoding keeps its convention bridges explicit (`SchwartzMap`
versus coordinatewise decay, total Fréchet versus mixed coordinate
derivatives, half-space smoothness, norm/PDE/energy conventions, and periodic
lifts versus the quotient). The decisive global critical estimate, rigidity
theorem, or exact breakdown witness is also open.

## Verify

The complete focused check is serial by design:

```bash
make check
```

Individual commands and pinned versions are documented in
[`REPRODUCIBILITY.md`](REPRODUCIBILITY.md). `make status` derives a current
human view from the canonical registry. Successful checks establish artifact
integrity and the stated support lemmas; they do not prove the Clay endpoint.

## Lineage

The campaign borrows proof-bearing status discipline from `~/reality`,
frontier/bridge separation from `~/reimann`, and a single fail-closed parallel
portfolio from `~/npnep`. It imports no mathematical conclusion from those
projects. Exact snapshots, transplanted patterns, and rejected anti-patterns
are recorded in the blueprint.
