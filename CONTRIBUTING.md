# Contributing

This is an evidence-gated research repository. Contributions are welcome when
they sharpen the exact problem-statement target, close a named obligation, falsify a route,
or improve a verifier without promoting an unproved claim.

## Before editing

1. Read `AGENTS.md` and `Navier/Problem.lean`.
2. Claim a disjoint file set. Do not overwrite another writer's uncommitted
   work.
3. State the route, the precise residual obligation, its consumer, and a
   falsifier before implementing a bridge or experiment.

## Evidence classes

- A Lean declaration is formal evidence only after it compiles in the pinned
  toolchain. A public closure claim also needs a raw `#print axioms` audit.
- A cited theorem is literature evidence only when its hypotheses and domain
  match the obligation being discharged.
- A numerical result is an observation. It cannot realize an analytic payload
  or the problem endpoint.
- An assumption may support a conditional theorem, but must remain visible in
  its theorem type.

Do not add custom axioms, `sorry`, result-as-hypothesis wrappers, vacuous
witnesses, domain substitutions, or handwritten proof-status registries. If a
route fails, preserve the smallest reproducible counterexample or mismatch in
the mathematical source or a focused regression test.

Experiment contributions must pin a tracked driver and every input to the
declared Git revision. They must replay in the isolated snapshot without
network access, undeclared writes, path-valued command arguments, or reuse of a
pre-existing output. A platform without the supported confinement primitive is
a replay RED, not permission to execute on the host tree.

## Required checks

Run the focused checks serially:

```bash
python3 -m unittest discover -s tests -v
lake env lean Navier.lean
lake env lean Navier/AxiomAudit.lean
lake env lean scripts/AuditAllAxioms.lean
```

The checks establish repository integrity; they do not establish either
global regularity or finite-time breakdown.
