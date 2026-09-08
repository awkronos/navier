# Navier — critical-path proof contract

The exact mathematical surface is `Navier/Problem.lean`. Determine its status
from current proofs or counterexamples; no instruction or planning label
predetermines the mathematical outcome. Local existence and conditional
continuation establish their stated conclusions.

- Select current obligations from `/tmp/open_math.json`, generated from exact
  compiler types, axioms, and dependencies.
  The lattice `CriticalMildTerminalNormBound` route requires a proved transport
  to the whole-space endpoint. Retain an assumption in a conditional theorem's
  type until its proof is supplied.

Prioritize statements feeding the original whole-space consumer. Do not add
redundant chain records, cofinality aliases, numerical surrogates, or
result-as-hypothesis wrappers. A conditional theorem must have satisfiable
hypotheses and supply an actual mathematical step to its named consumer.

Before edits inspect path-scoped git status/diff and recent history. Temporary
`sorry` is uncommitted search state only. One writer owns a file through its
verifier/commit boundary.

Verification:

```bash
~/.claude/scripts/open-math.py verify --project navier --report /tmp/proof-report.json --sidecar /tmp/open_math.json
lake env lean Navier/Analysis/<Target>.lean
lake env lean Navier.lean
```

Public theorem evidence additionally includes raw `#print axioms` contained in
`{propext, Classical.choice, Quot.sound}`. Never run concurrent full builds.
