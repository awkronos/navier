# Navier — critical-path proof contract

The exact mathematical surface is `Navier/Problem.lean`. Current status is
`scientificFrontier`; local existence and conditional continuation are not
global regularity.

- Canonical plan: `~/.claude/plans/open-math-critical-path.md`.
- Active row: `navier.bounded-chain-direct-limit` in
  `~/.claude/todos/open-math-goals.json`.
- Current node: parameterize the direct-limit consumer over a coherent cofinal
  chain and instantiate `boundedContinuationChain`.
- The remaining scientific hypothesis must stay explicit as
  `CriticalMildTerminalNormBound`; do not claim it is constructed.

Select only statements feeding that consumer. Do not add another chain record,
cofinality alias, numerical surrogate, or result-as-hypothesis wrapper. A
conditional theorem is valuable only if it reaches the actual global mild
solution and isolates this sole estimate.

Before edits inspect path-scoped git status/diff and recent history. Temporary
`sorry` is uncommitted search state only. One writer owns a file through its
verifier/commit boundary.

Verification:

```bash
lake env lean Navier/Analysis/<Target>.lean
lake env lean Navier.lean
```

Public theorem evidence additionally includes raw `#print axioms` contained in
`{propext, Classical.choice, Quot.sound}`. Never run concurrent full builds.
