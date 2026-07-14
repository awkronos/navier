# Navier — 3D Navier–Stokes Clay Campaign

This repository is a strict scientific-frontier attack on the Clay
Navier–Stokes existence-and-smoothness problem. Correct status is more
important than optimistic status.

## Authority and truth

- The exact mathematical surface is `Navier/Problem.lean`; public prose must
  match it and Charles Fefferman's official Clay formulation.
- `data/attack_registry.json` is the one machine-readable attack/dependency
  registry. Every other status view is derived from it.
- Lean compiler output is build truth. A public theorem claim additionally
  requires raw `#print axioms` output restricted to `{propext,
  Classical.choice, Quot.sound}` plus explicitly flagged `native_decide`.
- Numerical experiments are observations only. They never realize a theorem,
  bridge, payload, or Clay endpoint.

## Claim discipline

- Allowed synthesis verdicts are `CLOSED`, `DECOMPOSED`, `SCAFFOLDED`, `RED`,
  `FALSIFIED`, and `REVERTED`.
- The repository begins `SCAFFOLDED / SCIENTIFIC_FRONTIER`. Do not say the Clay
  problem, global regularity, or finite-time breakdown is proved unless the
  exact public endpoint passes the native verifier and axiom audit.
- Conditional criteria must name their assumption. Never turn a continuation
  criterion, critical-norm bound, compactness payload, or numerical enclosure
  into an unconditional conclusion.
- Ban custom axioms, `True`-like targets, zero/PUnit/empty-domain witnesses,
  result-as-hypothesis wrappers, domain swaps, and source-grep proof counts.

## Architecture

- `Navier/`: exact problem, scaling, epistemic dispositions, and frontier map.
- `data/` + `schemas/`: canonical approach, obligation, evidence, and status
  records.
- `scripts/`: fail-closed validators and status renderer.
- `tests/`: known-good and known-bad registry/verifier cases.
- `docs/`: human attack blueprint, barriers, references, and falsifications.

Every decomposition must expose a strictly smaller, non-vacuous residual with
a consumer path. Every falsification preserves a checked witness and prunes or
repairs the route. One writer owns a file until a verifier/commit boundary.

## Minimum verification

```bash
python3 -m unittest discover -s tests -v
python3 scripts/validate_registry.py data/attack_registry.json
lake env lean Navier.lean
```

Never run concurrent full Lean builds. Use a single targeted `lake env lean`
process, then audit named public declarations with `#print axioms`.

