# Reproducibility

## Pinned environment

- Lean: `leanprover/lean4:v4.31.0` (`lean-toolchain`)
- mathlib input tag: `v4.31.0`
- mathlib resolved revision:
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`lake-manifest.json`)
- Registry and validator runtime: Python 3.11 or newer, standard library only

The reference manifest records the primary-source URLs and the date on which
they were checked. Source availability and bibliographic metadata are not
mathematical verification.

## Rebuild

From a fresh clone with `elan`, `lake`, and Python available:

```bash
lake update
lake exe cache get
python3 -m unittest discover -s tests -v
python3 scripts/validate_registry.py data/attack_registry.json
lake build Navier
lake env lean Navier/AxiomAudit.lean
```

After dependencies are present, `make check` runs the focused Python,
registry, derived-status, full `Navier` module build, and source-level axiom
commands in that serial order. Building the module graph first prevents a
later audit from importing stale `.olean` files after a dependency edit.

Run Lean commands one at a time. The final file emits raw `#print axioms`
results for the named public declarations; keep that stdout with any closure
claim.

## What the checks mean

- The Python suite checks schema enforcement, dependency consistency,
  fail-closed evidence rules, and hostile fixtures.
- Registry validation checks the current canonical research state.
- Lean compilation checks that the definitions and proved infrastructure
  elaborate in the pinned kernel environment.
- The axiom audit reports the dependencies of named declarations.

None of these commands, by itself or in combination, proves Fefferman's
statement (A). The endpoint remains conjectural until an actual term of its
exact Lean type compiles and passes the axiom policy.

## Experiment replay boundary

Delivered computational manifests are validated with

```bash
python3 scripts/replay_experiment.py artifacts/runs/experiment.json
```

Execution is supported only where `/usr/bin/sandbox-exec` is available. The
gate replays tracked driver/input bytes from the pinned Git commit in a fresh,
write-confined snapshot; it never executes the current working-tree driver.
`--validate-only` checks a previously delivered output and its immutable
bindings without executing code. No experiment is delivered at initialization,
and no replay receipt is theorem evidence.
