# Reproducibility

## Pinned environment

- Lean: `leanprover/lean4:v4.31.0` (`lean-toolchain`)
- mathlib input tag: `v4.31.0`
- mathlib resolved revision:
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`lake-manifest.json`)

The reference manifest records the primary-source URLs and the date on which
they were checked. Source availability and bibliographic metadata are not
mathematical verification.

## Dependencies and focused verification

From a fresh clone with `elan`, `lake`, and Python available, obtain the
dependencies:

```bash
lake update
lake exe cache get
```

These commands do not compile the project's own modules. Compile required
project imports with the pinned single-file compiler in dependency order,
refreshing their `.olean` artifacts. Once those artifacts are available,
run the focused checks:

```bash
python3 -m unittest discover -s tests -v
lake env lean Navier.lean
lake env lean Navier/AxiomAudit.lean
lake env lean scripts/AuditAllAxioms.lean
```

After dependencies are present, `make check` runs the focused Python, Lean,
and axiom commands in that serial order.

Run Lean commands one at a time. `Navier/AxiomAudit.lean` emits raw
`#print axioms` results for the named public declarations; keep that stdout
with any proof claim. The imported-environment check is not a source rebuild.

## What the checks mean

- The Python suite checks the retained mathematical experiments and solver
  equivalence logic.
- Lean compilation checks that the definitions and proved infrastructure
  elaborate in the pinned kernel environment.
- The named axiom audit reports raw theorem dependencies. The exhaustive
  imported-module audit fails on any transitive axiom outside `propext`,
  `Classical.choice`, and `Quot.sound`, including dependencies hidden behind
  imported or private helpers. Refresh changed modules before running it;
  the audit does not rebuild source files.

None of these commands, by itself or in combination, proves Fefferman's
statement (A). Proving that endpoint requires a term of its exact Lean type
that compiles and passes the axiom policy.
