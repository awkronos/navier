# Reproducibility

## Pinned environment

- Lean: `leanprover/lean4:v4.31.0` (`lean-toolchain`)
- mathlib input tag: `v4.31.0`
- mathlib resolved revision:
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`lake-manifest.json`)

The reference manifest records the primary-source URLs and the date on which
they were checked. Source availability and bibliographic metadata are not
mathematical verification.

## Rebuild

From a fresh clone with `elan`, `lake`, and Python available:

```bash
lake update
lake exe cache get
python3 -m unittest discover -s tests -v
lake env lean Navier.lean
lake env lean Navier/AxiomAudit.lean
```

After dependencies are present, `make check` runs the focused Python, Lean,
and axiom commands in that serial order.

Run Lean commands one at a time. The final file emits raw `#print axioms`
results for the named public declarations; keep that stdout with any closure
claim.

## What the checks mean

- The Python suite checks the retained mathematical experiments and solver
  equivalence logic.
- Lean compilation checks that the definitions and proved infrastructure
  elaborate in the pinned kernel environment.
- The axiom audit reports the dependencies of named declarations.

None of these commands, by itself or in combination, proves Fefferman's
statement (A). The endpoint remains conjectural until an actual term of its
exact Lean type compiles and passes the axiom policy.
