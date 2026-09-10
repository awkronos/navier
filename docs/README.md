# Research documentation

The repository separates current theorem evidence from open research and
historical development records. Start with the first table when evaluating a
claim; planning documents and experiments do not override theorem types or
native compiler receipts.

## Current result and evidence

| Document | Purpose |
| --- | --- |
| [Result and frontier map](RESULT_MAP.md) | Authoritative claim-to-declaration map, exact premises, trust boundary, and current open/closed status |
| [Native breakdown mathematics and adaptive simulation](NATIVE_BREAKDOWN_AND_SOLVER.md) | Detailed guide to the constructed forced endpoint, useful conditional results, and solver validation |
| [Breakdown, uniqueness, and concentration](DYNAMICS_AND_CONCENTRATION.md) | Focused account of the pre-singular flow, slab uniqueness, terminal obstruction, and concentration scales |
| [Exact constructed force and the regularity obstruction](EXACT_FORCE_AND_REGULARITY.md) | The selected force formula, properties proved for that same force, and the exact competing classes excluded |
| [Computed analytic-axis construction](COMPUTED_AXIS_CONSTRUCTION.md) | Equations, truncation, reconstruction, residuals, and the exact boundary between the executable axis stage and the completed Lean witness |
| [Construction carrier review](CONSTRUCTION_REVIEW.md) | Clause-by-clause comparison with the official whole-space alternative-C carrier |
| [OpenAI construction provenance](OPENAI_CONSTRUCTION_PROVENANCE.md) | Pinned upstream revision, adaptation boundary, licensing, and source verification |
| [Reproducibility](../REPRODUCIBILITY.md) | Pinned toolchain, focused compiler commands, receipt semantics, and solver checks |

The [prepublication review](PREPUBLICATION_REVIEW.md) is a dated release record.
It supplements the files above and does not define mathematical status.

## Open mathematical frontier

| Document | Purpose |
| --- | --- |
| [Mathematical dependencies](DECOMPOSITION.md) | Exact inputs needed by the checked consumer for unforced whole-space global regularity |
| [Mathematical obligation navigation](OPEN_FRONTIER_MAP.md) | Short map from each live surface to its nearest unresolved input |
| [Formalization and verification](FORMALIZATION.md) | Representation comparisons, trust rules, and acceptance criteria for new proofs |
| [Barrier and kill matrix](BARRIERS.md) | Tests that prevent conditional, weak, numerical, or altered-model results from being promoted past their scope |
| [Falsification ledger](FALSIFICATION_LEDGER.md) | Append-only record of rejected claim classes and their repair conditions |

## Adjacent interpretation

The [Madelung correspondence note](MADELUNG_CORRESPONDENCE.md) records the
precise scalar and spinor hydrodynamic correspondences and the obstructions to
turning the selected forced flow into a quantum-mechanical result.

The Rust crate contains two numerical instruments with different domains and
claims. The finite analytic-axis evaluator reconstructs one explicitly
computable stage of the forced construction; the Fourier solver advances
periodic benchmark flows. Neither is proof evidence. Their roles and measured
quantities are separated in the [solver guide](../solver/README.md).

## Historical research records

These files retain unique development evidence. Their dated status and route
labels are historical and are superseded by `RESULT_MAP.md` for current claims.

| Document | Snapshot |
| --- | --- |
| [Attack blueprint](ATTACK.md) | Original route architecture and proposed proof program |
| [Polya strategy map](POLYA_MAP.md) | Match between an earlier Polya catalogue snapshot and Navier proof shapes |

Deterministic numerical artifacts have their own scope note in
[`artifacts/README.md`](../artifacts/README.md). Raw compiler and axiom evidence
lives locally under `reports/receipts/`, which is excluded from Git and its
published history. Each directory binds a distinct verification snapshot.
The source modules and audit commands remain available for reproduction.

The [periodic classical uniqueness module](../Navier/Analysis/PeriodicClassicalUniqueness.lean)
proves velocity uniqueness for every positive viscosity under the native
periodic velocity/pressure contract. Alternative B existence is still open;
see its current compiler receipt (local report).
