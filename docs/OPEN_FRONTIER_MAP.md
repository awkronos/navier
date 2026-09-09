# Mathematical obligation navigation

Use current theorem types and compiler evidence to select work. This file
does not assign fixed outcomes or prescribe a proof route.

## Current boundary

| Surface | Current status | Live edge |
| --- | --- | --- |
| Forced whole-space alternative C | **THEOREM**: `ConstructedBreakdown.wholeSpaceBreakdown` | Further work may sharpen mechanism, force semantics and finite-time localization; C itself has no remaining premise |
| Unforced whole-space alternative A | **OPEN**: `ProblemStatements.WholeSpaceGlobalRegularity` | Local existence, normalized continuation and arbitrary-large-data critical control must meet in one faithful whole-space consumer |
| Fourier-lattice continuation | **CONDITIONAL THEOREM** | `CriticalMildMixedTerminalBound` is the sharp uniform nonlinear estimate; whole-space reconstruction is also required |
| Periodic breakdown D | No closure claimed here | A forced whole-space theorem does not automatically transport to the periodic carrier |

The globally smooth object in the completed strengthened C result is the
force. The selected velocity is classical before its singular deadline and
cannot be continued as a global smooth bounded-energy solution. “Global smooth
velocity” would describe A or B and must not be inferred from C.

The exact original target and a conditional construction are described in
[`DECOMPOSITION.md`](DECOMPOSITION.md). The encoding comparison theorems and
checked energy/pressure counterexamples are listed in
[`FORMALIZATION.md`](FORMALIZATION.md).

The soundness cleanup removed admitted proof claims from:

- `BKMLogBootstrap.lean`: weighted-energy propagation and Sobolev-order
  energy estimates, together with claims that consumed them. The log-Grönwall,
  Fourier, Biot–Savart, and conditional transfer results remain.
- `ConditionalRegularity.lean`: the general Duhamel representation, source
  bounds, and resulting Prodi–Serrin/Constantin–Fefferman bridge claims.
  Compact-region, Gaussian convolution, integrability, and explicit strain
  counterexample results remain.
- `GalerkinModeData.lean`: general stable-basis and mode-data existence
  claims. The proved projection and coefficient-flow support remains.
- `LerayWeakExistence.lean`: all three existence wrappers depended on the
  admitted mode-data construction, so the file was removed. The proved
  conditional compactness and limit passage in `LerayWeak.lean` remain.

Removing an admission neither proves nor refutes its mathematical statement.
The surviving source supplies the smaller proved inputs for further work.
The general analytic estimates and the original unforced global target still
require proofs or exact counterexamples. The completed forced construction is
documented separately in the [result map](RESULT_MAP.md).

`scripts/AuditAllAxioms.lean` checks every declaration imported from a Navier
module, including private helpers and declarations in other namespaces, for
disallowed transitive axioms. Refresh changed modules before running it.
This detects admitted dependencies omitted by a handpicked public audit.
It does not decide whether the definitions faithfully encode a scientific
claim, or whether the hypotheses of a conditional theorem can be proved.

The dated residual ledger and research blueprint are historical records.
Their counts, line numbers, and proposed routes are not current verification
evidence or constraints on new proofs.
