# Mathematical dependencies

The target is `Navier.ProblemStatements.WholeSpaceGlobalRegularity` in
[`Problem.lean`](../Navier/Problem.lean). Its quantifiers and solution
requirements determine what a proof must establish. No prescribed route,
planning category, or status label determines its truth.

[`CriticalControlDecomposition.lean`](../Navier/Analysis/CriticalControlDecomposition.lean)
contains a proved construction of the exact target from three mathematical
inputs:

- `LocalClassicalExistence` for every admissible datum;
- `NormalizedContinuationFromCriticalControl N` for the same finite-energy,
  pressure-normalized local solution class;
- `APrioriCriticalControl N` for a specified quantity
  `N : ℝ → VelocityEvolution → ℝ≥0∞`, with finite bounds.

The theorem glues a coherent sequence of local solutions on cofinal horizons.
Its energy estimate comes from the pieces it constructs. Normalizing pressure
by subtracting its value at the spatial origin preserves the momentum equation
and removes the arbitrary time-dependent gauge.

These premises are explicit theorem inputs. The construction proves their
implication, and using it to prove the target requires proving all three for
a common quantity. A different proof route may establish the target directly.

[`PressureGaugeObstruction.lean`](../Navier/Analysis/PressureGaugeObstruction.lean)
refutes the former arbitrary-pressure continuation statement.
[`GlobalRegularityEndpoint.lean`](../Navier/Analysis/GlobalRegularityEndpoint.lean)
refutes automatic finite-energy recovery from smoothness and the PDE alone.
Both retain the exact rejected propositions so the counterexamples can be
checked. Neither refutes the original existential target.

The lattice mild-solution modules use summable Fourier coefficients on
`ℤ³`. Applying their results to this whole-space target requires an actual
reconstruction and transport of the PDE, smoothness, initial data and energy
conditions to `ℝ³`.

Verification commands and their scope are in
[`FORMALIZATION.md`](FORMALIZATION.md) and
[`REPRODUCIBILITY.md`](../REPRODUCIBILITY.md). Mathematical progress is a
proved statement or counterexample at its actual type, not a change to this
document.
