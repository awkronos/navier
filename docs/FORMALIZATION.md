# Formalization and verification

The target is `Navier.ProblemStatements.WholeSpaceGlobalRegularity` in
[`Navier/Problem.lean`](../Navier/Problem.lean). It quantifies over every
positive viscosity and every divergence-free Schwartz velocity on `ℝ³`,
and asks for velocity and pressure satisfying the classical unforced PDE,
initial condition, smoothness on nonnegative time, and uniformly bounded
finite energy.

Prove this proposition or its negation at its exact type. No planning phase,
status enum, instruction, or report fixes the outcome. A proof of a proposition's
definition being well formed is not a term of that proposition.

## Representation comparisons

The comparison obligations have mathematical providers:

| Comparison | Declaration | Module |
| --- | --- | --- |
| Schwartz data and coordinate decay | `fefferman_clause_four_iff_schwartz` | `Analysis/SchwartzConventionEquivalence.lean` |
| Half-space smoothness and smooth extension | `halfSpaceSmooth_iff_extension` | `Analysis/SeeleySynthesis.lean` |
| Fréchet and coordinate momentum equations | `satisfiesNavierStokes_iff_officialCoordinateEquations` | `Analysis/CoordinatePDEBridge.lean` |
| Incompressibility in coordinates | `incompressible_iff_officialCoordinateDivergenceFree` | `Analysis/CoordinatePDEBridge.lean` |
| Energy integrability and Euclidean energy | `currentWholeSpaceEnergyClause_iff_official` | `Analysis/EnergyOfficialClause.lean` |

Their exact types record the regularity and measurability hypotheses.
The retired `ProblemEncodingResidual`, `Frontier`, and `ProblemFrontier`
enumerations were planning data; their cardinality and dependency theorems
did not establish whether these comparisons were proved.

## Rejected energy recovery

`Analysis/GlobalRegularityEndpoint.lean` proves
`not_wholeSpaceEnergyClause`. The flow `u(t,x) = t e₀` and
pressure `p(t,x) = -x₀` satisfy the unforced equation from zero Schwartz
data, but the energy density at time one is a positive constant on infinite
volume. Smoothness and the PDE alone therefore do not imply finite energy
for every solution. Endpoint implications using that false universal
premise have been removed.

This counterexample concerns the universal energy-recovery assertion.
The original endpoint asks for existence of a finite-energy solution;
zero initial data have the zero solution. Any successful general construction
must establish energy control for the solution it produces.

## Pressure continuation repair

`Analysis/PressureGaugeObstruction.lean` proves
`not_rejectedSameGaugeContinuation` for every velocity quantity `N`.
The old interface demanded exact agreement of arbitrary pressure gauges.
Zero velocity and `p(t,x)=(1-t)⁻¹` satisfy its input on `[0,1)`, but any
smooth extension across one would be bounded on a compact time interval,
contradicting agreement with this pressure.

`Analysis/CriticalControlDecomposition.lean` now uses
`NormalizedContinuationFromCriticalControl`. The construction replaces each
local pressure by `p(t,x)-p(t,0)`, proves that this preserves smoothness and
the PDE, and carries that normalization through the continuation chain.
The continuation class now requires finite-energy slices and the
initial-energy inequality. The control quantity takes values in `ℝ≥0∞`,
and its threshold is finite, so infinite control cannot pass the bound.
The gluing theorem carries the local energy estimates into the exact original
`WholeSpaceGlobalRegularity` conclusion. Its local existence, normalized
continuation, and a priori bound remain explicit premises.

## Carrier and hypothesis checks

The critical mild continuation modules operate on weighted summable lattice
Fourier coefficients indexed by `ℤ³`. A result about that carrier reaches
the whole-space target only through a proved reconstruction and PDE/energy
transport on `ℝ³`. A uniform terminal norm assumption is an analytic
obligation, even when a direct-limit construction under it compiles.

Check each theorem's complete hypotheses. In particular, a pressure gauge
may depend on time; velocity control alone does not control that gauge.
A conditional theorem with a refuted premise cannot be used as a scientific
reduction.

## Verification

Compile changed sources and their affected consumers with the pinned
single-file Lean command, using the workspace build wrapper. Refresh exact
dependency artifacts when necessary. Print fully qualified theorem types
and raw `#print axioms`; strict proofs use only `propext`,
`Classical.choice`, and `Quot.sound`.

Source changes, compiler exit codes, and transitive axiom output support
claims about checked declarations. A stale import or report supplies no
current-source verification. Neither numerical observations nor successful
compilation of a conditional implication discharges its assumptions.

`scripts/AuditAllAxioms.lean` rejects disallowed transitive axioms for every
declaration originating in an imported Navier module, including private
helpers and declarations outside the `Navier` namespace. It is part of
`make check` and CI. The public import includes the Galerkin spectral support
modules so they are covered by this check as well.
