# Barrier and kill matrix

Status: **SCIENTIFIC_FRONTIER**
Scope: exact three-dimensional incompressible Navier–Stokes problem in
Fefferman's alternatives (A)–(D)

A barrier is not a reason to stop; it is a test that prevents a familiar
conditional or model result from being promoted as the missing payload. A
route that fails a kill test either records a narrower residual or pivots.

## 1. Universal barriers

| Barrier | Hard test | Killed claim class | Permitted pivot |
|---|---|---|---|
| Scaling/criticality | Compute every norm under \(u_\lambda=\lambda u(\lambda x,\lambda^2t)\) | Energy or a supercritical norm asserted to control concentration with no new gain | Search for a scale-critical local/frequency/geometric estimate |
| Energy-only | Does the decisive proof use more than \(\langle B(u,u),u\rangle=0\) and generic multiplier estimates? | “Energy plus harmonic analysis proves global regularity” | Identify a property of the exact bilinear symbol |
| Endpoint-as-assumption | Normalize all hypotheses and compare with the conclusion/continuation criterion | Serrin, \(L^\infty_tL^3_x\), BKM-type, or strain criterion simply assumed | Move the assumed bound into the open-residual field |
| Weak/smooth category | Check solution class, energy inequality, force, uniqueness, and regularity | Weak existence/nonuniqueness presented as whole-space global-regularity alternative–D | Build an explicit weak-to-smooth or breakdown bridge |
| Model/domain drift | Compare dimension, domain, dissipation, force, and nonlinearity | 2D, Euler, averaged, dyadic, hyperdissipative, bounded-domain, or periodic result presented as whole-space A | Prove a transfer theorem or quarantine the model |
| Compactness defect | Track pressure, strong convergence, nonlinear products, and nontriviality | Weak limit treated as a strong exact solution without defect accounting | Promote the defect to the first residual |
| Numerics-as-proof | Demand universal coverage, interval bounds, truncation and tail proof | Finite sampling or floating-point evidence presented as a theorem | Use observations to propose a falsifiable inequality |
| Wrapper laundering | Inspect whether a theorem only repackages a supplied endpoint witness | Record/constructor/status theorem counted as progress | Classify as wiring and keep frontier status unchanged |

## 2. Exact scaling barrier

The mixed norm scales as

\[
\|u_\lambda\|_{L_t^qL_x^p}
=\lambda^{1-3/p-2/q}\|u\|_{L_t^qL_x^p}.
\]

Thus \(3/p+2/q=1\) is critical. The energy-class quantities
\(L_t^\infty L_x^2\) and \(L_t^2\dot H_x^1\) have exponent \(-1/2\).
At a high-frequency/small-scale zoom they become smaller, so they cannot by
themselves rule out concentration. Interpolation of the two energy quantities
stays on the energy line and does not magically produce the critical Serrin
line. Every claim of such a gain must display the additional equation-specific
input.

## 3. Tao averaged-operator obstruction

Tao constructs an averaged bilinear operator \(\widetilde B\) for which the
equation

\[
\partial_tu=\Delta u+\widetilde B(u,u)
\]

retains the energy cancellation and the generic harmonic-analysis behavior
used by broad multiplier estimates, but has a smooth solution that blows up in
finite time [TAO2016]. This does **not** prove blowup for true Navier–Stokes.
It does prove a discriminator:

> If a proposed positive estimate is invariant under replacing the exact
> Navier–Stokes bilinear form by Tao's admissible averaged forms, that estimate
> cannot be the decisive global-regularity estimate.

The acceptable escape is concrete: state an algebraic, geometric, or
frequency-symbol property of the exact Leray-projected nonlinearity, prove
that the estimate uses it, and show why the property is not preserved by the
averaging.

## 4. Weak-solution nonuniqueness boundary

Leray supplies global finite-energy weak solutions [LERAY1934], while CKN
supplies partial regularity for suitable weak solutions [CKN1982]. Neither is
the smooth global solution demanded by (A).

Buckmaster and Vicol prove nonuniqueness in a class of finite-kinetic-energy
weak solutions [BUCKMASTER_VICOL2019]. Albritton, Brué, and Colombo prove
nonuniqueness of forced Leray solutions [ALBRITTON_BRUE_COLOMBO2022]. These
results are vital boundary evidence, but:

- weak nonuniqueness does not imply nonexistence of a smooth solution;
- the forced result does not answer unforced (A);
- nonuniqueness is not the breakdown conclusion in (C) or (D);
- a force/datum must separately satisfy Fefferman's exact smoothness, decay,
  and domain clauses before it can be used in a problem alternative.

Accordingly, a weak route is live only if it produces an explicit upgrade to
smoothness/uniqueness or an exact logical bridge to one of Fefferman's
breakdown statements.

## 5. Model and domain quarantine

The following may be used for theorem testing, counterexamples to generic
estimates, or formal infrastructure. They may not directly inhabit
Fefferman-A:

| Quarantined setting | Missing bridge to A |
|---|---|
| Two-dimensional Navier–Stokes | vortex stretching is absent; dimension is load-bearing |
| Euler equation | viscosity is zero and the energy/regularity mechanisms differ |
| Tao averaged equation | nonlinear operator is not the exact Leray-projected form |
| Dyadic/shell model | interaction graph and symbol are simplified |
| Hyperdissipative or hypodissipative equation | dissipation exponent differs |
| Axisymmetric/no-swirl or other symmetry class | arbitrary smooth data do not obey the symmetry |
| Periodic three-torus | this is alternative B, not the whole-space alternative A |
| Bounded or exterior domain | boundary conditions and pressure/Stokes operator differ |
| Forced equation | A and B require \(f=0\); C/D require exact force admissibility |
| Weak/distributional formulation | A/B require global \(C^\infty\) velocity and pressure |

A transfer theorem must name both models, transport all hypotheses, and
produce the exact consumer type. Similarity of notation is not a bridge.

## 6. Route-specific kill and pivot matrix

| Route | Minimal adversarial test | Kill event | Pivot after kill |
|---|---|---|---|
| R1 critical norms | rescaled concentrating smooth packets | constant depends on maximal time or assumes the target norm | localize the failed flux; R3/R5/R7 |
| R2 fixed point | arbitrarily large critical initial norm | contraction uses small data or small time only | keep local theory; analyze large term in R5/R7 |
| R3 vorticity geometry | high-vorticity fields with rapidly changing direction | alignment is assumed or loses critical scaling | catalog saturating geometry; R7 |
| R4 compactness/rigidity | rescaled sequence with pressure concentration | nonlinear defect or zero limiting profile survives | quantify defect; R5/R9 |
| R5 frequency cascade | adjacent and nonlocal exact divergence-free triads | derivative/log loss, divergent shell sum, or Tao-invariant estimate | exact symbol analysis in R7 |
| R6 Lagrangian | strong strain with modest energy | requires \(\int\|\nabla u\|_\infty\) as an input | localize strain; R3/R7 |
| R7 exact cancellation | exhaustive symbolic/numerical exact-triad probe | one admissible triad violates claimed sign/gain | weaken claim or expose cascade candidate to R11 |
| R8 analyticity | radius inequality near hypothetical critical growth | coefficient is just a continuation norm | identify coefficient; R5/R6 |
| R9 weak-to-smooth | suitable solution with CKN-scale defect | proves only partial/eventual regularity | minimal profile in R4 |
| R10 certified computation | tail and all-scale coverage audit | finite samples, non-rigorous floats, or circular tail bound | observation becomes conjecture for R3/R5/R7 |
| R11 exact breakdown | Fefferman clause-by-clause admissibility | different operator/domain/class or only weak nonuniqueness | use model only as positive-route falsifier |

## 7. Falsification protocol

For every new route claim:

1. write the exact quantified inequality and its domain;
2. compute its scaling exponent;
3. test zero, heat-flow, single-mode, two-mode, and exact triad examples where
   meaningful;
4. test whether its proof survives Tao averaging;
5. normalize assumptions against known continuation criteria;
6. audit weak/smooth and force/domain categories;
7. record a reproducible witness and disposition in
   FALSIFICATION_LEDGER.md;
8. only then wire a surviving claim into DECOMPOSITION.md.

A killed universal statement stays in the ledger. It may return only with a
strictly narrower statement that excludes the witness for a proved,
equation-derived reason.
