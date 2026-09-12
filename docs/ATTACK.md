# Navier–Stokes attack blueprint

Historical research blueprint; proposed routes are not constraints on new proofs.
Current dependencies and verification are described in `DECOMPOSITION.md`
and `FORMALIZATION.md`. Status and line-number claims below belong to the
development snapshots that produced this blueprint.
Research program baseline (initial contract commit):
**81448ed3e488b8b7d357ce430d52df4434f0c9cd**
Primary formal target: **Fefferman alternative (A), whole space, zero force**

Current status supersedes the historical route labels below: whole-space
forced alternative C is now proved by
`Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown`; unforced A and
periodic D are not proved here. See [`RESULT_MAP.md`](RESULT_MAP.md) for the
current claim and evidence boundary.

This document is an attack architecture, not a claimed solution. An established
criterion is recorded as a conditional bridge; it is never counted as the
unconditional estimate that the criterion requires. Every research route below
therefore names its first open residual and a test that can kill or redirect the
route.

## 1. Exact problem boundary

For velocity \(u:\mathbb R^3\times[0,\infty)\to\mathbb R^3\), pressure
\(p:\mathbb R^3\times[0,\infty)\to\mathbb R\), viscosity \(\nu>0\), initial
velocity \(u^\circ\), and force \(f\), the equations are

\[
\partial_t u+(u\cdot\nabla)u=\nu\Delta u-\nabla p+f,\qquad
\nabla\cdot u=0,\qquad u(\cdot,0)=u^\circ .
\]

“Rapid decay” below means Fefferman's clauses (4) and (5): every spatial
derivative of \(u^\circ\), and every spatial/time derivative of \(f\), decays
faster than every prescribed polynomial, uniformly on the stated spacetime
domain. “Periodic” means period one in every spatial coordinate, his clause
(8); the periodic force also obeys rapid time decay, clause (9).

The four admissible alternatives in Fefferman's official formulation are:

- **(A), existence and smoothness on \(\mathbb R^3\).** For every smooth,
  divergence-free, rapidly decaying \(u^\circ\), with \(\nu>0\) and \(f=0\),
  there exist \(p,u\in C^\infty(\mathbb R^3\times[0,\infty))\) solving the
  equations and satisfying a single uniform-in-time bound
  \(\int_{\mathbb R^3}|u(x,t)|^2\,dx<C\).
- **(B), existence and smoothness on \(\mathbb R^3/\mathbb Z^3\).** For every
  smooth, divergence-free, period-one \(u^\circ\), with \(\nu>0\) and \(f=0\),
  there exist smooth \(p,u\) on all nonnegative times solving the equations,
  with both \(u\) and \(p\) period one in every spatial coordinate. (Clause
  (10) explicitly imposes periodicity on \(u\), clause (11) imposes smoothness
  on both fields, and Fefferman's erratum makes pressure periodicity explicit.)
- **(C), breakdown on \(\mathbb R^3\).** For every fixed \(\nu>0\), there
  exist smooth, divergence-free, rapidly decaying \(u^\circ\) and smooth
  rapidly decaying \(f\) such that no pair \(p,u\) exists on
  \(\mathbb R^3\times[0,\infty)\) satisfying the equations, global smoothness,
  and the uniform energy bound.
- **(D), breakdown on \(\mathbb R^3/\mathbb Z^3\).** For every fixed
  \(\nu>0\), there exist smooth divergence-free period-one \(u^\circ\) and
  smooth period-one \(f\) with the required decay in time, such that no global
  smooth solution pair \(p,u\) exists with both fields satisfying the
  periodic conditions (including the pressure-periodicity erratum).

This is a semantic restatement of clauses (1)–(11) and alternatives (A)–(D) in
[FEFFERMAN2000]. It deliberately preserves three distinctions that are often
lost: (A)/(B) are unforced, (C)/(D) permit forcing, and periodic smoothness does
not prove the whole-space statement.

Alternative (A) is the first Lean target. Alternatives (B)–(D) remain explicit
siblings; a result for one is not transported to another.

## 2. Provenance and synthesis boundary

This dossier reuses research_program architecture, not mathematical conclusions, from
three local research repositories:

| Source snapshot | Provenance status | Pattern transplanted | Anti-pattern rejected here |
|---|---|---|---|
| Reality object **e38aacfd494562410ad0f6e0ae789a19b09271d1** | Observed during a peer-active/mutable research_program; **not a frozen dependency or stable worktree pin** | typed scientific contracts; separate realized/conjectural/quarantined/falsified/retired rows; preserved route tombstones; same-model predecessor checks; native validators | free “readback” fields that restate a target, record projection as realization, finite/numerical agreement promoted to continuum science, and deletion of failed routes |
| Reimann **6dab82adc30a6e9c0c3f54ad5b4f4f51168e4b5c** | Clean read-only snapshot | named frontier leaves, conditional-adapter versus payload separation, obstruction/false-form theorems, raw axiom boundary, and a dependency map from lower roots to endpoint | a green wrapper or adapter reported as the endpoint theorem; hidden endpoint assumptions; source-level proof-gap counts standing in for compiler/axiom evidence |
| npnep **a3e56a4c922f8103f680c28d5217245497ab7236** | Clean read-only snapshot | parallel approach portfolio, per-approach barrier analysis, reproducible research_program schema, and theorem/conjecture/experiment evidence tiers | experiments generalized as proofs, barrier-free route descriptions, stale prose overriding native evidence, and unfalsifiable research_program outputs |

The synthesis is intentionally one-way. No theorem, scientific payload, data
file, or mutable status from these repositories is an assumption of the
Navier–Stokes argument. Navier adopts only the audit shapes: explicit
producers/consumers, lower residuals, kill tests, evidence tiers, and retained
negative history. Primary Navier–Stokes sources, listed in the reference
manifest, remain the authority for mathematical claims.

## 3. Scaling and the supercritical energy barrier

If \(u\) solves the unforced equation, the rescaling

\[
u_\lambda(x,t)=\lambda u(\lambda x,\lambda^2t),\qquad
p_\lambda(x,t)=\lambda^2p(\lambda x,\lambda^2t)
\]

has the same viscosity and equation. At fixed time, the change of variables
\(y=\lambda x\) gives

\[
\|u_\lambda(t)\|_{L_x^p}
=\lambda^{1-3/p}\|u(\lambda^2t)\|_{L_x^p}.
\]

For finite \(q\), changing time variable \(s=\lambda^2t\) then gives

\[
\begin{aligned}
\|u_\lambda\|_{L_t^qL_x^p}^q
&=\int\lambda^{q(1-3/p)}
  \|u(\lambda^2t)\|_{L_x^p}^q\,dt\\
&=\lambda^{q(1-3/p)-2}\|u\|_{L_t^qL_x^p}^q,
\end{aligned}
\]

and hence, also with the usual \(q=\infty\) interpretation,

\[
\boxed{\ \|u_\lambda\|_{L_t^qL_x^p}
=\lambda^{\,1-3/p-2/q}\|u\|_{L_t^qL_x^p}\ }.
\]

The mixed norm is critical exactly when \(3/p+2/q=1\). In contrast,
\(L_t^\infty L_x^2\) and \(L_t^2\dot H_x^1\) both scale with exponent
\(-1/2\). Thus the energy estimate

\[
\tfrac12\|u(t)\|_2^2+
\nu\int_0^t\|\nabla u(s)\|_2^2\,ds
=\tfrac12\|u^\circ\|_2^2
\]

is supercritical relative to concentration: zooming into a smaller candidate
singularity makes the controlled energy quantity smaller. **Energy alone is
therefore insufficient to exclude scale-critical concentration.**

Tao's averaged equation [TAO2016] sharpens this into an attack gate. His
averaged bilinear operator retains the energy cancellation and the generic
order-zero harmonic-analysis structure, yet admits finite-time blowup.
Consequently, a positive route is killed if its decisive estimate uses only
energy cancellation plus estimates shared by Tao's averaged operator. It must
exploit a verifiable feature of the exact Leray-projected nonlinearity.

## 4. Shared prerequisites

These are reusable infrastructure, not route-specific discoveries.

| ID | Prerequisite | Required deliverable | Current evidence |
|---|---|---|---|
| P0 | Exact target | Predicates for Fefferman data, solution, energy, and alternatives A–D | A–D proposition surfaces are typed in `Navier/Problem.lean` and `Navier/OfficialProblem.lean`; seven convention/quotient bridges remain explicit against the official statement [FEFFERMAN2000] |
| P1 | Differential operators | Divergence, gradient, Laplacian, curl, Helmholtz/Leray projection, pressure recovery | Basic divergence/gradient/convection definitions, a product rule, and a coordinate convection expansion are checked; curl, Leray projection, pressure recovery, and integration identities remain |
| P2 | Function spaces | Schwartz/smooth data, Sobolev and mixed norms, weak and suitable solutions, critical spaces | Definitions and embeddings must be formalized |
| P3 | Scaling | Equation covariance and the exponent \(1-3/p-2/q\) | Exponent algebra, spatial/time power-integral identities, pointwise parabolic covariance, and finite-time integrability-faithful critical `L3`-mass-bound covariance are checked. The older raw-integral bound is retained only as a lossy transport leaf. Exact positive-viscosity transport preserves the PDE, initial datum, whole-space energy contract, periodic velocity and pressure, zero force, and arbitrary-force rapid decay; consequently each official A--D surface is equivalent to its exact viscosity-one surface. General `MemLp`/`snorm` and nested mixed norms, plus the five coordinatewise/Mathlib representation bridges, remain open |
| P4 | Local theory | Maximal smooth solution, uniqueness in its class, blowup alternative, restart theorem | A concrete `[0,T)` classical-solution record and a point-evaluation blowup consumer are checked: uniqueness plus fixed-point norm blowup excludes every official global pair because global smoothness gives a compact-time bound. Constructing the local/maximal solution and blowup remains open; analytic precedent [KATO1984], [KOCH_TATARU2001] |
| P5 | Energy interfaces | Smooth energy identity, Leray inequality, local energy inequality | Analytic precedent [LERAY1934], [CKN1982] |
| P6 | Regularity bridges | Serrin mixed-norm and endpoint \(L_t^\infty L_x^3\) continuation | Established conditional results [SERRIN1962], [ESS2003] |
| P7 | Compactness interfaces | Approximation, pressure bounds, strong/weak convergence, defect accounting | Required by routes R4/R9/R10 |
| P8 | Exact-structure test | A predicate distinguishing the true bilinear form from Tao-admissible averages | Both convolution orderings are now explicit. The old growing term cancels with its exchanged ordering; a second polarization survives symmetrization with coefficient `s`, has a conjugate-symmetric divergence-free six-mode table, modal rates `(0,-s,s)`, and squared-frequency-weighted rate `s^3`. An exhaustive `6 x 6` ordered-pair classification proves that the complete coefficient at one off-support output is exactly `s`, not merely that one pair is nonzero. An invariant generated network, exact PDE shell balance, and summability remain open |

P0–P8 may be developed in parallel. In this decomposition no route reaches (A)
without P0, P3, P4, and a checked bridge from its route certificate to global
continuation; the proved composition of exactly that bridge is
`wholeSpaceGlobalRegularity_of_local_continuation_apriori`
(`Navier/Analysis/CriticalControlDecomposition.lean:237`), whose three explicit
inputs are `LocalClassicalExistence`, `NormalizedContinuationFromCriticalControl N`,
and `APrioriCriticalControl N`. A different proof route may establish (A)
directly.

## 5. Parallel research routes

Evidence classes used below are: **established** (published theorem),
**formal-interface** (a definition or bridge still to be encoded),
**open-residual** (new mathematics), **obstruction** (published counterexample
or logical kill test), and **observation-only** (computation).

### R1 — Critical mixed-norm continuation

- **Dependencies:** P0, P2–P6.
- **Deliverable:** an unconditional bound
  \(\|u\|_{L_t^qL_x^p([0,T)\times\mathbb R^3)}<\infty\), uniformly for every
  finite \(T\), at \(3/p+2/q=1\); preferred endpoint
  \(L_t^\infty L_x^3\).
- **First strictly lower residual:** prove a localized, scale-invariant
  nonlinear-flux estimate from the equation and initial data that closes the
  critical norm without assuming it.
- **Kill criterion:** the proof imports the same Serrin/endpoint norm as a
  hypothesis, obtains it only for small data, or derives only a subcritical
  finite-time estimate whose constant diverges at the maximal time.
- **Pivot:** isolate the frequency or geometry responsible for failure and
  transfer that residual to R3, R5, or R7.
- **Evidence:** conditional continuation is established [PRODI1959],
  [SERRIN1962], [ESS2003]; the
  unconditional bound is **open-residual**.

### R2 — Mild fixed point in a critical space

- **Dependencies:** P1–P4 and heat-semigroup/bilinear estimates.
- **Deliverable:** a Duhamel solution in a critical Koch–Tataru/Kato-type space
  whose norm remains restartable on every interval.
- **First strictly lower residual:** an interval-independent decomposition or
  exact-structure estimate that makes the Duhamel map contractive for arbitrary
  large smooth data after evolution, without assuming eventual smallness.
- **Kill criterion:** the contraction constant is small only because the
  initial norm or time interval is small; concatenation constants accumulate
  without a global bound.
- **Pivot:** retain local existence as P4 and send the failed large-data term to
  R5/R7 for structural analysis.
- **Evidence:** local large-data and global small-data mechanisms are
  **established** [KATO1984], [KOCH_TATARU2001]; global arbitrary-data
  contraction is **open-residual**.

### R3 — Vorticity direction and strain depletion

- **Dependencies:** P1–P5, Biot–Savart/strain representation.
- **Deliverable:** a dynamically generated alignment or depletion estimate
  strong enough to control vortex stretching for every smooth datum.
- **First strictly lower residual:** derive quantitative coherence of
  \(\omega/|\omega|\), on the high-vorticity set and at the critical spatial
  scale, from the exact evolution rather than postulating it.
- **Kill criterion:** coherence is an initial/conditional hypothesis, excludes
  admissible high-vorticity configurations without a dynamical proof, or loses
  scale invariance.
- **Pivot:** construct exact Fourier/vortex configurations that saturate the
  failed bound and pass them to R7 or the falsification harness.
- **Evidence:** direction-based criteria are **established**
  [CONSTANTIN_FEFFERMAN1993]; automatic coherence is **open-residual**.

### R4 — Epsilon regularity, concentration compactness, and rigidity

- **Dependencies:** P0, P2, P4–P7; CKN local energy machinery.
- **Deliverable:** assuming first singular time, extract a nonzero minimal
  ancient solution and rule it out by a rigidity theorem.
- **First strictly lower residual:** obtain strong-enough compactness at the
  critical scaling with pressure and nonlinear defect controlled; then state a
  rigidity property not equivalent to the desired endpoint bound.
- **Kill criterion:** a defect measure survives, nontriviality is lost in the
  limit, or the rigidity hypothesis assumes the ancient solution's
  critical norm is bounded.
- **Pivot:** quantify the defect and redirect its support/scale to R5 or R9.
- **Evidence:** partial and epsilon regularity are **established** [CKN1982],
  and critical profile decomposition is established
  [GALLAGHER_KOCH_PLANCHON2013]; the universal compactness-rigidity closure is
  **open-residual**.

### R5 — Frequency envelope and cascade exclusion

- **Dependencies:** P1–P5, P8; genuine Littlewood–Paley and paraproduct theory.
- **Deliverable:** an endpoint-summable frequency-flux inequality preventing
  unbounded transfer to high frequencies.
- **First strictly lower residual:** lift the checked finite triad rates to the
  exact Fourier-series shell balance, close and control the recursively
  generated off-support network, and only then bound the collective
  high–high/low flux with neither derivative loss nor logarithmic accumulation.
- **Kill criterion:** shell summation diverges, one derivative is lost, the
  estimate is shared by Tao's averaged operator, or the envelope bound is
  equivalent to a critical continuation norm.
- **Pivot:** identify the offending triads and search for exact symbol
  cancellation in R7; if none exists, expose them as candidates for R11.
- **Evidence:** the checked symmetrized witness proves that exact unequal-shell
  transfer survives while constant-weight energy cancels. The complete
  `6 x 6` coefficient sum at a selected off-support wave is exactly `s`, so
  the six-mode support is rigorously non-invariant without a hidden
  pair-cancellation loophole.
  Quantitative frequency-localized control conditional on a critical bound is
  established [TAO2019]; unconditional cascade exclusion is **open-residual**,
  constrained by [TAO2016].

### R6 — Lagrangian deformation and vortex stretching

- **Dependencies:** P1–P5; flow-map existence while smooth.
- **Deliverable:** a deformation-gradient or accumulated-strain bound that
  prevents vorticity growth up to every finite time.
- **First strictly lower residual:** control
  \(\int_0^T\|\nabla u(t)\|_\infty\,dt\), or a strictly weaker quantity that
  closes the flow-map estimate, directly from viscous dynamics.
- **Kill criterion:** the decisive bound is exactly a continuation hypothesis
  under another name, or the flow representation requires the regularity it is
  supposed to prove.
- **Pivot:** localize the strain source and hand the nonlocal term to R3/R7.
- **Evidence:** representation while smooth is **established**; global bound is
  **open-residual**.

### R7 — Pressure/strain cancellation in the exact bilinear symbol

- **Dependencies:** P1–P5, P8.
- **Deliverable:** a coercive or sign/cancellation estimate for
  \(\mathbb P\nabla\cdot(u\otimes u)\) that is false for the averaged operator
  but true for the exact Navier–Stokes symbol.
- **First strictly lower residual:** formulate and prove a trilinear estimate on
  exact divergence-free Fourier triads that gains critical summability.
- **Kill criterion:** an exact triad falsifies the claimed sign/gain, or the
  proof uses only rotation/order-zero-multiplier invariant estimates and hence
  survives Tao averaging.
- **Pivot:** classify the saturating triads; feed coherent ones to R3 and
  multiscale ones to R5/R11.
- **Evidence:** pressure recovery and cancellation are established
  infrastructure; the critical gain is **open-residual** with
  **obstruction** [TAO2016].

### R8 — Analyticity/Gevrey radius

- **Dependencies:** P1–P5; Gevrey norms and analytic smoothing.
- **Deliverable:** a positive lower bound on the spatial analyticity radius on
  every finite time interval for arbitrary smooth data.
- **First strictly lower residual:** close the radius differential inequality
  with coefficients controlled by energy plus a genuinely new exact-structure
  quantity, not by an already critical norm.
- **Kill criterion:** the lower bound degenerates precisely when
  \(\|\nabla u\|_\infty\) or a Serrin norm diverges, making the route a wrapper
  around R1/R6.
- **Pivot:** extract the coefficient causing radius collapse and analyze it by
  frequency in R5.
- **Evidence:** conditional/local Gevrey smoothing is **established**
  [FOIAS_TEMAM1989]; uniform large-data radius is **open-residual**.

### R9 — Suitable weak solution to full regularity

- **Dependencies:** P0, P2, P5–P7.
- **Deliverable:** upgrade a global suitable/Leray solution for smooth unforced
  data to a unique smooth solution with no singular points.
- **First strictly lower residual:** strengthen the local energy/defect bound
  from “small singular set” to a scale-invariant exclusion of every singular
  cylinder.
- **Kill criterion:** the result is only almost-everywhere/partial regularity,
  eventual regularity, or weak–strong uniqueness conditional on a strong
  solution.
- **Pivot:** quantify the remaining singular measure and transfer its minimal
  concentration profile to R4.
- **Evidence:** weak existence and partial regularity are **established**
  [LERAY1934], [CKN1982]; total singularity exclusion is **open-residual**.
  Weak nonuniqueness results [BUCKMASTER_VICOL2019],
  [ALBRITTON_BRUE_COLOMBO2022] mark the category boundary; they neither prove
  nor disprove smooth unforced (A).

### R10 — Computer-assisted multiscale exclusion

- **Dependencies:** P0–P5, validated numerics, interval arithmetic, analytic
  truncation/tail theorems.
- **Deliverable:** a finite, independently checkable certificate covering all
  admissible normalized local configurations and all unresolved scales.
- **First strictly lower residual:** prove a compact finite-cover reduction and
  rigorous tail bound whose hypotheses encompass arbitrary smooth
  divergence-free data.
- **Kill criterion:** finite sampling replaces universal coverage, floating
  point output lacks interval certificates, the unresolved tail assumes
  regularity, or discretization error grows at the candidate singular scale.
- **Pivot:** use computations only to propose an analytic inequality for
  R3/R5/R7 and record it as a conjecture until proved.
- **Evidence:** until a universal certificate and checker exist, all outputs are
  **observation-only**.

### R11 — Exact breakdown witness for alternatives (C)/(D)

- **Dependencies:** P0–P5, P8; exact forcing/data admissibility audit.
- **Deliverable:** a smooth rapidly decaying (or periodic) datum/force meeting
  Fefferman's clauses for which no global physically reasonable solution
  exists in the corresponding sense: C includes clauses (6) and (7), while D
  includes clauses (10) and (11).
- **Exactness note:** C/D quantify an admissible force; they do not require
  \(f=0\) or prescribe “finite-time blowup” as the form of nonexistence. A
  zero-force singular construction would be a strictly stronger speculative
  subroute, not the definition of C/D.
- **First strictly lower residual:** construct an admissible viscosity-one
  partial solution, prove agreement with every official global solution, and
  establish finite-time point-norm blowup; alternatively embed a
  self-sustaining cascade in the exact Leray-projected nonlinearity while
  preserving incompressibility and the precise smooth/decay conditions.
- **Kill criterion:** the construction is only for an averaged, dyadic,
  hyperdissipative, Euler, axisymmetric, or weak formulation; or it establishes
  weak nonuniqueness rather than the required nonexistence statement.
- **Pivot:** retain the model as a falsifier of overly generic positive
  estimates, extract the exact-symbol mismatch, and send it to R7.
- **Evidence:** a checked point-evaluation consumer turns local agreement and
  point-norm blowup into nonexistence of an official whole-space or periodic
  global solution. Exact transport reduces all four official viscosity
  quantifiers to viscosity one. One phase-correct unequal-shell interaction
  and its full `6 x 6` off-support coefficient are also checked, but they do
  not form an invariant or self-sustaining network. Averaged blowup is an
  **obstruction** [TAO2016];
  weak nonuniqueness is a boundary result [BUCKMASTER_VICOL2019],
  [ALBRITTON_BRUE_COLOMBO2022]. The subsequently integrated construction now
  closes exact whole-space C; periodic D remains **open** in this repository.

## 6. Using the blueprint

These routes are research suggestions. Any valid proof or counterexample at
the exact target type is admissible, including one following a different
decomposition. Compare the actual hypotheses and carrier of each result with
its consumer and verify the proof with the pinned compiler and axiom audit.

## 7. Source keys

Bibliographic metadata and stable primary URLs for all bracketed keys are in
../references/manifest.json. The source roles are intentionally narrow:
published conditional results establish bridges and barriers, not the missing
global payload.
