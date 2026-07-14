# Dependency and residual decomposition

Status: **DECOMPOSED / SCIENTIFIC_FRONTIER**
Target: Fefferman alternative (A) on \(\mathbb R^3\)

The purpose of this decomposition is to make circularity mechanically visible.
The endpoint proposition is a consumer only. No record named “solution,”
“certificate,” or “payload” counts unless its fields are independently
inhabited at the required evidence level.

## 1. Artifact architecture

The work is split into the six artifact classes used by the Polya optimal
pattern library.

| Artifact class | Navier instance | What it may contain | What it may not hide |
|---|---|---|---|
| dataContract | Clay data, PDE operators, norms, weak/smooth solution predicates | Definitions and well-formedness proofs | Existence of the target solution |
| payloadRealization | A proved route-specific critical bound, rigidity result, or exact breakdown witness | The new analytic witness | The endpoint as a constructor field |
| bridgeContract | Local solution + continuation criterion \(\Rightarrow\) global solution | Established implication with explicit hypotheses | An assumed route payload |
| decompositionTree | Nodes P0–P8, B0–B7, R1–R11 below | Dependencies and residual ordering | Status promotion by naming |
| falsificationLedger | docs/FALSIFICATION_LEDGER.md | Failed claims, witnesses, pivots | Deleted or silently reworded failures |
| verifierInterface | Lean/compiler/axiom/source/JSON checks | Commands and expected evidence | Testimony in place of native output |

No artifact in this repository is presently kernel-closed for the endpoint.

## 2. Top-level dependency tree

The arrows below point from consumer to required producer:

    A0  FeffermanA
    ├── D0  arbitrary exact admissible datum u0, ν>0, f=0
    └── G0  GlobalSmoothFiniteEnergySolution
        ├── L0  maximal local smooth solution
        │   ├── P0–P4  equation, spaces, local estimates
        │   └── U0  uniqueness/restart compatibility
        ├── C0  NoFiniteBlowup certificate
        │   ├── K0  one checked continuation/rigidity bridge
        │   └── Q0  one unconditional route payload
        │       └── first open residual of R1 … R10
        └── E0  global finite-energy conclusion
            ├── smooth energy identity on each finite interval
            └── compatibility of the extended solution pieces

    N0  FeffermanCOrD (for every fixed ν>0)
    ├── D1  exact admissible datum u0, force f, and domain, parameterized by ν
    └── X0  NoGlobalPhysicallyReasonableSolution
        └── Q11  exact breakdown witness
            └── first open residual of R11

The only admissible constructors for Q0 are theorem artifacts produced by a
route. The following are not constructors:

- a field of type “FeffermanA” in a payload record;
- a field asserting the desired critical norm bound with no lower proof;
- a continuation theorem whose hypothesis is the desired bound;
- a boolean, proposition-valued status tag, or registry string;
- a theorem that returns its input endpoint assumption unchanged;
- a result on a different equation/domain with no proved transfer theorem.

This prevents both endpoint-as-assumption and wrapper progress.

## 3. Shared prerequisite nodes

| Node | Proposition or structure | Producers | Consumers | Status |
|---|---|---|---|---|
| P0 | Official clauses for Fefferman data and alternatives A–D | [FEFFERMAN2000], `Navier/Problem.lean`, and `Navier/OfficialProblem.lean` | every route, A0/N0 | A–D proposition surfaces typed; seven convention/quotient bridges remain explicit and no endpoint is inhabited |
| P1 | Vector calculus and Leray projection on \(\mathbb R^3\) | Mathlib plus `Navier/Analysis/VectorCalculus.lean` | all routes | product/coordinate leaves checked; curl, Leray, pressure recovery, and integration identities open |
| P2 | Schwartz, Sobolev, mixed, critical, weak, and suitable spaces | Mathlib plus new definitions | all routes | open formal infrastructure |
| P3 | Navier–Stokes scaling and norm exponent \(1-3/p-2/q\) | direct calculation plus `Navier/Scaling.lean`, `Navier/EnergyObstruction.lean`, and `Navier/Analysis/Covariance.lean` | R1, R4, R5, R9–R11 | exponent, separate power-integral rules, and spatial derivative/divergence covariance checked; actual mixed norm and full equation covariance open |
| P4 | maximal local smooth solution and restart | Kato/Koch–Tataru analytic theory | bridge K0, all routes | established analytic; Lean absent |
| P5 | smooth energy identity and weak/local energy inequalities | Leray/CKN analytic theory | all routes | established analytic; Lean absent |
| P6 | Serrin and endpoint \(L^3\) continuation | Serrin/ESS | bridge K0, R1/R4/R9 | established analytic; Lean absent |
| P7 | compactness with pressure/nonlinear-defect tracking | route-specific analysis | R4, R9, R10 | decomposed/open |
| P8 | exact-bilinear-symbol discriminator | `Navier/Routes/R7/ExactSymbol.lean`, `Navier/Routes/R7/Triad.lean`, `Navier/Routes/R7/ScaledTriad.lean`, plus new formulation | R5, R7, R11 | Leray/single-mode and collective triad-cancellation leaves checked; an individual transfer is proved frequency-unbounded, so a weighted collective shell gain distinguishing exact NS from generic energy cancellation remains open |

The first formal milestone—P0's statement-A surface, part of P1, the algebraic
and spatial-covariance part of P3, and the first P8 exact-symbol falsification
leaf—is implemented. It is useful even before the analytic imports exist
because it fixes exact consumer types and exposes domain or operator drift.

## 4. Bridge decomposition

The positive R1–R10 bridge must be factored into separately auditable
implications:

| Bridge | Input | Output | Why it is not the frontier |
|---|---|---|---|
| B0 local existence | admissible \(u^\circ,\nu\) | smooth solution on \([0,T_0)\) | classical local theory |
| B1 maximal extension | compatible local solutions | solution on \([0,T_*)\) | standard uniqueness/restart construction |
| B2 blowup alternative | \(T_*<\infty\) | divergence of a named control quantity | continuation theory |
| B3 route-to-control | positive route certificate Q0 | finiteness of that control quantity | route-specific bridge |
| B4 contradiction | B2 + B3 | \(T_*=\infty\) | elementary once types match |
| B5 regularity propagation | global maximal solution | \(C^\infty\) on all finite slabs | parabolic bootstrapping |
| B6 energy propagation | smooth solution + \(f=0\) | uniform energy bound | energy identity |
| B7 packaging | B1, B4–B6 | Fefferman (A) witness | endpoint wrapper only |

B7 cannot be marked ahead of B3. B3 itself cannot be marked ahead of a
payload Q0. In particular, proving B7 conditionally is useful wiring but is
not mathematical progress on the frontier.

## 5. Route payload interfaces and lower residuals

Each route output is narrower than (A). Each first residual is narrower still,
and has a direct falsification test.

| Route | Payload or consumer output | First lower residual | Residual is strictly lower because |
|---|---|---|---|
| R1 | finite critical mixed norm | local scale-invariant flux inequality | it is one estimate, not global existence |
| R2 | restartable global critical mild norm | large-data interval-independent contraction gain | it concerns the Duhamel map only |
| R3 | integrable vortex-stretching depletion | dynamically generated high-vorticity direction coherence | it is a geometric bound on one term |
| R4 | no nonzero minimal ancient blowup profile | strong compactness with zero nonlinear defect | it is a limit-passage statement |
| R5 | summable high-frequency flux | no-loss exact shell interaction bound | it is a trilinear frequency estimate |
| R6 | finite accumulated deformation/strain | derived bound for a weaker flow-control integral | it is an a priori integral inequality |
| R7 | exact-symbol critical gain | one Fourier-triad cancellation estimate | it is algebraic/analytic at the symbol level |
| R8 | positive analytic radius on finite intervals | noncircular radius differential inequality | it is an inequality for one Gevrey functional |
| R9 | absence of every singular cylinder | quantitative defect exclusion at one scale | it strengthens a local energy estimate |
| R10 | universal finite certificate | compact covering plus analytic tail theorem | it is a reduction theorem, not a simulation |
| R11 | Q11 exact C/D datum/force with breakdown, consumed by N0 rather than B3 | exact cascade interaction and admissibility lemma | it is a construction component, not nonexistence |

A residual is rejected as “not lower” if its statement contains A0, G0, C0,
or an equivalent universal critical bound in its assumptions.

## 6. Noncircularity audit

Every proposed theorem must pass these checks before it is wired upward:

1. **Assumption containment:** normalize hypotheses and search for A0, G0,
   “global smooth,” “no blowup,” or the exact conclusion norm.
2. **Consumer separation:** the route theorem file may import definitions and
   prerequisites, but not the endpoint wrapper theorem.
3. **Equation identity:** viscosity, dimension, force, projection, and domain
   are fields in the theorem statement; no prose-only match.
4. **Scaling audit:** every norm states its scaling exponent. A critical
   conclusion cannot be obtained from energy by an unstated compactness gain.
5. **Tao discriminator:** a decisive positive estimate must name the exact
   symbol property that fails for the averaged class [TAO2016].
6. **Weak/smooth audit:** existence of a weak solution is not a smooth
   solution payload; weak uniqueness/nonuniqueness does not answer A0.
7. **Status audit:** scaffolded, decomposed, conditional, scientificFrontier,
   red, and kernelClosed remain distinct.
8. **Native evidence:** a proof claim requires fresh compiler output and an
   axiom audit; a source claim requires a stable primary reference.

## 7. Formal dependency ownership

The proposed namespace split is intentionally one-way:

    Navier.Clay.Data
    Navier.Analysis.Scaling
    Navier.Analysis.Energy
    Navier.LocalTheory.Contract
    Navier.Regularity.Criteria
    Navier.Routes.<RouteName>.Payload
    Navier.Bridges.GlobalContinuation
    Navier.Problem

Navier.Problem may import the bridge. Route payload modules may not import
Navier.Problem. The machine-readable registry in
`data/attack_registry.json` mirrors these edges and its validator rejects an
experiment or wrong-domain payload on an exact endpoint proof path.

## 8. Closure conditions

For a positive resolution, closure requires all of the following:

- an inhabited exact Fefferman-A data/solution contract;
- native proof of one route payload with no endpoint-equivalent assumption;
- native proof of B0–B7 with matching whole-space, unforced hypotheses;
- source and model/domain audit;
- single-file Lean compilation and raw axiom output limited to the repository's
  accepted kernel primitives;
- fresh registry and artifact validators.

Until then the honest verdict is **DECOMPOSED**, with the first unresolved
mathematical leaf on each route recorded above.
