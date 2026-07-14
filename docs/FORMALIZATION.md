# Lean formalization roadmap

Status: **SCAFFOLDED / SCIENTIFIC_FRONTIER**

The formal source tree now exists. `Navier/Problem.lean` is the canonical
statement-A encoding; `Navier/Scaling.lean`, `Navier/Disposition.lean`, and
`Navier/Frontier.lean` provide checked algebraic and status infrastructure.
`Navier/ClayFrontier.lean` fixes the conjectural disposition, and
`Navier/AxiomAudit.lean` emits the complete public trace. They do not realize
the endpoint. Two convention-comparison residuals and the entire global
analytic payload remain open. Alternative (A) on the whole space is the first
formal target; interfaces described as “proposed” below do not yet exist in
Lean.

## 1. Target semantics

The implemented top-level proposition has this logical shape:

\[
\begin{aligned}
\mathsf{FeffermanA}:\quad
\forall \nu>0,\ \forall u^\circ,\quad&
\mathsf{SmoothRapidDecay}(u^\circ)\ \land\
\mathsf{DivergenceFree}(u^\circ)\\
&\Longrightarrow
\exists (u,p),\
\mathsf{SolvesNS}_{\mathbb R^3}(\nu,0,u^\circ,u,p)\\
&\hspace{42mm}\land\
\mathsf{SmoothGlobal}(u,p)\\
&\hspace{42mm}\land\
\sup_{t\ge0}\int_{\mathbb R^3}|u(x,t)|^2\,dx<\infty .
\end{aligned}
\]

The current encoding represents rapid decay using Mathlib's `SchwartzMap`.
Identifying that convention with Fefferman's coordinatewise quantifiers—for
every multi-index \(\alpha\) and every \(K\), some constant
\(C_{\alpha,K}\) bounds
\(|\partial^\alpha u^\circ(x)|(1+|x|)^K\)—is the named
`schwartzConventionEquivalence` residual.

**Status (rapid-decay direction): CLOSED.** `Navier.ConventionBridges.schwartzmap_satisfies_fefferman_rapid_decay`
proves every Mathlib `SchwartzMap` on `ℝ³` satisfies Fefferman's coordinatewise
rapid-decay bound (the safety-relevant half of clause (4): the carrier admits
only rapidly-decaying data), kernel-clean. The companion smoothness direction
is now explicit as
`Navier.ConventionBridges.schwartzmap_satisfies_fefferman_smoothness` at
Mathlib's `∞` regularity. This distinction matters: `∞` is ordinary C∞,
whereas Mathlib's larger `ω` index is analytic regularity. The
converse representation from Fefferman's coordinatewise smooth rapid-decay
class to a bundled `SchwartzMap` remains open, so the named convention
equivalence is not closed. The global solution domain includes
\(t=0\), the initial trace is explicit, viscosity is positive, forcing is
identically zero, and pressure and velocity are `ContDiffOn` the closed
half-space. Equivalence of that within-derivative convention to Fefferman's
boundary-smoothness wording is the separate
`halfSpaceSmoothnessEquivalence` residual.

Separate proposed definitions FeffermanB, FeffermanC, and FeffermanD should
encode the exact periodic/forced alternatives. They are sibling targets and
must not be definitionally conflated with A. The B/D surfaces must include
periodic pressure, as required by Fefferman's erratum.

## 2. Module order

| Phase | Module | Output | Verification boundary | Status |
|---|---|---|---|---|
| F0 | `Navier/Problem.lean` | Concrete \(\mathbb R^3\) fields, Fréchet/within derivatives, zero force, classical-solution predicate, statement-A encoding, two representation residuals | targeted compile plus official-quantifier audit | implemented scaffold; endpoint conjectural |
| F1 | `Navier/Problem.lean` and `Navier/Analysis/VectorCalculus.lean` | divergence, scalar gradient, convection, product rule, and coordinate expansion exist; curl, tensor divergence, Leray projection, and integration identities remain | identities on smooth compactly supported fields | partial |
| F2 | `Navier/Problem.lean` now; proposed `Navier/Analysis/Spaces.lean` | Schwartz initial data and energy integrability exist; Sobolev, mixed, weak/suitable, and critical spaces remain | coercions, measurability, norm equality tests | partial |
| F3 | `Navier/Scaling.lean`, `Navier/EnergyObstruction.lean`, and `Navier/Analysis/Covariance.lean` | algebraic exponent \(1-3/p-2/q\), separate spatial/time power-integral rules, spatial derivative/divergence covariance, and finite/reciprocal examples | single-file compile and raw axiom audit | partial; full equation and actual mixed-norm covariance open |
| F4 | proposed `Navier/Analysis/Energy.lean` | smooth energy identity; weak and local energy contracts | compact-support cutoff and limit assumptions explicit | open |
| F5 | proposed `Navier/LocalTheory/Contract.lean` | maximal local solution, uniqueness, restart, blowup-alternative interfaces | no endpoint/global witness in input records | open analytic port |
| F6 | proposed `Navier/Regularity/Criteria.lean` | Serrin and endpoint-\(L^3\) conditional continuation contracts | hypotheses and scaling match primary results | open analytic port |
| F7 | proposed `Navier/Routes/*/Payload.lean` | one narrow route certificate per ATTACK.md | theorem uses only lower nodes and exposes its first residual | scientific frontier |
| F8 | proposed `Navier/Bridges/GlobalContinuation.lean` | local theory + route certificate \(\Rightarrow\) global smooth finite-energy solution | dependency/no-circular-import audit | open conditional wiring |
| F9 | `Navier/Disposition.lean`, `Navier/Frontier.lean`, `Navier/ClayFrontier.lean`, `Navier/AxiomAudit.lean` | proof-bearing status gate, ranked dependency view, conjectural statement-A disposition, and exhaustive public axiom commands | compile plus raw axiom audit | implemented status/audit scaffold; blocked on F7 |

The implemented parts of F0–F3 are reusable infrastructure; the table keeps
their unimplemented analytic portions explicit. F5/F6 are substantial
translations of known analysis. F7 is where new mathematics must occur. F8
and the status wiring in F9 must remain thin consumers so their completion
cannot disguise an empty F7.

## 3. Data contracts

The implemented `IsClassicalSolution` contains smoothness, trace,
incompressibility, the pointwise PDE, integrability, and one uniform energy
bound. `ScientificDisposition` carries proof evidence only in its `realized`
constructor, and the current statement-A disposition is `conjectural`.

The following additional proposed structures should contain data and proved
laws only:

- **WholeSpaceDatum:** viscosity, positive-viscosity proof, initial velocity,
  smoothness, divergence-free proof, and rapid-decay witnesses.
- **NSSolutionOn:** time interval, velocity, pressure, smoothness on the stated
  domain, equation proof, divergence-free proof, and initial trace.
- **EnergyControlled:** one explicit constant and a proof of the uniform
  \(L^2\) bound; not merely pointwise finiteness.
- **MaximalSolution:** local solution, maximal time, compatibility/restart,
  uniqueness, and a proved blowup alternative.
- **CriticalControl:** the exact norm, exponents, critical-scaling equality,
  and a proof of finiteness derived by a route theorem.
- **PositiveRouteCertificate:** a tagged sum of narrowly typed R1–R10 outputs,
  each with its own bridge theorem; never a field of type FeffermanA.
- **BreakdownCertificate:** the separate R11 output consumed only by the exact
  FeffermanC/FeffermanD branch; it cannot be passed to GlobalContinuation.

For C/D, a BreakdownDatum must include the force and all of Fefferman's
smoothness/decay or periodicity witnesses. “No global physically reasonable
solution” is the conclusion, not an input field.

## 4. First formal leaf: scaling

Scaling is the best first target because it is central to every route and
independent of the unresolved PDE existence theory. The present Lean module
proves only the scalar arithmetic of the exponent and critical line; it does
not claim an analytic mixed-norm scaling theorem.

The remaining formal sequence is:

1. define \(S_\lambda u(x,t)=\lambda u(\lambda x,\lambda^2t)\) for
   \(\lambda>0\);
2. lift the checked spatial power-integral identity to an actual spatial
   \(L^p\) norm theorem with its domain and integrability hypotheses;
3. lift the checked scalar time-integral identity to the outer \(L^q\) layer;
4. connect those analytic results to the already checked exponent
   \(1-3/p-2/q\) and critical-line arithmetic;
5. instantiate energy at \((p,q)=(2,\infty)\) and obtain exponent \(-1/2\);
6. encode “energy alone is not scale coercive” as a precise sequence of
   rescaled nonzero test fields whose energy norm tends to zero while the
   critical norm remains fixed.

Step 6 is an obstruction theorem, not a philosophical comment, and becomes a
regression test against accidental energy-only promotions.

**Status (step 6): REALIZED.** `Navier.EnergyObstruction.energy_not_scale_coercive`
proves, for every nonzero `φ ∈ L² ∩ L³` on `ℝ³` with positive `L³` mass and every
`ε > 0`, a rescaling `u_c(x) = c · φ(c · x)` whose `L²` energy is below `ε` while
its scale-critical `L³` mass is unchanged and positive. The two scaling lemmas
`l2_energy_dilation` (`L²` energy rescales by `c⁻¹`) and `l3_critical_dilation`
(`L³` invariant) are proved by `MeasureTheory.Measure.integral_comp_smul` and
`Module.finrank_fin_fun` (the change-of-variables on `ℝ³`). Kernel-clean; raw
`#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`. This closes the
formal side of falsification entry `F-001`. It does not advance the Clay
endpoint.

## 5. Known-result ports versus frontier payloads

Each analytic result is formalized in two layers:

- a **statement contract** that fixes all hypotheses and conclusions; and
- a **realization theorem** whose proof is either ported from primary
  mathematics or remains explicitly uninhabited.

For example, a Serrin contract may consume a local smooth solution and a
finite \(L_t^qL_x^p\) norm on \([0,T)\) with \(3/p+2/q\le1\), then produce
continuation past \(T\). That theorem is a conditional bridge. It does not
produce the norm. The R1 payload theorem must have the datum and lower PDE
estimates as inputs and the norm bound as its conclusion.

The same separation applies to:

- Koch–Tataru/Banach fixed-point local theory versus arbitrary-data global
  control;
- Constantin–Fefferman conditional vorticity coherence versus automatic
  coherence;
- CKN epsilon/partial regularity versus exclusion of all singular points;
- Gevrey smoothing versus a uniform positive radius;
- weak existence versus smooth global existence.

## 6. Polya use in Lean

POLYA_MAP.md records the only currently matching theorem shapes. The initial
formal uses should be limited to:

- FixedPointBanach.apply after the complete Duhamel metric space and
  contraction estimate exist;
- Bootstrap.apply after the good-time set is proved nonempty, open, and closed;
- VitaliCovering.apply after parabolic cylinders satisfy its Data contract;
- CompactnessNormalFamilies.apply only for compact-domain equicontinuous
  approximants;
- small support uses of BanachSteinhaus.apply and TriangleInequality.apply.

No import should be added for a catalogue-name match alone. In particular, the
existing Polya EnergyMethod and DyadicDecomposition theorems have the wrong
domains for PDE energy and Littlewood–Paley analysis.

## 7. Anti-circularity implementation rules

1. Before route modules are added, extract their lower data/operator imports
   from `Navier/Problem.lean` so a route never imports a module that imports
   the endpoint wrapper. The current combined statement file is acceptable
   for fixing the surface, but is not the final producer/consumer split.
2. A payload structure may not contain FeffermanA, global smoothness, no
   finite blowup, or an equivalent continuation norm as an unproved field.
3. Every assumption-bearing theorem receives a machine-readable hypothesis
   inventory, including domain, force, equation, solution class, and scaling.
4. A bridge proof cannot change the evidence status of its input payload.
5. Model theorems live in a Quarantine namespace until a checked transfer
   theorem reaches an exact Clay type.
6. Numerical data types cannot coerce to proof-bearing route certificates.
7. A theorem declaration with an axiom/sorry dependency remains conditional
   even if every wrapper above it compiles.

## 8. Native verification ladder

At each phase, the implementation runs the narrowest native check:

1. compile the edited module alone with the project's pinned Lean toolchain;
2. compile Navier/Problem.lean only after its dependencies exist;
3. run targeted positive and negative examples for exact quantifiers;
4. emit raw #print axioms for each exported theorem;
5. accept only \(\{\mathsf{propext},\mathsf{Classical.choice},
   \mathsf{Quot.sound}\}\), plus an explicitly documented native_decide
   witness where the repository policy permits it;
6. validate the attack registry and reference manifest;
7. bind every report to the exact Git revision and source bytes.

Aggregate build success is insufficient for a claimed inhabitant if its axiom
trace includes an open analytic payload. The trace of the proposition
definition alone does not supply an inhabitant. Source grep is not an axiom
audit.

## 9. Roadmap exit criteria

- **F0-A encoding milestone:** the current statement-A surface compiles, but
  its two convention-equivalence residuals remain visible. Full F0 exit still
  requires A–D round-trip tests against the official force, pressure,
  periodicity, domain, and decay clauses.
- **F3 algebra milestone:** the exponent, separate space/time power-integral
  identities, spatial derivative/divergence covariance, and critical-line
  arithmetic compile and are axiom-audited. Full F3 exit still requires full
  equation covariance and an actual nested mixed-norm theorem. The
  energy-supercritical obstruction is already realized.
- **F5/F6 exit:** local and conditional results compile with no concealed
  endpoint hypothesis.
- **F7 exit for A:** one of R1–R10 has a genuinely proved first residual,
  survives all barrier tests, and has native evidence. R11 has a separate C/D
  exit through an exact BreakdownCertificate.
- **F9 exit:** a theorem inhabiting `Clay.StatementA` compiles, its dependency
  graph reaches that F7 realization, and its raw axiom audit is clean.

Before F7, the honest project-level status remains
**SCAFFOLDED / SCIENTIFIC_FRONTIER**, regardless of how much conditional
infrastructure has been formalized.
