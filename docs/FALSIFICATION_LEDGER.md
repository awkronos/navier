# Falsification ledger

Ledger initialized: **2026-07-14**
Campaign baseline (initial contract commit):
**81448ed3e488b8b7d357ce430d52df4434f0c9cd**

This ledger records failed claim classes and boundary mistakes, not failed
people or papers. A published theorem remains valid in its stated scope even
when a stronger use of it is killed. Entries are never deleted; a repaired,
strictly narrower successor links back to the original ID.

Statuses:

- **RED:** the stated universal/inferential claim has a counterexample or
  direct logical/source contradiction.
- **DECOMPOSED:** the claimed route is only conditional; a named lower residual
  remains.
- **QUARANTINED:** the claim concerns a different model/domain/solution class
  and lacks a transfer theorem.

## Initial ledger

| ID | Status | Claim tested | Falsifier or audit witness | Consequence | Permitted successor |
|---|---|---|---|---|---|
| F-001 | RED | The smooth energy identity alone controls a scale-critical norm | Under \(u_\lambda=\lambda u(\lambda x,\lambda^2t)\), energy scales as \(\lambda^{-1/2}\) while a critical norm scales as \(\lambda^0\) | No scale-uniform critical inequality can be obtained from energy size alone | Add a named exact-structure or geometric estimate and retest |
| F-002 | RED | Energy cancellation plus generic harmonic-analysis estimates suffice for global regularity | Tao's averaged bilinear equation preserves those coarse properties and admits finite-time blowup [TAO2016] | Any decisive positive estimate must distinguish the exact Navier–Stokes bilinear symbol | State the discriminator and show failure under Tao averaging |
| F-003 | RED | A continuation criterion is itself an unconditional route payload | Logical normalization: “if \(N(u)<\infty\), then continue” does not prove \(N(u)<\infty\) | Serrin/ESS remain bridge results, not R1 closure | Prove the norm from strictly lower hypotheses |
| F-004 | DECOMPOSED | Banach contraction gives arbitrary-large-data global existence | Kato/Koch–Tataru mechanisms obtain local large-data or global small-data control [KATO1984], [KOCH_TATARU2001] | FixedPointBanach may close local wiring only | Produce an interval-independent large-data gain not based on assumed smallness |
| F-005 | RED | CKN partial regularity proves that every suitable solution is smooth | CKN controls the parabolic size of the singular set; it does not show the set is empty [CKN1982] | Partial regularity cannot inhabit FeffermanA | Add a quantitative all-cylinder exclusion theorem |
| F-006 | RED | Leray weak existence proves Fefferman alternative A | A requires globally smooth velocity and pressure; Leray supplies a finite-energy weak solution [LERAY1934] | Weak existence is a lower producer only | Prove weak-to-strong regularity for every admissible smooth datum |
| F-007 | RED | Weak nonuniqueness proves Fefferman C or D | Nonuniqueness is not nonexistence of every global smooth physically reasonable solution; the solution/force classes also require an exact audit [BUCKMASTER_VICOL2019], [ALBRITTON_BRUE_COLOMBO2022] | These papers mark a weak-category boundary, not a Clay breakdown witness | Construct an exact C/D datum and force and prove the stated nonexistence |
| F-008 | QUARANTINED | A periodic global theorem automatically proves the whole-space theorem | Fefferman states B and A as distinct alternatives with different domains [FEFFERMAN2000] | No B-to-A coercion is admitted | Supply a theorem transporting all data, pressure, decay, and energy properties |
| F-009 | RED | Polya EnergyMethod is a formal PDE energy theorem | Its live theorem concerns finite additive energy and small difference sets | Name similarity cannot supply P5 | Formalize a new kinetic/local-energy theorem with the correct integral domain |
| F-010 | RED | Polya DyadicDecomposition supplies Littlewood–Paley theory | Its live theorem is dyadic pigeonholing for a finite set of natural numbers | It cannot build R5 frequency projections or Besov estimates | Add genuine Fourier projection/paraproduct infrastructure |
| F-011 | DECOMPOSED | Instantaneous analyticity alone prevents finite-time singularity | Known Gevrey estimates are conditional/local and their radius bounds can depend on quantities that may diverge [FOIAS_TEMAM1989] | Analyticity is a diagnostic unless its radius inequality closes noncircularly | Prove a positive radius bound from lower exact-structure control |
| F-012 | RED | A large finite numerical survey proves a universal regularity or blowup statement | Finite samples do not cover arbitrary smooth data or unresolved arbitrarily small scales | Numerical results remain observation-only | Give interval certificates, a compact finite-cover theorem, and an analytic tail bound |
| F-013 | RED | Weak convergence of approximate solutions passes the quadratic term automatically | The product \(u_n\otimes u_n\) needs strong convergence or explicit defect control; weak convergence alone is insufficient | R4/R9 compactness must expose pressure and nonlinear defects | Prove strong local compactness or carry and eliminate a defect measure |
| F-014 | DECOMPOSED | A vorticity-direction criterion shows the direction condition is dynamically automatic | Constantin–Fefferman supplies a conditional geometric criterion, not a derivation of its hypothesis for every datum [CONSTANTIN_FEFFERMAN1993] | R3's first residual is the dynamical coherence estimate | Derive coherence on the high-vorticity set from the exact evolution |
| F-015 | RED | Fefferman C/D are defined as zero-force blowup statements | The official C/D statements quantify an admissible smooth force and conclude absence of a global physically reasonable solution [FEFFERMAN2000] | Do not replace the official target by a narrower paraphrase | Treat zero-force breakdown as a stronger optional subroute; retain force in the exact target |
| F-016 | RED | The official wording of C/D specifically requires a finite-time blowup profile | The official conclusion is nonexistence of a global solution satisfying the listed clauses; it does not prescribe a profile/mechanism [FEFFERMAN2000] | A local-theory equivalence may not be assumed silently | Prove any equivalence as a separate bridge, or use the exact nonexistence conclusion |
| F-017 | QUARANTINED | Blowup for Tao's averaged equation is blowup for Navier–Stokes | The averaged bilinear operator is different from the exact Leray-projected nonlinearity [TAO2016] | Averaged blowup is an obstruction to generic positive arguments only | Prove an exact-symbol embedding before any C/D use |
| F-018 | RED | A compiling endpoint wrapper establishes scientific closure when its payload is assumed or axiomatized | Dependency/axiom inspection distinguishes a checked implication from realization of its premise | Wrapper progress is wiring and keeps frontier status unchanged | Supply the lower payload and rerun raw axiom/dependency audits |
| F-019 | QUARANTINED | A two-dimensional, axisymmetric, bounded-domain, hyperdissipative, or Euler theorem can be reported as A | At least one load-bearing dimension/domain/dissipation/nonlinearity field differs | Model results remain benchmarks | Prove a field-by-field transfer theorem to the exact whole-space equation |
| F-020 | RED | Source grep, status prose, or a registry boolean is sufficient proof evidence | Such text can be stale or disconnected from theorem dependencies; only native compiler/axiom output checks the formal artifact | Status cannot mint closure | Bind fresh native output to the exact revision and declaration |

## Integration audit additions

| ID | Status | Claim tested | Falsifier or audit witness | Consequence | Permitted successor |
|---|---|---|---|---|---|
| F-021 | RED | A periodic B/D contract may constrain velocity but omit pressure periodicity | 2026-07-14 audit at formal-source revision `528ff6f4fa06d7ea4dcebbd308eaee2d5dfcb07f`; Fefferman's official erratum explicitly adds \(p(x+e_j,t)=p(x,t)\) | Any future B/D surface or validator must require periodicity of both fields | Add adversarial contract tests that reject a velocity-only periodic surface |

## Route test queue

These are not yet falsifications; they are the first adversarial probes to run
when a concrete inequality is proposed.

| Test ID | Route | Input family | Failure signal |
|---|---|---|---|
| T-001 | R1 | rescaled compactly supported divergence-free packets | a “uniform” constant changes with \(\lambda\) |
| T-002 | R3 | high-vorticity packets with rapidly rotating direction | coherence estimate lacks an equation-derived exclusion |
| T-003 | R5/R7 | exact divergence-free Fourier triads across adjacent and separated shells | claimed sign/gain fails on one admissible triad |
| T-004 | R4/R9 | concentrating suitable approximants with pressure tracked | limit loses nontriviality or retains nonlinear defect |
| T-005 | R8 | Gevrey radius inequality under critical-norm growth | coefficient is equivalent to Serrin/strain continuation input |
| T-006 | R10 | adversarial data outside a proposed finite cover plus high-frequency tail | certificate has uncovered configurations or circular tail hypotheses |
| T-007 | R11 | clause-by-clause Fefferman audit of datum, force, domain, and solution class | any field belongs to an averaged/model/weak problem rather than C/D |

## Entry protocol

Every new entry must record:

1. the exact quantified claim, not a slogan;
2. route and dependency node;
3. date, source revision, and command or primary-source witness;
4. whether the witness refutes the mathematics, the inference, or only a model
   transfer;
5. the smallest repaired statement that excludes the witness for a proved
   reason; and
6. links to superseding ledger IDs without erasing the original.

A route is killed only at the granularity of the tested claim. A counterexample
to a proposed sign estimate does not by itself kill all exact-structure
approaches; it forces the next proposal to be narrower and to explain the
witness.
