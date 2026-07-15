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

F-001's formal side was realized on 2026-07-14 at `d0a728f`:
`Navier.EnergyObstruction.energy_not_scale_coercive` proves the obstruction by
constructing rescalings whose `L²` energy is arbitrarily small while their
scale-critical `L³` mass stays fixed and positive. The entry remains RED: the
theorem certifies that energy alone cannot control the critical quantity.

## Integration audit additions

| ID | Status | Claim tested | Falsifier or audit witness | Consequence | Permitted successor |
|---|---|---|---|---|---|
| F-021 | RED | A periodic B/D contract may constrain velocity but omit pressure periodicity | 2026-07-14 audit at formal-source revision `528ff6f4fa06d7ea4dcebbd308eaee2d5dfcb07f`; Fefferman's official erratum explicitly adds \(p(x+e_j,t)=p(x,t)\) | Any future B/D surface or validator must require periodicity of both fields | Add adversarial contract tests that reject a velocity-only periodic surface |
| F-022 | RED | Separate spatial power-integral and scalar time-integral dilation identities realize the full \(L_t^qL_x^p\) scaling theorem | The checked signatures contain no nested mixed norm, outer \(q\)-power/root, link from the time observable to a spatial \(L^p\) norm, or combined covariance theorem | `lp_dilation_scaling` and `time_dilation_scaling` remain valid lower infrastructure, but full mixed-norm scaling stays open | Define the actual nested norm with its measurability/integrability domain and prove the combined identity |
| F-023 | RED | Cancellation of the six real divergence-free triad coefficients forces every ordered coefficient to vanish or have a favorable sign | At `37d41c1`, `Navier.Routes.R7.witness_nontermwise_cancellation` proves one admissible ordered coefficient is `1` while the six-coefficient sum is `0` | The algebraic cancellation is collective and cannot be promoted to termwise depletion | Add phases and projection explicitly, then test a weighted/grouped shell identity on the preserved triad |
| F-024 | RED | A normalized phase-aware triad coefficient with fixed phases and polarizations admits a frequency-uniform unweighted bound | `Navier.Routes.R7.phased_normalized_coefficient_unbounded_across_positive_scale` bundles the full scaled-triad admissibility certificate and exceeds every real bound at a positive common scale | Any viable cascade estimate must supply a compensating weight, derivative placement, collective cancellation, or field-level constraint | State shell weights and a conjugate-symmetric Fourier realization before testing summability |
| F-025 | RED | Mathlib `ContDiffOn ℝ ⊤` denotes ordinary C∞ smoothness in the Clay surface | Mathlib distinguishes `∞` (coerced top of `ℕ∞`, C∞) from outer `ω`/`⊤` (analytic); the corrected surface and Schwartz bridge compile at `90df8f8` | Using outer `⊤` silently strengthened Fefferman's clause (6) to analyticity | Use scoped `∞` and retain the separate closed-half-space convention bridge |
| F-026 | RED | Periodic alternatives B/D inherit the whole-space bounded-energy clause (7) | Fefferman invokes only (1), (2), (3), (10), (11) for B/D; `Navier.IsPeriodicClassicalSolution` at `bf8dbc7` therefore contains no whole-space energy field | Whole-space energy on a nonzero periodic lift is the wrong object and cannot enter B/D | Develop torus energy only as auxiliary analysis, not as an official endpoint field |
| F-027 | RED | The all-real `orderedTransfer` witness is already a physical Fourier energy-transfer witness | `Navier.Routes.R7.unphased_witness_real_part_zero` shows that restoring the derivative factor `i` gives zero real part; `phased_normalized_witness_coefficient` gives `1` only after normalized projection, a fixed `-i` advector phase, and receiver conjugation are explicit | The older theorem is a real trilinear symbol coefficient, not a Fourier-series energy rate | Construct a conjugate-symmetric finite-energy Fourier field and derive its shell-flux identity from the exact PDE |
| F-028 | RED | Unbounded growth of one ordered phase-aware coefficient implies a nonzero full convolution output | At `893a138`, `phased_symmetrized_scaled_witness_cancels` proves that the exchanged ordering is `-s`, exactly canceling the original `s` term for every scale | The original witness falsifies termwise estimates only; it cannot drive a symmetrized cascade | Sum both input orderings before every sign, growth, or shell-transfer claim |
| F-029 | RED | Restoring both convolution orderings makes every admissible triad output vanish | At `a7867f6`, the distinct divergence-free polarizations `A=(0,1,1)`, `B=(1,0,0)`, `C=(1,-1,1)` give a normalized phase-aware symmetrized coefficient exactly equal to `s`; the six signed modes have conjugate coefficients | Symmetrization is a required gate, not a universal depletion mechanism | Test collective weighted rates and the complete generated Fourier support |
| F-030 | RED | Collective energy cancellation forbids transfer between unequal frequency shells | At `e954f59`, the three receiver rates are exactly `(0,-s,s)`: constant weights cancel, but squared-frequency weighting is `s^3>0` for `s>0` | Energy conservation permits exact redistribution from the unit shell to the `sqrt(2)` shell | Seek a summable collective weight or dynamical mechanism; termwise sign and constant-weight arguments are insufficient |
| F-031 | RED | The conjugate-symmetric six-mode witness is a quadratically invariant finite Fourier subsystem | At `93862c0`, an exhaustive classification of all 36 ordered pairs proves that exactly `(-k,l)` and `(l,-k)` reach `(-s,s,0)`, their complete projected coefficient is `s`, and the output lies outside all six modes for `s!=0` | The table is a real Fourier polynomial and shell-transfer probe, not a closed ODE or PDE solution | Enumerate the recursively generated convolution network and prove leakage control, cancellation, or an invariant enlargement |
| F-032 | RED | The receiver labeled `K` in the weighted-rate table should use the phase attached to the positive `K` mode | The output wave in that row is `-K`; adversarial phase audit at `34ee65f` corrected the Hermitian receiver phase from `-i` to `+i`. The exact rate remains zero after correction | Mode labels cannot substitute for output-wave signs when conjugate phases are selected | Derive every receiver phase from the signed output wave and retain a regression theorem for the corrected rate |
| F-033 | RED | One nonzero off-support ordered pair proves that the complete Fourier convolution leaks | Other ordered pairs at the same output could in principle cancel it. The exhaustive theorem at `93862c0` removes that loophole by classifying all 36 pairs and proving the full coefficient equals `s` | Pairwise nonvanishing is discovery evidence, not a field-level coefficient theorem | Sum every ordered pair producing the output before promoting a finite-field leakage claim |
| F-034 | RED | A finite raw integral of `‖u(t,x)‖^3` by itself certifies that a slice lies in `L^3` | Mathlib defines the integral of a nonintegrable function to be zero, so the old `CriticalL3BoundOn` can hold vacuously. At `83cca16`, `IntegrableCriticalL3BoundOn` repairs the contract by requiring nonnegative bound and slice integrability, and proves exact positive-scaling iff theorems | The old theorems remain valid only as raw-integral transport and cannot support an unconditional critical-norm claim | Use the repaired integrable contract, or a stronger `MemLp`/`snorm` interface, before any continuation argument |

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
