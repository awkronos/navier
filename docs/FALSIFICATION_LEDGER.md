# Falsification ledger

Ledger initialized: **2026-07-14**
Research program baseline (initial contract commit):
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

Table columns map one-to-one onto the six entry-protocol fields below:
quantified claim, route · dependency node, date · revision · witness,
witness class, smallest repaired statement (Consequence + Permitted
successor), and successor links. Witness classes:

- **M** — the witness refutes the mathematics (a counterexample to the stated
  universal claim);
- **I** — the witness refutes an inference, attribution, or misreading of
  scope; the underlying mathematics stands in its own scope;
- **T** — the witness shows only that a model transfer is absent; neither
  model is refuted.

## Initial ledger

Dates and revisions: every entry in this table was opened at ledger init
(2026-07-14, baseline `81448ed`) unless its witness cell names a different
revision; the witness cell then also names the primary source or command
that checks the claim.

| ID | Status | Claim tested (exact quantified form) | Route · dependency node | Falsifier or audit witness (date · revision) | Witness refutes | Consequence | Permitted successor | Supersessions / links |
|---|---|---|---|---|---|---|---|---|
| F-001 | RED | The smooth energy identity alone controls a scale-critical norm | universal scaling barrier · P3; test T-001 | Under \(u_\lambda=\lambda u(\lambda x,\lambda^2t)\), energy scales as \(\lambda^{-1/2}\) while a critical norm scales as \(\lambda^0\) | M | No scale-uniform critical inequality can be obtained from energy size alone | Add a named exact-structure or geometric estimate and retest | Formal side REALIZED (`c411f27`): `Navier.EnergyObstruction.energy_not_scale_coercive` certifies the obstruction kernel-clean |
| F-002 | RED | Energy cancellation plus generic harmonic-analysis estimates suffice for global regularity — i.e. every argument that uses only properties of the bilinear form preserved under Tao-admissible averaging settles global regularity | positive-route gate · P8; tests T-003/T-007 | [TAO2016]: the averaged bilinear equation preserves those coarse properties and admits finite-time blowup | M | Any decisive positive estimate must distinguish the exact Navier–Stokes bilinear symbol | State the discriminator and show failure under Tao averaging | Gate restated in `BARRIERS.md` §3 and `ATTACK.md` §3 |
| F-003 | RED | A continuation criterion is itself an unconditional route payload — "if \(N(u)<\infty\) then continue" supplies the bound | R1 endpoint · P6 | Logical normalization: "if \(N(u)<\infty\), then continue" does not prove \(N(u)<\infty\) | I | Serrin/ESS remain bridge results, not R1 closure | Prove the norm from strictly lower hypotheses | — |
| F-004 | DECOMPOSED | Banach contraction gives arbitrary-large-data global existence | R2 fixed point · P4 | [KATO1984], [KOCH_TATARU2001]: these mechanisms obtain local large-data or global small-data control | I | FixedPointBanach may close local wiring only | Produce an interval-independent large-data gain not based on assumed smallness | — |
| F-005 | RED | CKN partial regularity proves that every suitable solution is smooth | R9 weak-to-smooth · P7 | [CKN1982]: CKN controls the parabolic size of the singular set; it does not show the set is empty | I | Partial regularity cannot inhabit FeffermanA | Add a quantitative all-cylinder exclusion theorem | — |
| F-006 | RED | Leray weak existence proves Fefferman alternative A | R4/R9 · P5 | [LERAY1934]: A requires globally smooth velocity and pressure; Leray supplies a finite-energy weak solution | I | Weak existence is a lower producer only | Prove weak-to-strong regularity for every admissible smooth datum | — |
| F-007 | RED | Weak nonuniqueness proves Fefferman C or D | R11 exact breakdown · P0 | [BUCKMASTER_VICOL2019], [ALBRITTON_BRUE_COLOMBO2022]: nonuniqueness is not nonexistence of every global smooth physically reasonable solution; the solution/force classes also require an exact audit | I | These papers mark a weak-category boundary, not a problem-statement breakdown witness | Construct an exact C/D datum and force and prove the stated nonexistence | Forced C/D later inhabited independently (`ConstructedBreakdown.wholeSpaceBreakdown`); the ledger entry still bars citing the nonuniqueness papers as the witness |
| F-008 | QUARANTINED | A periodic global theorem automatically proves the whole-space theorem | transfer · P0 (domain clauses) | [FEFFERMAN2000] states B and A as distinct alternatives with different domains | T | No B-to-A coercion is admitted | Supply a theorem transporting all data, pressure, decay, and energy properties | Partial successor landed 2026-09-16: `Navier.Transfer.LatticeExtensionTransport` (`OPEN_FRONTIER_MAP.md` lattice→whole-space row); declared residual `MildSelfMapTransport` |
| F-009 | RED | Polya EnergyMethod is a formal PDE energy theorem — i.e. the catalogue entry can be consumed as an energy estimate | infrastructure mislabel · P5 | Its live theorem concerns finite additive energy and small difference sets | I | Name similarity cannot supply P5 | Formalize a new kinetic/local-energy theorem with the correct integral domain | — |
| F-010 | RED | Polya DyadicDecomposition supplies Littlewood–Paley theory — i.e. the catalogue entry provides frequency projections and Besov estimates | infrastructure mislabel · P3/R5 | Its live theorem is dyadic pigeonholing for a finite set of natural numbers | I | It cannot build R5 frequency projections or Besov estimates | Add genuine Fourier projection/paraproduct infrastructure | — |
| F-011 | DECOMPOSED | Instantaneous analyticity alone prevents finite-time singularity | R8 analyticity · P6 | [FOIAS_TEMAM1989]: known Gevrey estimates are conditional/local and their radius bounds can depend on quantities that may diverge | I | Analyticity is a diagnostic unless its radius inequality closes noncircularly | Prove a positive radius bound from lower exact-structure control | — |
| F-012 | RED | A large finite numerical survey proves a universal regularity or blowup statement | R10 certified computation · evidence tier; test T-006 | Finite samples do not cover arbitrary smooth data or unresolved arbitrarily small scales | I | Numerical results remain observation-only | Give interval certificates, a compact finite-cover theorem, and an analytic tail bound | Successor target recorded in `NS5-SOLVER-FINDINGS.md` §6 (`interval_cert`/rustfftw route) |
| F-013 | RED | Weak convergence of approximate solutions passes the quadratic term automatically | R4 compactness/rigidity · P7; test T-004 | The product \(u_n\otimes u_n\) needs strong convergence or explicit defect control; weak convergence alone is insufficient | M | R4/R9 compactness must expose pressure and nonlinear defects | Prove strong local compactness or carry and eliminate a defect measure | Partial successor landed 2026-09-16 (`e655a44`, W7O-NV2): `Analysis.GalerkinEnergyBudget` budgets the Riesz–Kolmogorov/Aubin–Lions input; named residual is the `hprojectedWeak` commutator carry (`OPEN_FRONTIER_MAP.md` Galerkin modal compactness row) |
| F-014 | DECOMPOSED | A vorticity-direction criterion shows the direction condition is dynamically automatic | R3 vorticity geometry · P8; test T-002 | [CONSTANTIN_FEFFERMAN1993] supplies a conditional geometric criterion, not a derivation of its hypothesis for every datum | I | R3's first residual is the dynamical coherence estimate (still open at current source: `ATTACK.md` R3 marks automatic coherence **open-residual**) | Derive coherence on the high-vorticity set from the exact evolution | — |
| F-015 | RED | Fefferman C/D are defined as zero-force blowup statements | R11 target statement · P0; test T-007 | [FEFFERMAN2000]: the official C/D statements quantify an admissible smooth force and conclude absence of a global physically reasonable solution | I | Do not replace the official target by a narrower paraphrase | Treat zero-force breakdown as a stronger optional subroute; retain force in the exact target | — |
| F-016 | RED | The official wording of C/D specifically requires a finite-time blowup profile | R11 target statement · P0; test T-007 | [FEFFERMAN2000]: the official conclusion is nonexistence of a global solution satisfying the listed clauses; it does not prescribe a profile/mechanism | I | A local-theory equivalence is not assumed without proof | Prove any equivalence as a separate bridge, or use the exact nonexistence conclusion | — |
| F-017 | QUARANTINED | Blowup for Tao's averaged equation is blowup for Navier–Stokes | transfer · P8; test T-007 | [TAO2016]: the averaged bilinear operator is different from the exact Leray-projected nonlinearity | T | Averaged blowup is an obstruction to generic positive arguments only | Prove an exact-symbol embedding before any C/D use | — |
| F-018 | RED | A compiling endpoint wrapper establishes scientific closure when its payload is assumed or axiomatized | evidence discipline · all routes | Dependency/axiom inspection distinguishes a checked implication from realization of its premise | I | Wrapper progress is wiring and keeps frontier status unchanged | Supply the lower payload and rerun raw axiom/dependency audits | — |
| F-019 | QUARANTINED | A two-dimensional, axisymmetric, bounded-domain, hyperdissipative, or Euler theorem can be reported as A | transfer · P0; test T-007 | At least one load-bearing dimension/domain/dissipation/nonlinearity field differs | T | Model results remain benchmarks | Prove a field-by-field transfer theorem to the exact whole-space equation | Upstream unforced Euler breakdown `Euler.euler_breakdown_R3` (`OPENAI2026_EULER`) re-verified 2026-09-13: settles the Euler model only; `BARRIERS.md` §5 quarantine stands |
| F-020 | RED | Source grep, status prose, or a registry boolean is sufficient proof evidence | evidence discipline · all routes | Such text can be stale or disconnected from theorem dependencies; only native compiler/axiom output checks the formal artifact | I | Status cannot mint closure | Bind fresh native output to the exact revision and declaration | — |

### Notes

- F-001 formal side REALIZED (2026-07-14, `c411f27`):
  `Navier.EnergyObstruction.energy_not_scale_coercive` proves the obstruction
  kernel-clean — a rescaling whose `L²` energy is arbitrarily small while its
  scale-critical `L³` mass stays fixed and positive. The entry remains RED: it
  records that energy alone cannot control the critical quantity, which the
  theorem now certifies rather than refutes.

## Integration audit additions

| ID | Status | Claim tested (exact quantified form) | Route · dependency node | Falsifier or audit witness (date · revision) | Witness refutes | Consequence | Permitted successor | Supersessions / links |
|---|---|---|---|---|---|---|---|---|
| F-021 | RED | A periodic B/D contract may constrain velocity but omit pressure periodicity | B/D surfaces · P0; test T-007 | 2026-07-14 audit at formal-source revision `528ff6f4fa06d7ea4dcebbd308eaee2d5dfcb07f`; Fefferman's official erratum explicitly adds \(p(x+e_j,t)=p(x,t)\) | I | Any future B/D surface or validator must require periodicity of both fields | Add adversarial contract tests that reject a velocity-only periodic surface | `PeriodicClassicalUniqueness` consumes periodic velocity **and** periodic pressure (`RESULT_MAP.md`) |
| F-022 | RED | The datum-uniform restart engine `HorizonIndependentRestart N` (step `h = h(ν, M)` chosen before the datum) is a strictly weaker, classical continuation leaf of crown A for `N = bkmVorticityControl` or `N = preterminalEnergyControl`, the hard content residing in the a priori leaf | A consumer · `CriticalControlDecomposition` continuation leaf, `RestartPaste.HorizonIndependentRestart` | 2026-09-22 · branch `m/ns-0922` from `ed433e8` · `Analysis.ContinuationScaleSelfImprovement.normalizedContinuation_iff_arbitraryStep`: for every `ZoomMonotone N` the datum-uniform leaf is EQUIVALENT to continuation by every step length `L` (zoom in by `μ = L/δ + 1`, step `δ`, zoom out: extension by `μ²δ ≥ L`); `bkmVorticityControl_parabolicScaled` (exact zoom invariance) and `preterminalEnergyControl_parabolicScaled_le` (energy scales by `λ⁻¹`) instantiate it (`arbitraryStep_bkm_of_horizonIndependentRestart`, `arbitraryStep_energy_of_horizonIndependentRestart`); strict axioms | I | The two datum-uniform restart leaves each assert that every admissible solution with finite control extends to every longer horizon — not strictly weaker than the crown's continuation content (B9a(ii)); they cannot be discharged by a classical continuation criterion, whose restart length depends on a datum Sobolev budget | Datum-dependent order: `CriticalControlDecomposition.DatumContinuationFromCriticalControl` / `RestartPaste.DatumHorizonIndependentRestart` (step chosen after the datum; the zoom changes the datum, so the self-improvement does not apply), consumed by `wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori` and `ContinuationScaleSelfImprovement.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_datumRestart` | The old datum-uniform consumers remain as corollaries (`datumContinuation_of_normalizedContinuation`, `datumRestart_of_horizonIndependentRestart`) |
| F-023 | DECOMPOSED | The classical BKM continuation theorem [BKM1984] supplies `RestartPaste.DatumHorizonIndependentRestart bkmVorticityControl` on the full `SolvesBefore` class (joint smoothness, finite-energy slices, datum-level energy inequality) | A consumer · third input of `ContinuationScaleSelfImprovement.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_datumRestart` | 2026-09-22 · branch `f/ns-restart-0922` from `d9086f9` · scope audit: the classical theorem is stated on a class carrying a Sobolev budget and time continuity in it, and its restart agreement clause is Kato uniqueness in that class; `SolvesBefore` carries neither (a jointly smooth evolution with finite-energy slices need not be `L²`-continuous in time: a bump translated to infinity as `t ↓ 0`, extended by zero), so the full-class restart contains `Analysis.ClassRestartDecomposition.FullClassRestartUniqueness` (`restartUniquenessIn_trivial_iff`), a weak–strong uniqueness statement in the finite-energy smooth class that no cited theorem supplies | I | The inference "[BKM1984] ⟹ restart on `SolvesBefore`" has an unfilled uniqueness/budget gap; the leaf itself is not refuted (no smooth finite-energy non-unique solution is exhibited) | Class-threaded leaves: `Analysis.ClassRestartDecomposition.wholeSpaceGlobalRegularity_of_classBudgetRestart` consumes `LocalExistenceIn C`, `APrioriCriticalControlIn C bkmVorticityControl`, `BudgetLocalExistenceIn C B`, `BudgetPropagationIn C B bkmVorticityControl`, `RestartUniquenessIn C` for a `SolutionClass C` of the prover's choosing (intended `C([a,b); H^s)`, `B = ‖·‖_{H^s}`); pressure agreement on the open overlap is derived (`pressure_eq_of_velocity_eq_interior`); at `trivialClass` the threaded leaves are the existing ones (`localExistenceIn_trivial_iff`, `aPrioriCriticalControlIn_trivial_iff`, `datumContinuationIn_trivial_iff`); strict axioms | Refines F-022's datum-dependent order; the full-class endpoint remains as the `trivialClass` instance (`wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_viaClass`) |
| F-024 | RED | Schwartz class persists for smooth finite-energy whole-space Navier–Stokes solutions, so `BKMLogBootstrap.SchwartzSlicedSolution` ("slices are Schwartz fields") is the regularity frame of the `H³` energy method (its docstring: persistence "is standard") | carrier · brick (g) `H³` budget; class instantiation of `ClassRestartDecomposition` | 2026-09-22 · branch `f/ns-restart-0922` · primary sources: Dobrokhotov–Shafarevich 1994 (Math. Notes 55): if `u(t)` decays faster than `|x|^{-4}` then `∫ uᵢuⱼ dx = c(t) δᵢⱼ`; Brandolese 2004 (Math. Ann. 329, arXiv 2003-04-28): the `|x|^{-4}` rate is attained at positive times for generic data — Schwartz decay is lost instantly unless the momentum-flux matrix stays isotropic | M | The Schwartz-sliced class is generically empty at positive times, so `LocalExistenceIn (sliceClass (∃ s : SchwartzVelocity, ⇑s = ·))` is false for generic data; the repository `H³` carriers `sobolevH3NormSq`, `biotSavartLogInequality`, `exists_fderivSupBound_of_sobolevH3` are Schwartz-only static inequalities (valid as stated) and cannot instantiate the class leaves slice-wise | An `H³` budget on general smooth fields (`∑_{n<4} ∫ ‖Dⁿv‖²` with integrability in the class, time continuity in the class law) and the same inequalities re-carried there; `SchwartzSlicedSolution` retained only for the isotropic-momentum subclass | Blocks the `C = C([a,a+L); H^s)` instantiation of F-023 until the general-field carrier exists |
| F-025 | RED | The classical BKM continuation criterion [BKM1984] supplies a restart step uniform in the horizon (`∃ δ ∀ T`, the order of `DatumContinuationFromCriticalControl` / `RestartPaste.DatumHorizonIndependentRestart` / `ClassRestartDecomposition.DatumRestartIn`) | A consumer · continuation leaf quantifier order | 2026-09-22 · branch `f/ns-restart-0922` · the BKM Grönwall bound `‖u(t)‖_{H^s} ≤ ‖u₀‖ exp(C∫₀ᵗ(1 + ‖ω‖_{L²} + ‖ω‖_∞(1 + log⁺‖u‖_{H^s})))` has a constant growing with `t` through `1 + ‖ω‖_{L²}` even under `∫‖ω‖_∞ ≤ M`; the classical order is `∀ T̄ ∃ δ ∀ T ≤ T̄` | I | A horizon-uniform step is a non-classical strengthening of the continuation input; asking it of a prover asks more than BKM proves | `Analysis.ClassRestartLocallyUniform`: `LocallyUniformContinuationIn`, `LocallyUniformRestartIn`, `BudgetPropagationLocallyUniformIn` (`K = K(ν,u₀,M,T̄)`); the composition `wholeSpaceGlobalRegularity_of_localIn_locallyUniform_aprioriIn` uses one chain with steps `δ ⌈T⌉₊` (unbounded since a bounded chain has steps ≥ the minimum of finitely many positive `δ k`; chain assembly in `wholeSpaceGlobalRegularity_of_chain_aux`); horizon-uniform leaves imply the locally uniform ones; strict axioms | Refines F-022/F-023; endpoint `wholeSpaceGlobalRegularity_of_classBudgetRestart_locallyUniform` |

## Route test queue

These are not yet falsifications; they are the first adversarial probes to run
when a concrete inequality is proposed. A §6 row of `BARRIERS.md` with no F-id
here is a kill **class** that has not been executed, not a kill.

| Test ID | Route | Input family | Failure signal |
|---|---|---|---|
| T-001 | R1 | rescaled compactly supported divergence-free packets | a "uniform" constant changes with \(\lambda\) |
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
to a proposed sign estimate kills that estimate, not all exact-structure
approaches; it forces the next proposal to be narrower and to explain the
witness.

Re-runnable status-prose check over the docs (vocabulary sweep required by
`research-mathematics.md` §2): `python3 scripts/status_vocab_sweep.py` from the
repository root lists every residual/modulo/remains/ceiling/impossible hit with
its file and line; each hit must be checked against the elaborated signature or
current file state it names before being inherited or repeated.
