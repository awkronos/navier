# navier theorem ladder — 3D Navier–Stokes regularity (Fefferman A–D)

SELECT_TARGET picks the LOWEST open R1 rung; priority R1 > R2 > R3 > R4
(`orchestration.md` §Frontier-rung prioritization).

| # | rung | class | status | reference |
|---|---|---|---|---|
| 1 | Beale–Kato–Majda criterion: blowup at T ⟺ ∫₀ᵀ ‖ω(t)‖_∞ dt = ∞ | R1 | **ESTABLISHED** `Navier/Analysis/BealeKatoMajda.lean` (`0d43dae`) | BKM, CMP 94 (1984); Majda–Bertozzi §3.4 |
| 2 | Seeley extension leaf (named residual from `halfSpaceSmoothnessEquivalence`) | R1 | OPEN | Seeley 1964 |
| 3 | Multi-frequency mild layer extending the one-frequency Kato LWP (`c91c66e`, `c537f8d`) | R1 | OPEN | Kato 1984 |
| 4 | Leray weak existence via the guarded energy-integral layer | R1 | OPEN | Leray 1934; landed energy leaves |
| 5 | Prodi–Serrin / ESŠ conditional-regularity bridges | R3 | OPEN | ≤1 per headline |
| W | Full 3D regularity — StatementA–D dispositions flip only with kernel evidence | R2 wall | OPEN | R7 finite-Fourier dynamics = blowup-candidate laboratory |

## Rung 1 (BKM) — ESTABLISHED 2026-07-16 (`fable/clay-navier-20260716`)

`Navier/Analysis/BealeKatoMajda.lean` (`0d43dae`, `2c0ed42`, `35e5eb9`), all
`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, umbrella-wired,
`lake build` GREEN:

- `gronwall_log_apriori` — time-dependent (integral-form) Grönwall a-priori
  bound `Y' ≤ g·Y ⟹ Y t ≤ Y 0·exp(∫₀ᵗ g)`, rate `g` only `ContinuousOn [0,T]`
  so it may be `‖ω‖_∞`. Mathlib has ONLY constant-rate `gronwallBound`; this
  time-dependent form is the analytic engine of BKM and is the genuinely new
  content. Fully unconditional.
- `BKMControl` — the criterion in the velocity/vorticity framework with an
  EXPLICIT finite improper-integral hypothesis (rate `ContinuousOn` the
  half-open `[0,T)`, may blow up at `T`); `BKMControl.controlZero` proves
  non-vacuity. Step-0e checked against the already-global-layer trap.
- `BKMControl.velocity_bounded` — finite vorticity integral ⟹ uniform velocity
  bound on `[0,T)`.
- `BKMControl.excludes_pointEvaluationBreakdown` — consumes the repo's
  `PointEvaluationBreakdownWitness`: a finite vorticity integral is logically
  incompatible with the finite-time breakdown used to deny global existence.
- `BKMAnalyticResidual` — the two Mathlib-absent PDE inputs that BUILD a
  `BKMControl` from a solution (Biot–Savart/log-Sobolev inequality ~400 LOC;
  Sobolev embedding domination) named with references — declared, never assumed.

## R2 wall — numbered obstruction record

Maximal attempts on the R2 wall log a numbered obstruction here: exact
statement, Mathlib-verified absence, reference, est LOC. An obstruction
delimits an exhausted technique; the wall stays OPEN.

### W1 — Transversality-cancellation route is single-frequency (2026-07-16, `d1c290f`)

`Navier/Analysis/FrequencyCascadeObstruction.lean`, axiom-clean, GREEN.
The one-frequency global-regularity mechanism (`FrequencyMildGlobal`:
`nsOneFrequencySymbol` `TransverseAnnihilating` ⟹ nonlinearity vanishes) does
**not** extend to ≥2 frequencies: `crossInteraction_survives_transversality`
exhibits a concrete two-mode configuration (`q₁=e₀,q₂=e₁,v₁=e₁,v₂=e₀`), each
mode transverse to its own frequency, with nonzero cross-transport interaction
`e₀+e₁`. `crossInteraction_diagonal_{eq_two_symbol,transverse_eq_zero}` certify
this is the correct generalization (diagonal = 2× the one-frequency symbol,
vanishing when `v⟂q`). REDIRECT: a multi-frequency route must CONTROL cross-mode
transport (energy / BKM vorticity a-priori estimate — rung 1), never eliminate
it by exact cancellation. Does NOT falsify StatementA.

Next R2 routes not yet attempted (est LOC): Prodi–Serrin critical-norm bridge
(rung 5, R3, ~200 LOC over `Navier.Scaling` critical line + a critical-norm
control hypothesis); vorticity-direction Constantin–Fefferman geometric
regularity (`vorticityDirection` already in `Vorticity.lean`, ~300 LOC);
enstrophy energy inequality `d/dt‖ω‖₂² ≤ ‖∇u‖_∞‖ω‖₂²` (~250 LOC, feeds BKM).

## Sorry-first tower campaign (2026-07-16, `fable/clay-navier-20260716` cont.)

Full-proof skeleton towers laid per Tim's mission shift; umbrella `lake build
Navier` GREEN, 13 compiler-confirmed sorried obligations (opened 15, closed 2
same-wave). Tractability-ordered inventory (file : decl [ref; est LOC]):

| # | obligation | file | ref / route | est LOC |
|---|---|---|---|---|
| 1 | `isMultiMildSolutionOn_unique` ✅ ESTABLISHED (`c75263f`+`ed9080f`; axioms [propext, Classical.choice, Quot.sound] re-verified fresh) | MultiFrequencyMild | Grönwall/contraction as FrequencyDuhamel | ~150 |
| 2 | `vorticityTransportEquation` ✅ ESTABLISHED (`ce9edf5`+`fea63b8`; axioms [propext, Classical.choice, Quot.sound] fresh-printed) | Enstrophy | transport iff (`d35c359`) ∘ convection–curl identity (ConvectionCurl.lean: product rule + Clairaut + gradient-square cross identity under div u = 0) | — |
| 3 | `sobolevEmbeddingDomination` | BKMLogBootstrap | H³↪L∞ Fourier/Cauchy–Schwarz; M–B Lemma 3.2 | ~250 |
| 4 | `multiMild_extends_of_apriori_bound` | MultiFrequencyMild | finite-mode BKM, ODE continuation | ~300 |
| 5 | `sobolevControlContinuity` | BKMLogBootstrap | dominated convergence over slices; M–B §3.2.3 | ~300 |
| 6 | `enstrophyDifferentialInequality` | Enstrophy | diff-under-integral + parts; M–B §3.3. ⚠ Truth-check (2026-07-22): the ≤ mechanism is sound Kato-style (transport/viscous cutoff boundary terms are tail-enstrophy-controlled; the uncontrolled −2ν∫|∇ω|² has a sign), but the `HasDerivAt`-at-every-t claim under only per-slice ω∈L² is where M–B uses H^m machinery this statement lacks — closure route is the cutoff identity + interchange, or a Pattern-A hypothesis strengthening (local-uniform domination / ∇ω ∈ L²_loc). Pointwise integrand layer ESTABLISHED axiom-clean in EnstrophyPointwise.lean (`e856148`): ∂_v|w|²=2⟨w,∂_v w⟩, Bochner Δ|w|²=2⟨w,Δw⟩+2∑|∂ᵢw|², 2ν⟨w,Δw⟩≤νΔ|w|². | ~350 |
| 7 | `exists_isMultiMildSolutionOn_local` | MultiFrequencyMild | product Duhamel contraction; Kato 1984 | ~400 |
| 8 | `biotSavartLogInequality` | BKMLogBootstrap | Biot–Savart + CZ + log interp; BKM 1984 Lemma 1 | ~400 |
| 9 | `katoCommutatorEstimate` | BKMLogBootstrap | H³ energy commutator; Kato–Ponce 1988 | ~600 |
| 10 | `seeleyExtensionProperty_holds` | SeeleyExtension | reflection series; Seeley PAMS 15 (1964) | ~600 |
| 11 | `constantinFefferman_velocity_bounded` | ConditionalRegularity | geometric depletion; CF 1993 | ~600 |
| 12 | `prodiSerrin_velocity_bounded` | ConditionalRegularity | critical-norm bootstrap; Prodi/Serrin/ESŠ | ~800 |
| 13 | `leray_weak_existence` | LerayWeak | Galerkin + Aubin–Lions; Leray 1934, Temam Ch III | ~1500 |

PROVED this campaign (all `#print axioms ⊆ {propext, Classical.choice,
Quot.sound}`): `gronwall_loglinear_apriori` (log-transform bootstrap — the
verifier-flagged BKM mechanism) + `LogBKMControl` layer (velocity_bounded,
breakdown exclusion, non-vacuity); `stretching_pointwise_bound` +
`officialInner` CS layer + `enstrophy` defs; the honest Galerkin
`truncatedConvectionSymbol` + resonant-triple = crossInteraction identity +
`truncated_cascade_witness` + one-frequency heat-flow consistency;
`multiMild_inner_frequency_eq_zero` (transversality automatic — CLOSED,
strengthened, hypothesis dropped); Leray weak layer structure + zero smoke +
`exists_nonzero_testFunction` (CLOSED: curl-of-bump construction, Clairaut
div-free, line-constancy nonzero, smoothTransition envelope).

DERIVED conditional on skeletons (sorryAx disclosed):
`logBKMControl_of_schwartzSliced` (the tower composes end-to-end: solutions +
4 analytic inputs ⟹ LogBKMControl ⟹ uniform bound);
`enstrophy_apriori_bound` (Grönwall wiring, produces the M₂ majorant the BKM
wiring consumes); `halfSpaceSmooth_iff_extension`.

Assembly line once #3, #6, #8, #9 close: ∫‖ω‖_∞ < ∞ → biotSavart gradient
majorant → enstrophy M₂ → LogBKMControl → velocity bounded → no pointwise
breakdown. That is the full BKM theorem for this repo's classical solutions.
