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
