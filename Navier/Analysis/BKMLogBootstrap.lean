import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.BKMLogLeaves
import Navier.Analysis.UniformDecayDominated
import Navier.Analysis.BiotSavartKernel
import Navier.Analysis.BiotSavartCore
import Navier.Analysis.BiotSavartIntegrationByParts
import Navier.Analysis.BiotSavartNearBounds
import Navier.Analysis.BiotSavartGradientRecovery
import Navier.Analysis.CZNearField
import Navier.Analysis.EnergyNormBridge
import Navier.Analysis.GronwallAffine
import Navier.Analysis.KatoPonceLeibniz
import Navier.Analysis.CurlDerivativeBridge
import Navier.Analysis.WeightedCommutator
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# BKM log bootstrap: from the Biot–Savart log inequality to the criterion

The Beale–Kato–Majda continuation theorem is proved (BKM, CMP 94 (1984);
Majda–Bertozzi §3.4) by applying Grönwall **to a log-transformed control**:
the Biot–Savart log inequality only bounds `‖∇u‖_∞` by
`‖ω‖_∞·(1 + log(e + ‖u‖_{H³}))`, so the `H³` energy estimate delivers the
*log-linear* differential inequality

  `Y' ≤ g · Y · (1 + log Y)`,   `Y(t) = 1 + ‖u(t)‖²_{H³}`,  `g ≈ C(1 + ‖ω‖_∞)`,

not the linear one.  Setting `W = 1 + log Y` reduces it to `W' ≤ g·W`, which is
exactly `gronwall_log_apriori`; unwinding gives the doubly-exponential bound
`Y t ≤ exp((1 + log Y 0)·exp(∫₀ᵗ g) − 1)`.

## Certified here (no sorry)

* `gronwall_loglinear_apriori` — the log-transform bootstrap, unconditional.
* `LogBKMControl` — the criterion package with the log-linear inequality
  (the shape Biot–Savart actually delivers), plus non-vacuity witness.
* `LogBKMControl.velocity_bounded`, `LogBKMControl.excludes_pointEvaluationBreakdown`
  — finite vorticity integral ⟹ uniform velocity bound ⟹ no pointwise blow-up.

* `sobolevH2NormSq_le_sobolevH3NormSq` — the `H³ ⊆ H²` norm inclusion.
* `integrable_inv_one_add_normSq_sq` — the Bessel weight `(1 + |ξ|²)⁻²` is
  integrable on `ℝ³` (decay exponent `4 > 3 = dim`); this is the *only*
  dimension-dependent input to `H²(ℝ³) ↪ L^∞`, and it is exactly what fails
  for `H¹`.
* `not_integrable_inv_one_add_normSq` — the matching **sharpness** certificate:
  the `H¹` weight `(1 + |ξ|²)⁻¹` is *not* integrable on `ℝ³`, so the `H²` order
  in `exists_agmonSupBound` is load-bearing, not decoration.
* `integral_le_besselWeightMass_mul_sqrt` — the weighted Cauchy–Schwarz step.
* `exists_besselFourierMajorant` — the Fourier majorant itself, certified via
  the Euclidean/complex model transport, `exists_weighted_plancherel` and
  `exists_euclModel_h2_bound`.
* `exists_agmonSupBound` — the Agmon/Sobolev embedding `H²(ℝ³) ↪ L^∞`, now
  **kernel-clean end to end** (`#print axioms` shows only `propext`,
  `Classical.choice`, `Quot.sound`).
* `integrableOn_bsKernelScalar_sq_farField` — the Biot–Savart kernel tail is
  square-integrable on `{1 ≤ ‖z‖}` (the far-field half of the Calderón–Zygmund
  size layer for `exists_biotSavartLogTextbook`), by comparison with the
  certified Bessel weight.
* `integral_bsKernelScalar_annulus_le_log` — **the logarithmic middle shell**:
  `∫_{ρ ≤ |z| < 1} 1/(4π|z|³) ≤ (2·vol(B₁)/π)·(1 + log(1/ρ)/log 2)`.  This is
  the layer that *produces* the logarithm in Beale–Kato–Majda: the annulus
  meets only `⌊log₂(1/ρ)⌋ + 1` unit-scale dyadic shells and each carries the
  same scale-invariant mass.  The integer-weight near-field bound
  `integral_norm_mul_bsKernelScalar_ball_le` and the far-field bound are also
  certified.  The actual Morrey weight has the exact sharp scaling
  `I(ρ) = ρ^(1/4) I(1)` by
  `integral_norm_rpow_oneFourth_mul_bsKernelScalar_ball_eq`, and
  `integral_norm_bsKernelScalar_smul_of_holder_le` packages the quantitative
  Hölder convolution estimate.  The representation `∇u = PV(∇K ∗ ω)`
  remains in `exists_biotSavartKernelSplitting`.
* the four analytic inputs below are **derived**, each from one named residual
  plus a certified leaf in `Navier/Analysis/BKMLogLeaves.lean`.

## Named residuals (honest `sorry`, truth-checked signatures)

The three named PDE inputs (`BKMAnalyticResidual` in `BealeKatoMajda.lean`) are
no longer opaque `sorry`s.  Each is now derived from a *strictly lower* named
residual carrying its own reference, LOC estimate and dependency list, and the
bookkeeping between the two is certified in `BKMLogLeaves`:

| consumer | named residual | certified leaf |
|---|---|---|
| `biotSavartLogInequality` | `exists_biotSavartLogTextbook` (textbook `log(e+‖u‖_{H³})` shape) | `bkm_log_shape_transfer` |
| `sobolevEmbeddingDomination` | `exists_besselFourierMajorant` — **now CERTIFIED** (Fourier inversion + Plancherel symbol bookkeeping) | `integrable_inv_one_add_normSq_sq` + `integral_le_besselWeightMass_mul_sqrt` + `le_mul_sqrt_of_le_majorant` |
| `sobolevControlContinuity` | `sliceSeminorm_locallyBounded` (locally uniform propagation of the Schwartz seminorms `‖·‖_{0,n}`, `‖·‖_{2,n}`, `n < 4`; Majda–Bertozzi §3.2.3) — `exists_sliceLocallyUniformDecayBound` is now **derived** from it, and the two are **equivalent** | `schwartz_iteratedFDeriv_sq_decay_seminorm` + `schwartz_seminorm_le_of_sq_decay` + `sliceSeminormLocallyBounded_of_locallyUniformDecay` + `continuousOn_sum_range` + `sliceIteratedFDeriv_continuousOn` |
| `katoCommutatorEstimate` | `exists_sobolevOrderEnergyEstimate` (one derivative order) | `exists_hasDerivAt_sum_range_le` |

Majorants stay hypothesis-carried (Step-0e: avoids `⨆`-junk vacuity; each
statement is monotone in its majorant, so the hypothesis-carried form follows
from the classical one — for the two `√`/`log` majorants that monotonicity is
now *proved*, not asserted, in `BKMLogLeaves`).

`logBKMControl_of_schwartzSliced` then **derives** a `LogBKMControl` from the
skeletons — the composition type-checks end-to-end, so once the three analytic
sorries close, the criterion is fully built from solutions.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped LineDeriv Matrix

namespace Navier.Analysis.BealeKatoMajda

open Navier
open Navier.Analysis.BKMLogLeaves
open Navier.Analysis.UniformDecayDominated
open Navier.Analysis.Vorticity
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.CZNearField
open Navier.Analysis.EnergyNormBridge
open Navier.Analysis.OfficialABEncoding
open Navier.Breakdown

/-!
## The log-transform Grönwall bootstrap (unconditional)
-/

/-- **Log-linear Grönwall bootstrap.**  If `Y ≥ 1` satisfies
`Y' ≤ g·Y·(1 + log Y)` — the inequality shape the Biot–Savart log estimate
delivers — then `Y t ≤ exp((1 + log (Y 0))·exp(∫₀ᵗ g) − 1)`.

Proof: `W = 1 + log Y` satisfies `W' = Y'/Y ≤ g·W`, and `gronwall_log_apriori`
bounds `W`; exponentiating back gives the doubly-exponential bound.  This is
the exact mechanism of Beale–Kato–Majda's proof. -/
theorem gronwall_loglinear_apriori
    {Y Y' g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hgc : ContinuousOn g (Set.Icc 0 T))
    (hYc : ContinuousOn Y (Set.Icc 0 T))
    (hYderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hY1 : ∀ t ∈ Set.Icc 0 T, 1 ≤ Y t)
    (hbound : ∀ t ∈ Set.Ioo 0 T, Y' t ≤ g t * (Y t * (1 + Real.log (Y t)))) :
    ∀ t ∈ Set.Icc 0 T,
      Y t ≤ Real.exp ((1 + Real.log (Y 0)) *
        Real.exp (∫ s in (0:ℝ)..t, g s) - 1) := by
  have hYpos : ∀ t ∈ Set.Icc 0 T, 0 < Y t :=
    fun t ht => lt_of_lt_of_le one_pos (hY1 t ht)
  have hlognn : ∀ t ∈ Set.Icc 0 T, 0 ≤ Real.log (Y t) :=
    fun t ht => Real.log_nonneg (hY1 t ht)
  set W : ℝ → ℝ := fun t => 1 + Real.log (Y t) with hWdef
  have hWc : ContinuousOn W (Set.Icc 0 T) := by
    apply continuousOn_const.add
    apply Real.continuousOn_log.comp hYc
    intro t ht; exact ne_of_gt (hYpos t ht)
  have hWderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt W (Y' t / Y t) t := by
    intro t ht
    have := ((hYderiv t ht).log
      (ne_of_gt (hYpos t ⟨le_of_lt ht.1, le_of_lt ht.2⟩))).const_add 1
    simpa [hWdef] using this
  have hWpos : ∀ t ∈ Set.Icc 0 T, 0 < W t := by
    intro t ht
    have := hlognn t ht
    simp only [hWdef]; linarith
  have hWbound : ∀ t ∈ Set.Ioo 0 T, Y' t / Y t ≤ g t * W t := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [div_le_iff₀ (hYpos t htIcc)]
    calc Y' t ≤ g t * (Y t * (1 + Real.log (Y t))) := hbound t ht
      _ = g t * W t * Y t := by simp only [hWdef]; ring
  have hcore := gronwall_log_apriori hT hgc hWc hWderiv hWpos hWbound
  intro t ht
  have hWt := hcore t ht
  have hW0 : W 0 = 1 + Real.log (Y 0) := rfl
  have hlogYt : Real.log (Y t) ≤
      (1 + Real.log (Y 0)) * Real.exp (∫ s in (0:ℝ)..t, g s) - 1 := by
    have : W t = 1 + Real.log (Y t) := rfl
    rw [hW0] at hWt
    linarith [hWt]
  calc Y t = Real.exp (Real.log (Y t)) := (Real.exp_log (hYpos t ht)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlogYt

/-!
## The log-linear criterion package
-/

/-- A **log-linear Beale–Kato–Majda control**: like `BKMControl`, but with the
log-linear differential inequality `Y' ≤ rate·Y·(1 + log Y)` — the inequality
the Biot–Savart log estimate actually delivers (the linear `Y' ≤ rate·Y` is
NOT available for Navier–Stokes; only the log-degraded form is).  The finite
improper vorticity-rate integral remains the criterion's hypothesis. -/
structure LogBKMControl (u : VelocityEvolution) (T : ℝ) where
  /-- The regularity control `Y(t) ≥ 1` (think `1 + ‖u(t)‖²_{H³}`). -/
  control : ℝ → ℝ
  /-- Its pointwise derivative on `(0,T)`. -/
  controlDeriv : ℝ → ℝ
  /-- A time-integrable majorant of `C(1 + ‖ω(t)‖_∞)`-type quantities. -/
  rate : ℝ → ℝ
  rate_continuousOn : ContinuousOn rate (Set.Ico 0 T)
  control_continuousOn : ContinuousOn control (Set.Ico 0 T)
  control_hasDerivAt : ∀ t ∈ Set.Ioo 0 T, HasDerivAt control (controlDeriv t) t
  control_ge_one : ∀ t ∈ Set.Ico 0 T, 1 ≤ control t
  /-- The log-linear BKM differential inequality. -/
  loglinear_inequality : ∀ t ∈ Set.Ioo 0 T,
    controlDeriv t ≤ rate t * (control t * (1 + Real.log (control t)))
  /-- **(H-diff), Pattern-A.**  Each spatial slice is genuinely differentiable.
  Without it `vorticity u t x = staticCurl (u t) x` is the `fderiv` **junk value**
  `0` wherever `u t` fails to be differentiable, and `rate_dominates_vorticity`
  below is satisfied at `rate ≡ 0` by fields that are not even continuous:
  `VacuityAudit.preRepairBKMFields_vacuous_of_ballStep` exhibits the indicator of
  the unit ball in direction `e₀` doing exactly that, and
  `VacuityAudit.ballStep_not_differentiable` certifies that this field is the one
  excluded here.  `VelocityEvolution` carries no regularity of its own, so this
  field is the only thing standing between the criterion and that junk. -/
  velocity_differentiable :
    ∀ t ∈ Set.Ico 0 T, ∀ x : Space, DifferentiableAt ℝ (u t) x
  /-- **(H-div), Pattern-A.**  Incompressibility.  Differentiability alone does
  not repair the criterion: by Clairaut every smooth gradient field `∇φ` has
  `staticCurl (∇φ) ≡ 0`, so it too satisfies `rate_dominates_vorticity` at
  `rate ≡ 0` while having divergence `Δφ ≠ 0` — it is not a Navier–Stokes
  velocity at all.  Witness:
  `VacuityAudit.preRepairBKMFields_vacuous_of_curlFree`.  With both fields
  present the bounded inhabitants with `rate ≡ 0` are, by Liouville, the
  constants. -/
  incompressible :
    ∀ t ∈ Set.Ico 0 T, ∀ x : Space, staticDivergence (u t) x = 0
  /-- `rate t` dominates the vorticity supremum at time `t`. -/
  rate_dominates_vorticity :
    ∀ t ∈ Set.Ico 0 T, ∀ x : Space,
      officialEuclideanNorm (vorticity u t x) ≤ rate t
  /-- The regularity control dominates the velocity pointwise. -/
  control_dominates_velocity :
    ∀ t ∈ Set.Ico 0 T, ∀ x : Space, ‖u t x‖ ≤ control t
  /-- **The criterion's hypothesis**: the improper rate integral converges. -/
  finite_vorticity_integral :
    ∃ B : ℝ, ∀ t ∈ Set.Ico 0 T, (∫ s in (0:ℝ)..t, rate s) ≤ B

namespace LogBKMControl

variable {u : VelocityEvolution} {T : ℝ}

/-- **BKM continuation, log-linear form: finite vorticity integral ⟹ the
velocity stays uniformly bounded on `[0,T)`** (doubly-exponential bound). -/
theorem velocity_bounded (c : LogBKMControl u T) (hT : 0 < T) :
    ∃ M : ℝ, ∀ t ∈ Set.Ico 0 T, ∀ x : Space, ‖u t x‖ ≤ M := by
  obtain ⟨B, hB⟩ := c.finite_vorticity_integral
  refine ⟨Real.exp ((1 + Real.log (c.control 0)) * Real.exp B - 1), ?_⟩
  have h0mem : (0:ℝ) ∈ Set.Ico 0 T := ⟨le_rfl, hT⟩
  have hc0 : 1 ≤ c.control 0 := c.control_ge_one 0 h0mem
  intro t ht x
  have hIcc_sub : Set.Icc 0 t ⊆ Set.Ico 0 T := by
    intro s hs; exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  have hIoo_sub : Set.Ioo 0 t ⊆ Set.Ioo 0 T := by
    intro s hs; exact ⟨hs.1, lt_trans hs.2 ht.2⟩
  have hcore := gronwall_loglinear_apriori (Y := c.control)
    (Y' := c.controlDeriv) (g := c.rate) (T := t) ht.1
    (c.rate_continuousOn.mono hIcc_sub)
    (c.control_continuousOn.mono hIcc_sub)
    (fun s hs => c.control_hasDerivAt s (hIoo_sub hs))
    (fun s hs => c.control_ge_one s (hIcc_sub hs))
    (fun s hs => c.loglinear_inequality s (hIoo_sub hs))
    t ⟨ht.1, le_rfl⟩
  -- monotone: ∫₀ᵗ rate ≤ B and 1 + log(control 0) ≥ 1 > 0
  have hcoef : 0 ≤ 1 + Real.log (c.control 0) := by
    have := Real.log_nonneg hc0; linarith
  have hexp : Real.exp (∫ s in (0:ℝ)..t, c.rate s) ≤ Real.exp B :=
    Real.exp_le_exp.mpr (hB t ht)
  have hmono : (1 + Real.log (c.control 0)) *
      Real.exp (∫ s in (0:ℝ)..t, c.rate s) - 1 ≤
      (1 + Real.log (c.control 0)) * Real.exp B - 1 := by
    have := mul_le_mul_of_nonneg_left hexp hcoef
    linarith
  calc ‖u t x‖ ≤ c.control t := c.control_dominates_velocity t ht x
    _ ≤ Real.exp ((1 + Real.log (c.control 0)) *
        Real.exp (∫ s in (0:ℝ)..t, c.rate s) - 1) := hcore
    _ ≤ Real.exp ((1 + Real.log (c.control 0)) * Real.exp B - 1) :=
        Real.exp_le_exp.mpr hmono

/-- A log-linear control excludes the repository's pointwise finite-time
breakdown witness — same consumption as `BKMControl`, at the weaker (true for
Navier–Stokes) log-linear inequality. -/
theorem excludes_pointEvaluationBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField}
    {GlobalSolution : VelocityEvolution → PressureEvolution → Prop}
    (w : PointEvaluationBreakdownWitness ν f u₀ T GlobalSolution)
    (c : LogBKMControl w.localSolution.velocity T) : False := by
  have hT : 0 < T := w.localSolution.terminalTime_pos
  obtain ⟨M, hM⟩ := c.velocity_bounded hT
  obtain ⟨t, ht0, htT, hlarge⟩ := w.point_norm_unbounded M
  exact (not_lt_of_ge (hM t ⟨ht0, htT⟩ w.point)) hlarge

/-- Step-0e non-vacuity: the zero velocity carries a `LogBKMControl` on every
horizon (control `≡ 1`, rate `≡ 0`; `log 1 = 0`). -/
def controlZero (T : ℝ) : LogBKMControl (fun _ _ => 0) T where
  control := fun _ => 1
  controlDeriv := fun _ => 0
  rate := fun _ => 0
  rate_continuousOn := continuousOn_const
  control_continuousOn := continuousOn_const
  control_hasDerivAt := fun t _ => hasDerivAt_const t 1
  control_ge_one := fun t _ => le_rfl
  loglinear_inequality := fun t _ => by norm_num
  velocity_differentiable := fun _ _ _ => differentiableAt_const _
  incompressible := fun _ _ _ => by simp [staticDivergence]
  rate_dominates_vorticity := fun t _ x => by
    have hv : vorticity (fun _ _ => 0) t x = 0 := by
      simp [vorticity, staticCurl]
    rw [hv, (officialEuclideanNorm_eq_zero_iff 0).mpr rfl]
  control_dominates_velocity := fun t _ x => by norm_num
  finite_vorticity_integral := ⟨0, fun t _ => by simp⟩

end LogBKMControl

/-!
## Skeletons: the analytic inputs over Schwartz fields

Reference statements with honest `sorry` bodies.  Majorants are
hypothesis-carried (each classical statement is monotone in the corresponding
norm, so these forms follow from the textbook ones and avoid `⨆`-junk
vacuity).  Norm convention: `‖·‖` on `Space → Space` values is Mathlib's Pi
(sup) norm; all `ℝ³` norms are equivalent, constants are absorbed into `C`
(the official-norm comparison was tracked as the
`currentSpaceNormEuclideanNormEquivalence` encoding residual, since retired in
`Problem.lean`; the transports live in `Analysis.EnergyNormBridge` and
`Analysis.ForceNormBridge`).
-/

/-- The squared inhomogeneous `H³(ℝ³)` Sobolev norm of a Schwartz velocity
field: `∑_{n ≤ 3} ‖D^n u‖²_{L²}`.  Schwartz decay makes every summand a
genuine (finite) integral. -/
def sobolevH3NormSq (u : SchwartzVelocity) : ℝ :=
  ∑ n ∈ Finset.range 4, ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2

/-- The squared `H³` norm is nonnegative (each summand is an integral of a
square). -/
theorem sobolevH3NormSq_nonneg (u : SchwartzVelocity) :
    0 ≤ sobolevH3NormSq u := by
  apply Finset.sum_nonneg
  intro n _
  exact integral_nonneg (fun x => by positivity)

/-- The squared inhomogeneous `H²(ℝ³)` Sobolev norm of a Schwartz velocity
field: `∑_{n ≤ 2} ‖D^n u‖²_{L²}`.  `H²` is already *strictly* above the
critical order `3/2` in three dimensions, so it is the sharp order at which the
sup-norm embedding used by the BKM assembly holds. -/
def sobolevH2NormSq (u : SchwartzVelocity) : ℝ :=
  ∑ n ∈ Finset.range 3, ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2

/-- **`H³ ⊆ H²` at the level of norms (certified, no sorry).**  The `H²` sum runs
over `Finset.range 3 ⊆ Finset.range 4` and the omitted `n = 3` summand is an
integral of a square, hence nonnegative. -/
theorem sobolevH2NormSq_le_sobolevH3NormSq (u : SchwartzVelocity) :
    sobolevH2NormSq u ≤ sobolevH3NormSq u := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr (by omega))) ?_
  intro n _ _
  exact integral_nonneg (fun x => by positivity)

/-- **Per-order domination by the `H³` norm (certified, no sorry).**  For each
derivative order `n < 4`, the order-`n` energy `∫ ‖Dⁿu‖²` is one summand of
`sobolevH3NormSq u`, and the omitted summands are integrals of squares.  This
is the step that converts a Kato–Ponce commutator bound stated against
`‖Dⁿu‖_{L²}` into the `‖u‖²_{H³}` shape that
`exists_sobolevOrderEnergyEstimate` and the Grönwall consumer use. -/
theorem sobolevOrderNormSq_le_sobolevH3NormSq (u : SchwartzVelocity) {n : ℕ}
    (hn : n < 4) :
    (∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2) ≤ sobolevH3NormSq u :=
  Finset.single_le_sum
    (f := fun m => ∫ x : Space, ‖iteratedFDeriv ℝ m (⇑u) x‖ ^ 2)
    (fun m _ => integral_nonneg (fun x => by positivity))
    (Finset.mem_range.mpr hn)

/-- **The Calderón–Zygmund cutoff optimisation (certified, no sorry).**  This is
the step that *manufactures the logarithm* in the Beale–Kato–Majda inequality,
isolated as a statement of pure real analysis.

Suppose a quantity `Y` admits, at **every** cutoff scale `ρ ∈ (0, 1]`, the
three-term Calderón–Zygmund split

  `Y ≤ A · ρ^{1/4} · M + B · Mω · (1 + log(1/ρ)) + F`

— near field `O(ρ^{1/4}·M)` (the Hölder-`1/4` cancellation weight supplied by
`exists_agmonMorreyBound`, with `M = ‖u‖_{H³}`), logarithmic shell
`O(Mω·(1 + log(1/ρ)))` (supplied by `integral_bsKernelScalar_annulus_le_log`),
and a `ρ`-independent far-field term `F` (supplied by
`integrableOn_bsKernelScalar_sq_farField` paired with `‖ω‖_{L²}` by
Cauchy–Schwarz).  Then `Y` obeys the *`ρ`-free* logarithmic bound

  `Y ≤ A + 4·B·Mω·(1 + log(e + M)) + F`.

**The optimising scale.**  Take `ρ := (e + M)^{-4}`, which lies in `(0, e^{-4}]`
for every `M ≥ 0`, so it is an admissible cutoff *without any smallness or
largeness hypothesis on `M`* — this is exactly why the `e +` guard is written
into the conclusion rather than a bare `log M`.  At that scale
`ρ^{1/4} = (e + M)^{-1}`, so the near-field term collapses to
`A · M / (e + M) ≤ A`, while `log(1/ρ) = 4 log(e + M)` turns the shell term
into `B·Mω·(1 + 4 log(e + M)) ≤ 4·B·Mω·(1 + log(e + M))`, the last step using
`log(e + M) ≥ 1 > 0`.

**Endpoint check.**  `e + M ≥ e > 1` for `M ≥ 0`, hence `log(e + M) ≥ 1`, so
every term of the conclusion is nonnegative and the bound is never vacuously
unsatisfiable — contrast a bare `log log`-type majorant, which goes negative at
its own left endpoint. -/
theorem le_of_forall_cutoff_le
    {Y A B F Mω M : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hMω : 0 ≤ Mω) (hM : 0 ≤ M)
    (h : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      Y ≤ A * ρ ^ ((1 : ℝ) / 4) * M + B * Mω * (1 + Real.log (1 / ρ)) + F) :
    Y ≤ A + 4 * B * Mω * (1 + Real.log (Real.exp 1 + M)) + F := by
  set L : ℝ := Real.exp 1 + M with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  set ρ : ℝ := L ^ (-(4 : ℝ)) with hρdef
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hL0 _
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
  have hpow : ρ ^ ((1 : ℝ) / 4) = L⁻¹ := by
    rw [hρdef, ← Real.rpow_mul hL0.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hlogρ : Real.log (1 / ρ) = 4 * Real.log L := by
    rw [one_div, Real.log_inv, hρdef, Real.log_rpow hL0]; ring
  have hkey := h ρ hρ0 hρ1
  rw [hpow, hlogρ] at hkey
  have h1 : A * L⁻¹ * M ≤ A := by
    rw [mul_comm A L⁻¹, mul_assoc, inv_mul_le_iff₀ hL0]
    have hML : M ≤ L := by rw [hLdef]; nlinarith [Real.exp_pos (1 : ℝ)]
    nlinarith
  have h2 : B * Mω * (1 + 4 * Real.log L) ≤ 4 * B * Mω * (1 + Real.log L) := by
    nlinarith [mul_nonneg hB hMω]
  linarith

/-!
### Schwartz vorticity and the exact representation residual

The near-field Morrey estimate applies to Schwartz maps.  The first two
declarations construct the curl inside Schwartz space and prove, rather than
assume, the derivative-loss estimate `H²(curl u) ≤ C H³(u)`.  The final
declaration isolates the one remaining analytic primitive: the physical-space
principal-value Biot--Savart representation, including its local term and the
finite tensor reduction to the certified radial kernel estimates below.
-/

private theorem integrable_normSq_iteratedFDeriv_early
    (u : SchwartzVelocity) (n : ℕ) :
    Integrable (fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2) := by
  have hM : ∀ x, ‖iteratedFDeriv ℝ n (⇑u) x‖ ≤
      (SchwartzMap.seminorm ℝ 0 n) u :=
    fun x => u.norm_iteratedFDeriv_le_seminorm ℝ n x
  have hcont : Continuous
      (fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2) :=
    ((ContDiff.continuous_iteratedFDeriv (m := n) (hf := u.smooth ⊤)
      (by exact_mod_cast le_top)).norm).pow 2
  refine ((SchwartzMap.integrable_pow_mul_iteratedFDeriv volume u 0 n).const_mul
    ((SchwartzMap.seminorm ℝ 0 n) u)).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 =
      ‖iteratedFDeriv ℝ n (⇑u) x‖ *
        ‖iteratedFDeriv ℝ n (⇑u) x‖ := by ring
  rw [hs]
  calc
    ‖iteratedFDeriv ℝ n (⇑u) x‖ *
          ‖iteratedFDeriv ℝ n (⇑u) x‖
        ≤ (SchwartzMap.seminorm ℝ 0 n) u *
            (‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑u) x‖) := by
          simp only [pow_zero, one_mul]
          exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    _ = _ := rfl

/-- The Schwartz curl loses exactly one derivative in `L²`, uniformly through
orders `0,1,2`; this is the quantitative input needed by Morrey--Agmon. -/
theorem exists_staticCurlSchwartz_h2_le_h3 :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SchwartzVelocity,
      sobolevH2NormSq (staticCurlSchwartz u) ≤ C * sobolevH3NormSq u := by
  obtain ⟨K, hKpos, hK⟩ :=
    Navier.Analysis.CurlDerivativeBridge.exists_norm_iteratedFDeriv_staticCurl_le
  refine ⟨3 * K ^ 2, by positivity, fun u => ?_⟩
  have horder : ∀ n : ℕ, n < 3 →
      (∫ x : Space,
        ‖iteratedFDeriv ℝ n (⇑(staticCurlSchwartz u)) x‖ ^ 2) ≤
          K ^ 2 * sobolevH3NormSq u := by
    intro n hn
    have hpoint : ∀ x : Space,
        ‖iteratedFDeriv ℝ n (⇑(staticCurlSchwartz u)) x‖ ^ 2 ≤
          K ^ 2 * ‖iteratedFDeriv ℝ (n + 1) (⇑u) x‖ ^ 2 := by
      intro x
      have hc := hK n (⇑u) (u.smooth (n + 1)) x
      have hfun : (⇑(staticCurlSchwartz u) : Space → Space) =
          staticCurl (⇑u) := by
        funext y
        exact staticCurlSchwartz_apply u y
      rw [hfun]
      nlinarith [norm_nonneg (iteratedFDeriv ℝ n (staticCurl (⇑u)) x),
        norm_nonneg (iteratedFDeriv ℝ (n + 1) (⇑u) x)]
    have hint : Integrable (fun x : Space =>
        K ^ 2 * ‖iteratedFDeriv ℝ (n + 1) (⇑u) x‖ ^ 2) :=
      (integrable_normSq_iteratedFDeriv_early u (n + 1)).const_mul _
    calc
      (∫ x : Space,
          ‖iteratedFDeriv ℝ n (⇑(staticCurlSchwartz u)) x‖ ^ 2)
          ≤ ∫ x : Space,
              K ^ 2 * ‖iteratedFDeriv ℝ (n + 1) (⇑u) x‖ ^ 2 :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => by positivity) hint
          (Filter.Eventually.of_forall hpoint)
      _ = K ^ 2 *
          (∫ x : Space, ‖iteratedFDeriv ℝ (n + 1) (⇑u) x‖ ^ 2) :=
        integral_const_mul _ _
      _ ≤ K ^ 2 * sobolevH3NormSq u := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg K)
        exact sobolevOrderNormSq_le_sobolevH3NormSq u (by omega)
  rw [sobolevH2NormSq]
  calc
    (∑ n ∈ Finset.range 3,
        ∫ x : Space,
          ‖iteratedFDeriv ℝ n (⇑(staticCurlSchwartz u)) x‖ ^ 2)
        ≤ ∑ _n ∈ Finset.range 3, K ^ 2 * sobolevH3NormSq u :=
      Finset.sum_le_sum fun n hn => horder n (Finset.mem_range.mp hn)
    _ = 3 * K ^ 2 * sobolevH3NormSq u := by simp; ring


/-- **[NAMED RESIDUAL -- exact physical-space Biot--Savart representation.]**
For a supplied `H²` upper bound on the Schwartz vorticity, the principal-value
formula for `∇u` splits into its locally integrable Morrey-cancellation term,
logarithmic annulus, local distributional term, and square-integrable far
field.

This is strictly below the BKM statement: its Sobolev quantity belongs to the
vorticity itself, before the proved curl derivative-loss bridge below converts
it to `H³(u)`, and no cutoff optimization occurs.  The off-origin connection
between the actual vector kernel derivative and `bsGradKernel` is certified by
`bsVectorKernel_coordinateLine_hasDerivAt_gradKernel`; the radial estimates
are the certified near/shell/far theorems below.  The finite punctured
integration-by-parts step is
`integral_bsGradKernel_testFactor_ibp_away`.  What remains here is the
puncture-closing limit with its origin local term, its application to the
velocity, and finite tensor norm bookkeeping. -/
theorem exists_biotSavartKernelSplit_of_curlH2 :
    ∃ A B F : ℝ, 0 < A ∧ 0 < B ∧ 0 < F ∧
      ∀ (u : SchwartzVelocity), DivergenceFreeInitial u →
        ∀ H₂ Mω M₂ : ℝ,
          sobolevH2NormSq (staticCurlSchwartz u) ≤ H₂ →
          (∀ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ≤ Mω) →
          (∫ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ^ 2) ≤ M₂ →
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
          ∀ x : Space,
            ‖fderiv ℝ (⇑u) x‖ ≤
              A * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂
                + B * Mω * (1 + Real.log (1 / ρ))
                + F * Real.sqrt M₂ := by
  have kernelDerivativeCertificate :
      ∀ (z : Space), z ≠ 0 → ∀ i j : Fin 3,
        HasDerivAt (fun t : ℝ => bsVectorKernel (z + t • basisVector i) j)
          ((1 / (4 * Real.pi)) * bsGradKernel i j z) 0 :=
    fun z hz i j => bsVectorKernel_coordinateLine_hasDerivAt_gradKernel hz i j
  have localTermNormalization :
      (∑ i : Fin 3, bsKernelDistributionLocalTerm i i) = 1 :=
    bsKernelDistributionLocalTerm_trace
  sorry

/-- **[DERIVED from `exists_biotSavartKernelSplit_of_curlH2`.]**
Biot–Savart representation + Calderón–Zygmund three-term split; BKM 1984
Lemma 1; Majda–Bertozzi Prop. 3.8; Stein,
*Singular Integrals* (1970) Ch. II §4; est ~350 LOC.]**  For a divergence-free
Schwartz field and **every** cutoff scale `ρ ∈ (0, 1]`, the velocity gradient
splits as

  `‖∇u(x)‖ ≤ A·ρ^{1/4}·‖u‖_{H³} + B·‖ω‖_∞·(1 + log(1/ρ)) + F·‖ω‖_{L²}`.

This is `exists_biotSavartLogTextbook` with the *cutoff still free*: it is a
strictly lower residual, because the passage from this `ρ`-indexed family to
the `ρ`-free logarithmic shape is now certified as `le_of_forall_cutoff_le`
above, and `exists_biotSavartLogTextbook` is derived from it below.

**What the lower residual still carries.**  The Biot–Savart representation
`∇u = PV(∇K ∗ ω)` with its local term, for divergence-free Schwartz fields —
genuinely Mathlib-absent — and the tensor/operator-norm reduction from that
representation to the three certified scalar kernel regions.  **The
curl-component bridge is no
longer part of it**: `CurlDerivativeBridge.exists_norm_iteratedFDeriv_staticCurl_le`
certifies `‖Dⁿ(staticCurl u)(x)‖ ≤ C‖D^{n+1}u(x)‖` at *every* order `n` with a
single constant (and `officialEuclideanNorm_staticCurl_le` gives the order-`0`
case in the Euclidean point norm the majorant `Mω` uses), which is exactly the
bookkeeping that feeds the vorticity into `exists_agmonMorreyBound`.

**What it no longer carries.**  The integer-weight near-field estimate is
certified at the bottom of this file:
`integral_norm_mul_bsKernelScalar_ball_le` (`O(ρ)` against the cancellation
weight `‖z‖`); the exact fractional scaling and its quantitative Hölder
convolution consumer are
`integral_norm_rpow_oneFourth_mul_bsKernelScalar_ball_eq` and
`integral_norm_bsKernelScalar_smul_of_holder_le`.  The logarithmic shell
`integral_bsKernelScalar_annulus_le_log`
(`O(1 + log(1/ρ))`), far field `integrableOn_bsKernelScalar_sq_farField`
(`L²`, paired with `‖ω‖_{L²}` by Cauchy–Schwarz); the Hölder-`1/4` near-field
input is `exists_agmonMorreyBound`; and the cutoff optimisation is
`le_of_forall_cutoff_le`.

**Satisfiability at both endpoints.**  At `ρ = 1` the bound reads
`A·‖u‖_{H³} + B·‖ω‖_∞ + F·‖ω‖_{L²}`, which already dominates `‖∇u‖_∞` by the
`H³ ↪ C¹` embedding for `A` large; as `ρ ↓ 0` the shell term diverges, so the
family is not constraining there.  The bundle is therefore inhabited, not
vacuous. -/
theorem exists_biotSavartKernelSplitting :
    ∃ A B F : ℝ, 0 < A ∧ 0 < B ∧ 0 < F ∧
      ∀ (u : SchwartzVelocity), DivergenceFreeInitial u →
        ∀ Mω M₂ : ℝ,
          (∀ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ≤ Mω) →
          (∫ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ^ 2) ≤ M₂ →
          ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
          ∀ x : Space,
            ‖fderiv ℝ (⇑u) x‖ ≤
              A * ρ ^ ((1 : ℝ) / 4) * Real.sqrt (sobolevH3NormSq u)
                + B * Mω * (1 + Real.log (1 / ρ))
                + F * Real.sqrt M₂ := by
  obtain ⟨K, hKpos, hK⟩ := exists_staticCurlSchwartz_h2_le_h3
  obtain ⟨A, B, F, hApos, hBpos, hFpos, hsplit⟩ :=
    exists_biotSavartKernelSplit_of_curlH2
  refine ⟨A * Real.sqrt K, B, F, by positivity, hBpos, hFpos, ?_⟩
  intro u hdiv Mω M₂ hMω hM₂ ρ hρ0 hρ1 x
  have hcurlH2 : sobolevH2NormSq (staticCurlSchwartz u) ≤
      K * sobolevH3NormSq u := by
    simpa [sobolevH2NormSq, sobolevH3NormSq] using hK u
  have hbound := hsplit u hdiv
    (K * sobolevH3NormSq u) Mω M₂ hcurlH2 hMω hM₂ ρ hρ0 hρ1 x
  rw [Real.sqrt_mul hKpos.le] at hbound
  convert hbound using 1 <;> ring

/-- **[DERIVED — no `sorry` in this declaration.  Reduced to the strictly lower
residual `exists_biotSavartKernelSplitting` (Biot–Savart representation +
Calderón–Zygmund split, est ~350 LOC) via the certified cutoff optimisation
`le_of_forall_cutoff_le`.  BKM 1984 Lemma 1; Majda–Bertozzi Prop. 3.8;
Stein, *Singular Integrals* (1970) Ch. II §4.]**
The Biot–Savart logarithmic inequality in its **textbook shape**

  `‖∇u‖_∞ ≤ C(1 + ‖ω‖_∞·(1 + log(e + ‖u‖_{H³})) + ‖ω‖_{L²})`,

with `‖u‖_{H³} = √(sobolevH3NormSq u)` written out as
`Real.sqrt (sobolevH3NormSq u)` and `e = Real.exp 1`.  The two vorticity
majorants stay hypothesis-carried; the right-hand side is monotone in both, so
this form follows from the classical statement.

**Status.**  This declaration is *conditional*, not closed: it is proved from
`exists_biotSavartKernelSplitting`, which propagates the honest lower residual
`exists_biotSavartKernelSplit_of_curlH2`.  The
constant produced here is `max A (max (4B) F)` in that residual's constants.

**What the derivation certifies.**  Exactly the log-producing step: the
`ρ`-indexed Calderón–Zygmund family is collapsed at the optimising scale
`ρ = (e + ‖u‖_{H³})^{-4}`, which is admissible for every value of the `H³`
norm, so no smallness/largeness case split is needed and the `e +` guard is
genuine rather than cosmetic.

**Dependencies still carried by the lower residual (Mathlib-absent).**  The
Biot–Savart representation `∇u = ∇K ∗ ω` for the homogeneous degree `−3`
kernel `∇K`, with its local term, for divergence-free Schwartz fields, and
the tensor/operator-norm reduction to the certified scalar kernel estimates.
The fractional near-field moment, including its sharp `ρ^(1/4)` scaling, and
the curl-component bridge are certified below and in
`Navier.Analysis.CurlDerivativeBridge`, respectively.

**What is no longer residual.**  The cutoff optimisation is certified as
`le_of_forall_cutoff_le` above.  The passage from this citable shape to the
`log (1 + Ms)` shape the bootstrap consumes — including the transfer to an
arbitrary `H³`-majorant `Ms` — is certified in
`BKMLogLeaves.bkm_log_shape_transfer`, at the cost of the constant factor `3`.
The integer-weight near field `integral_norm_mul_bsKernelScalar_ball_le`
(`O(ρ)` with cancellation weight `‖z‖`) and fractional-weight integrability
are certified at the bottom of this file, as are the logarithmic shell
`integral_bsKernelScalar_annulus_le_log` (`O(1 + log(1/ρ))`, the source of the
logarithm), far field `integrableOn_bsKernelScalar_sq_farField` (`L²`, paired
with `‖ω‖_{L²}` by Cauchy–Schwarz).  The near-field **Hölder input** is
certified as `exists_agmonMorreyBound` (Morrey–Agmon, `H²(ℝ³) ↪ C^{0,1/4}`
for Schwartz fields, kernel axioms only): the cancellation factor
`|ω(x−z) − ω(x)|` is `O(‖z‖^{1/4})` with constant `O(√(sobolevH2NormSq))` of
the vorticity components — exactly the `H³`-of-`u` order this statement
carries, not the `H⁴` that a Lipschitz/`‖∇ω‖∞` route would cost — so the
cutoff optimisation at `ρ ≈ ‖u‖_{H³}^{-4}` produces the `log(e + ‖u‖_{H³})`
factor.  What remains genuinely Mathlib-absent is the Biot–Savart
*representation* `∇u = PV(∇K ∗ ω)` (with its local term) for divergence-free
Schwartz fields, which is what converts these kernel estimates into a bound
on `‖∇u‖_∞`.  The curl-component bridge that feeds the vorticity into
`exists_agmonMorreyBound` is **no longer residual**: it is certified at every
derivative order, with one constant, as
`CurlDerivativeBridge.exists_norm_iteratedFDeriv_staticCurl_le`. -/
theorem exists_biotSavartLogTextbook :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity), DivergenceFreeInitial u →
        ∀ Mω M₂ : ℝ,
          (∀ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ≤ Mω) →
          (∫ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ^ 2) ≤ M₂ →
          ∀ x : Space,
            ‖fderiv ℝ (⇑u) x‖ ≤
              C * (1 + Mω * (1 + Real.log (Real.exp 1 +
                Real.sqrt (sobolevH3NormSq u))) + Real.sqrt M₂) := by
  obtain ⟨A, B, F, hA, hB, hF, hsplit⟩ := exists_biotSavartKernelSplitting
  refine ⟨max A (max (4 * B) F), lt_of_lt_of_le hA (le_max_left _ _), ?_⟩
  intro u hu Mω M₂ hMω hM₂ x
  have hMωnn : 0 ≤ Mω :=
    le_trans (officialEuclideanNorm_nonneg (staticCurl (⇑u) 0)) (hMω 0)
  have hMnn : 0 ≤ Real.sqrt (sobolevH3NormSq u) := Real.sqrt_nonneg _
  have hM₂nn : 0 ≤ Real.sqrt M₂ := Real.sqrt_nonneg _
  have key :=
    le_of_forall_cutoff_le (Y := ‖fderiv ℝ (⇑u) x‖) (A := A) (B := B)
      (F := F * Real.sqrt M₂) (Mω := Mω)
      (M := Real.sqrt (sobolevH3NormSq u)) hA.le hB.le hMωnn hMnn
      (fun ρ hρ0 hρ1 => hsplit u hu Mω M₂ hMω hM₂ ρ hρ0 hρ1 x)
  set S : ℝ := 1 + Real.log (Real.exp 1 + Real.sqrt (sobolevH3NormSq u)) with hSdef
  have hSnn : 0 ≤ S := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 + Real.sqrt (sobolevH3NormSq u) := by
      have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      linarith
    have := Real.log_nonneg h1
    rw [hSdef]; linarith
  set C : ℝ := max A (max (4 * B) F) with hCdef
  have hAC : A ≤ C := le_max_left _ _
  have hBC : 4 * B ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hFC : F ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have e1 : 4 * B * Mω * S ≤ C * (Mω * S) := by
    calc 4 * B * Mω * S = (4 * B) * (Mω * S) := by ring
      _ ≤ C * (Mω * S) := mul_le_mul_of_nonneg_right hBC (mul_nonneg hMωnn hSnn)
  have e2 : F * Real.sqrt M₂ ≤ C * Real.sqrt M₂ :=
    mul_le_mul_of_nonneg_right hFC hM₂nn
  have hexp : C * (1 + Mω * S + Real.sqrt M₂)
      = C + C * (Mω * S) + C * Real.sqrt M₂ := by ring
  rw [hexp]
  linarith

/-- **[DERIVED from `exists_biotSavartLogTextbook`.]**
The Biot–Savart logarithmic inequality: for a divergence-free Schwartz field,
the velocity gradient is bounded by the vorticity sup norm times a *logarithm*
of the `H³` norm, plus the vorticity `L²` norm:

  `‖∇u‖_∞ ≤ C(1 + Mω·(1 + log(1 + Ms)) + √M₂)`

for any majorants `Mω ≥ ‖ω‖_∞`, `M₂ ≥ ‖ω‖²_{L²}`, `Ms ≥ ‖u‖²_{H³}`.  The
`log(1+‖·‖²)` form is equivalent to the textbook `log(e+‖·‖)` up to `C`.

Closure route: Biot–Savart representation `∇u = ∇K ∗ ω` (kernel absent from
Mathlib), near-field Calderón–Zygmund cancellation + cutoff at scale
`ρ = ‖u‖_{H³}^{-1}`-type log interpolation, far-field kernel in `L²(|x|>1)`
paired with `‖ω‖_{L²}`.  Genuinely Mathlib-absent: singular-integral theory. -/
theorem biotSavartLogInequality :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity), DivergenceFreeInitial u →
        ∀ Mω M₂ Ms : ℝ,
          (∀ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ≤ Mω) →
          (∫ x : Space,
            officialEuclideanNorm (staticCurl (⇑u) x) ^ 2) ≤ M₂ →
          sobolevH3NormSq u ≤ Ms →
          ∀ x : Space,
            ‖fderiv ℝ (⇑u) x‖ ≤
              C * (1 + Mω * (1 + Real.log (1 + Ms)) + Real.sqrt M₂) := by
  obtain ⟨C, hCpos, hC⟩ := exists_biotSavartLogTextbook
  refine ⟨3 * C, by linarith, ?_⟩
  intro u hdiv Mω M₂ Ms hMω hM₂ hMs x
  have hMωnn : 0 ≤ Mω :=
    le_trans (officialEuclideanNorm_nonneg _) (hMω 0)
  exact bkm_log_shape_transfer (le_of_lt hCpos) hMωnn
    (sobolevH3NormSq_nonneg u) hMs (hC u hdiv Mω M₂ hMω hM₂ x)

/-- The squared `H²` norm is nonnegative (each summand is an integral of a
square). -/
theorem sobolevH2NormSq_nonneg (u : SchwartzVelocity) :
    0 ≤ sobolevH2NormSq u := by
  apply Finset.sum_nonneg
  intro n _
  exact integral_nonneg (fun x => by positivity)

/-!
### The Bessel weight `(1 + |ξ|²)⁻²` on `ℝ³` (certified, no sorry)

The part of the Agmon embedding `H²(ℝ³) ↪ L^∞` that is *specific to three
dimensions* is the finiteness of `∫_{ℝ³} (1 + |ξ|²)^{-2} dξ`: on the Euclidean
model this is the radial integral `∫₀^∞ 4πr²/(1+r²)² dr = π²`, finite precisely
because the decay exponent `4` strictly exceeds the dimension `3`.  The `H¹`
analogue `∫_{ℝ³} (1 + |ξ|²)^{-1} dξ` **diverges** (`∫₀^R 4πr²/(1+r²) dr ∼ 4πR`),
which is why the `H²` order in `exists_agmonSupBound` is load-bearing and not
decoration.  Everything below is dimension-generic Lean; `ℝ³` enters through
the single arithmetic fact `Module.finrank ℝ Space = 3 < 4`.

Reference: E. M. Stein, *Singular Integrals and Differentiability Properties of
Functions*, Princeton University Press 1970, Ch. V §3 (Bessel potentials);
S. Agmon, *Lectures on Elliptic Boundary Value Problems*, Van Nostrand 1965.
-/

/-- The reciprocal Bessel weight `ξ ↦ (1 + ‖ξ‖²)⁻¹` is continuous (the
denominator is bounded below by `1`). -/
theorem continuous_inv_one_add_normSq :
    Continuous (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro ξ; positivity

/-- **Bessel-weight integrability in three dimensions (certified, no sorry).**
`ξ ↦ (1 + ‖ξ‖²)⁻²` is `volume`-integrable on `Space = ℝ³`, because the decay
exponent `4` strictly exceeds `Module.finrank ℝ Space = 3`.

This is the sole dimension-dependent input to the Agmon embedding: with the
exponent `2` in place of `4` (the `H¹` weight) the integral diverges, so this
lemma is exactly the reason `H²` — and not `H¹` — embeds into `L^∞` on `ℝ³`.

Reference: Stein, *Singular Integrals and Differentiability Properties of
Functions*, Princeton 1970, Ch. V §3. -/
theorem integrable_inv_one_add_normSq_sq :
    Integrable (fun ξ : Space => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) := by
  have hr : (Module.finrank ℝ Space : ℝ) < 4 := by
    have h3 : Module.finrank ℝ Space = 3 := by simp
    rw [h3]; norm_num
  refine (integrable_rpow_neg_one_add_norm_sq (E := Space) (μ := volume)
    (r := 4) hr).congr ?_
  filter_upwards with ξ
  rw [show (-4 : ℝ) / 2 = -(2 : ℕ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

/-- **Sharpness of the `H²` order (certified, no sorry).**  The `H¹` Bessel
weight `ξ ↦ (1 + ‖ξ‖²)⁻¹` is **not** integrable on `ℝ³`: its decay exponent `2`
does not exceed `Module.finrank ℝ Space = 3`.

This is the exact counterpart of `integrable_inv_one_add_normSq_sq`, and it is
what makes the `H²` hypothesis in `exists_agmonSupBound` load-bearing rather
than decorative: the same Fourier/Cauchy–Schwarz route run at order `1` has no
finite weight to pair against, so it yields no `L^∞` bound.  (Indeed
`H¹(ℝ³) ↪ L^∞` is false.)

Proof: on `ball 0 R` with `R ≥ 1` the integrand is `≥ (2R²)⁻¹`, while
`volume (ball 0 R) = R³ · volume (ball 0 1)` by `Measure.addHaar_ball`, so the
lower Lebesgue integral is at least `(R/2)·volume (ball 0 1) → ∞`.

Reference: Stein, *Singular Integrals and Differentiability Properties of
Functions*, Princeton 1970, Ch. V §3 (the Bessel potential `G_s` is in `L²`
iff `2s > n`). -/
theorem not_integrable_inv_one_add_normSq :
    ¬ Integrable (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) := by
  intro hint
  set M : ENNReal := ∫⁻ ξ : Space, ‖((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹‖ₑ with hM
  have hMlt : M < ⊤ := hint.2
  set v : ENNReal := (volume : Measure Space) (Metric.ball (0 : Space) 1) with hv
  have hvpos : 0 < v := Metric.measure_ball_pos _ _ one_pos
  have hvne : v ≠ ⊤ := measure_ball_lt_top.ne
  have key : ∀ R : ℝ, 1 ≤ R →
      ENNReal.ofReal ((2 * R ^ 2)⁻¹) *
        (volume : Measure Space) (Metric.ball (0 : Space) R) ≤ M := by
    intro R hR
    have hms : MeasurableSet (Metric.ball (0 : Space) R) := measurableSet_ball
    rw [← lintegral_indicator_const hms]
    refine lintegral_mono fun ξ => ?_
    by_cases hξ : ξ ∈ Metric.ball (0 : Space) R
    · rw [Set.indicator_of_mem hξ]
      have hlt : ‖ξ‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hξ
      have hnn : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
      have hb : (1 : ℝ) + ‖ξ‖ ^ 2 ≤ 2 * R ^ 2 := by nlinarith
      have hpos : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
      have hinv : ((2 * R ^ 2 : ℝ))⁻¹ ≤ ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ := inv_anti₀ hpos hb
      calc ENNReal.ofReal ((2 * R ^ 2)⁻¹)
          ≤ ENNReal.ofReal (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) := ENNReal.ofReal_le_ofReal hinv
        _ = ‖((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹‖ₑ := by rw [Real.enorm_eq_ofReal (by positivity)]
    · rw [Set.indicator_of_notMem hξ]; exact zero_le
  have hball : ∀ R : ℝ, 0 ≤ R →
      (volume : Measure Space) (Metric.ball (0 : Space) R)
        = ENNReal.ofReal (R ^ 3) * v := by
    intro R hR
    rw [Measure.addHaar_ball _ _ hR]
    congr 2
    simp
  have final : ∀ R : ℝ, 1 ≤ R → R / 2 * v.toReal ≤ M.toReal := by
    intro R hR
    have h0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
    have h := key R hR
    rw [hball R h0, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at h
    have heq : (2 * R ^ 2)⁻¹ * R ^ 3 = R / 2 := by
      have hR0 : R ≠ 0 := by positivity
      field_simp
    rw [heq] at h
    have h2 := ENNReal.toReal_mono hMlt.ne h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  have hvr : 0 < v.toReal := ENNReal.toReal_pos hvpos.ne' hvne
  obtain ⟨R, hR1, hRbig⟩ : ∃ R : ℝ, 1 ≤ R ∧ M.toReal < R / 2 * v.toReal := by
    refine ⟨max 1 (2 * (M.toReal + 1) / v.toReal), le_max_left _ _, ?_⟩
    have h2 : 2 * (M.toReal + 1) / v.toReal ≤ max 1 (2 * (M.toReal + 1) / v.toReal) :=
      le_max_right _ _
    have h3 : 2 * (M.toReal + 1) / v.toReal * v.toReal = 2 * (M.toReal + 1) := by
      field_simp
    nlinarith [h3, h2, hvr]
  linarith [final R hR1]

/-- The `L¹(ℝ³)` mass `∫ (1 + ‖ξ‖²)⁻² dξ` of the Bessel weight.  Finite by
`integrable_inv_one_add_normSq_sq`; on the Euclidean model of `ℝ³` its value is
`π²`, but only finiteness is used below. -/
def besselWeightMass : ℝ := ∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹

/-- **Weighted Cauchy–Schwarz against the Bessel weight (certified, no sorry).**
For nonnegative `h : ℝ³ → ℝ` whose Bessel-weighted version `(1 + ‖ξ‖²)·h` is
square integrable,

  `∫ h ≤ √(∫ (1+‖ξ‖²)⁻²) · √(∫ ((1+‖ξ‖²)·h)²)`.

Proof: write `h = (1+‖ξ‖²)⁻¹ · ((1+‖ξ‖²)·h)` and apply Hölder with the
conjugate pair `(2,2)`; the first factor lies in `L²(ℝ³)` by
`integrable_inv_one_add_normSq_sq`.  Applied with `h = ‖û‖` this is precisely
the Cauchy–Schwarz step of the Agmon/Sobolev embedding (Stein, *Singular
Integrals*, Princeton 1970, Ch. V §3). -/
theorem integral_le_besselWeightMass_mul_sqrt
    {h : Space → ℝ} (hnn : ∀ ξ : Space, 0 ≤ h ξ)
    (hmem : MemLp (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) 2) :
    ∫ ξ : Space, h ξ ≤
      Real.sqrt besselWeightMass *
        Real.sqrt (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) ^ 2) := by
  have hpq : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hfsq : Integrable (fun ξ : Space => (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) ^ 2) := by
    simpa [inv_pow] using integrable_inv_one_add_normSq_sq
  have hf : MemLp (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹) 2 :=
    (memLp_two_iff_integrable_sq continuous_inv_one_add_normSq.aestronglyMeasurable).mpr hfsq
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure Space)) hpq
    (f := fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹)
    (g := fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ)
    (Filter.Eventually.of_forall fun ξ => by positivity)
    (Filter.Eventually.of_forall fun ξ => by have := hnn ξ; positivity)
    (by simpa using hf) (by simpa using hmem)
  have hprod : ∀ ξ : Space,
      ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * (((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) = h ξ := by
    intro ξ; field_simp
  simp only [hprod] at key
  have hrw : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
    intro y; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrw] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [besselWeightMass, inv_pow] using key

open scoped FourierTransform LineDeriv

/-!
### Euclidean/complex model transport for the Fourier majorant (certified, no sorry)

`Space = Fin 3 → ℝ` carries the Pi (sup) norm, so it has **no** `InnerProductSpace ℝ`
instance and no `NormedSpace ℂ` instance — both verified against the compiler:
`example : InnerProductSpace ℝ Space := by infer_instance` and
`example : NormedSpace ℂ Space := by infer_instance` each fail with
`failed to synthesize instance`.  Mathlib's Schwartz Fourier transform
(`SchwartzMap.instFourierTransform` in
`Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`) requires
`[InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]`
on the domain and `[NormedSpace ℂ E]` on the codomain, so it does not apply to
`𝓢(Space, Space)` on the nose.  The transport built here is the fix: the domain
moves to `EuclideanSpace ℝ (Fin 3)` (definitionally `PiLp 2 fun _ : Fin 3 => ℝ`,
same carrier, ℓ² norm, volume-preserving by `PiLp.volume_preserving_ofLp`) and the
codomain to `EuclideanSpace ℂ (Fin 3)`, via Mathlib's
`SchwartzMap.compCLMOfContinuousLinearEquiv` and `SchwartzMap.postcompCLM`.
-/

/-- The Euclidean (ℓ²) model of `Space`, on the same carrier `Fin 3 → ℝ`. -/
abbrev EuclSpace := EuclideanSpace ℝ (Fin 3)

/-- The complex Euclidean codomain, needed because Mathlib's Fourier transform
takes values in a `ℂ`-normed space. -/
abbrev CxSpace := EuclideanSpace ℂ (Fin 3)

/-- The coordinate identification `EuclideanSpace ℝ (Fin 3) ≃L[ℝ] Space`.  It is the
identity on carriers and changes only the norm. -/
def euclCoords : EuclSpace ≃L[ℝ] Space := EuclideanSpace.equiv (Fin 3) ℝ

/-- Componentwise inclusion `ℝ³ ↪ ℂ³`, landing in the complex Euclidean space. -/
def realToCx : Space →L[ℝ] CxSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => (WithLp.toLp 2 (fun i => ((a i : ℂ))) : CxSpace)
      map_add' := by intro a b; ext i; simp
      map_smul' := by intro c a; ext i; simp }

@[simp] theorem realToCx_apply (a : Space) (i : Fin 3) : realToCx a i = (a i : ℂ) := by
  simp [realToCx]

/-- The Pi (sup) norm of `ℝ³` is dominated by the ℓ² norm of its complex image.
This is the direction the majorant bound needs: it lets the sup-norm conclusion
`‖u x‖ ≤ ∫ h` be read off from the Euclidean model. -/
theorem norm_le_norm_realToCx (a : Space) : ‖a‖ ≤ ‖realToCx a‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  have h1 : ‖(realToCx a) i‖ ≤ ‖realToCx a‖ := by
    rw [EuclideanSpace.norm_eq]
    refine (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr ?_
    exact Finset.single_le_sum (f := fun j => ‖(realToCx a) j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  rw [realToCx_apply] at h1
  simpa using h1

/-- The Euclidean/complex model of a Schwartz velocity field: precompose with the
coordinate identification (`compCLMOfContinuousLinearEquiv`) and postcompose with the
componentwise complexification (`postcompCLM`).  Both are Mathlib's own Schwartz-space
operations, so the result is a genuine `SchwartzMap EuclSpace CxSpace` and Mathlib's Fourier
transform applies to it. -/
def euclModel (u : SchwartzVelocity) : SchwartzMap EuclSpace CxSpace :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) realToCx
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ euclCoords u)

@[simp] theorem euclModel_apply (u : SchwartzVelocity) (y : EuclSpace) :
    euclModel u y = realToCx (u (euclCoords y)) := rfl

/-- **Fourier-inversion majorant on the Euclidean model (certified, no sorry).**
For a Schwartz map into a complex Hilbert space, the sup norm is dominated by the
`L¹` mass of its Fourier transform: `‖v y‖ = ‖𝓕⁻(𝓕 v) y‖ ≤ ∫ ‖𝓕 v‖`.  This is the
inversion half of `exists_besselFourierMajorant`; the Schwartz-level inversion pair
is Mathlib's `FourierPair.fourierInv_fourier_eq`
(Hörmander, *The Analysis of Linear PDO I*, 2nd ed. Springer 1990, Thm 7.1.5). -/
theorem norm_le_integral_norm_fourier (v : SchwartzMap EuclSpace CxSpace) (y : EuclSpace) :
    ‖v y‖ ≤ ∫ ξ : EuclSpace, ‖(𝓕 v) ξ‖ := by
  have hinv : (𝓕⁻ (𝓕 v) : SchwartzMap EuclSpace CxSpace) = v := FourierPair.fourierInv_fourier_eq v
  have h1 : v y = 𝓕⁻ ((𝓕 v : SchwartzMap EuclSpace CxSpace) : EuclSpace → CxSpace) y := by
    conv_lhs => rw [← hinv]
    rw [SchwartzMap.fourierInv_coe]
  rw [h1, Real.fourierInv_eq_fourier_neg]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- **Volume transport between the two models (certified, no sorry).**  `Space` and
`EuclSpace` share a carrier and the coordinate map is volume preserving
(`PiLp.volume_preserving_ofLp`), so every Lebesgue integral transports verbatim. -/
theorem integral_space_eq_euclSpace (f : Space → ℝ) :
    ∫ ξ : Space, f ξ = ∫ y : EuclSpace, f (euclCoords y) := by
  have hmp : MeasureTheory.MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ))
      (volume : Measure EuclSpace) (volume : Measure Space) :=
    PiLp.volume_preserving_ofLp (Fin 3)
  rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding]
  rfl

/-!
### Leaf 1: weighted Plancherel on the Euclidean model (certified, no sorry)

The coordinate-derivative route.  Mathlib's Plancherel for Schwartz maps
(`SchwartzMap.integral_norm_sq_fourier`) needs an inner-product codomain, which
`iteratedFDeriv` does not have (it lands in a space of multilinear maps).  So the
symbol identity is run on **line derivatives** `∂_{eᵢ}` instead
(`SchwartzMap.fourier_lineDerivOp_eq`: `𝓕(∂_m f) = (2πi)⟪·,m⟫ · 𝓕 f`), whose
codomain is still `CxSpace`.  Summing over the orthonormal basis turns the symbol
product into a power of `‖ξ‖` because `∑_{i₁…i_n} ⟪ξ,e_{i₁}⟫²⋯⟪ξ,e_{i_n}⟫² =
(∑_i ξ_i²)^n = ‖ξ‖^{2n}`, and the passage back to the `iteratedFDeriv` operator
norm is one application of `ContinuousMultilinearMap.le_opNorm` at unit vectors.
Stein, *Singular Integrals*, Princeton 1970, Ch. V §3.
-/

private abbrev SV := SchwartzMap EuclSpace CxSpace

private theorem norm_fourier_lineDeriv (v : SV) (m ξ : EuclSpace) :
    ‖𝓕 (∂_{m} v) ξ‖ = 2 * Real.pi * |inner ℝ ξ m| * ‖𝓕 v ξ‖ := by
  have h : (inner ℝ · m : EuclSpace → ℝ).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp [h, norm_smul, abs_of_pos Real.pi_pos]
  ring

private noncomputable def eucBasis (i : Fin 3) : EuclSpace := EuclideanSpace.single i (1:ℝ)

@[simp] private theorem norm_eucBasis (i : Fin 3) : ‖eucBasis i‖ = 1 := by
  simp [eucBasis]

@[simp] private theorem inner_eucBasis (ξ : EuclSpace) (i : Fin 3) :
    (inner ℝ ξ (eucBasis i) : ℝ) = ξ i := by
  simp [eucBasis, EuclideanSpace.inner_single_right]

private theorem sum_inner_eucBasis_sq (ξ : EuclSpace) :
    ∑ i : Fin 3, (inner ℝ ξ (eucBasis i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
  simp only [inner_eucBasis]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [sq_abs]

private theorem integrable_pow_mul_normSq (f : SV) (k : ℕ) :
    Integrable (fun ξ : EuclSpace => ‖ξ‖ ^ k * ‖f ξ‖ ^ 2) := by
  have hM : ∀ x, ‖f x‖ ≤ (SchwartzMap.seminorm ℝ 0 0) f := fun x => f.norm_le_seminorm ℝ x
  have hM0 : (0:ℝ) ≤ (SchwartzMap.seminorm ℝ 0 0) f := le_trans (norm_nonneg _) (hM 0)
  refine ((f.integrable_pow_mul volume k).const_mul ((SchwartzMap.seminorm ℝ 0 0) f)).mono'
    ((by fun_prop : Continuous fun ξ : EuclSpace => ‖ξ‖ ^ k * ‖f ξ‖ ^ 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : ‖ξ‖ ^ k * ‖f ξ‖ ^ 2 = (‖ξ‖ ^ k * ‖f ξ‖) * ‖f ξ‖ := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (hM ξ) (by positivity) |>.trans_eq (by ring)

private theorem integrable_weight_mul_normSq (f : SV) (k : ℕ) (g : EuclSpace → ℝ)
    (hg : Continuous g) (hgb : ∀ ξ, |g ξ| ≤ ‖ξ‖ ^ k) :
    Integrable (fun ξ : EuclSpace => g ξ * ‖f ξ‖ ^ 2) := by
  refine (integrable_pow_mul_normSq f k).mono'
    ((by fun_prop : Continuous fun ξ : EuclSpace => g ξ * ‖f ξ‖ ^ 2).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖f ξ‖ ^ 2)]
  exact mul_le_mul_of_nonneg_right (hgb ξ) (by positivity)

private theorem integral_lineDeriv_sq (v : SV) (m : EuclSpace) :
    ∫ x : EuclSpace, ‖(∂_{m} v) x‖ ^ 2
      = 4 * Real.pi ^ 2 * ∫ ξ : EuclSpace, (inner ℝ ξ m : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier (∂_{m} v), ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖𝓕 (∂_{m} v) ξ‖ ^ 2 = 4 * Real.pi ^ 2 * ((inner ℝ ξ m : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2)
  rw [norm_fourier_lineDeriv]
  rw [mul_pow, mul_pow, mul_pow, sq_abs]
  ring

private theorem integrable_inner_sq (v : SV) (m : EuclSpace) (hm : ‖m‖ ≤ 1) :
    Integrable (fun ξ : EuclSpace => (inner ℝ ξ m : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2) := by
  refine integrable_weight_mul_normSq (𝓕 v) 2 _ (by fun_prop) fun ξ => ?_
  rw [abs_of_nonneg (by positivity)]
  have h := abs_real_inner_le_norm ξ m
  calc (inner ℝ ξ m : ℝ) ^ 2 = |(inner ℝ ξ m : ℝ)| ^ 2 := by rw [sq_abs]
    _ ≤ (‖ξ‖ * ‖m‖) ^ 2 := by gcongr
    _ = ‖ξ‖ ^ 2 * ‖m‖ ^ 2 := by ring
    _ ≤ ‖ξ‖ ^ 2 * 1 ^ 2 := by gcongr
    _ = ‖ξ‖ ^ 2 := by ring

private theorem sum_integral_lineDeriv_sq (v : SV) :
    ∑ i : Fin 3, ∫ x : EuclSpace, ‖(∂_{eucBasis i} v) x‖ ^ 2
      = 4 * Real.pi ^ 2 * ∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  simp_rw [integral_lineDeriv_sq]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun i _ => integrable_inner_sq v (eucBasis i) (by simp))]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (∑ i : Fin 3, (inner ℝ ξ (eucBasis i) : ℝ) ^ 2 * ‖𝓕 v ξ‖ ^ 2) = ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2
  rw [← Finset.sum_mul, sum_inner_eucBasis_sq]

private theorem integrable_normSq_iteratedFDeriv (v : SV) (n : ℕ) :
    Integrable (fun x : EuclSpace => ‖iteratedFDeriv ℝ n (⇑v) x‖ ^ 2) := by
  have hM : ∀ x, ‖iteratedFDeriv ℝ n (⇑v) x‖ ≤ (SchwartzMap.seminorm ℝ 0 n) v :=
    fun x => v.norm_iteratedFDeriv_le_seminorm ℝ n x
  have hM0 : (0:ℝ) ≤ (SchwartzMap.seminorm ℝ 0 n) v := le_trans (norm_nonneg _) (hM 0)
  have hcont : Continuous fun x : EuclSpace => ‖iteratedFDeriv ℝ n (⇑v) x‖ ^ 2 :=
    ((ContDiff.continuous_iteratedFDeriv (m := n) (hf := v.smooth ⊤)
      (by exact_mod_cast le_top)).norm).pow 2
  refine ((SchwartzMap.integrable_pow_mul_iteratedFDeriv volume v 0 n).const_mul
    ((SchwartzMap.seminorm ℝ 0 n) v)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : ‖iteratedFDeriv ℝ n (⇑v) x‖ ^ 2
      = ‖iteratedFDeriv ℝ n (⇑v) x‖ * ‖iteratedFDeriv ℝ n (⇑v) x‖ := by ring
  rw [this]
  calc ‖iteratedFDeriv ℝ n (⇑v) x‖ * ‖iteratedFDeriv ℝ n (⇑v) x‖
      ≤ (SchwartzMap.seminorm ℝ 0 n) v * (‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑v) x‖) := by
        simp only [pow_zero, one_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    _ = _ := rfl

private theorem integrable_quartic_weight (v : SV) (j : Fin 3) :
    Integrable (fun ξ : EuclSpace =>
      (‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) * ‖𝓕 v ξ‖ ^ 2) := by
  refine integrable_weight_mul_normSq (𝓕 v) 4 _ (by fun_prop) fun ξ => ?_
  rw [abs_of_nonneg (by positivity)]
  have h := abs_real_inner_le_norm ξ (eucBasis j)
  have h2 : (inner ℝ ξ (eucBasis j) : ℝ) ^ 2 ≤ ‖ξ‖ ^ 2 := by
    calc (inner ℝ ξ (eucBasis j) : ℝ) ^ 2 = |(inner ℝ ξ (eucBasis j) : ℝ)| ^ 2 := by rw [sq_abs]
      _ ≤ (‖ξ‖ * ‖eucBasis j‖) ^ 2 := by gcongr
      _ = ‖ξ‖ ^ 2 := by simp
  calc ‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2 ≤ ‖ξ‖ ^ 2 * ‖ξ‖ ^ 2 := by gcongr
    _ = ‖ξ‖ ^ 4 := by ring

private theorem sum_integral_lineDeriv2_sq (v : SV) :
    ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x : EuclSpace, ‖(∂_{eucBasis i} (∂_{eucBasis j} v)) x‖ ^ 2
      = 16 * Real.pi ^ 4 * ∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2 := by
  have step : ∀ j : Fin 3,
      (∑ i : Fin 3, ∫ x : EuclSpace, ‖(∂_{eucBasis i} (∂_{eucBasis j} v)) x‖ ^ 2)
        = 16 * Real.pi ^ 4 * ∫ ξ : EuclSpace,
            (‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) * ‖𝓕 v ξ‖ ^ 2 := by
    intro j
    have hpt : ∀ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 (∂_{eucBasis j} v) ξ‖ ^ 2
        = 4 * Real.pi ^ 2 * ((‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) * ‖𝓕 v ξ‖ ^ 2) := by
      intro ξ
      rw [norm_fourier_lineDeriv, mul_pow, mul_pow, mul_pow, sq_abs]
      ring
    rw [sum_integral_lineDeriv_sq (∂_{eucBasis j} v),
      integral_congr_ae (Filter.Eventually.of_forall hpt), MeasureTheory.integral_const_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => step j), ← Finset.mul_sum,
    ← integral_finsetSum _ (fun j _ => integrable_quartic_weight v j)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show (∑ j : Fin 3, (‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) * ‖𝓕 v ξ‖ ^ 2)
      = ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2
  rw [← Finset.sum_mul]
  have : (∑ j : Fin 3, ‖ξ‖ ^ 2 * (inner ℝ ξ (eucBasis j) : ℝ) ^ 2) = ‖ξ‖ ^ 4 := by
    rw [← Finset.mul_sum, sum_inner_eucBasis_sq]; ring
  rw [this]

private theorem norm_lineDeriv_le (v : SV) (m x : EuclSpace) :
    ‖(∂_{m} v) x‖ ≤ ‖iteratedFDeriv ℝ 1 (⇑v) x‖ * ‖m‖ := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, norm_iteratedFDeriv_one]
  exact (fderiv ℝ (⇑v) x).le_opNorm m

private theorem lineDeriv2_eq (v : SV) (m m' x : EuclSpace) :
    (∂_{m} (∂_{m'} v)) x = iteratedFDeriv ℝ 2 (⇑v) x ![m, m'] := by
  have hdiff : Differentiable ℝ (fderiv ℝ (⇑v)) :=
    (ContDiff.fderiv_right (m := (1 : ℕ∞)) (v.smooth 2) (by norm_num)).differentiable (by norm_num)
  have hfun : ((∂_{m'} v : SV) : EuclSpace → CxSpace)
      = fun y : EuclSpace => (fderiv ℝ (⇑v) y) m' := by
    funext y; exact SchwartzMap.lineDerivOp_apply_eq_fderiv m' v y
  rw [iteratedFDeriv_two_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun,
    fderiv_clm_apply (hdiff x) (differentiableAt_const m')]
  simp

private theorem norm_lineDeriv2_le (v : SV) (m m' x : EuclSpace) :
    ‖(∂_{m} (∂_{m'} v)) x‖ ≤ ‖iteratedFDeriv ℝ 2 (⇑v) x‖ * (‖m‖ * ‖m'‖) := by
  rw [lineDeriv2_eq]
  refine le_trans ((iteratedFDeriv ℝ 2 (⇑v) x).le_opNorm ![m, m']) ?_
  simp [Fin.prod_univ_two]

private theorem sum3_const (c : ℝ) : (∑ _i : Fin 3, c) = 3 * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

private theorem sum33_const (c : ℝ) : (∑ _j : Fin 3, ∑ _i : Fin 3, c) = 9 * c := by
  rw [sum3_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem weight_sq_expand (v : SV) (ξ : EuclSpace) :
    (((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) ^ 2
      = ‖ξ‖ ^ 0 * ‖𝓕 v ξ‖ ^ 2 + (2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) + ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2) := by
  simp only [pow_zero, one_mul]
  ring

private theorem integrable_weight_sq (v : SV) :
    Integrable (fun ξ : EuclSpace => (((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) ^ 2) := by
  have h0 := integrable_pow_mul_normSq (𝓕 v) 0
  have h2 := integrable_pow_mul_normSq (𝓕 v) 2
  have h4 := integrable_pow_mul_normSq (𝓕 v) 4
  have h24 : Integrable (fun ξ : EuclSpace =>
      2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) + ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2) := (h2.const_mul 2).add h4
  have hall : Integrable (fun ξ : EuclSpace =>
      ‖ξ‖ ^ 0 * ‖𝓕 v ξ‖ ^ 2 + (2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) + ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2)) := h0.add h24
  exact hall.congr (Filter.Eventually.of_forall fun ξ => (weight_sq_expand v ξ).symm)

theorem memLp_weight_fourier (v : SV) :
    MemLp (fun ξ : EuclSpace => ((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) 2 volume := by
  refine (memLp_two_iff_integrable_sq ?_).mpr (integrable_weight_sq v)
  exact ((by fun_prop : Continuous fun ξ : EuclSpace =>
    ((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖)).aestronglyMeasurable

set_option maxHeartbeats 1000000 in
theorem exists_weighted_plancherel :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SV,
      (∫ ξ : EuclSpace, (((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) ^ 2)
        ≤ C * ∑ n ∈ Finset.range 3, ∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2 := by
  refine ⟨3, by norm_num, fun v => ?_⟩
  have hA0nn : (0:ℝ) ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 0 (⇑v) y‖ ^ 2 :=
    integral_nonneg fun y => by positivity
  have hA1nn : (0:ℝ) ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2 :=
    integral_nonneg fun y => by positivity
  have hA2nn : (0:ℝ) ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 :=
    integral_nonneg fun y => by positivity
  have h0 := integrable_pow_mul_normSq (𝓕 v) 0
  have h2 := integrable_pow_mul_normSq (𝓕 v) 2
  have h4 := integrable_pow_mul_normSq (𝓕 v) 4
  have hsplit : (∫ ξ : EuclSpace, (((1:ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v ξ‖) ^ 2)
      = (∫ ξ : EuclSpace, ‖𝓕 v ξ‖ ^ 2)
        + (2 * (∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2)
          + ∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2) := by
    have h24 : Integrable (fun ξ : EuclSpace =>
        2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) + ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2) := (h2.const_mul 2).add h4
    have h2c : Integrable (fun ξ : EuclSpace => 2 * (‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2)) := h2.const_mul 2
    rw [integral_congr_ae (Filter.Eventually.of_forall (weight_sq_expand v)),
      integral_add h0 h24, integral_add h2c h4, MeasureTheory.integral_const_mul]
    simp
  have hA : (∫ ξ : EuclSpace, ‖𝓕 v ξ‖ ^ 2)
      = ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 0 (⇑v) y‖ ^ 2 := by
    rw [SchwartzMap.integral_norm_sq_fourier]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ‖v y‖ ^ 2 = ‖iteratedFDeriv ℝ 0 (⇑v) y‖ ^ 2
    rw [norm_iteratedFDeriv_zero]
  have hle1 : ∀ i : Fin 3, (∫ x : EuclSpace, ‖(∂_{eucBasis i} v) x‖ ^ 2)
      ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2 := by
    intro i
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      (integrable_normSq_iteratedFDeriv v 1) (Filter.Eventually.of_forall fun x => ?_)
    have hb := norm_lineDeriv_le v (eucBasis i) x
    simp only [norm_eucBasis, mul_one] at hb
    have h0' := norm_nonneg ((∂_{eucBasis i} v) x)
    nlinarith
  have hS1 : 4 * Real.pi ^ 2 * (∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2)
      ≤ 3 * ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2 := by
    rw [← sum_integral_lineDeriv_sq v, ← sum3_const (∫ y : EuclSpace,
      ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2)]
    exact Finset.sum_le_sum fun i _ => hle1 i
  have hle2 : ∀ i j : Fin 3,
      (∫ x : EuclSpace, ‖(∂_{eucBasis i} (∂_{eucBasis j} v)) x‖ ^ 2)
        ≤ ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 := by
    intro i j
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      (integrable_normSq_iteratedFDeriv v 2) (Filter.Eventually.of_forall fun x => ?_)
    have hb := norm_lineDeriv2_le v (eucBasis i) (eucBasis j) x
    simp only [norm_eucBasis, mul_one] at hb
    have h0' := norm_nonneg ((∂_{eucBasis i} (∂_{eucBasis j} v)) x)
    nlinarith
  have hS2 : 16 * Real.pi ^ 4 * (∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2)
      ≤ 9 * ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 := by
    rw [← sum_integral_lineDeriv2_sq v, ← sum33_const (∫ y : EuclSpace,
      ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2)]
    exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hle2 i j
  have hpi : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hBnn : (0:ℝ) ≤ ∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 :=
    integral_nonneg fun ξ => by positivity
  have hDnn : (0:ℝ) ≤ ∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2 :=
    integral_nonneg fun ξ => by positivity
  have hpi2 : (9:ℝ) < Real.pi ^ 2 := by nlinarith
  have hpi4 : (81:ℝ) < Real.pi ^ 4 := by nlinarith
  have hB' : 2 * (∫ ξ : EuclSpace, ‖ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2)
      ≤ 3 * ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2 := by nlinarith
  have hD' : (∫ ξ : EuclSpace, ‖ξ‖ ^ 4 * ‖𝓕 v ξ‖ ^ 2)
      ≤ 3 * ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 := by nlinarith
  have hsum : (∑ n ∈ Finset.range 3, ∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2)
      = (∫ y : EuclSpace, ‖iteratedFDeriv ℝ 0 (⇑v) y‖ ^ 2)
        + (∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑v) y‖ ^ 2)
        + ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑v) y‖ ^ 2 := by
    simp [Finset.sum_range_succ]
  rw [hsplit, hA, hsum]
  linarith

/-!
### Leaf 2: model comparison, and the assembly (certified, no sorry)

`euclModel u = realToCx ∘ u ∘ euclCoords` is a composition with two continuous
linear maps, so `ContinuousLinearMap.iteratedFDeriv_comp_left` and
`ContinuousLinearMap.iteratedFDeriv_comp_right` give
`‖D^n (euclModel u) y‖ ≤ ‖realToCx‖ · ‖euclCoords‖^n · ‖D^n u (euclCoords y)‖`.
Since `n < 3` the operator-norm powers are absorbed into a single constant, and
`integral_space_eq_euclSpace` transports the resulting integrals back to `Space`.
Only finite-dimensional norm equivalence is used; no analysis.
-/

private theorem norm_le_norm_toEucl (ξ : Space) : ‖ξ‖ ≤ ‖euclCoords.symm ξ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  have h1 : ‖(euclCoords.symm ξ) i‖ ≤ ‖euclCoords.symm ξ‖ := by
    rw [EuclideanSpace.norm_eq]
    refine (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr ?_
    exact Finset.single_le_sum (f := fun j => ‖(euclCoords.symm ξ) j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : (euclCoords.symm ξ) i = ξ i := rfl
  rw [h2] at h1
  exact h1

private theorem iteratedFDeriv_euclModel_le (u : SchwartzVelocity) (n : ℕ) (y : EuclSpace) :
    ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖
      ≤ ‖realToCx‖ * (‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖
          * ∏ _i : Fin n, ‖(euclCoords : EuclSpace →L[ℝ] Space)‖) := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (⇑u) := u.smooth ⊤
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space)) :=
    hu.comp (euclCoords : EuclSpace →L[ℝ] Space).contDiff
  have heq : (⇑(euclModel u)) = (⇑realToCx) ∘ ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space)) := by
    funext z; simp [euclModel_apply]
  rw [heq]
  calc ‖iteratedFDeriv ℝ n ((⇑realToCx) ∘ ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space))) y‖
      = ‖realToCx.compContinuousMultilinearMap
          (iteratedFDeriv ℝ n ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space)) y)‖ := by
        rw [ContinuousLinearMap.iteratedFDeriv_comp_left realToCx hcomp.contDiffAt
          (by exact_mod_cast le_top)]
    _ ≤ ‖realToCx‖ * ‖iteratedFDeriv ℝ n ((⇑u) ∘ (euclCoords : EuclSpace →L[ℝ] Space)) y‖ :=
        realToCx.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖realToCx‖ * (‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖
          * ∏ _i : Fin n, ‖(euclCoords : EuclSpace →L[ℝ] Space)‖) := by
        gcongr
        rw [ContinuousLinearMap.iteratedFDeriv_comp_right
          (euclCoords : EuclSpace →L[ℝ] Space) hu y (by exact_mod_cast le_top)]
        exact ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
private theorem integrable_normSq_iteratedFDeriv_space (u : SchwartzVelocity) (n : ℕ) :
    Integrable (fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2) := by
  have hM : ∀ x, ‖iteratedFDeriv ℝ n (⇑u) x‖ ≤ (SchwartzMap.seminorm ℝ 0 n) u :=
    fun x => u.norm_iteratedFDeriv_le_seminorm ℝ n x
  have hM0 : (0:ℝ) ≤ (SchwartzMap.seminorm ℝ 0 n) u := le_trans (norm_nonneg _) (hM 0)
  have hcont : Continuous fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 :=
    ((ContDiff.continuous_iteratedFDeriv (m := n) (hf := u.smooth ⊤)
      (by exact_mod_cast le_top)).norm).pow 2
  refine ((SchwartzMap.integrable_pow_mul_iteratedFDeriv volume u 0 n).const_mul
    ((SchwartzMap.seminorm ℝ 0 n) u)).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2
      = ‖iteratedFDeriv ℝ n (⇑u) x‖ * ‖iteratedFDeriv ℝ n (⇑u) x‖ := by ring
  rw [hsq]
  calc ‖iteratedFDeriv ℝ n (⇑u) x‖ * ‖iteratedFDeriv ℝ n (⇑u) x‖
      ≤ (SchwartzMap.seminorm ℝ 0 n) u * (‖x‖ ^ 0 * ‖iteratedFDeriv ℝ n (⇑u) x‖) := by
        simp only [pow_zero, one_mul]
        exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    _ = _ := rfl

theorem exists_euclModel_h2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SchwartzVelocity,
      (∑ n ∈ Finset.range 3, ∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖ ^ 2)
        ≤ C * sobolevH2NormSq u := by
  set k := ‖realToCx‖ with hk
  set e := ‖(euclCoords : EuclSpace →L[ℝ] Space)‖ with he
  have hk0 : 0 ≤ k := norm_nonneg _
  have he0 : 0 ≤ e := norm_nonneg _
  set M := k * (1 + e) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M ^ 2 + 1, by positivity, fun u => ?_⟩
  have hmp : MeasureTheory.MeasurePreserving (@WithLp.ofLp 2 (Fin 3 → ℝ))
      (volume : Measure EuclSpace) (volume : Measure Space) :=
    PiLp.volume_preserving_ofLp (Fin 3)
  have key : ∀ n : ℕ, n ≤ 2 →
      (∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖ ^ 2)
        ≤ M ^ 2 * ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 := by
    intro n hn
    have hint : Integrable
        (fun y : EuclSpace => M ^ 2 * ‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ ^ 2) :=
      (hmp.integrable_comp_of_integrable (integrable_normSq_iteratedFDeriv_space u n)).const_mul (M ^ 2)
    have htrans : (∫ y : EuclSpace, M ^ 2 * ‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ ^ 2)
        = M ^ 2 * ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul,
        integral_space_eq_euclSpace (fun x : Space => ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2)]
    rw [← htrans]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity) hint
      (Filter.Eventually.of_forall fun y => ?_)
    have hb := iteratedFDeriv_euclModel_le u n y
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← hk, ← he] at hb
    have hen : e ^ n ≤ (1 + e) ^ 2 := by
      interval_cases n <;> nlinarith
    have hb2 : ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖
        ≤ M * ‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ := by
      refine hb.trans ?_
      rw [hM]
      calc k * (‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ * e ^ n)
          ≤ k * (‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ * (1 + e) ^ 2) := by gcongr
        _ = k * (1 + e) ^ 2 * ‖iteratedFDeriv ℝ n (⇑u) (euclCoords y)‖ := by ring
    have h0 := norm_nonneg (iteratedFDeriv ℝ n (⇑(euclModel u)) y)
    have h1 := norm_nonneg (iteratedFDeriv ℝ n (⇑u) (euclCoords y))
    nlinarith
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2 :=
    fun n => integral_nonneg fun x => by positivity
  have hsum : sobolevH2NormSq u
      = (∫ x : Space, ‖iteratedFDeriv ℝ 0 (⇑u) x‖ ^ 2)
        + (∫ x : Space, ‖iteratedFDeriv ℝ 1 (⇑u) x‖ ^ 2)
        + ∫ x : Space, ‖iteratedFDeriv ℝ 2 (⇑u) x‖ ^ 2 := by
    simp [sobolevH2NormSq, Finset.sum_range_succ]
  rw [show (∑ n ∈ Finset.range 3, ∫ y : EuclSpace, ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖ ^ 2)
      = (∫ y : EuclSpace, ‖iteratedFDeriv ℝ 0 (⇑(euclModel u)) y‖ ^ 2)
        + (∫ y : EuclSpace, ‖iteratedFDeriv ℝ 1 (⇑(euclModel u)) y‖ ^ 2)
        + ∫ y : EuclSpace, ‖iteratedFDeriv ℝ 2 (⇑(euclModel u)) y‖ ^ 2 from by
      simp [Finset.sum_range_succ], hsum]
  have k0 := key 0 (by norm_num)
  have k1 := key 1 (by norm_num)
  have k2 := key 2 (by norm_num)
  nlinarith [hnn 0, hnn 1, hnn 2, hM0]

private theorem euclCoords_symm_coe : (⇑euclCoords.symm : Space → EuclSpace)
    = (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclSpace) := rfl

/-- **[CERTIFIED — Fourier inversion + Plancherel + Bessel-symbol bookkeeping
for `SchwartzMap Space Space`; Stein, *Singular Integrals and Differentiability
Properties of Functions*, Princeton 1970, Ch. V §3; L. Hörmander, *The Analysis
of Linear Partial Differential Operators I*, 2nd ed. Springer 1990, §7.1 and
§7.9.]**

Every Schwartz velocity field admits a nonnegative **Fourier majorant density**
`h` — classically `h = ‖û‖` in the convention `u(x) = ∫ e^{2πi⟨x,ξ⟩} û(ξ) dξ` —
which dominates the sup norm through inversion, `‖u(x)‖ ≤ ∫ ‖û‖`, and whose
Bessel-weighted `L²` mass is controlled by the *physical* `H²` norm,
`∫ (1+|ξ|²)²‖û‖² ≤ C·‖u‖²_{H²}`: expand `(1+|ξ|²)² = 1 + 2|ξ|² + |ξ|⁴` and match
the three terms against `n = 0, 1, 2` via Plancherel and `ℱ(D^n u) =
(2πiξ)^{⊗n} û`.

**Why this is strictly lower than `exists_agmonSupBound`.**  It contains no
sup-norm/Sobolev inequality and no dimensional hypothesis.  The dimensional
content — that `(1+|ξ|²)⁻²` is integrable on `ℝ³` exactly because `4 > 3`, and
the Cauchy–Schwarz that turns that into the embedding — is discharged above by
`integrable_inv_one_add_normSq_sq` and `integral_le_besselWeightMass_mul_sqrt`.
What remains here is pure Fourier bookkeeping, provable without any reference
to `exists_agmonSupBound`.

**The obstruction, verified against the compiler.**  `Space = Fin 3 → ℝ` carries
the Pi (sup) norm, so both
`example : InnerProductSpace ℝ Space := by infer_instance` and
`example : NormedSpace ℂ Space := by infer_instance` fail with
`failed to synthesize instance`.  Mathlib's Schwartz Fourier transform
(`SchwartzMap.instFourierTransform`) needs `[InnerProductSpace ℝ V]
[FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]` on the domain and
`[NormedSpace ℂ E]` on the codomain, so it does not apply to `𝓢(Space, Space)`
on the nose.  That is the whole of the obstruction: it is an instance mismatch,
not a missing theorem.

**What is now built (certified above, no sorry).**  The transport is in place —
`euclCoords`, `realToCx`, `norm_le_norm_realToCx`, `euclModel`,
`integral_space_eq_euclSpace` — and so is the inversion half,
`norm_le_integral_norm_fourier`.  The correction to the earlier dependency list:
Fourier inversion and Plancherel are **not** Mathlib-absent.  Inversion for
Schwartz maps is `FourierPair.fourierInv_fourier_eq`, and Plancherel is
`SchwartzMap.integral_norm_sq_fourier : ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2`
(`Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`).  The transport API
is `SchwartzMap.compCLMOfContinuousLinearEquiv` and `SchwartzMap.postcompCLM`.

**The two leaves, both certified above.**

* `exists_weighted_plancherel` — *weighted Plancherel on the Euclidean model*
  [Stein Ch. V §3]:
  `∃ C > 0, ∀ v : 𝓢(EuclSpace, CxSpace),
   ∫ y, ((1 + ‖y‖²)·‖𝓕 v y‖)² ≤ C · ∑_{n < 3} ∫ y, ‖iteratedFDeriv ℝ n v y‖²`,
  together with `MemLp ((1 + ‖·‖²)·‖𝓕 v ·‖) 2`.  Route: expand
  `(1 + r²)² = 1 + 2r² + r⁴`, and get each `∫ ‖y‖^{2n}‖𝓕 v y‖²` from
  `SchwartzMap.integral_norm_sq_fourier` applied to the coordinate derivatives
  `∂_{i₁}…∂_{i_n} v` — summing over `(i₁,…,i_n)` turns the symbol product into
  `‖y‖^{2n}` because `∑_{i₁…i_n} y_{i₁}²⋯y_{i_n}² = (∑_i y_i²)^n`.  Working with
  coordinate derivatives rather than `iteratedFDeriv` directly is what keeps the
  codomain an inner-product space, which Plancherel requires; the passage back to
  the `iteratedFDeriv` operator norm is the finite-dimensional multilinear-norm
  comparison and carries the constant.
* `exists_euclModel_h2_bound` — *model comparison* [finite-dimensional norm
  equivalence]:
  `∃ C > 0, ∀ u, ∑_{n < 3} ∫ y, ‖iteratedFDeriv ℝ n (euclModel u) y‖² ≤
   C · sobolevH2NormSq u`.  Only norm equivalence on `Fin 3 → ℝ` and on the
  spaces of `n`-linear maps out of it, plus `integral_space_eq_euclSpace`.

The assembly below takes `h ξ = ‖𝓕 (euclModel u) (euclCoords.symm ξ)‖`, with
`norm_le_norm_realToCx` and `norm_le_integral_norm_fourier` supplying
`‖u x‖ ≤ ∫ h`, `norm_le_norm_toEucl` (Pi sup norm ≤ ℓ² norm) making the weight
transport monotone in the right direction, and `integral_space_eq_euclSpace`
moving the integrals between the two models. -/
theorem exists_besselFourierMajorant :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : SchwartzVelocity, ∃ h : Space → ℝ,
        (∀ ξ : Space, 0 ≤ h ξ) ∧
        MemLp (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) 2 ∧
        (∀ x : Space, ‖(⇑u) x‖ ≤ ∫ ξ : Space, h ξ) ∧
        (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) ^ 2) ≤ C * sobolevH2NormSq u := by
  obtain ⟨C₁, hC₁, hplan⟩ := exists_weighted_plancherel
  obtain ⟨C₂, hC₂, hmod⟩ := exists_euclModel_h2_bound
  refine ⟨C₁ * C₂, by positivity, fun u => ?_⟩
  set v : SchwartzMap EuclSpace CxSpace := euclModel u with hv
  have hmpT : MeasureTheory.MeasurePreserving
      (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclSpace) (volume : Measure Space)
      (volume : Measure EuclSpace) := PiLp.volume_preserving_toLp (Fin 3)
  have hcontF : Continuous fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖ := by
    fun_prop
  refine ⟨fun ξ => ‖𝓕 v (euclCoords.symm ξ)‖, fun ξ => norm_nonneg _, ?_, ?_, ?_⟩
  · have hG : MemLp (fun ξ : Space =>
        ((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) 2 volume := by
      rw [euclCoords_symm_coe]
      exact (memLp_weight_fourier v).comp_measurePreserving hmpT
    refine hG.of_le hcontF.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    have hle := norm_le_norm_toEucl ξ
    have h1 : (0:ℝ) ≤ ‖𝓕 v (euclCoords.symm ξ)‖ := norm_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    have h2 : ‖ξ‖ ^ 2 ≤ ‖euclCoords.symm ξ‖ ^ 2 := by
      have := norm_nonneg ξ; nlinarith
    nlinarith
  · intro x
    have h1 : ‖(⇑u) x‖ ≤ ‖v (euclCoords.symm x)‖ := by
      rw [hv, euclModel_apply]
      simp only [ContinuousLinearEquiv.apply_symm_apply]
      exact norm_le_norm_realToCx (u x)
    have h2 : ‖v (euclCoords.symm x)‖ ≤ ∫ ξ : EuclSpace, ‖𝓕 v ξ‖ :=
      norm_le_integral_norm_fourier v _
    have h3 : (∫ ξ : Space, ‖𝓕 v (euclCoords.symm ξ)‖) = ∫ ξ : EuclSpace, ‖𝓕 v ξ‖ := by
      rw [integral_space_eq_euclSpace (fun ξ : Space => ‖𝓕 v (euclCoords.symm ξ)‖)]
      simp
    rw [h3]; linarith
  · have hintE : Integrable
        (fun y : EuclSpace => (((1 : ℝ) + ‖y‖ ^ 2) * ‖𝓕 v y‖) ^ 2) := by
      refine (memLp_two_iff_integrable_sq ?_).mp (memLp_weight_fourier v)
      exact ((by fun_prop : Continuous fun y : EuclSpace =>
        ((1 : ℝ) + ‖y‖ ^ 2) * ‖𝓕 v y‖)).aestronglyMeasurable
    have hint : Integrable (fun ξ : Space =>
        (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2) := by
      rw [euclCoords_symm_coe]
      exact hmpT.integrable_comp_of_integrable hintE
    have hstep1 : (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2)
        ≤ ∫ ξ : Space,
            (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity) hint
        (Filter.Eventually.of_forall fun ξ => ?_)
      show (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2
          ≤ (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2
      have hle := norm_le_norm_toEucl ξ
      have h1 : (0:ℝ) ≤ ‖𝓕 v (euclCoords.symm ξ)‖ := norm_nonneg _
      have h2 : ‖ξ‖ ^ 2 ≤ ‖euclCoords.symm ξ‖ ^ 2 := by
        have := norm_nonneg ξ; nlinarith
      have hmul : ((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖
          ≤ ((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖ := by gcongr
      have hnn : (0:ℝ) ≤ ((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖ := by positivity
      nlinarith
    have hstep2 : (∫ ξ : Space,
          (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2)
        = ∫ y : EuclSpace, (((1 : ℝ) + ‖y‖ ^ 2) * ‖𝓕 v y‖) ^ 2 := by
      rw [integral_space_eq_euclSpace (fun ξ : Space =>
        (((1 : ℝ) + ‖euclCoords.symm ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2)]
      simp
    have hS : (0:ℝ) ≤ sobolevH2NormSq u := sobolevH2NormSq_nonneg u
    calc (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖𝓕 v (euclCoords.symm ξ)‖) ^ 2)
        ≤ ∫ y : EuclSpace, (((1 : ℝ) + ‖y‖ ^ 2) * ‖𝓕 v y‖) ^ 2 := hstep1.trans_eq hstep2
      _ ≤ C₁ * ∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2 := hplan v
      _ ≤ C₁ * (C₂ * sobolevH2NormSq u) := by
          have hh := hmod u
          rw [← hv] at hh
          nlinarith
      _ = C₁ * C₂ * sobolevH2NormSq u := by ring

/-- Concrete non-vacuous base case for the Fourier-majorant interface: the
zero Schwartz velocity is represented by the zero Fourier majorant.  Retained as
a Step-0e non-vacuity anchor for the majorant interface; the universal statement
above is now certified, so this is no longer the only inhabitant. -/
theorem besselFourierMajorant_zero :
    ∃ h : Space → ℝ,
      (∀ ξ : Space, 0 ≤ h ξ) ∧
      MemLp (fun ξ : Space => ((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) 2 ∧
      (∀ x : Space, ‖((0 : SchwartzVelocity) : Space → Space) x‖ ≤
        ∫ ξ : Space, h ξ) ∧
      (∫ ξ : Space, (((1 : ℝ) + ‖ξ‖ ^ 2) * h ξ) ^ 2) ≤
        sobolevH2NormSq (0 : SchwartzVelocity) := by
  refine ⟨fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro ξ
    exact le_rfl
  · simpa using (MemLp.zero (μ := volume) (p := (2 : ENNReal)))
  · intro x
    simp
  · simpa using sobolevH2NormSq_nonneg (0 : SchwartzVelocity)

/-- **[DERIVED from `exists_besselFourierMajorant`.]**  Agmon / Sobolev
embedding `H²(ℝ³) ↪ L^∞` (`s = 2 > 3/2 = n/2`); Majda–Bertozzi Lemma 3.2;
Agmon, *Lectures on Elliptic Boundary Value Problems*, Van Nostrand 1965;
Stein, *Singular Integrals*, Princeton 1970, Ch. V.  The sup norm of a Schwartz
field is dominated by the square root of its `H²` norm:
`‖u‖_∞ ≤ C·‖u‖_{H²}`.  This is the **sharp** derivative order for the embedding
used by the BKM assembly, one order below the `H³` control the criterion
actually carries.

The derivation is the classical two-line Fourier argument, now assembled from
certified parts: take the Fourier majorant density `h` supplied by
`exists_besselFourierMajorant`, bound `‖u(x)‖ ≤ ∫ h` by inversion, split
`h = (1+|ξ|²)⁻¹·((1+|ξ|²)h)` and apply
`integral_le_besselWeightMass_mul_sqrt`, whose weight has finite mass by
`integrable_inv_one_add_normSq_sq` — the `4 > 3` step that fails for `H¹`. -/
theorem exists_agmonSupBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (x : Space),
        ‖(⇑u) x‖ ≤ C * Real.sqrt (sobolevH2NormSq u) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := exists_besselFourierMajorant
  refine ⟨Real.sqrt besselWeightMass * Real.sqrt C₀ + 1, by positivity, ?_⟩
  intro u x
  obtain ⟨h, hnn, hmem, hsup, hplan⟩ := hC₀ u
  have hS : (0 : ℝ) ≤ Real.sqrt (sobolevH2NormSq u) := Real.sqrt_nonneg _
  have hstep : ∫ ξ : Space, h ξ ≤
      Real.sqrt besselWeightMass * Real.sqrt (C₀ * sobolevH2NormSq u) :=
    le_trans (integral_le_besselWeightMass_mul_sqrt hnn hmem)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hplan) (Real.sqrt_nonneg _))
  calc ‖(⇑u) x‖
      ≤ ∫ ξ : Space, h ξ := hsup x
    _ ≤ Real.sqrt besselWeightMass * Real.sqrt (C₀ * sobolevH2NormSq u) := hstep
    _ = (Real.sqrt besselWeightMass * Real.sqrt C₀) *
          Real.sqrt (sobolevH2NormSq u) := by
        rw [Real.sqrt_mul hC₀pos.le]; ring
    _ ≤ (Real.sqrt besselWeightMass * Real.sqrt C₀ + 1) *
          Real.sqrt (sobolevH2NormSq u) :=
        mul_le_mul_of_nonneg_right (by linarith) hS

/-- **[DERIVED from `exists_agmonSupBound`.]**  Agmon/Sobolev embedding, s = 3 > 3/2;
Majda–Bertozzi Lemma 3.2; est ~250 LOC.]**  The sup norm of a Schwartz field is
dominated by (the square root of) its `H³` norm: `‖u‖_∞ ≤ C·√Ms` for any
majorant `Ms ≥ ‖u‖²_{H³}`.  Closure route: Fourier inversion +
Cauchy–Schwarz against `(1+|ξ|²)^{-s}` (integrable for `s > 3/2`); needs the
Schwartz Fourier–Plancherel API, present in Mathlib, plus derivative-to-symbol
bookkeeping. -/
theorem sobolevEmbeddingDomination :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (Ms : ℝ), sobolevH3NormSq u ≤ Ms →
        ∀ x : Space, ‖(⇑u) x‖ ≤ C * Real.sqrt Ms := by
  obtain ⟨C, hCpos, hC⟩ := exists_agmonSupBound
  refine ⟨C, hCpos, ?_⟩
  intro u Ms hMs x
  exact le_mul_sqrt_of_le_majorant (le_of_lt hCpos) (hC u x)
    (le_trans (sobolevH2NormSq_le_sobolevH3NormSq u) hMs)

/-!
### The Morrey–Agmon Hölder seminorm bound (certified, no sorry)

`exists_agmonSupBound` controls the *size* of a Schwartz field by its `H²`
norm; the Biot–Savart near field in `exists_biotSavartLogTextbook` consumes
the *difference* version — a Hölder modulus of continuity at the same `H²`
order.  The derivative count is the point: bounding the near-field
cancellation `|ω(x-z) - ω(x)|` by `‖∇ω‖∞·‖z‖` costs a full extra derivative
of the vorticity and would push the log inequality onto `H⁴`, while a Hölder
bound at any exponent `s < 1/2` is available at exactly `H²` of `ω`, hence at
the `H³` of `u` that the BKM statement carries.  The exponent certified here
is `s = 1/4`: the frequency-side bound is the single global pointwise
inequality `min(2, 2π|ξ|h)² ≤ 4·√(2π|ξ|h)`, so the only dimensional input is
the weighted moment `∫ (1+‖ξ‖²)⁻²·√‖ξ‖ dξ < ∞` (radially
`∫₀^∞ r^{5/2}/(1+r²)² dr`, tail `∫^∞ r^{-3/2} dr`), discharged by the same
Japanese-bracket integrability that powers the Agmon chain, at exponent
`7/2 > 3`.

References: S. Agmon, *Lectures on Elliptic Boundary Value Problems*, Van
Nostrand 1965; Stein, *Singular Integrals and Differentiability Properties of
Functions*, Princeton 1970, Ch. V §3 (Bessel potentials) and Ch. II §4.
-/

/-- The Fourier character is `4π`-Lipschitz in its argument below the trivial
bound: `‖𝐞 a - 𝐞 b‖ ≤ min 2 (4π|a - b|)`.  The cap `2` handles the
large-phase regime; on `2π|a-b| ≤ 1` the linear bound is
`Complex.norm_exp_sub_one_le`. -/
private theorem norm_fourierChar_coe_sub_le (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖
      ≤ min 2 (4 * Real.pi * |a - b|) := by
  have hnorm1 : ∀ θ : ℝ, ‖(Real.fourierChar θ : ℂ)‖ = 1 := by
    intro θ
    exact mem_sphere_zero_iff_norm.mp (Real.fourierChar θ).property
  have hfactor : (Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)
      = (Real.fourierChar b : ℂ) * ((Real.fourierChar (a - b) : ℂ) - 1) := by
    have h1 : (Real.fourierChar a : ℂ)
        = (Real.fourierChar b : ℂ) * (Real.fourierChar (a - b) : ℂ) := by
      rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul,
        show b + (a - b) = a from by ring]
    rw [h1]; ring
  rw [hfactor, norm_mul, hnorm1 b, one_mul]
  have htriv : ‖(Real.fourierChar (a - b) : ℂ) - 1‖ ≤ 2 := by
    calc ‖(Real.fourierChar (a - b) : ℂ) - 1‖
        ≤ ‖(Real.fourierChar (a - b) : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hnorm1 (a - b), norm_one]; norm_num
  have hlin : 2 * Real.pi * |a - b| ≤ 1 →
      ‖(Real.fourierChar (a - b) : ℂ) - 1‖ ≤ 4 * Real.pi * |a - b| := by
    intro hz
    have harg : ‖(↑(2 * Real.pi * (a - b)) : ℂ) * Complex.I‖ = 2 * Real.pi * |a - b| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [Real.fourierChar_apply]
    calc ‖Complex.exp (↑(2 * Real.pi * (a - b)) * Complex.I) - 1‖
        ≤ 2 * ‖(↑(2 * Real.pi * (a - b)) : ℂ) * Complex.I‖ :=
          Complex.norm_exp_sub_one_le (harg ▸ hz)
      _ = 4 * Real.pi * |a - b| := by rw [harg]; ring
  by_cases hc : 2 * Real.pi * |a - b| ≤ 1
  · exact le_min htriv (hlin hc)
  · have h2 : (2 : ℝ) ≤ 4 * Real.pi * |a - b| := by
      have hc' := not_le.mp hc
      nlinarith [Real.pi_pos, abs_nonneg (a - b)]
    rw [min_eq_left h2]
    exact htriv

/-- The squared minimum bound underlying the Hölder exponent `1/4`:
`(min 2 (2t))² ≤ 4√t` for `t ≥ 0`.  This one inequality replaces the
frequency split at `|ξ| ~ h⁻¹`: the near-field uses `min(2, 2t) ≤ 2t` and the
far field `min ≤ 2`, and `t² ≤ √t` on `[0,1]` interpolates between them at
the price of the sub-endpoint exponent. -/
private theorem min_two_two_mul_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (min 2 (2 * t)) ^ 2 ≤ 4 * Real.sqrt t := by
  have h1 : min 2 (2 * t) ≤ 2 * min 1 t := by
    by_cases hc : t ≤ 1
    · rw [min_eq_right (by nlinarith : 2 * t ≤ 2), min_eq_right hc]
    · rw [not_le] at hc
      rw [min_eq_left (by nlinarith : (2 : ℝ) ≤ 2 * t), min_eq_left (le_of_lt hc)]
      norm_num
  have h2 : (min 1 t) ^ 2 ≤ Real.sqrt t := by
    by_cases hc : t ≤ 1
    · rw [min_eq_right hc]
      have ht4 : t ^ 4 ≤ t := by
        have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht hc
        calc t ^ 4 = t * t ^ 3 := by ring
          _ ≤ t * 1 := mul_le_mul_of_nonneg_left h3 ht
          _ = t := mul_one t
      rw [show t ^ 2 = Real.sqrt ((t ^ 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      refine Real.sqrt_le_sqrt ?_
      rw [show (t ^ 2) ^ 2 = t ^ 4 from by ring]
      exact ht4
    · rw [not_le] at hc
      rw [min_eq_left (le_of_lt hc)]
      calc (1 : ℝ) ^ 2 = 1 := by ring
        _ = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt t := Real.sqrt_le_sqrt (le_of_lt hc)
  have hnn : (0 : ℝ) ≤ min 2 (2 * t) := le_min (by norm_num) (by nlinarith)
  calc (min 2 (2 * t)) ^ 2 ≤ (2 * min 1 t) ^ 2 := pow_le_pow_left₀ hnn h1 2
    _ = 4 * (min 1 t) ^ 2 := by ring
    _ ≤ 4 * Real.sqrt t := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- The quartic Bessel weight on the Euclidean model (the `EuclSpace`
counterpart of `integrable_inv_one_add_normSq_sq`). -/
private theorem integrable_bessel_sq_inv_eucl :
    Integrable (fun ξ : EuclSpace => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) volume := by
  have hfr : (Module.finrank ℝ EuclSpace : ℝ) < 4 := by
    have h3 : Module.finrank ℝ EuclSpace = 3 := by simp
    rw [h3]; norm_num
  have h := integrable_rpow_neg_one_add_norm_sq (E := EuclSpace) (μ := volume)
    (r := 4) hfr
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  show ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹
  rw [show (-(4 : ℝ)) / 2 = -(2 : ℕ) by norm_num, Real.rpow_neg (by positivity),
    Real.rpow_natCast]

/-- The Bessel-weighted half-moment is finite on `ℝ³`:
`ξ ↦ √‖ξ‖·(1+‖ξ‖²)⁻²` is integrable (radially `∫₀^∞ r^{5/2}(1+r²)⁻² dr`,
tail `∫^∞ r^{-3/2} dr`).  This is the only dimensional input to the Morrey
bound; it comes from the same Japanese-bracket integrability as the Agmon
weight, at exponent `7/2 > 3`. -/
private theorem integrable_sqrt_norm_mul_bessel_sq_inv :
    Integrable (fun ξ : EuclSpace => Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹)
      volume := by
  have hfr : (Module.finrank ℝ EuclSpace : ℝ) < 7 / 2 := by
    have h3 : Module.finrank ℝ EuclSpace = 3 := by simp
    rw [h3]; norm_num
  have h := integrable_rpow_neg_one_add_norm_sq (E := EuclSpace) (μ := volume)
    (r := 7 / 2) hfr
  have hcont : Continuous fun ξ : EuclSpace =>
      Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
    refine (Real.continuous_sqrt.comp continuous_norm).mul ?_
    apply Continuous.inv₀
    · fun_prop
    · intro ξ; positivity
  refine h.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹‖
    ≤ (1 + ‖ξ‖ ^ 2) ^ (-(7 / 2 : ℝ) / 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hx : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have hw1 : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have hs1 : ‖ξ‖ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
    conv_lhs => rw [show ‖ξ‖ = Real.sqrt (‖ξ‖ ^ 2) from (Real.sqrt_sq hx).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖ξ‖])
  have hsqrt : Real.sqrt ‖ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (1 / 4 : ℝ) := by
    calc Real.sqrt ‖ξ‖ ≤ Real.sqrt (Real.sqrt (1 + ‖ξ‖ ^ 2)) := Real.sqrt_le_sqrt hs1
      _ = (1 + ‖ξ‖ ^ 2) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hw1.le]
        congr 1
        norm_num
  calc Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹
      = Real.sqrt ‖ξ‖ * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℕ) : ℝ) := by
        rw [Real.rpow_neg hw1.le, Real.rpow_natCast]
    _ ≤ (1 + ‖ξ‖ ^ 2) ^ (1 / 4 : ℝ) * (1 + ‖ξ‖ ^ 2) ^ (-(2 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hw1.le _)
    _ = (1 + ‖ξ‖ ^ 2) ^ (-(7 / 2) / 2 : ℝ) := by
        rw [← Real.rpow_add hw1, show ((1 : ℝ) / 4 + -(2 : ℕ)) = -(7 / 2) / 2 by norm_num]

/-- The quartic Bessel weight times the square of a continuous factor bounded
by `2` is integrable (dominated by `4` times the weight). -/
private theorem integrable_bessel_mul_sq {φ : EuclSpace → ℝ} (hφcont : Continuous φ)
    (hφnn : ∀ ξ, 0 ≤ φ ξ) (hφ2 : ∀ ξ, φ ξ ≤ 2) :
    Integrable (fun ξ : EuclSpace => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2)
      volume := by
  have hcont : Continuous fun ξ : EuclSpace => (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2 := by
    refine (Continuous.inv₀ (by fun_prop) (fun ξ => by positivity)).mul (hφcont.pow 2)
  refine (integrable_bessel_sq_inv_eucl.const_mul 4).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  show ‖(((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2‖ ≤ 4 * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hφsq : (φ ξ) ^ 2 ≤ 4 := by
    have := pow_le_pow_left₀ (hφnn ξ) (hφ2 ξ) 2
    nlinarith
  calc (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2 ≤ (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * 4 :=
        mul_le_mul_of_nonneg_left hφsq (by positivity)
    _ = 4 * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by ring

/-- Cauchy–Schwarz against the Bessel weight with an extra bounded factor
kept in the weight term: for continuous `0 ≤ φ ≤ 2` and nonneg `ψ` with
`(1+‖ξ‖²)·ψ` in `L²`,

  `∫ φ·ψ ≤ √(∫ (1+‖ξ‖²)⁻²·φ²) · √(∫ ((1+‖ξ‖²)·ψ)²)`.

This is `integral_le_besselWeightMass_mul_sqrt` with the phase factor
retained in the first factor — the `L²` pairing is unchanged; only the first
factor is sharpened from the full weight mass to the phase-weighted one. -/
private theorem integral_phase_mul_le_sqrt_weighted
    {φ : EuclSpace → ℝ} (hφcont : Continuous φ) (hφnn : ∀ ξ, 0 ≤ φ ξ)
    (hφ2 : ∀ ξ, φ ξ ≤ 2)
    {ψ : EuclSpace → ℝ} (hψnn : ∀ ξ, 0 ≤ ψ ξ)
    (hψmem : MemLp (fun ξ : EuclSpace => ((1 : ℝ) + ‖ξ‖ ^ 2) * ψ ξ) 2 volume) :
    ∫ ξ : EuclSpace, φ ξ * ψ ξ ≤
      Real.sqrt (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2) *
        Real.sqrt (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) * ψ ξ) ^ 2) := by
  have hpq : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hfmem : MemLp (fun ξ : EuclSpace => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * φ ξ) 2 volume := by
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact ((Continuous.inv₀ (by fun_prop) (fun ξ => by positivity)).mul
        hφcont).aestronglyMeasurable
    · refine (integrable_bessel_mul_sq hφcont hφnn hφ2).congr
        (Filter.Eventually.of_forall fun ξ => ?_)
      show (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (φ ξ) ^ 2
        = (((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * φ ξ) ^ 2
      rw [mul_pow, inv_pow]
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq
    (f := fun ξ : EuclSpace => ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * φ ξ)
    (g := fun ξ : EuclSpace => ((1 : ℝ) + ‖ξ‖ ^ 2) * ψ ξ)
    (Filter.Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hφnn ξ))
    (Filter.Eventually.of_forall fun ξ => mul_nonneg (by positivity) (hψnn ξ))
    (by simpa using hfmem) (by simpa using hψmem)
  have hprod : ∀ ξ : EuclSpace,
      ((1 : ℝ) + ‖ξ‖ ^ 2)⁻¹ * φ ξ * (((1 : ℝ) + ‖ξ‖ ^ 2) * ψ ξ) = φ ξ * ψ ξ := by
    intro ξ
    field_simp
  simp only [hprod] at key
  have hrw : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
    intro y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [hrw] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [mul_pow, inv_pow] using key

/-- The phase-weighted Bessel mass is `O(√h)`: with `w = (1+‖ξ‖²)⁻²`,
`∫ w·min(2, 4π‖ξ‖h)² ≤ 4√(2πh)·∫ w·√‖ξ‖`.  This is the whole frequency
localization of the Morrey argument in one global pointwise step. -/
private theorem integral_weighted_min_sq_le {h : ℝ} (hh : 0 ≤ h) :
    ∫ ξ : EuclSpace,
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2
      ≤ 4 * Real.sqrt (2 * Real.pi * h) *
          ∫ ξ : EuclSpace, Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ := by
  have hmincont : Continuous fun ξ : EuclSpace => min 2 (4 * Real.pi * ‖ξ‖ * h) := by
    fun_prop
  have hpt : ∀ ξ : EuclSpace,
      (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2
        ≤ 4 * Real.sqrt (2 * Real.pi * h) *
            (Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) := by
    intro ξ
    have hsq := min_two_two_mul_sq_le (t := 2 * Real.pi * ‖ξ‖ * h) (by positivity)
    rw [show 2 * (2 * Real.pi * ‖ξ‖ * h) = 4 * Real.pi * ‖ξ‖ * h from by ring] at hsq
    have hsqrt : Real.sqrt (2 * Real.pi * ‖ξ‖ * h)
        = Real.sqrt (2 * Real.pi * h) * Real.sqrt ‖ξ‖ := by
      rw [show 2 * Real.pi * ‖ξ‖ * h = (2 * Real.pi * h) * ‖ξ‖ from by ring]
      exact Real.sqrt_mul (by positivity) _
    rw [hsqrt] at hsq
    calc (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2
        ≤ (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ *
            (4 * (Real.sqrt (2 * Real.pi * h) * Real.sqrt ‖ξ‖)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 4 * Real.sqrt (2 * Real.pi * h) *
            (Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) := by ring
  have hintR : Integrable (fun ξ : EuclSpace =>
      4 * Real.sqrt (2 * Real.pi * h) *
        (Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹)) volume :=
    integrable_sqrt_norm_mul_bessel_sq_inv.const_mul _
  calc ∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2
      ≤ ∫ ξ : EuclSpace, 4 * Real.sqrt (2 * Real.pi * h) *
          (Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹) :=
        integral_mono_ae
          (integrable_bessel_mul_sq hmincont (fun ξ => le_min (by norm_num) (by positivity))
            (fun ξ => min_le_left _ _))
          hintR (Filter.Eventually.of_forall hpt)
    _ = 4 * Real.sqrt (2 * Real.pi * h) *
          ∫ ξ : EuclSpace, Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ :=
        integral_const_mul _ _

/-- The inverse Fourier transform difference, bounded by the phase-twisted
`L¹` mass of the transform: `𝓕⁻g(y₁) - 𝓕⁻g(y₂) = ∫ (𝐞⟪ξ,y₁⟫ - 𝐞⟪ξ,y₂⟫)·g(ξ)
dξ`, then norm of integral ≤ integral of norm. -/
private theorem norm_fourierInv_sub_le {g : EuclSpace → CxSpace}
    (hgcont : Continuous g) (hg : Integrable g volume) (y₁ y₂ : EuclSpace) :
    ‖𝓕⁻ g y₁ - 𝓕⁻ g y₂‖ ≤
      ∫ ξ : EuclSpace,
        ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
          * ‖g ξ‖ := by
  have hφcont : Continuous fun ξ : EuclSpace =>
      ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
        * ‖g ξ‖ := by
    fun_prop
  have hint : ∀ y : EuclSpace,
      Integrable (fun ξ : EuclSpace => Real.fourierChar (inner ℝ ξ y) • g ξ) volume := by
    intro y
    have h := (Real.fourierIntegral_convergent_iff (μ := volume) (f := g) (-y)).mpr hg
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    show Real.fourierChar (-inner ℝ ξ (-y)) • g ξ = Real.fourierChar (inner ℝ ξ y) • g ξ
    rw [inner_neg_right, neg_neg]
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← integral_sub (hint y₁) (hint y₂)]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_ae ((hint y₁).sub (hint y₂)).norm
    ((hg.norm.const_mul 2).mono' hφcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_))
    (Filter.Eventually.of_forall fun ξ => ?_)
  · have hb : ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ)
        - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖ ≤ 2 :=
      le_trans (norm_fourierChar_coe_sub_le _ _) (min_le_left _ _)
    show ‖‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
        * ‖g ξ‖‖ ≤ 2 * ‖g ξ‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · show ‖Real.fourierChar (inner ℝ ξ y₁) • g ξ
        - Real.fourierChar (inner ℝ ξ y₂) • g ξ‖
      ≤ ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
        * ‖g ξ‖
    have heq : Real.fourierChar (inner ℝ ξ y₁) • g ξ
        - Real.fourierChar (inner ℝ ξ y₂) • g ξ
        = ((Real.fourierChar (inner ℝ ξ y₁) : ℂ)
            - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)) • g ξ := by
      rw [Circle.smul_def, Circle.smul_def, ← sub_smul]
    rw [heq, norm_smul]

/-- **Morrey–Agmon on the Euclidean model (certified, no sorry).**  For a
Schwartz map `v : 𝓢(EuclSpace, CxSpace)` the Hölder seminorm at exponent
`1/4` is controlled by the `H²` energy: the inversion difference is
phase-twisted (`norm_fourierInv_sub_le`), the phase is `min(2, 4π‖ξ‖h)`
(`norm_fourierChar_coe_sub_le` with `abs_real_inner_le_norm`), Cauchy–Schwarz
against the Bessel weight splits off `√(∫ w·min²) = O(h^{1/4})`
(`integral_weighted_min_sq_le`), and the surviving weighted `L²` mass of
`𝓕 v` is weighted Plancherel (`exists_weighted_plancherel`). -/
private theorem exists_morrey_euclModel :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (v : SV) (y₁ y₂ : EuclSpace),
      ‖v y₁ - v y₂‖ ≤
        C₁ * Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
          ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) * ‖y₁ - y₂‖ ^ (1 / 4 : ℝ) := by
  obtain ⟨Cp, hCppos, hplan⟩ := exists_weighted_plancherel
  set M : ℝ := ∫ ξ : EuclSpace, Real.sqrt ‖ξ‖ * (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ with hMdef
  have hMnn : 0 ≤ M := integral_nonneg fun ξ => by positivity
  refine ⟨Real.sqrt (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt M * Real.sqrt Cp + 1,
    by positivity, fun v y₁ y₂ => ?_⟩
  have hv : ∀ y : EuclSpace, v y = 𝓕⁻ (⇑(𝓕 v : SV)) y := by
    intro y
    have hinv : (𝓕⁻ (𝓕 v : SV) : SchwartzMap EuclSpace CxSpace) = v :=
      FourierPair.fourierInv_fourier_eq v
    conv_lhs => rw [← hinv]
    rw [SchwartzMap.fourierInv_coe]
  have hgint : Integrable (⇑(𝓕 v : SV)) volume := (𝓕 v : SV).integrable
  rw [hv y₁, hv y₂]
  set h : ℝ := ‖y₁ - y₂‖ with hhdef
  have hhnn : 0 ≤ h := norm_nonneg _
  have hφcont : Continuous fun ξ : EuclSpace =>
      ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖ := by
    fun_prop
  have hφmin : ∀ ξ : EuclSpace,
      ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
        ≤ min 2 (4 * Real.pi * ‖ξ‖ * h) := by
    intro ξ
    refine le_trans (norm_fourierChar_coe_sub_le _ _) (min_le_min le_rfl ?_)
    have hinner : |inner ℝ ξ y₁ - inner ℝ ξ y₂| ≤ ‖ξ‖ * h := by
      rw [← inner_sub_right]
      exact abs_real_inner_le_norm _ _
    calc 4 * Real.pi * |inner ℝ ξ y₁ - inner ℝ ξ y₂|
        ≤ 4 * Real.pi * (‖ξ‖ * h) := mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 4 * Real.pi * ‖ξ‖ * h := by ring
  have hcs := integral_phase_mul_le_sqrt_weighted hφcont (fun ξ => norm_nonneg _)
    (fun ξ => le_trans (norm_fourierChar_coe_sub_le _ _) (min_le_left _ _))
    (fun ξ => norm_nonneg _) (memLp_weight_fourier v)
  have hA : (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ *
        ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖ ^ 2)
      ≤ ∫ ξ : EuclSpace,
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ * (min 2 (4 * Real.pi * ‖ξ‖ * h)) ^ 2 :=
    integral_mono_ae
      (integrable_bessel_mul_sq hφcont (fun ξ => norm_nonneg _)
        (fun ξ => le_trans (norm_fourierChar_coe_sub_le _ _) (min_le_left _ _)))
      (integrable_bessel_mul_sq (by fun_prop) (fun ξ => le_min (by norm_num) (by positivity))
        (fun ξ => min_le_left _ _))
      (Filter.Eventually.of_forall fun ξ =>
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (hφmin ξ) 2) (by positivity))
  have hfirst := le_trans hA (integral_weighted_min_sq_le hhnn)
  have hsecond : (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖(𝓕 v : SV) ξ‖) ^ 2)
      ≤ Cp * (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
        ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) := hplan v
  have hsqrtM : Real.sqrt (4 * Real.sqrt (2 * Real.pi * h) * M)
      = Real.sqrt (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt M * h ^ (1 / 4 : ℝ) := by
    have e1 : Real.sqrt (2 * Real.pi * h) = Real.sqrt (2 * Real.pi) * Real.sqrt h :=
      Real.sqrt_mul (by positivity) _
    rw [e1]
    rw [show (4 : ℝ) * (Real.sqrt (2 * Real.pi) * Real.sqrt h) * M
        = (4 * Real.sqrt (2 * Real.pi) * M) * Real.sqrt h from by ring]
    rw [Real.sqrt_mul (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hMnn),
      Real.sqrt_mul (mul_nonneg (by positivity) (Real.sqrt_nonneg _))]
    have e3 : Real.sqrt (Real.sqrt h) = h ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hhnn]
      congr 1
      norm_num
    rw [e3]
  have hsqrtCp : Real.sqrt (Cp * (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
        ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2))
      = Real.sqrt Cp * Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
        ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) :=
    Real.sqrt_mul hCppos.le _
  calc ‖𝓕⁻ (⇑(𝓕 v : SV)) y₁ - 𝓕⁻ (⇑(𝓕 v : SV)) y₂‖
      ≤ ∫ ξ : EuclSpace,
          ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ) - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖
            * ‖(𝓕 v : SV) ξ‖ :=
        norm_fourierInv_sub_le (𝓕 v : SV).continuous hgint y₁ y₂
    _ ≤ Real.sqrt (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) ^ 2)⁻¹ *
            ‖(Real.fourierChar (inner ℝ ξ y₁) : ℂ)
              - (Real.fourierChar (inner ℝ ξ y₂) : ℂ)‖ ^ 2) *
          Real.sqrt (∫ ξ : EuclSpace, (((1 : ℝ) + ‖ξ‖ ^ 2) * ‖(𝓕 v : SV) ξ‖) ^ 2) := hcs
    _ ≤ Real.sqrt (4 * Real.sqrt (2 * Real.pi * h) * M) *
          Real.sqrt (Cp * (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2)) :=
        mul_le_mul (Real.sqrt_le_sqrt hfirst) (Real.sqrt_le_sqrt hsecond)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt M * Real.sqrt Cp) *
          Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) * h ^ (1 / 4 : ℝ) := by
        rw [hsqrtM, hsqrtCp]; ring
    _ ≤ (Real.sqrt (4 * Real.sqrt (2 * Real.pi)) * Real.sqrt M * Real.sqrt Cp + 1) *
          Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑v) y‖ ^ 2) * h ^ (1 / 4 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hhnn _)
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-- **[DERIVED from the certified Fourier chain above.]**  **Morrey–Agmon:
`H²(ℝ³) ↪ C^{0,1/4}` for Schwartz fields (certified, no sorry).**  The
Hölder seminorm at exponent `1/4` is dominated by the `H²` norm:
`‖u x - u y‖ ≤ C·√(sobolevH2NormSq u)·‖x - y‖^{1/4}` — the difference
companion of `exists_agmonSupBound` at the same derivative order.

This is the near-field input the BKM log inequality consumes through the
cancellation `ω(x-z) - ω(x)`: applied to the vorticity components (whose `H²`
energies are bounded by `sobolevH3NormSq u`, one derivative up), it upgrades
the certified near-field layer `integral_norm_mul_bsKernelScalar_ball_le`
from `O(ρ·‖∇ω‖∞)` — which would cost `H⁴` — to `O(ρ^{1/4}·‖u‖_{H³})`, the
order the cutoff optimisation at `ρ ≈ ‖u‖_{H³}^{-4}` turns into the
`log(e + ‖u‖_{H³})` factor.  What remains residual for
`exists_biotSavartLogTextbook` is the Biot–Savart representation
`∇u = PV(∇K ∗ ω)` itself (including its local term). -/
theorem exists_agmonMorreyBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SchwartzVelocity) (x y : Space),
      ‖(⇑u) x - (⇑u) y‖ ≤
        C * Real.sqrt (sobolevH2NormSq u) * ‖x - y‖ ^ (1 / 4 : ℝ) := by
  obtain ⟨C₁, hC₁pos, hmor⟩ := exists_morrey_euclModel
  obtain ⟨C₂, hC₂pos, hmod⟩ := exists_euclModel_h2_bound
  refine ⟨C₁ * Real.sqrt C₂ * ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ) + 1,
    by positivity, fun u x y => ?_⟩
  have hnorm : ‖(⇑u) x - (⇑u) y‖
      ≤ ‖euclModel u (euclCoords.symm x) - euclModel u (euclCoords.symm y)‖ := by
    have heq : euclModel u (euclCoords.symm x) - euclModel u (euclCoords.symm y)
        = realToCx ((⇑u) x - (⇑u) y) := by
      rw [euclModel_apply, euclModel_apply, ContinuousLinearEquiv.apply_symm_apply,
        ContinuousLinearEquiv.apply_symm_apply]
      exact (map_sub realToCx _ _).symm
    rw [heq]
    exact norm_le_norm_realToCx _
  have hdist : ‖euclCoords.symm x - euclCoords.symm y‖
      ≤ ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ * ‖x - y‖ := by
    have hh := ContinuousLinearMap.le_opNorm
      (euclCoords.symm : Space →L[ℝ] EuclSpace) (x - y)
    rwa [ContinuousLinearEquiv.coe_coe, map_sub] at hh
  have hpow : ‖euclCoords.symm x - euclCoords.symm y‖ ^ (1 / 4 : ℝ)
      ≤ ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ)
          * ‖x - y‖ ^ (1 / 4 : ℝ) := by
    calc ‖euclCoords.symm x - euclCoords.symm y‖ ^ (1 / 4 : ℝ)
        ≤ (‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ * ‖x - y‖) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hdist (by norm_num)
      _ = ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ)
            * ‖x - y‖ ^ (1 / 4 : ℝ) :=
          Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  calc ‖(⇑u) x - (⇑u) y‖
      ≤ ‖euclModel u (euclCoords.symm x) - euclModel u (euclCoords.symm y)‖ := hnorm
    _ ≤ C₁ * Real.sqrt (∑ n ∈ Finset.range 3, ∫ y : EuclSpace,
            ‖iteratedFDeriv ℝ n (⇑(euclModel u)) y‖ ^ 2)
          * ‖euclCoords.symm x - euclCoords.symm y‖ ^ (1 / 4 : ℝ) :=
        hmor _ _ _
    _ ≤ C₁ * Real.sqrt (C₂ * sobolevH2NormSq u)
          * (‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ)
            * ‖x - y‖ ^ (1 / 4 : ℝ)) := by
        refine mul_le_mul ?_ hpow (Real.rpow_nonneg (norm_nonneg _) _)
          (mul_nonneg hC₁pos.le (Real.sqrt_nonneg _))
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (hmod u)) hC₁pos.le
    _ = (C₁ * Real.sqrt C₂ * ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ))
          * Real.sqrt (sobolevH2NormSq u) * ‖x - y‖ ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_mul hC₂pos.le]; ring
    _ ≤ (C₁ * Real.sqrt C₂ * ‖(euclCoords.symm : Space →L[ℝ] EuclSpace)‖ ^ (1 / 4 : ℝ) + 1)
          * Real.sqrt (sobolevH2NormSq u) * ‖x - y‖ ^ (1 / 4 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-- A classical solution whose nonnegative-time slices are Schwartz fields.
This is the regularity frame in which the `H³` energy method operates; the
persistence of Schwartz class itself is standard for smooth bounded-energy
solutions (rapid decay propagates; Majda–Bertozzi §3.1–3.2). -/
structure SchwartzSlicedSolution (ν : ℝ) (u₀ : SchwartzVelocity) where
  velocity : VelocityEvolution
  pressure : PressureEvolution
  slice : ℝ → SchwartzVelocity
  slice_eq : ∀ t : ℝ, 0 ≤ t → ⇑(slice t) = velocity t
  solution : IsClassicalSolution ν zeroForce u₀ velocity pressure

open scoped ContDiff Pointwise in
/-- **Slice–joint derivative transfer (certified, no sorry).**  At a
nonnegative time `t`, the full iterated spatial derivative of the slice
`velocity t` equals the joint within-derivative of the spacetime map on the
closed half-space `Ici 0 ×ˢ univ`, composed with the spatial inclusion
`y ↦ (0, y)`.  The proof factors the slice as
`joint ∘ ((t, 0) + ·) ∘ ContinuousLinearMap.inr` and combines
`ContinuousLinearMap.iteratedFDerivWithin_comp_right` with the translation
invariance `iteratedFDerivWithin_comp_add_left`; the shifted set
`{z | (t, 0) + z ∈ Ici 0 ×ˢ univ} = Ici (-t) ×ˢ univ` keeps unique
differentiability. -/
theorem iteratedFDeriv_slice_eq_within_compContinuousLinearMap
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    iteratedFDeriv ℝ n (S.velocity t) x =
      (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => S.velocity z.1 z.2)
        (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)) (t, x)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ Space) := by
  classical
  have hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => S.velocity z.1 z.2)
      (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)) :=
    S.solution.velocity_smooth
  set a : ℝ × Space := (t, 0) with hadef
  set σ : Set (ℝ × Space) :=
    (fun z : ℝ × Space => a + z) ⁻¹'
      (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)) with hσdef
  have hσ : σ = Set.Ici (-t) ×ˢ (Set.univ : Set Space) := by
    ext ⟨t', y⟩
    simp only [hσdef, Set.mem_preimage, Set.mem_prod, Set.mem_Ici, Set.mem_univ,
      and_true, hadef, Prod.mk_add_mk]
    constructor <;> intro h <;> linarith
  have hσuniq : UniqueDiffOn ℝ σ := by
    rw [hσ]
    exact (uniqueDiffOn_Ici _).prod uniqueDiffOn_univ
  have hmem : ∀ y : Space, (ContinuousLinearMap.inr ℝ ℝ Space) y ∈ σ := by
    intro y
    rw [hσ, ContinuousLinearMap.inr_apply]
    exact Set.mem_prod.mpr ⟨by simpa using neg_nonpos.mpr ht, Set.mem_univ y⟩
  have hpre : (ContinuousLinearMap.inr ℝ ℝ Space) ⁻¹' σ = Set.univ :=
    eq_univ_of_forall hmem
  have hpreuniq : UniqueDiffOn ℝ ((ContinuousLinearMap.inr ℝ ℝ Space) ⁻¹' σ) := by
    rw [hpre]; exact uniqueDiffOn_univ
  have hmap : (ContinuousLinearMap.inr ℝ ℝ Space) x ∈ σ := hmem x
  have hsmooth : ContDiffOn ℝ ∞
      ((fun z : ℝ × Space => S.velocity z.1 z.2) ∘ fun z => a + z) σ :=
    hf.comp (contDiffOn_const.add contDiffOn_id) (Subset.refl _)
  have hcomp := (ContinuousLinearMap.inr ℝ ℝ Space).iteratedFDerivWithin_comp_right
      hsmooth hσuniq hpreuniq hmap (show n ≤ ∞ from mod_cast le_top)
  have hfun : (((fun z : ℝ × Space => S.velocity z.1 z.2) ∘ (fun z => a + z)) ∘
      (ContinuousLinearMap.inr ℝ ℝ Space)) = S.velocity t := by
    funext y
    simp [Function.comp_apply, hadef, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk]
  have hshift : iteratedFDerivWithin ℝ n
      ((fun z : ℝ × Space => S.velocity z.1 z.2) ∘ (fun z => a + z)) σ
      ((ContinuousLinearMap.inr ℝ ℝ Space) x)
      = iteratedFDerivWithin ℝ n (fun z : ℝ × Space => S.velocity z.1 z.2)
        (a +ᵥ σ) (a + (ContinuousLinearMap.inr ℝ ℝ Space) x) := by
    have h := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ)
      (f := fun z : ℝ × Space => S.velocity z.1 z.2) (s := σ) n a
      ((ContinuousLinearMap.inr ℝ ℝ Space) x)
    simpa [Function.comp_def] using h
  have hσs : a +ᵥ σ = (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)) := by
    rw [hσdef]
    ext z
    constructor
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      apply Set.mem_vadd_set.mpr
      exact ⟨z - a, by simpa using hz, by simp [vadd_eq_add]⟩
  have hpoint : a + (ContinuousLinearMap.inr ℝ ℝ Space) x = (t, x) := by
    rw [hadef, ContinuousLinearMap.inr_apply, Prod.mk_add_mk]
    simp
  rw [hpre, iteratedFDerivWithin_univ, hfun, hshift, hσs, hpoint] at hcomp
  exact hcomp

open scoped ContDiff in
/-- **Fixed-point time continuity of every spatial slice derivative
(certified, no sorry).**  For a Schwartz-sliced classical solution, each
fixed `x` the map `t ↦ ‖D^n u(t, x)‖²` is continuous on nonnegative time.
This uses only joint half-space smoothness: the joint within-derivative is
continuous on the closed half-space
(`ContDiffOn.continuousOn_iteratedFDerivWithin`), post-composition with the
spatial inclusion is continuous (`compContinuousLinearMapL`), restriction to
the curve `t ↦ (t, x)` preserves continuity, and
`iteratedFDeriv_slice_eq_within_compContinuousLinearMap` identifies the
result with the slice's own iterated derivative; `slice_eq` transports to the
Schwartz slices.  No PDE input — the genuinely PDE-dependent half of
`exists_locallyUniformSliceDecay` is the uniform decay bound. -/
theorem sliceIteratedFDeriv_continuousOn
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
    (n : ℕ) (x : Space) :
    ContinuousOn (fun t => ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2)
      (Set.Ici 0) := by
  have hA : ContinuousOn
      (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => S.velocity z.1 z.2)
        (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)))
      (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)) :=
    S.solution.velocity_smooth.continuousOn_iteratedFDerivWithin
      (show n ≤ ∞ from mod_cast le_top)
      ((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ)
  have hB : ContinuousOn
      (fun z : ℝ × Space => (iteratedFDerivWithin ℝ n
          (fun z : ℝ × Space => S.velocity z.1 z.2)
          (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)) z).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inr ℝ ℝ Space))
      (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => ContinuousLinearMap.inr ℝ ℝ Space)).continuous.comp_continuousOn hA
  have hC : ContinuousOn
      (fun t : ℝ => (iteratedFDerivWithin ℝ n
          (fun z : ℝ × Space => S.velocity z.1 z.2)
          (Set.Ici (0:ℝ) ×ˢ (Set.univ : Set Space)) (t, x)).compContinuousLinearMap
            (fun _ => ContinuousLinearMap.inr ℝ ℝ Space))
      (Set.Ici 0) := by
    apply hB.comp (continuousOn_id.prodMk continuousOn_const)
    intro t ht
    exact ⟨ht, Set.mem_univ x⟩
  have hD : ContinuousOn (fun t : ℝ => iteratedFDeriv ℝ n (S.velocity t) x)
      (Set.Ici 0) := by
    apply hC.congr
    intro t ht
    exact iteratedFDeriv_slice_eq_within_compContinuousLinearMap S n ht x
  apply ((hD.norm).pow 2).congr
  intro t ht
  show ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2 =
    ‖iteratedFDeriv ℝ n (S.velocity t) x‖ ^ 2
  rw [S.slice_eq t ht]

/-- **Rapid decay of every Schwartz iterated derivative, in the quartic weight
the BKM dominated-convergence layer actually consumes.**  For each order `n`,

  `‖D^n f x‖² ≤ K · (1 + ‖x‖)^{-4}`  for all `x`,

with `K = 8·(C₀² + C₄·C₀)` assembled from the two Schwartz seminorm bounds
`f.decay 0 n` and `f.decay 4 n`.  The factor `8` is the sharp comparison
`(1 + r)⁴ ≤ 8·(1 + r⁴)` on `r ≥ 0`, with equality at `r = 1`.

This is the order-`n`, `rpow`-weight strengthening of
`GalerkinSpaceEquicontinuity.schwartz_norm_sq_decay`, which covers only `n = 0`
in the `D/(1 + ‖x‖⁴)` normalisation. -/
theorem schwartz_iteratedFDeriv_sq_decay {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : SchwartzMap Space F) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Space,
      ‖iteratedFDeriv ℝ n f x‖ ^ 2 ≤ K * (1 + ‖x‖) ^ (-4 : ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ := f.decay 0 n
  obtain ⟨C4, hC4pos, hC4⟩ := f.decay 4 n
  have h0 : ∀ x : Space, ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C0 := by
    intro x; simpa using hC0 x
  have h4 : ∀ x : Space, ‖x‖ ^ 4 * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ C4 := by
    intro x; simpa using hC4 x
  refine ⟨8 * (C0 ^ 2 + C4 * C0), by positivity, fun x => ?_⟩
  have hxpos : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hrw : (1 + ‖x‖) ^ (-4 : ℝ) = ((1 + ‖x‖) ^ (4 : ℕ))⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hxpos.le,
      Real.rpow_natCast]
  rw [hrw, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖x‖) ^ (4 : ℕ))]
  have hcmp : (1 + ‖x‖) ^ (4 : ℕ) ≤ 8 * (1 + ‖x‖ ^ 4) := by
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1), sq_nonneg (‖x‖ + 1),
      sq_nonneg (‖x‖ ^ 2 - 1), sq_nonneg (‖x‖ ^ 2 - ‖x‖)]
  have hkey : ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖ ^ 4) ≤ C0 ^ 2 + C4 * C0 := by
    calc ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖ ^ 4)
        = ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2
            + (‖x‖ ^ 4 * ‖iteratedFDeriv ℝ n (⇑f) x‖) * ‖iteratedFDeriv ℝ n (⇑f) x‖ := by
          ring
      _ ≤ C0 ^ 2 + C4 * C0 :=
          add_le_add (pow_le_pow_left₀ (norm_nonneg _) (h0 x) 2)
            (mul_le_mul (h4 x) (h0 x) (norm_nonneg _) hC4pos.le)
  calc ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖) ^ (4 : ℕ)
      ≤ ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (8 * (1 + ‖x‖ ^ 4)) :=
        mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = 8 * (‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖ ^ 4)) := by ring
    _ ≤ 8 * (C0 ^ 2 + C4 * C0) := by linarith

/-- **The fixed-time half of `exists_sliceLocallyUniformDecayBound`, certified.**
At each *single* nonnegative time the target inequality holds outright, for all
four derivative orders at once, with a constant depending on that time: take
the maximum of the four order-wise constants supplied by
`schwartz_iteratedFDeriv_sq_decay`.

**Why this pins the residual exactly.**  The open statement asks for a `K` that
works simultaneously for every `t` in a neighborhood of `t₀`.  This theorem
supplies `K` for each `t` separately, kernel-clean, from the Schwartz structure
of the slice alone.  What remains open is therefore *only the uniformity of `K`
over a time neighborhood* — and that uniformity is genuinely unavailable from
smoothness plus Schwartz slices, by the witness recorded on the residual below:
for `v t x = (t − t₀)³·ψ((t − t₀)²x)` with `ψ = exp(−‖·‖²)`, the exact
optimisation over `s = t − t₀` gives

  `sup_s ‖v(s,x)‖² = (3/4)^{3/2}·e^{−3/2}·‖x‖^{−3}`

(confirmed numerically to seven digits at `‖x‖ = 1, 10, 10², 10³, 10⁴`), so
`sup_s ‖v(s,x)‖²·(1 + ‖x‖)⁴ ~ C·‖x‖ → ∞` while every slice stays Schwartz and
the joint map stays `C^∞`.  The residual must therefore consume the
Navier–Stokes clauses of `IsClassicalSolution`, not merely `velocity_smooth`. -/
theorem exists_sliceFixedTimeDecayBound
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀) (t : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, n < 4 → ∀ x : Space,
      ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2 ≤ K * (1 + ‖x‖) ^ (-4 : ℝ) := by
  choose K hKpos hK using fun n : ℕ => schwartz_iteratedFDeriv_sq_decay (S.slice t) n
  refine ⟨max (max (K 0) (K 1)) (max (K 2) (K 3)), ?_, ?_⟩
  · exact lt_of_lt_of_le (hKpos 0) (le_max_of_le_left (le_max_left _ _))
  · have hle : ∀ m : ℕ, m < 4 → K m ≤ max (max (K 0) (K 1)) (max (K 2) (K 3)) := by
      intro m hm
      interval_cases m
      · exact le_max_of_le_left (le_max_left _ _)
      · exact le_max_of_le_left (le_max_right _ _)
      · exact le_max_of_le_right (le_max_left _ _)
      · exact le_max_of_le_right (le_max_right _ _)
    intro n hn x
    have hwpos : (0 : ℝ) ≤ (1 + ‖x‖) ^ (-4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    exact le_trans (hK n x) (mul_le_mul_of_nonneg_right (hle n hn) hwpos)

/-- **Seminorm-explicit form of the quartic decay bound (certified).**  The
constant in `schwartz_iteratedFDeriv_sq_decay` is not merely existential: it is
`8·(‖f‖_{0,n}² + ‖f‖_{2,n}²)` in the Schwartz seminorms
`SchwartzMap.seminorm ℝ k n`.  Only the weight exponent `k = 2` is needed,
because the weight enters *squared*:

  `‖D^n f x‖²·(1 + ‖x‖⁴) = ‖D^n f x‖² + (‖x‖²·‖D^n f x‖)² ≤ ‖f‖_{0,n}² + ‖f‖_{2,n}²`,

and then `(1 + r)⁴ ≤ 8(1 + r⁴)` (sharp, equality at `r = 1`).

Making the constant explicit is what converts the *fixed-time* bound into a
*locally uniform* one: uniformity of `K` over a time neighbourhood is now
exactly local boundedness of two Schwartz seminorms of the slice. -/
theorem schwartz_iteratedFDeriv_sq_decay_seminorm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : SchwartzMap Space F) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n f x‖ ^ 2
      ≤ 8 * ((SchwartzMap.seminorm ℝ 0 n f) ^ 2 + (SchwartzMap.seminorm ℝ 2 n f) ^ 2)
          * (1 + ‖x‖) ^ (-4 : ℝ) := by
  have h0 : ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ SchwartzMap.seminorm ℝ 0 n f :=
    f.norm_iteratedFDeriv_le_seminorm ℝ n x
  have h2 : ‖x‖ ^ 2 * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ SchwartzMap.seminorm ℝ 2 n f :=
    SchwartzMap.le_seminorm ℝ 2 n f x
  have hxpos : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hrw : (1 + ‖x‖) ^ (-4 : ℝ) = ((1 + ‖x‖) ^ (4 : ℕ))⁻¹ := by
    rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hxpos.le,
      Real.rpow_natCast]
  rw [hrw, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖x‖) ^ (4 : ℕ))]
  have hcmp : (1 + ‖x‖) ^ (4 : ℕ) ≤ 8 * (1 + ‖x‖ ^ 4) := by
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1), sq_nonneg (‖x‖ + 1),
      sq_nonneg (‖x‖ ^ 2 - 1), sq_nonneg (‖x‖ ^ 2 - ‖x‖)]
  have hkey : ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖ ^ 4)
      ≤ (SchwartzMap.seminorm ℝ 0 n f) ^ 2 + (SchwartzMap.seminorm ℝ 2 n f) ^ 2 := by
    calc ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖ ^ 4)
        = ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2
            + (‖x‖ ^ 2 * ‖iteratedFDeriv ℝ n (⇑f) x‖) ^ 2 := by ring
      _ ≤ (SchwartzMap.seminorm ℝ 0 n f) ^ 2 + (SchwartzMap.seminorm ℝ 2 n f) ^ 2 :=
          add_le_add (pow_le_pow_left₀ (norm_nonneg _) h0 2)
            (pow_le_pow_left₀ (by positivity) h2 2)
  calc ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖) ^ (4 : ℕ)
      ≤ ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (8 * (1 + ‖x‖ ^ 4)) :=
        mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = 8 * (‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖ ^ 4)) := by ring
    _ ≤ 8 * ((SchwartzMap.seminorm ℝ 0 n f) ^ 2
          + (SchwartzMap.seminorm ℝ 2 n f) ^ 2) := by linarith

/-- **Converse of `schwartz_iteratedFDeriv_sq_decay_seminorm` (certified).**  A
quartic-weight decay bound at order `n` *forces* the two Schwartz seminorms
`‖f‖_{0,n}` and `‖f‖_{2,n}` to be at most `√K`.

Together the two directions certify that the seminorm formulation is **not a
strengthening** of the decay bound but an equivalent restatement of it, with
constants `K ↦ √K` and `M ↦ 16M²`.  This is what makes the residual below a
strictly-lower leaf rather than a harder replacement obligation. -/
theorem schwartz_seminorm_le_of_sq_decay {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : SchwartzMap Space F) (n : ℕ) {K : ℝ}
    (h : ∀ x : Space, ‖iteratedFDeriv ℝ n f x‖ ^ 2 ≤ K * (1 + ‖x‖) ^ (-4 : ℝ)) :
    SchwartzMap.seminorm ℝ 0 n f ≤ Real.sqrt K ∧
      SchwartzMap.seminorm ℝ 2 n f ≤ Real.sqrt K := by
  have key : ∀ x : Space,
      ‖iteratedFDeriv ℝ n (⇑f) x‖ * (1 + ‖x‖) ^ 2 ≤ Real.sqrt K := by
    intro x
    have hxpos : (0 : ℝ) < 1 + ‖x‖ := by positivity
    have h4 : (0 : ℝ) < (1 + ‖x‖) ^ (4 : ℕ) := by positivity
    have hrw : (1 + ‖x‖) ^ (-4 : ℝ) = ((1 + ‖x‖) ^ (4 : ℕ))⁻¹ := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hxpos.le,
        Real.rpow_natCast]
    have hx := h x
    rw [hrw] at hx
    have hnn : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ n (⇑f) x‖ * (1 + ‖x‖) ^ 2 := by positivity
    have hsq : (‖iteratedFDeriv ℝ n (⇑f) x‖ * (1 + ‖x‖) ^ 2) ^ 2 ≤ K := by
      calc (‖iteratedFDeriv ℝ n (⇑f) x‖ * (1 + ‖x‖) ^ 2) ^ 2
          = ‖iteratedFDeriv ℝ n (⇑f) x‖ ^ 2 * (1 + ‖x‖) ^ (4 : ℕ) := by ring
        _ ≤ (K * ((1 + ‖x‖) ^ (4 : ℕ))⁻¹) * (1 + ‖x‖) ^ (4 : ℕ) :=
            mul_le_mul_of_nonneg_right hx h4.le
        _ = K := by field_simp
    calc ‖iteratedFDeriv ℝ n (⇑f) x‖ * (1 + ‖x‖) ^ 2
        = Real.sqrt ((‖iteratedFDeriv ℝ n (⇑f) x‖ * (1 + ‖x‖) ^ 2) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt hsq
  constructor
  · refine SchwartzMap.seminorm_le_bound ℝ 0 n f (Real.sqrt_nonneg K) fun x => ?_
    have hone : (1 : ℝ) ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
    have := key x
    rw [pow_zero, one_mul]
    nlinarith [norm_nonneg (iteratedFDeriv ℝ n (⇑f) x)]
  · refine SchwartzMap.seminorm_le_bound ℝ 2 n f (Real.sqrt_nonneg K) fun x => ?_
    have hmono : ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
    have := key x
    nlinarith [norm_nonneg (iteratedFDeriv ℝ n (⇑f) x)]

/-- **The PDE residual of `exists_sliceLocallyUniformDecayBound`, isolated.**
Local-in-time boundedness of the two Schwartz seminorms `‖·‖_{0,n}` and
`‖·‖_{2,n}`, `n < 4`, of the slices of a Schwartz-sliced classical solution.

By `schwartz_iteratedFDeriv_sq_decay_seminorm` and its converse
`schwartz_seminorm_le_of_sq_decay` this predicate is **equivalent** to the
locally uniform quartic decay bound (both implications certified below), so
nothing is gained or lost by working with it — it is the same obligation in the
vocabulary Majda–Bertozzi §3.2.3 states it in. -/
def SliceSeminormLocallyBounded {ν : ℝ} {u₀ : SchwartzVelocity}
    (S : SchwartzSlicedSolution ν u₀) : Prop :=
  ∀ t₀ ∈ Set.Ici (0 : ℝ), ∃ r M : ℝ, 0 < r ∧
    ∀ t ∈ Set.Ici (0 : ℝ) ∩ Metric.ball t₀ r, ∀ n : ℕ, n < 4 →
      SchwartzMap.seminorm ℝ 0 n (S.slice t) ≤ M ∧
        SchwartzMap.seminorm ℝ 2 n (S.slice t) ≤ M

/-! ### The residual of `sliceSeminorm_locallyBounded`, and its route

**[Majda–Bertozzi §3.2.3; est ~200 LOC.]**  The whole PDE content of
`exists_sliceLocallyUniformDecayBound`, and nothing else: near every
nonnegative time, the seminorms `‖u(t)‖_{0,n}`, `‖u(t)‖_{2,n}` for `n < 4` admit
a single bound.

**Route.**  Polynomially weighted energy inequalities for `‖x^α D^β u‖_{L²}`,
`|α| ≤ 2`, `|β| ≤ 5`: differentiating the weighted `L²` norm along the
Navier–Stokes flow produces a viscous good term, a commutator term
`[x^α, u·∇]D^β u` bounded by the *unweighted* `H^s` norm times the weighted
norm, and a pressure term handled by the Calderón–Zygmund bound on
`∇²(-Δ)^{-1}`; Grönwall against `uniformly_bounded_energy` then closes the
inequality on a time interval whose length depends only on the energy bound.
The passage from the weighted `L²` control to the pointwise seminorms is
Sobolev embedding `H²(ℝ³) ↪ L^∞`, already certified in this file as
`exists_agmonSupBound`.

**Dependencies.**  `S.solution.equation`, `S.solution.incompressible`,
`S.solution.finite_energy`, `S.solution.uniformly_bounded_energy`; the
slice/joint derivative transfer
`iteratedFDeriv_slice_eq_within_compContinuousLinearMap` (certified above); the
Calderón–Zygmund pressure bound.

**Non-vacuity (the file's witness, applied directly to the seminorms).**
Smoothness plus Schwartz slices is provably insufficient: for
`v t x = (t − t₀)³·ψ((t − t₀)²x)` with `ψ = exp(−‖·‖²)`, write `s = t − t₀` and
substitute `y = s²x`.  Then `‖x‖² = ‖y‖²/s⁴`, so

  `‖v s‖_{2,0} = sup_x ‖x‖²·s³ψ(s²x) = s^{−1}·sup_y ‖y‖²ψ(y) = e^{−1}/s → ∞`

as `s → 0`, while `‖v s‖_{0,0} = s³ → 0`.  (Checked numerically: `e^{−1}/s` at
`s = 1, 1/2, 1/5, 1/10, 1/20` gives `0.36788, 0.73576, 1.83940, 3.67879,
7.35759`, matching `sup_x ‖x‖²s³ψ(s²x)` to five digits.)  So the `k = 2`
seminorm alone already diverges on a family that is `C^∞` on `ℝ × ℝ³` with
every slice Schwartz — no locally uniform `M` exists.  This is the same witness
that makes `sup_s ‖v(s,x)‖²(1 + ‖x‖)⁴ ~ C‖x‖` diverge at the decay end
(`sup_s ‖v(s,x)‖² = (3/4)^{3/2}e^{−3/2}‖x‖^{−3}`), as the certified equivalence
requires.  The predicate therefore genuinely consumes the Navier–Stokes clauses
of `IsClassicalSolution`, not merely `velocity_smooth`.
-/

/-- **The weighted-energy differential inequality the PDE supplies**
(Majda–Bertozzi §3.2.3, the *hypothesis* half of the argument).

Near every nonnegative time there is a window `[0,T]`, a scalar control `E`
dominating the quartic-weighted pointwise size of every derivative of order
`n < 4`, and continuous nonnegative `a, b` with

  `E' ≤ a·E + b`   on `(0,T)`.

`a` is the commutator/Calderón–Zygmund rate `C(1 + ‖∇u‖_∞)` produced by
`[x^α, u·∇]D^β u` (whose order-zero character is certified in
`Navier.Analysis.WeightedCommutator`) together with the pressure bound on
`∇²(-Δ)^{-1}`; `b`
collects the unweighted forcing, which is controlled by
`uniformly_bounded_energy`.  The additive `b` is exactly why the *purely
multiplicative* Grönwall lemmas already in this repository
(`gronwall_log_apriori`) do not suffice.

This is a **strictly lower** obligation than `SliceSeminormLocallyBounded`:
the theorem immediately below derives the latter from it, kernel-clean. -/
def WeightedEnergyAffineControl {ν : ℝ} {u₀ : SchwartzVelocity}
    (S : SchwartzSlicedSolution ν u₀) : Prop :=
  ∀ t₀ ∈ Set.Ici (0 : ℝ), ∃ T : ℝ, t₀ < T ∧ ∃ E E' a b : ℝ → ℝ,
    ContinuousOn a (Set.Icc 0 T) ∧ ContinuousOn b (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc 0 T, 0 ≤ a t) ∧ (∀ t ∈ Set.Icc 0 T, 0 ≤ b t) ∧
    ContinuousOn E (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Ioo 0 T, HasDerivAt E (E' t) t) ∧
    (∀ t ∈ Set.Ioo 0 T, E' t ≤ a t * E t + b t) ∧
    (∀ t ∈ Set.Icc 0 T, ∀ n : ℕ, n < 4 → ∀ x : Space,
      ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2 ≤ E t * (1 + ‖x‖) ^ (-4 : ℝ))

/-- **[NAMED RESIDUAL — the weighted energy identity and its commutator /
Calderón–Zygmund pressure estimate; Majda–Bertozzi §3.2.3; est ~200 LOC.]**
The *whole* remaining PDE content of `sliceSeminorm_locallyBounded`.

Differentiating `E(t) = Σ_{|α| ≤ 2, |β| ≤ 5} ‖x^α D^β u(t)‖²_{L²}` along the
flow produces (i) the viscous good term `−2ν‖∇(x^α D^β u)‖²_{L²} ≤ 0`, (ii) the
commutator term `⟨[x^α, u·∇]D^β u, x^α D^β u⟩` bounded by `C(1+‖∇u‖_∞)·E`, and
(iii) the pressure term, bounded via the Calderón–Zygmund estimate on
`∇²(-Δ)^{-1}`; the unweighted forcing is controlled by
`S.solution.uniformly_bounded_energy`.  That is exactly the shape
`WeightedEnergyAffineControl` records.

**What this residual no longer carries.**  The Grönwall step and the passage
from the weighted control to the two Schwartz seminorms are certified below in
`sliceSeminormLocallyBounded_of_weightedEnergyAffineControl`, using the affine
time-dependent Grönwall leaf
`Navier.Analysis.GronwallAffine.gronwall_affine_apriori`.  The **commutator
identity** in (ii) is certified in `Navier.Analysis.WeightedCommutator`:

  `convectiveDeriv_coord_smul`      `[x_j, u·∇] f = − u_j·f`
  `convectiveDeriv_coord_pow_smul`  `[(x_j)^k, u·∇] f = − k(x_j)^{k−1}u_j·f`

so the commutator is proved to be of **order zero in `f`** — it costs no
derivative, trading one power of the weight for one power of `u`.  That is
precisely why (ii) is bounded by `C(1+‖∇u‖_∞)·E` and hence why the inequality
closes as the *affine* `E' ≤ aE + b` rather than a quasilinear one.  What
remains residual here is the weighted energy *identity* (differentiation of
`E` under the integral along the flow) and the Calderón–Zygmund pressure
bound on `∇²(-Δ)^{-1}`, and nothing else. -/
theorem weightedEnergyAffineControl_of_navierStokes
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀) :
    WeightedEnergyAffineControl S := by
  sorry

/-- **[CERTIFIED — no `sorry` in this declaration; the Grönwall + extraction
step of `sliceSeminorm_locallyBounded`.]**  The weighted-energy differential
inequality forces the locally uniform seminorm bound.

Two named edges are discharged here and are no longer residual:

* the **affine time-dependent Grönwall step**
  `Navier.Analysis.GronwallAffine.exists_bound_of_affine_gronwall`
  (`E' ≤ a·E + b` with continuous nonnegative `a, b` gives one constant `M`
  bounding `E` on the whole window) — Mathlib carries only the *constant-rate*
  `gronwallBound`, and this repository carried only the *multiplicative*
  `gronwall_log_apriori`, which needs `Y > 0` and has no forcing term;
* the passage from the weighted `L²`/pointwise control to the two Schwartz
  seminorms, which is `schwartz_seminorm_le_of_sq_decay` above.

What remains residual is therefore exactly the *derivation* of
`WeightedEnergyAffineControl` from the Navier–Stokes clauses — the weighted
energy identity, its commutator estimate and the Calderón–Zygmund pressure
bound — and nothing else. -/
theorem sliceSeminormLocallyBounded_of_weightedEnergyAffineControl
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
    (h : WeightedEnergyAffineControl S) :
    SliceSeminormLocallyBounded S := by
  intro t₀ ht₀
  obtain ⟨T, hT₀T, E, E', a, b, hac, hbc, hanonneg, hbnonneg, hEc, hEderiv,
    hEbound, hdecay⟩ := h t₀ ht₀
  have hT : (0 : ℝ) ≤ T := le_trans ht₀ (le_of_lt hT₀T)
  obtain ⟨M, hM⟩ := Navier.Analysis.GronwallAffine.exists_bound_of_affine_gronwall
    hT hac hbc hanonneg hbnonneg hEc hEderiv hEbound
  refine ⟨T - t₀, Real.sqrt M, by linarith, ?_⟩
  intro t ht n hn
  have htIcc : t ∈ Set.Icc (0 : ℝ) T := by
    refine ⟨ht.1, ?_⟩
    have := Metric.mem_ball.mp ht.2
    rw [Real.dist_eq] at this
    have := abs_lt.mp this
    linarith [this.2]
  have hpt : ∀ x : Space,
      ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2 ≤ M * (1 + ‖x‖) ^ (-4 : ℝ) := by
    intro x
    have hw : (0 : ℝ) ≤ (1 + ‖x‖) ^ (-4 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    exact le_trans (hdecay t htIcc n hn x)
      (mul_le_mul_of_nonneg_right (hM t htIcc) hw)
  exact schwartz_seminorm_le_of_sq_decay (S.slice t) n hpt

/-- **[NAMED RESIDUAL, strictly reduced.]**  Only the derivation of
`WeightedEnergyAffineControl` remains: the Grönwall step and the seminorm
extraction are certified in
`sliceSeminormLocallyBounded_of_weightedEnergyAffineControl` above. -/
theorem sliceSeminorm_locallyBounded
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀) :
    SliceSeminormLocallyBounded S :=
  sliceSeminormLocallyBounded_of_weightedEnergyAffineControl S
    (weightedEnergyAffineControl_of_navierStokes S)

/-- **[DERIVED, certified.]**  The reverse implication of the equivalence: a
locally uniform quartic decay bound gives locally uniform seminorm bounds.
Certifies that `sliceSeminorm_locallyBounded` is not a strengthened
replacement obligation. -/
theorem sliceSeminormLocallyBounded_of_locallyUniformDecay
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
    (h : ∀ t₀ ∈ Set.Ici (0 : ℝ), ∃ r K : ℝ, 0 < r ∧
      ∀ t ∈ Set.Ici (0 : ℝ) ∩ Metric.ball t₀ r, ∀ n : ℕ, n < 4 → ∀ x : Space,
        ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2 ≤ K * (1 + ‖x‖) ^ (-4 : ℝ)) :
    SliceSeminormLocallyBounded S := by
  intro t₀ ht₀
  obtain ⟨r, K, hr, hK⟩ := h t₀ ht₀
  refine ⟨r, Real.sqrt K, hr, fun t ht n hn => ?_⟩
  exact schwartz_seminorm_le_of_sq_decay (S.slice t) n fun x => hK t ht n hn x

/-- **[DERIVED from `sliceSeminorm_locallyBounded`.]**  Along a Schwartz-sliced classical
solution, near every nonnegative time `t₀` there is a uniform polynomial decay
bound on every slice derivative of order `n < 4`: a single `K` and radius
`r > 0` with

  `‖D^n u(t,x)‖² ≤ K·(1 + ‖x‖)⁻⁴`   for all `t ∈ Ici 0 ∩ B(t₀, r)`, all `x`.

This is the *only* genuinely PDE-dependent input to
`sobolevOrderIntegralContinuity`: paired with the certified dominator
integrability `(1 + ‖x‖)⁻⁴ ∈ L¹(ℝ³)` it is exactly the dominated-convergence
data for one derivative order at a time.

**Why this is a genuine hypothesis and not bookkeeping.**  Joint smoothness
together with Schwartz slices is *provably insufficient* to produce this
locally uniform bound.  Witness (verified numerically before formalisation,
and exact by scaling): on `ℝ³` take `ψ(y) = exp(-‖y‖²)` and

  `v t x := (t - t₀)³ · ψ((t - t₀)² x)`.

Then `(t,x) ↦ v t x` is `C^∞` on all of `ℝ × ℝ³`, every slice `v t` is Schwartz
(at `t = t₀` it is identically `0`), yet for `n = 0`

  `sup_{t near t₀} ‖v(t, x)‖² · (1 + ‖x‖)⁴ ~ C·‖x‖⁻³ · (1 + ‖x‖)⁴ → ∞`,

mass escaping to spatial infinity at exactly the rate `‖x‖⁻³` that keeps the
`L²` norm constant (`∫ ‖v t ·‖² = ‖ψ‖²_{L²}` for every `t ≠ t₀`, `0` at
`t = t₀`).  Hence no such `K` exists for that family, and any proof must use
the Navier–Stokes clauses of `IsClassicalSolution` (`equation`,
`incompressible`, `finite_energy`, `uniformly_bounded_energy`) and not merely
`velocity_smooth`.

**Dependencies.**  Exactly one: `sliceSeminorm_locallyBounded`, the
locally-in-time propagation of the two Schwartz seminorms `‖·‖_{0,n}`,
`‖·‖_{2,n}` for `n < 4` along the flow.  The passage from those seminorms to
this quartic pointwise bound, with the explicit constant `K = 16M²`, is
certified by `schwartz_iteratedFDeriv_sq_decay_seminorm`; the converse passage
`K ↦ √K` is certified by `schwartz_seminorm_le_of_sq_decay` and lifted to
families by `sliceSeminormLocallyBounded_of_locallyUniformDecay`, so this
statement and its hypothesis are **equivalent** — the reduction moves the
obligation into Majda–Bertozzi's own vocabulary without strengthening it.

**What is no longer residual.**  All of the analysis-side content: the
fixed-time decay (`schwartz_iteratedFDeriv_sq_decay`,
`exists_sliceFixedTimeDecayBound`), the seminorm-explicit constant and its
converse (both above), the fixed-`x` time continuity
(`sliceIteratedFDeriv_continuousOn`, from joint half-space smoothness alone),
the dominated-convergence step itself, the measurability of every integrand,
the slice/joint derivative transfer
(`iteratedFDeriv_slice_eq_within_compContinuousLinearMap`), and the assembly of
the four orders into the `H³` norm (`BKMLogLeaves.continuousOn_sum_range`).
What remains is the weighted-energy/Grönwall propagation and nothing else. -/
theorem exists_sliceLocallyUniformDecayBound
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀) :
    ∀ t₀ ∈ Set.Ici (0 : ℝ), ∃ r K : ℝ, 0 < r ∧
      ∀ t ∈ Set.Ici (0 : ℝ) ∩ Metric.ball t₀ r, ∀ n : ℕ, n < 4 → ∀ x : Space,
        ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2 ≤ K * (1 + ‖x‖) ^ (-4 : ℝ) := by
  intro t₀ ht₀
  obtain ⟨r, M, hr, hM⟩ := sliceSeminorm_locallyBounded S t₀ ht₀
  refine ⟨r, 16 * M ^ 2, hr, fun t ht n hn x => ?_⟩
  obtain ⟨h0, h2⟩ := hM t ht n hn
  have hw : (0 : ℝ) ≤ (1 + ‖x‖) ^ (-4 : ℝ) := Real.rpow_nonneg (by positivity) _
  refine le_trans (schwartz_iteratedFDeriv_sq_decay_seminorm (S.slice t) n x) ?_
  refine mul_le_mul_of_nonneg_right ?_ hw
  have hsum : (SchwartzMap.seminorm ℝ 0 n (S.slice t)) ^ 2
      + (SchwartzMap.seminorm ℝ 2 n (S.slice t)) ^ 2 ≤ M ^ 2 + M ^ 2 :=
    add_le_add (pow_le_pow_left₀ (apply_nonneg _ _) h0 2)
      (pow_le_pow_left₀ (apply_nonneg _ _) h2 2)
  linarith

/-- **[DERIVED from `exists_sliceLocallyUniformDecayBound`.]**  The
dominated-convergence data for one derivative order along a Schwartz-sliced
classical solution: the locally uniform decay bound (the named residual above,
the genuinely PDE-dependent conjunct) together with the certified fixed-`x`
time continuity `sliceIteratedFDeriv_continuousOn`. -/
theorem exists_locallyUniformSliceDecay
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀) :
    (∀ t₀ ∈ Set.Ici (0 : ℝ), ∃ r K : ℝ, 0 < r ∧
        ∀ t ∈ Set.Ici (0 : ℝ) ∩ Metric.ball t₀ r, ∀ n : ℕ, n < 4 → ∀ x : Space,
          ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2 ≤ K * (1 + ‖x‖) ^ (-4 : ℝ)) ∧
      (∀ n : ℕ, n < 4 → ∀ x : Space, ContinuousOn
        (fun t => ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2) (Set.Ici 0)) :=
  ⟨exists_sliceLocallyUniformDecayBound S,
    fun n _ x => sliceIteratedFDeriv_continuousOn S n x⟩

/-- **[DERIVED from `exists_locallyUniformSliceDecay`.]**  Per-derivative-order
control continuity; Majda–Bertozzi §3.2.3.  Along a Schwartz-sliced classical
solution, and for **one** derivative order `n < 4` at a time, the map
`t ↦ ∫ ‖D^n u(t,x)‖² dx` is continuous on nonnegative time.

The derivation is
`UniformDecayDominated.continuousOn_integral_of_locallyUniformDecay` applied to
the shared decay gap; the measurability of every integrand and the
nonnegativity are supplied here, kernel-clean, from smoothness of the Schwartz
slice (`ContDiff.continuous_iteratedFDeriv`).  Nothing about continuity of the
integral remains open — only the decay bound remains residual; the fixed-`x`
time continuity is certified as `sliceIteratedFDeriv_continuousOn`. -/
theorem sobolevOrderIntegralContinuity
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
    {n : ℕ} (hn : n < 4) :
    ContinuousOn (fun t => ∫ x : Space,
      ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2) (Set.Ici 0) := by
  obtain ⟨hdecay, hcont⟩ := exists_locallyUniformSliceDecay S
  refine continuousOn_integral_of_locallyUniformDecay
    (F := fun t x => ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2) ?_ ?_ ?_ ?_
  · intro t
    exact ((ContDiff.continuous_iteratedFDeriv le_rfl
      ((S.slice t).smooth n)).norm.pow 2).aestronglyMeasurable
  · intro t x; positivity
  · intro x; exact hcont n hn x
  · intro t₀ ht₀
    obtain ⟨r, K, hr, hb⟩ := hdecay t₀ ht₀
    exact ⟨r, K, hr, fun t ht x => hb t ht n hn x⟩

/-- **[DERIVED from `sobolevOrderIntegralContinuity`.]**  Majda–Bertozzi §3.2.3;
est ~300 LOC.]**  Along a Schwartz-sliced classical solution the `H³`-norm
control `t ↦ ‖u(t)‖²_{H³}` is continuous on nonnegative time.  Closure route:
dominated convergence over the jointly-smooth slices with locally uniform
Schwartz seminorm bounds. -/
theorem sobolevControlContinuity
    {ν : ℝ} {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀) :
    ContinuousOn (fun t => sobolevH3NormSq (S.slice t)) (Set.Ici 0) := by
  have h : ∀ n ∈ Finset.range 4,
      ContinuousOn (fun t => ∫ x : Space,
        ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2) (Set.Ici 0) :=
    fun n hn => sobolevOrderIntegralContinuity S (Finset.mem_range.mp hn)
  show ContinuousOn (fun t => ∑ n ∈ Finset.range 4,
      ∫ x : Space, ‖iteratedFDeriv ℝ n (⇑(S.slice t)) x‖ ^ 2) (Set.Ici 0)
  exact continuousOn_sum_range h

/-- **[NAMED RESIDUAL — Kato–Ponce commutator / per-order energy estimate;
Majda–Bertozzi Prop. 3.7; Kato–Ponce, *CPAM* **41** (1988) 891–907;
est ~600 LOC.]**  Along a Schwartz-sliced classical solution with a pointwise
gradient majorant `G`, and for **one** derivative order `n < 4` at a time, the
order-`n` energy `t ↦ ∫ ‖D^n u(t,x)‖² dx` is differentiable on positive time
with derivative at most `C·G(t)·‖u(t)‖²_{H³}`.

**Dependencies still carried.**  Differentiation under the `L²(ℝ³)` integral
for the jointly-smooth slices; the pressure term vanishing after integration by
parts (incompressibility); the viscous term `−2ν∫‖D^{n+1}u‖²` being `≤ 0` for
`ν ≥ 0`; the divergence-free cancellation `⟨u·∇D^n u, D^n u⟩ = 0` that removes
the top-order Leibniz term; and the Gagliardo–Nirenberg interpolation that
converts `Σ_{i≥1} ‖D^i u‖_∞‖D^{n−i+1}u‖_{L²}` into `‖∇u‖_∞‖u‖_{H^n}`.

**What is no longer residual — the Leibniz + Hölder core of the integer-order
Kato–Ponce estimate.**  For integer `n` the commutator bound is *not* the
fractional Kato–Ponce theorem: it is the bilinear Leibniz rule followed by
`L²`-Hölder with the low-order factor in `L^∞`.  Both steps are now certified
kernel-clean in `Navier/Analysis/KatoPonceLeibniz.lean`:

* `Navier.Analysis.KatoPonceLeibniz.norm_iteratedFDeriv_bilinear_le_of_supBound`
  — Leibniz with a sup majorant on the first factor;
* `Navier.Analysis.KatoPonceLeibniz.integral_mul_norm_le_sqrt_mul_sqrt`
  — the `p = q = 2` Hölder step in this repository's
  `√(∫‖D^n u‖²)` energy vocabulary;
* `Navier.Analysis.KatoPonceLeibniz.integral_norm_iteratedFDeriv_bilinear_mul_le`
  — the assembly
  `∫‖D^n B(f,g)‖·‖D^n h‖ ≤ ‖B‖ Σ_i C(n,i)·A_i·‖D^{n−i}g‖_{L²}·‖D^n h‖_{L²}`,
  which is exactly the pairing the energy estimate takes.

**What is no longer residual.**  Summing the four orders — the differentiability
of the `H³` energy and the accumulation of the four bounds into the single
constant `4C` — is certified by
`BKMLogLeaves.exists_hasDerivAt_sum_range_le`. -/
theorem exists_sobolevOrderEnergyEstimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ν : ℝ}, 0 ≤ ν →
      ∀ {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
        {T : ℝ} (G : ℝ → ℝ),
        (∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Space,
          ‖fderiv ℝ (S.velocity t) x‖ ≤ G t) →
        ∀ t ∈ Set.Ioo (0:ℝ) T, ∀ n : ℕ, n < 4 →
          ∃ D : ℝ,
            HasDerivAt (fun s => ∫ x : Space,
              ‖iteratedFDeriv ℝ n (⇑(S.slice s)) x‖ ^ 2) D t ∧
            D ≤ C * G t * sobolevH3NormSq (S.slice t) := by
  sorry

/-- **[DERIVED from `exists_sobolevOrderEnergyEstimate`.]**  `H³` energy estimate;
Majda–Bertozzi Prop. 3.7; Kato–Ponce CPAM 41 (1988); est ~600 LOC.]**
Along a Schwartz-sliced classical solution with a pointwise gradient majorant
`G`, the `H³` energy `t ↦ ‖u(t)‖²_{H³}` is differentiable on positive time
with derivative at most `C·G(t)·‖u(t)‖²_{H³}`: differentiating the `H³` energy,
the pressure term vanishes (divergence-free), the viscous term is dissipative
(`ν ≥ 0`), and the convection commutator is bounded by `C‖∇u‖_∞‖u‖²_{H³}`.

Statement shape: derivative existence and its bound are asserted together
(both are part of the classical estimate); the majorant `G` is
hypothesis-carried. -/
theorem katoCommutatorEstimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ν : ℝ}, 0 ≤ ν →
      ∀ {u₀ : SchwartzVelocity} (S : SchwartzSlicedSolution ν u₀)
        {T : ℝ} (G : ℝ → ℝ),
        (∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Space,
          ‖fderiv ℝ (S.velocity t) x‖ ≤ G t) →
        ∀ t ∈ Set.Ioo (0:ℝ) T,
          ∃ D : ℝ,
            HasDerivAt (fun s => sobolevH3NormSq (S.slice s)) D t ∧
            D ≤ C * G t * sobolevH3NormSq (S.slice t) := by
  obtain ⟨C, hCpos, hC⟩ := exists_sobolevOrderEnergyEstimate
  refine ⟨4 * C, by linarith, ?_⟩
  intro ν hν u₀ S T G hG t ht
  have hstep : ∀ n ∈ Finset.range 4,
      ∃ D : ℝ, HasDerivAt (fun s => ∫ x : Space,
        ‖iteratedFDeriv ℝ n (⇑(S.slice s)) x‖ ^ 2) D t ∧
        D ≤ C * G t * sobolevH3NormSq (S.slice t) :=
    fun n hn => hC hν S G hG t ht n (Finset.mem_range.mp hn)
  obtain ⟨D, hD, hDle⟩ :=
    exists_hasDerivAt_sum_range_le
      (F := fun n s => ∫ x : Space,
        ‖iteratedFDeriv ℝ n (⇑(S.slice s)) x‖ ^ 2) hstep
  refine ⟨D, hD, ?_⟩
  calc D ≤ ((4:ℕ) : ℝ) * (C * G t * sobolevH3NormSq (S.slice t)) := hDle
    _ = 4 * C * G t * sobolevH3NormSq (S.slice t) := by push_cast; ring


/-!
## The tower composes: solutions + analytic inputs ⟹ the criterion
-/

/-- **The BKM tower composes.**  A Schwartz-sliced classical solution with a
continuous vorticity-sup majorant `Mω` and vorticity-`L²` majorant `M₂` whose
combined improper integral is finite carries a `LogBKMControl` — so by
`LogBKMControl.velocity_bounded` the velocity is uniformly bounded on `[0,T)`
and no pointwise breakdown occurs.

This theorem consumes the four skeleton statements above; its own contribution
(the constant bookkeeping, the `(1 + a(1+L) + b) ≤ (1+a+b)(1+L)` absorption,
the `√s ≤ 1+s` domination rescale, and the assembly of all continuity/
derivative facts) is fully proved.  It certifies that once the analytic
sorries close, the criterion is *built from solutions* with no statement-level
gap. -/
theorem logBKMControl_of_schwartzSliced
    {ν T : ℝ} (hν : 0 ≤ ν) {u₀ : SchwartzVelocity}
    (S : SchwartzSlicedSolution ν u₀)
    (Mω M₂ : ℝ → ℝ)
    (hMωc : ContinuousOn Mω (Set.Ico 0 T))
    (hM₂c : ContinuousOn M₂ (Set.Ico 0 T))
    (hMω : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Space,
      officialEuclideanNorm (staticCurl (S.velocity t) x) ≤ Mω t)
    (hM₂ : ∀ t ∈ Set.Ico (0:ℝ) T,
      (∫ x : Space,
        officialEuclideanNorm (staticCurl (S.velocity t) x) ^ 2) ≤ M₂ t)
    (hfin : ∃ B : ℝ, ∀ t ∈ Set.Ico (0:ℝ) T,
      (∫ s in (0:ℝ)..t, (1 + Mω s + Real.sqrt (M₂ s))) ≤ B) :
    Nonempty (LogBKMControl S.velocity T) := by
  classical
  obtain ⟨CB, hCBpos, hBS⟩ := biotSavartLogInequality
  obtain ⟨CS, hCSpos, hSE⟩ := sobolevEmbeddingDomination
  obtain ⟨CK, hCKpos, hKato⟩ := katoCommutatorEstimate
  -- the H³ control and constants
  set N : ℝ → ℝ := fun s => sobolevH3NormSq (S.slice s) with hNdef
  set c : ℝ := max CS 1 with hcdef
  have hc1 : (1:ℝ) ≤ c := le_max_right _ _
  have hcpos : (0:ℝ) < c := lt_of_lt_of_le one_pos hc1
  set M : ℝ := max (CK * CB) 1 with hMdef
  have hM1 : (1:ℝ) ≤ M := le_max_right _ _
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le one_pos hM1
  have hNnn : ∀ t : ℝ, 0 ≤ N t := fun t => sobolevH3NormSq_nonneg _
  have hMωnn : ∀ t ∈ Set.Ico (0:ℝ) T, 0 ≤ Mω t := by
    intro t ht
    exact le_trans (officialEuclideanNorm_nonneg _) (hMω t ht 0)
  -- divergence-free slices from incompressibility
  have hdivfree : ∀ t ∈ Set.Ico (0:ℝ) T, DivergenceFreeInitial (S.slice t) := by
    intro t ht x
    have hst : ⇑(S.slice t) = S.velocity t := S.slice_eq t ht.1
    show staticDivergence (fun y => (S.slice t) y) x = 0
    have hd := S.solution.incompressible t ht.1 x
    simpa [staticDivergence, divergence, spatialDerivative, hst] using hd
  -- gradient majorant from the Biot–Savart log inequality
  set G : ℝ → ℝ := fun t =>
    CB * (1 + Mω t * (1 + Real.log (1 + N t)) + Real.sqrt (M₂ t)) with hGdef
  have hGnn : ∀ t ∈ Set.Ico (0:ℝ) T, 0 ≤ G t := by
    intro t ht
    have hL : 0 ≤ Real.log (1 + N t) :=
      Real.log_nonneg (by linarith [hNnn t])
    have := hMωnn t ht
    have hb := Real.sqrt_nonneg (M₂ t)
    have hpar : 0 ≤ 1 + Mω t * (1 + Real.log (1 + N t)) + Real.sqrt (M₂ t) := by
      nlinarith
    exact mul_nonneg (le_of_lt hCBpos) hpar
  have hG : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Space,
      ‖fderiv ℝ (S.velocity t) x‖ ≤ G t := by
    intro t ht x
    have hst : ⇑(S.slice t) = S.velocity t := S.slice_eq t ht.1
    have hcurl : ∀ y : Space,
        officialEuclideanNorm (staticCurl (⇑(S.slice t)) y) ≤ Mω t := by
      intro y; rw [hst]; exact hMω t ht y
    have hcurl2 :
        (∫ y : Space,
          officialEuclideanNorm (staticCurl (⇑(S.slice t)) y) ^ 2) ≤ M₂ t := by
      rw [hst]; exact hM₂ t ht
    have := hBS (S.slice t) (hdivfree t ht) (Mω t) (M₂ t) (N t)
      hcurl hcurl2 le_rfl x
    rw [hst] at this
    exact this
  -- H³ derivative facts through `deriv` (no choice function needed)
  have hNderiv : ∀ t ∈ Set.Ioo (0:ℝ) T,
      HasDerivAt N (deriv N t) t ∧ deriv N t ≤ CK * G t * N t := by
    intro t ht
    obtain ⟨D, hD, hDle⟩ := hKato hν S G hG t ht
    have hd : deriv N t = D := hD.deriv
    rw [hd]
    exact ⟨hD, hDle⟩
  -- assemble the control
  refine ⟨{
    control := fun t => c * (1 + N t)
    controlDeriv := fun t => c * deriv N t
    rate := fun t => M * (1 + Mω t + Real.sqrt (M₂ t))
    rate_continuousOn := ?_
    control_continuousOn := ?_
    control_hasDerivAt := ?_
    control_ge_one := ?_
    loglinear_inequality := ?_
    rate_dominates_vorticity := ?_
    control_dominates_velocity := ?_
    finite_vorticity_integral := ?_
    velocity_differentiable := ?_
    incompressible := ?_ }⟩
  · -- rate continuity
    exact continuousOn_const.mul ((continuousOn_const.add hMωc).add
      (Real.continuous_sqrt.comp_continuousOn hM₂c))
  · -- control continuity
    exact continuousOn_const.mul (continuousOn_const.add
      ((sobolevControlContinuity S).mono Set.Ico_subset_Ici_self))
  · -- derivative
    intro t ht
    exact ((hNderiv t ht).1.const_add 1).const_mul c
  · -- control ≥ 1
    intro t ht
    nlinarith [hNnn t]
  · -- the log-linear inequality (constant bookkeeping chain)
    intro t ht
    have htIco : t ∈ Set.Ico (0:ℝ) T := ⟨le_of_lt ht.1, ht.2⟩
    obtain ⟨-, hDle⟩ := hNderiv t ht
    have hL : 0 ≤ Real.log (1 + N t) :=
      Real.log_nonneg (by linarith [hNnn t])
    have hb : 0 ≤ Real.sqrt (M₂ t) := Real.sqrt_nonneg _
    have hmω := hMωnn t htIco
    have hn := hNnn t
    -- absorption: 1 + a(1+L) + b ≤ (1+a+b)(1+L)
    have habsorb : 1 + Mω t * (1 + Real.log (1 + N t)) + Real.sqrt (M₂ t) ≤
        (1 + Mω t + Real.sqrt (M₂ t)) * (1 + Real.log (1 + N t)) := by
      nlinarith
    have hGle : G t ≤ CB * ((1 + Mω t + Real.sqrt (M₂ t)) *
        (1 + Real.log (1 + N t))) := by
      exact mul_le_mul_of_nonneg_left habsorb (le_of_lt hCBpos)
    -- step 1: deriv N ≤ CK·G·N ≤ CK·G·(1+N)
    have hstep1 : deriv N t ≤ CK * G t * (1 + N t) := by
      refine le_trans hDle ?_
      have : 0 ≤ CK * G t := mul_nonneg (le_of_lt hCKpos) (hGnn t htIco)
      nlinarith
    -- step 2: expand G, absorb into rate shape
    have hfactor : 0 ≤ (1 + Mω t + Real.sqrt (M₂ t)) := by nlinarith
    have honePlusL : 0 ≤ 1 + Real.log (1 + N t) := by linarith
    have honePlusN : 0 ≤ 1 + N t := by linarith
    have hstep2 : CK * G t * (1 + N t) ≤
        (CK * CB) * ((1 + Mω t + Real.sqrt (M₂ t)) *
          (1 + Real.log (1 + N t))) * (1 + N t) := by
      have h1 : CK * G t ≤ (CK * CB) * ((1 + Mω t + Real.sqrt (M₂ t)) *
          (1 + Real.log (1 + N t))) := by
        calc CK * G t ≤ CK * (CB * ((1 + Mω t + Real.sqrt (M₂ t)) *
            (1 + Real.log (1 + N t)))) :=
              mul_le_mul_of_nonneg_left hGle (le_of_lt hCKpos)
          _ = (CK * CB) * ((1 + Mω t + Real.sqrt (M₂ t)) *
              (1 + Real.log (1 + N t))) := by ring
      exact mul_le_mul_of_nonneg_right h1 honePlusN
    have hstep3 : (CK * CB) * ((1 + Mω t + Real.sqrt (M₂ t)) *
        (1 + Real.log (1 + N t))) * (1 + N t) ≤
        M * ((1 + Mω t + Real.sqrt (M₂ t)) *
          (1 + Real.log (1 + N t))) * (1 + N t) := by
      have hMge : CK * CB ≤ M := le_max_left _ _
      have hnn : 0 ≤ (1 + Mω t + Real.sqrt (M₂ t)) *
          (1 + Real.log (1 + N t)) := mul_nonneg hfactor honePlusL
      have := mul_le_mul_of_nonneg_right hMge hnn
      exact mul_le_mul_of_nonneg_right this honePlusN
    -- step 4: log(c(1+N)) ≥ log(1+N)
    have hlogc : Real.log (1 + N t) ≤ Real.log (c * (1 + N t)) := by
      have h1N : (0:ℝ) < 1 + N t := by linarith
      rw [Real.log_mul (ne_of_gt hcpos) (ne_of_gt h1N)]
      have := Real.log_nonneg hc1
      linarith
    -- assemble
    have hrateNN : 0 ≤ M * (1 + Mω t + Real.sqrt (M₂ t)) :=
      mul_nonneg (le_of_lt hMpos) hfactor
    calc c * deriv N t
        ≤ c * (CK * G t * (1 + N t)) :=
          mul_le_mul_of_nonneg_left hstep1 (le_of_lt hcpos)
      _ ≤ c * (M * ((1 + Mω t + Real.sqrt (M₂ t)) *
            (1 + Real.log (1 + N t))) * (1 + N t)) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcpos)
          exact le_trans hstep2 hstep3
      _ = M * (1 + Mω t + Real.sqrt (M₂ t)) *
            ((c * (1 + N t)) * (1 + Real.log (1 + N t))) := by ring
      _ ≤ M * (1 + Mω t + Real.sqrt (M₂ t)) *
            ((c * (1 + N t)) * (1 + Real.log (c * (1 + N t)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hrateNN
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (le_of_lt hcpos) honePlusN)
          linarith
  · -- (H-diff): the Schwartz slices are differentiable, so `vorticity` is the
    -- genuine curl and not the `fderiv` junk value
    intro t ht x
    have hst : ⇑(S.slice t) = S.velocity t := S.slice_eq t ht.1
    have hd : DifferentiableAt ℝ (⇑(S.slice t)) x :=
      (((S.slice t).smooth 1).differentiable (by norm_num)).differentiableAt
    rwa [hst] at hd
  · -- (H-div): incompressibility, straight from the classical solution
    intro t ht x
    have hd := S.solution.incompressible t ht.1 x
    simpa [staticDivergence, divergence, spatialDerivative] using hd
  · -- rate dominates vorticity
    intro t ht x
    have h1 := hMω t ht x
    have hb : 0 ≤ Real.sqrt (M₂ t) := Real.sqrt_nonneg _
    have hmω := hMωnn t ht
    have hchain : Mω t ≤ M * (1 + Mω t + Real.sqrt (M₂ t)) := by
      nlinarith
    exact le_trans h1 hchain
  · -- control dominates velocity
    intro t ht x
    have hst : ⇑(S.slice t) = S.velocity t := S.slice_eq t ht.1
    have hemb := hSE (S.slice t) (N t) le_rfl x
    rw [hst] at hemb
    have hsqrt : Real.sqrt (N t) ≤ 1 + N t := by
      nlinarith [Real.sq_sqrt (hNnn t), Real.sqrt_nonneg (N t)]
    have hCSc : CS ≤ c := le_max_left _ _
    calc ‖S.velocity t x‖ ≤ CS * Real.sqrt (N t) := hemb
      _ ≤ CS * (1 + N t) :=
          mul_le_mul_of_nonneg_left hsqrt (le_of_lt hCSpos)
      _ ≤ c * (1 + N t) := by
          have h1N : 0 ≤ 1 + N t := by linarith [hNnn t]
          exact mul_le_mul_of_nonneg_right hCSc h1N
  · -- finite improper integral
    obtain ⟨B, hB⟩ := hfin
    refine ⟨M * B, ?_⟩
    intro t ht
    have : (∫ s in (0:ℝ)..t, M * (1 + Mω s + Real.sqrt (M₂ s))) =
        M * ∫ s in (0:ℝ)..t, (1 + Mω s + Real.sqrt (M₂ s)) :=
      intervalIntegral.integral_const_mul _ _
    rw [this]
    exact mul_le_mul_of_nonneg_left (hB t ht) (le_of_lt hMpos)

/-!
## The Biot–Savart kernel far field (certified, no sorry)

The Calderón–Zygmund size layer for `exists_biotSavartLogTextbook` splits the
convolution `∇K ∗ ω` into a near field (`|z| < ρ`, controlled by `ρ·‖∇ω‖_∞`),
a logarithmic shell (`ρ < |z| < 1`, controlled by `‖ω‖_∞·log(1/ρ)`), and a far
field (`|z| > 1`, where the kernel is `L²` and pairs with `‖ω‖_{L²}` by
Cauchy–Schwarz).  The far-field `L²` integrability is certified here; the
near-field cancellation bound is certified in the next section
(`integral_norm_mul_bsKernelScalar_ball_le`); the logarithmic-shell bound and
the Biot–Savart representation itself remain residual (see the dependency list
of `exists_biotSavartLogTextbook`).
-/

/-- **Far-field `L²` integrability of the Biot–Savart kernel (certified, no
sorry).**  On `{z | 1 ≤ ‖z‖}` the kernel tail `bsKernelScalar²` — bounded
pointwise by `(16π²·|z|⁶)⁻¹` via `bsKernelScalar_sq_le` — is integrable: in
three dimensions the radial tail `∫₁^∞ ρ²/ρ⁶ dρ` converges.  This is the
far-field half of the Calderón–Zygmund size layer feeding
`exists_biotSavartLogTextbook`: the tail convolution against the vorticity is
then controlled by `‖ω‖_{L²}` through Cauchy–Schwarz.

The proof compares against the certified Bessel weight `(1 + ‖z‖²)⁻²`
(`integrable_inv_one_add_normSq_sq`) through
`‖z‖ ≤ officialEuclideanNorm z` and `(1 + ‖z‖²)³ ≤ 8‖z‖⁶` for `‖z‖ ≥ 1`. -/
theorem integrableOn_bsKernelScalar_sq_farField :
    IntegrableOn (fun z : Space => bsKernelScalar z ^ 2) {z : Space | 1 ≤ ‖z‖}
      volume := by
  set s : Set Space := {z : Space | 1 ≤ ‖z‖} with hsdef
  have hs : MeasurableSet s :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hne : ∀ z : Space, z ∈ s → z ≠ 0 := by
    intro z hz h0
    rw [h0, hsdef] at hz
    simp only [Set.mem_setOf_eq, norm_zero] at hz
    exact absurd hz (by norm_num)
  have hcontK : ContinuousOn bsKernelScalar s := by
    have hbr : ContinuousOn
        (fun z : Space => 1 / (4 * Real.pi * officialEuclideanNorm z ^ 3)) s := by
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact continuousOn_const.mul
          (continuous_officialEuclideanNorm.continuousOn.pow 3)
      · intro z hz
        have hone : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le one_pos hz
        have hpos : (0 : ℝ) < officialEuclideanNorm z :=
          lt_of_lt_of_le hone (norm_le_officialEuclideanNorm z)
        exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
          (pow_ne_zero 3 (ne_of_gt hpos))
    exact hbr.congr fun z hz => bsKernelScalar_apply_of_ne_zero (hne z hz)
  have haes : AEStronglyMeasurable (fun z : Space => bsKernelScalar z ^ 2)
      (volume.restrict s) :=
    (hcontK.pow 2).aestronglyMeasurable hs
  have hg : Integrable
      (fun z : Space => (1 / (2 * Real.pi ^ 2)) * (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹) :=
    integrable_inv_one_add_normSq_sq.const_mul _
  refine (hg.integrableOn).mono' haes ?_
  rw [ae_restrict_iff' hs]
  filter_upwards with z hz
  have hz' : (1 : ℝ) ≤ ‖z‖ := by rw [hsdef] at hz; exact hz
  have hone : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le one_pos hz'
  have hoge : ‖z‖ ≤ officialEuclideanNorm z := norm_le_officialEuclideanNorm z
  have hker := bsKernelScalar_sq_le (hne z hz)
  have ho6pos : (0 : ℝ) < officialEuclideanNorm z ^ 6 :=
    pow_pos (lt_of_lt_of_le hone hoge) 6
  have h6pos : (0 : ℝ) < ‖z‖ ^ 6 := pow_pos hone 6
  have h12pos : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hstep2 : (officialEuclideanNorm z ^ 6)⁻¹ ≤ (‖z‖ ^ 6)⁻¹ :=
    inv_anti₀ h6pos (pow_le_pow_left₀ (norm_nonneg _) hoge 6)
  have hw : (1 : ℝ) + ‖z‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg ‖z‖, hz', hone]
  have hpow : ((1 : ℝ) + ‖z‖ ^ 2) ^ 3 ≤ (2 * ‖z‖ ^ 2) ^ 3 :=
    pow_le_pow_left₀ h12pos.le hw 3
  have hinv3 : ((2 * ‖z‖ ^ 2) ^ 3)⁻¹ ≤ (((1 : ℝ) + ‖z‖ ^ 2) ^ 3)⁻¹ :=
    inv_anti₀ (pow_pos h12pos 3) hpow
  have h23 : ((2 * ‖z‖ ^ 2) ^ 3)⁻¹ = (1 / 8) * (‖z‖ ^ 6)⁻¹ := by
    have he : (2 * ‖z‖ ^ 2) ^ 3 = 8 * ‖z‖ ^ 6 := by ring
    rw [he, mul_inv]
    norm_num
  have hbase : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  have h32 : (((1 : ℝ) + ‖z‖ ^ 2) ^ 3)⁻¹ ≤ (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ :=
    inv_anti₀ (pow_pos h12pos 2) (pow_le_pow_right₀ hbase (by norm_num))
  have h6 : (‖z‖ ^ 6)⁻¹ ≤ 8 * (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    rw [show (‖z‖ ^ 6)⁻¹ = 8 * ((2 * ‖z‖ ^ 2) ^ 3)⁻¹ from by rw [h23]; ring]
    exact mul_le_mul_of_nonneg_left (le_trans hinv3 h32) (by norm_num)
  have hbound : bsKernelScalar z ^ 2 ≤
      (1 / (2 * Real.pi ^ 2)) * (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ :=
  calc bsKernelScalar z ^ 2
      ≤ 1 / (16 * Real.pi ^ 2 * officialEuclideanNorm z ^ 6) := hker
    _ = (1 / (16 * Real.pi ^ 2)) * (officialEuclideanNorm z ^ 6)⁻¹ := by
        rw [div_eq_mul_inv, one_mul, mul_inv, div_eq_mul_inv, one_mul]
    _ ≤ (1 / (16 * Real.pi ^ 2)) * (‖z‖ ^ 6)⁻¹ :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ ≤ (1 / (16 * Real.pi ^ 2)) * (8 * (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = (1 / (2 * Real.pi ^ 2)) * (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ := by
        field_simp
        ring
  have hgnn : (0 : ℝ) ≤ 1 / (2 * Real.pi ^ 2) * (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    positivity
  have hknn : (0 : ℝ) ≤ bsKernelScalar z ^ 2 := pow_nonneg (bsKernelScalar_nonneg z) 2
  simpa only [Real.norm_eq_abs, abs_of_nonneg hknn, abs_of_nonneg hgnn] using hbound

/-!
## The Biot–Savart kernel near field (certified, no sorry)

The near-field half of the Calderón–Zygmund size layer.  The kernel
`∇K ∼ 1/(4π|z|³)` is *not* locally integrable at the origin (radially
`∫₀^ρ r²·r⁻³ dr` diverges); the near-field convolution is controlled by the
first-order cancellation `|ω(x−z) − ω(x)| ≤ ‖∇ω‖∞·|z|`, which supplies one
power of `|z|`.  The weighted kernel `|z|·bsKernelScalar z ∼ 1/(4π|z|²)` *is*
integrable on `ball 0 ρ`, with mass `≤ (2·vol(B₁)/π)·ρ`: decompose the ball
into the dyadic shells `ρ/2^{k+1} < |z| ≤ ρ/2^k`, on shell `k` the weighted
kernel is `≤ 4^k/(πρ²)` while the shell volume is `≤ (ρ/2^k)³·vol(B₁)`, so the
shells contribute the geometric series `(ρ·vol(B₁)/π)·∑ₖ 2⁻ᵏ = 2ρ·vol(B₁)/π`.
-/


/-- **The actual Hölder-`1/4` near-field kernel is locally integrable.**

After Morrey cancellation, the singular factor is
`|z|^(1/4) |z|^(-3) = |z|^(-11/4)`.  Since `11/4 < 3`, the finite-dimensional
power-integrability criterion applies on every ball.  This is the precise
integrability input used when `exists_agmonMorreyBound` is paired with the
Biot–Savart kernel; the previously certified `|z|`-weighted estimate alone
does not imply this fractional endpoint near the origin. -/
theorem integrableOn_norm_rpow_oneFourth_mul_bsKernelScalar_ball (ρ : ℝ) :
    IntegrableOn
      (fun z : Space => ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z)
      (Metric.ball 0 ρ) volume := by
  apply integrableOn_ball_of_norm_le_rpow
    (E := Space) (F := ℝ) (C := 1 / (4 * Real.pi))
      (by simp) (by norm_num : (11 : ℝ) / 4 < Module.finrank ℝ Space)
  · filter_upwards with z
    by_cases hz : z = 0
    · subst z
      simp [bsKernelScalar_zero]
    · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hoge : ‖z‖ ≤ officialEuclideanNorm z := norm_le_officialEuclideanNorm z
      have hden : 4 * Real.pi * ‖z‖ ^ 3 ≤
          4 * Real.pi * officialEuclideanNorm z ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hoge 3) (by positivity)
      rw [Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _)
          (bsKernelScalar_nonneg z)), bsKernelScalar_apply_of_ne_zero hz]
      calc
        ‖z‖ ^ ((1 : ℝ) / 4) *
              (1 / (4 * Real.pi * officialEuclideanNorm z ^ 3)) ≤
            ‖z‖ ^ ((1 : ℝ) / 4) * (1 / (4 * Real.pi * ‖z‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (by positivity) hden)
            (Real.rpow_nonneg (norm_nonneg z) _)
        _ = (1 / (4 * Real.pi)) * ‖z‖ ^ (-((11 : ℝ) / 4)) := by
          rw [show ‖z‖ ^ (3 : ℕ) = ‖z‖ ^ (3 : ℝ) by
            exact (Real.rpow_natCast ‖z‖ 3).symm]
          calc
            ‖z‖ ^ ((1 : ℝ) / 4) *
                (1 / (4 * Real.pi * ‖z‖ ^ (3 : ℝ))) =
              (1 / (4 * Real.pi)) *
                (‖z‖ ^ ((1 : ℝ) / 4) * (‖z‖ ^ (3 : ℝ))⁻¹) := by ring
            _ = (1 / (4 * Real.pi)) * ‖z‖ ^ (-((11 : ℝ) / 4)) := by
              rw [← Real.rpow_neg hn.le, ← Real.rpow_add hn]
              norm_num
  · have hpowMeas : Measurable (fun z : Space => ‖z‖ ^ ((1 : ℝ) / 4)) :=
      (continuous_norm.rpow_const fun _ => Or.inr (by norm_num)).measurable
    exact (hpowMeas.mul measurable_bsKernelScalar).aestronglyMeasurable

/-- The fractional Morrey-weighted kernel is homogeneous of degree `-11/4`.
This is the scaling identity behind the sharp `ρ^(1/4)` near-field mass. -/
theorem norm_rpow_oneFourth_mul_bsKernelScalar_smul
    {ρ : ℝ} (hρ : 0 < ρ) (z : Space) :
    ‖ρ • z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar (ρ • z) =
      ρ ^ (-((11 : ℝ) / 4)) *
        (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
  by_cases hz : z = 0
  · subst z
    simp [bsKernelScalar_zero]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
      bsKernelScalar_homogeneous ρ z hρ.ne' hz, abs_of_pos hρ,
      Real.mul_rpow hρ.le (norm_nonneg z)]
    have hinv : ρ⁻¹ ^ (3 : ℕ) = ρ ^ (-(3 : ℝ)) := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hρ.le]
      norm_num
    rw [hinv]
    calc
      ρ ^ ((1 : ℝ) / 4) * ‖z‖ ^ ((1 : ℝ) / 4) *
          (ρ ^ (-(3 : ℝ)) * bsKernelScalar z) =
          (ρ ^ ((1 : ℝ) / 4) * ρ ^ (-(3 : ℝ))) *
            (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by ring
      _ = ρ ^ (-((11 : ℝ) / 4)) *
          (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
        rw [← Real.rpow_add hρ]
        norm_num

/-- **Sharp fractional near-field mass.**  The degree-`-11/4` weighted
Biot–Savart kernel has exactly the dimensionally predicted ball scaling
`I(ρ) = ρ^(1/4) I(1)`. -/
theorem integral_norm_rpow_oneFourth_mul_bsKernelScalar_ball_eq
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z in Metric.ball (0 : Space) ρ,
        ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) =
      ρ ^ ((1 : ℝ) / 4) *
        ∫ z in Metric.ball (0 : Space) 1,
          ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z := by
  let f : Space → ℝ :=
    fun z => ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z
  have hchange := Measure.setIntegral_comp_smul_of_pos volume f
    (Metric.ball (0 : Space) 1) hρ
  rw [smul_unitBall_of_pos hρ] at hchange
  simp only [f, norm_rpow_oneFourth_mul_bsKernelScalar_smul hρ] at hchange
  rw [MeasureTheory.integral_const_mul] at hchange
  have hd : Module.finrank ℝ Space = 3 := by simp
  simp only [hd, smul_eq_mul] at hchange
  have hρ3 : ρ ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hρ.ne'
  have hcoeff : ρ ^ (3 : ℝ) * ρ ^ (-((11 : ℝ) / 4)) =
      ρ ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hρ]
    norm_num
  calc
    (∫ z in Metric.ball (0 : Space) ρ,
        ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) =
        ρ ^ (3 : ℕ) * ((ρ ^ (3 : ℕ))⁻¹ *
          ∫ z in Metric.ball (0 : Space) ρ,
            ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
          field_simp
    _ = ρ ^ (3 : ℕ) *
        (ρ ^ (-((11 : ℝ) / 4)) *
          ∫ z in Metric.ball (0 : Space) 1,
            ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
          rw [← hchange]
    _ = ρ ^ ((1 : ℝ) / 4) *
        ∫ z in Metric.ball (0 : Space) 1,
          ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z := by
          rw [show ρ ^ (3 : ℕ) = ρ ^ (3 : ℝ) by
            exact (Real.rpow_natCast ρ 3).symm]
          rw [← mul_assoc, hcoeff]

/-- **Hölder cancellation makes the Biot–Savart near-field convolution
integrable.**  This is the direct consumer form of
`integrableOn_norm_rpow_oneFourth_mul_bsKernelScalar_ball`: any strongly
measurable vector difference bounded by `H·|z|^(1/4)` can be multiplied by the
degree-`-3` kernel on a ball. -/
theorem integrableOn_bsKernelScalar_smul_of_holder
    (F : Space → Space) (H ρ : ℝ) (hH : 0 ≤ H)
    (hF : AEStronglyMeasurable F volume)
    (hholder : ∀ z, ‖F z‖ ≤ H * ‖z‖ ^ ((1 : ℝ) / 4)) :
    IntegrableOn (fun z => bsKernelScalar z • F z) (Metric.ball 0 ρ) volume := by
  have hbase :=
    (integrableOn_norm_rpow_oneFourth_mul_bsKernelScalar_ball ρ).const_mul H
  refine hbase.mono' ?_ ?_
  · exact (measurable_bsKernelScalar.aestronglyMeasurable.smul hF).restrict
  · filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bsKernelScalar_nonneg z)]
    have hknn := bsKernelScalar_nonneg z
    have hleft := mul_le_mul_of_nonneg_left (hholder z) hknn
    calc
      bsKernelScalar z * ‖F z‖ ≤
          bsKernelScalar z * (H * ‖z‖ ^ ((1 : ℝ) / 4)) := hleft
      _ = |H| * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
        rw [abs_of_nonneg hH]
        ring
      _ = H * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
        rw [abs_of_nonneg hH]

/-- **Quantitative Hölder near-field convolution bound.**  A vector
difference controlled by `H·|z|^(1/4)` contributes at most the universal
unit-ball weighted-kernel mass times `H·ρ^(1/4)`.  This is the precise
near-field estimate consumed by `exists_biotSavartKernelSplitting` once the
principal-value Biot–Savart representation supplies the difference. -/
theorem integral_norm_bsKernelScalar_smul_of_holder_le
    (F : Space → Space) (H : ℝ) {ρ : ℝ} (hH : 0 ≤ H) (hρ : 0 < ρ)
    (hF : AEStronglyMeasurable F volume)
    (hholder : ∀ z, ‖F z‖ ≤ H * ‖z‖ ^ ((1 : ℝ) / 4)) :
    (∫ z in Metric.ball (0 : Space) ρ,
        ‖bsKernelScalar z • F z‖) ≤
      H * ρ ^ ((1 : ℝ) / 4) *
        ∫ z in Metric.ball (0 : Space) 1,
          ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z := by
  have hleft : IntegrableOn (fun z => ‖bsKernelScalar z • F z‖)
      (Metric.ball (0 : Space) ρ) volume :=
    (integrableOn_bsKernelScalar_smul_of_holder F H ρ hH hF hholder).norm
  have hright : IntegrableOn
      (fun z : Space => H * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z))
      (Metric.ball (0 : Space) ρ) volume :=
    (integrableOn_norm_rpow_oneFourth_mul_bsKernelScalar_ball ρ).const_mul H
  calc
    (∫ z in Metric.ball (0 : Space) ρ,
        ‖bsKernelScalar z • F z‖) ≤
        ∫ z in Metric.ball (0 : Space) ρ,
          H * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
      refine setIntegral_mono_on hleft hright Metric.isOpen_ball.measurableSet ?_
      intro z _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (bsKernelScalar_nonneg z)]
      calc
        bsKernelScalar z * ‖F z‖ ≤
            bsKernelScalar z * (H * ‖z‖ ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (hholder z) (bsKernelScalar_nonneg z)
        _ = H * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by ring
    _ = H * (∫ z in Metric.ball (0 : Space) ρ,
          ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
      rw [MeasureTheory.integral_const_mul]
    _ = H * (ρ ^ ((1 : ℝ) / 4) *
          ∫ z in Metric.ball (0 : Space) 1,
            ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
      rw [integral_norm_rpow_oneFourth_mul_bsKernelScalar_ball_eq hρ]
    _ = H * ρ ^ ((1 : ℝ) / 4) *
          ∫ z in Metric.ball (0 : Space) 1,
            ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z := by ring


/-!
## The Biot–Savart kernel logarithmic shell (certified, no sorry)

The middle layer of the Calderón–Zygmund splitting, and **the layer that
produces the logarithm** in the Beale–Kato–Majda inequality.  Between the
near-field cutoff `ρ` and the far-field radius `1` the kernel is integrated
*without* any cancellation weight; what keeps the mass finite is that the
annulus `{ρ ≤ ‖z‖} ∩ B₁` meets only the first `N ≈ log₂(1/ρ)` unit-scale
dyadic shells `czShell 1 k`, and every shell contributes the *same* constant
mass: amplitude `≤ 2·8ᵏ/π` against volume `≤ 8⁻ᵏ·vol(B₁)`.  So the total is
`(2·vol(B₁)/π)·N`, and the dyadic count `N` is exactly `log₂(1/ρ)` rounded up
— the logarithmic divergence of `∫ |z|⁻³` in three dimensions.

Together with `integral_norm_mul_bsKernelScalar_ball_le` (near field, integer
weight `‖z‖`) and `integrableOn_bsKernelScalar_sq_farField` (far field, `L²`),
this closes those three stated estimates.  The actual Morrey cancellation uses
the fractional weight `‖z‖^(1/4)`; its exact quantitative `O(ρ^(1/4))`
scaling and Hölder convolution form are certified above.  The Biot–Savart
principal-value representation remains for `exists_biotSavartLogTextbook`.
-/

/-- **Unit-scale shell amplitude bound (certified).**  On the dyadic shell
`czShell 1 k = B₁ ∩ {2^{-(k+1)} < ‖z‖ ≤ 2^{-k}}` the Biot–Savart kernel — with
*no* cancellation weight — is at most `2·8ᵏ/π`:
`1/(4π|z|³) ≤ 1/(4π·(2^{-(k+1)})³) = 8^{k+1}/(4π)`.  The passage from the
kernel's Euclidean norm to the shell's product norm uses
`‖z‖ ≤ officialEuclideanNorm z`. -/
theorem czShell_kernel_le {k : ℕ} {z : Space} (hz : z ∈ czShell 1 k) :
    bsKernelScalar z ≤ 2 * 8 ^ k / Real.pi := by
  obtain ⟨-, hlo, -⟩ := hz
  have hpos : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
  have hn : 0 < ‖z‖ := lt_trans hpos hlo
  rw [bsKernelScalar_apply_of_ne_zero (norm_pos_iff.mp hn)]
  have hoge := norm_le_officialEuclideanNorm z
  have hle1 : (1 : ℝ) / (4 * Real.pi * officialEuclideanNorm z ^ 3)
      ≤ 1 / (4 * Real.pi * ‖z‖ ^ 3) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hoge 3) (by positivity))
  have hden : 4 * Real.pi * ((1 : ℝ) / 2 ^ (k + 1)) ^ 3 ≤ 4 * Real.pi * ‖z‖ ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlo.le 3)
      (by positivity)
  have hkey : (1 : ℝ) / (4 * Real.pi * (1 / 2 ^ (k + 1)) ^ 3)
      = 2 * 8 ^ k / Real.pi := by
    have h8 : ((2 : ℝ) ^ (k + 1)) ^ 3 = 8 * 8 ^ k := by
      rw [← pow_mul, mul_comm (k + 1) 3, pow_mul]
      norm_num [pow_succ, mul_comm]
    have hpi := Real.pi_ne_zero
    rw [div_pow, one_pow, h8]
    field_simp
    ring
  calc (1 : ℝ) / (4 * Real.pi * officialEuclideanNorm z ^ 3)
      ≤ 1 / (4 * Real.pi * ‖z‖ ^ 3) := hle1
    _ ≤ 1 / (4 * Real.pi * ((1 : ℝ) / 2 ^ (k + 1)) ^ 3) :=
        one_div_le_one_div_of_le (by positivity) hden
    _ = 2 * 8 ^ k / Real.pi := hkey

/-- **The dyadic shell count is logarithmic (certified).**  If `2^{-N} < ρ`
then the annulus `B₁ ∩ {ρ ≤ ‖z‖}` is covered by the *first `N`* unit-scale
shells: a point of the annulus is nonzero, hence lies in some `czShell 1 k` by
`ball_subset_iUnion_czShell`, and `k ≥ N` would force
`ρ ≤ ‖z‖ ≤ 2^{-k} ≤ 2^{-N} < ρ`. -/
theorem annulus_subset_biUnion_czShell {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ}
    (hN : 1 / 2 ^ N < ρ) :
    Metric.ball (0 : Space) 1 ∩ {z : Space | ρ ≤ ‖z‖} ⊆
      ⋃ k ∈ Finset.range N, czShell 1 k := by
  intro z hz
  obtain ⟨hball, hlow⟩ := hz
  simp only [Set.mem_setOf_eq] at hlow
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hmem := ball_subset_iUnion_czShell (ρ := (1 : ℝ)) one_pos hball
  rw [mem_insert_iff] at hmem
  rcases hmem with h | h
  · exact absurd h hz0
  · rw [mem_iUnion] at h
    obtain ⟨k, hk⟩ := h
    have hhi : ‖z‖ ≤ 1 / 2 ^ k := hk.2.2
    have hkN : k < N := by
      by_contra hcon
      have hNk : N ≤ k := Nat.not_lt.mp hcon
      have hmono : (1 : ℝ) / 2 ^ k ≤ 1 / 2 ^ N :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ one_le_two hNk)
      linarith
    exact mem_biUnion (Finset.mem_range.mpr hkN) hk

/-- **Every unit-scale shell carries the same mass (certified).**  Amplitude
`2·8ᵏ/π` times volume `≤ 8⁻ᵏ·vol(B₁)` is the `k`-independent constant
`(2/π)·vol(B₁)`.  This scale invariance is precisely why the shell count, not
the shell sizes, controls the integral. -/
theorem setLIntegral_czShell_kernel_le (k : ℕ) :
    ∫⁻ z in czShell 1 k, ENNReal.ofReal (bsKernelScalar z) ∂volume
      ≤ ENNReal.ofReal (2 / Real.pi) * volume (Metric.ball (0 : Space) 1) := by
  calc ∫⁻ z in czShell 1 k, ENNReal.ofReal (bsKernelScalar z) ∂volume
      ≤ ∫⁻ _ in czShell 1 k, ENNReal.ofReal (2 * 8 ^ k / Real.pi) ∂volume :=
        setLIntegral_mono measurable_const fun _z hz =>
          ENNReal.ofReal_le_ofReal (czShell_kernel_le hz)
    _ = ENNReal.ofReal (2 * 8 ^ k / Real.pi) * volume (czShell 1 k) :=
        setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (2 * 8 ^ k / Real.pi)
          * (ENNReal.ofReal (((1 : ℝ) / 2 ^ k) ^ 3)
              * volume (Metric.ball (0 : Space) 1)) :=
        mul_le_mul_of_nonneg_left (volume_czShell_le one_pos k) zero_le
    _ = ENNReal.ofReal (2 / Real.pi) * volume (Metric.ball (0 : Space) 1) := by
        rw [← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have h8 : ((2 : ℝ) ^ k) ^ 3 = 8 ^ k := by
          rw [← pow_mul, mul_comm k 3, pow_mul]; norm_num
        have hpi := Real.pi_ne_zero
        have h8k : ((8 : ℝ) ^ k) ≠ 0 := by positivity
        rw [div_pow, one_pow, h8]
        field_simp

/-- **The logarithmic shell, lower-Lebesgue form (certified).**  For any `N`
with `2^{-N} < ρ`, the kernel mass on `B₁ ∩ {ρ ≤ ‖z‖}` is at most
`(2N/π)·vol(B₁)`.  The shells are pairwise disjoint and measurable, so the
covering of the annulus by the first `N` of them turns the set integral into a
finite sum of `N` equal constants. -/
theorem lintegral_bsKernelScalar_annulus_le {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ}
    (hN : 1 / 2 ^ N < ρ) :
    ∫⁻ z in Metric.ball (0 : Space) 1 ∩ {z : Space | ρ ≤ ‖z‖},
        ENNReal.ofReal (bsKernelScalar z) ∂volume
      ≤ ENNReal.ofReal (2 * N / Real.pi) * volume (Metric.ball (0 : Space) 1) := by
  refine le_trans (lintegral_mono'
    (Measure.restrict_mono (annulus_subset_biUnion_czShell hρ hN) le_rfl) le_rfl) ?_
  rw [lintegral_biUnion_finset ((czShell_disjoint one_pos).set_pairwise _)
    (fun b _ => measurableSet_czShell 1 b)]
  calc ∑ k ∈ Finset.range N,
        ∫⁻ z in czShell 1 k, ENNReal.ofReal (bsKernelScalar z) ∂volume
      ≤ ∑ _k ∈ Finset.range N,
          ENNReal.ofReal (2 / Real.pi) * volume (Metric.ball (0 : Space) 1) :=
        Finset.sum_le_sum fun k _ => setLIntegral_czShell_kernel_le k
    _ = (N : ENNReal) * (ENNReal.ofReal (2 / Real.pi)
          * volume (Metric.ball (0 : Space) 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ENNReal.ofReal (2 * N / Real.pi) * volume (Metric.ball (0 : Space) 1) := by
        rw [← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **The logarithmic shell, Bochner form (certified).**  Same bound for the
real integral; finiteness comes from the `lintegral` bound above and
`vol(B₁) < ∞`. -/
theorem integral_bsKernelScalar_annulus_le {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ}
    (hN : 1 / 2 ^ N < ρ) :
    ∫ z in Metric.ball (0 : Space) 1 ∩ {z : Space | ρ ≤ ‖z‖}, bsKernelScalar z
      ≤ 2 * (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi * N := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall bsKernelScalar_nonneg)
    measurable_bsKernelScalar.aestronglyMeasurable]
  have htop2 : (ENNReal.ofReal (2 * N / Real.pi)
      * volume (Metric.ball (0 : Space) 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Space)) (r := 1)).ne
  have htop : (∫⁻ z in Metric.ball (0 : Space) 1 ∩ {z : Space | ρ ≤ ‖z‖},
      ENNReal.ofReal (bsKernelScalar z) ∂volume) ≠ ⊤ :=
    ne_top_of_le_ne_top htop2 (lintegral_bsKernelScalar_annulus_le hρ hN)
  refine le_trans ((ENNReal.toReal_le_toReal htop htop2).mpr
    (lintegral_bsKernelScalar_annulus_le hρ hN)) ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  apply le_of_eq
  ring

/-- **The Calderón–Zygmund logarithmic shell bound (certified, no sorry).**
For `0 < ρ ≤ 1`,

  `∫_{ρ ≤ |z| < 1} 1/(4π|z|³) dz ≤ (2·vol(B₁)/π)·(1 + log(1/ρ)/log 2)`.

**This is where the logarithm in Beale–Kato–Majda comes from.**  Taking the
near-field cutoff at `ρ ≈ ‖u‖_{H³}^{-1}` turns the right-hand side into
`C·(1 + log‖u‖_{H³})`, which is the `log(e + ‖u‖_{H³})` factor of
`exists_biotSavartLogTextbook`; the near field then contributes `O(ρ‖∇ω‖_∞)`
via `integral_norm_mul_bsKernelScalar_ball_le` and the far field `O(‖ω‖_{L²})`
via `integrableOn_bsKernelScalar_sq_farField`.

The dyadic count is `N = ⌊log₂(1/ρ)⌋ + 1`, which satisfies both `2^{-N} < ρ`
(so `annulus_subset_biUnion_czShell` applies) and `N ≤ 1 + log₂(1/ρ)` (so the
bound is genuinely logarithmic and not merely finite). -/
theorem integral_bsKernelScalar_annulus_le_log {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) :
    ∫ z in Metric.ball (0 : Space) 1 ∩ {z : Space | ρ ≤ ‖z‖}, bsKernelScalar z
      ≤ 2 * (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi
          * (1 + Real.log (1 / ρ) / Real.log 2) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set x : ℝ := Real.log (1 / ρ) / Real.log 2 with hxdef
  have hxnn : 0 ≤ x := by
    refine div_nonneg (Real.log_nonneg ?_) hl2.le
    rw [le_div_iff₀ hρ0]; linarith
  have hxN : x < (⌊x⌋₊ + 1 : ℕ) := by
    have h := Nat.lt_floor_add_one x
    push_cast
    exact h
  have hNle : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ 1 + x := by
    have h := Nat.floor_le hxnn
    push_cast
    linarith
  have hNρ : 1 / 2 ^ (⌊x⌋₊ + 1 : ℕ) < ρ := by
    have h2 : Real.log (1 / ρ) < ((⌊x⌋₊ + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [hxdef, div_lt_iff₀ hl2] at hxN; exact hxN
    have h3 : Real.log (1 / ρ) < Real.log ((2 : ℝ) ^ (⌊x⌋₊ + 1 : ℕ)) := by
      rw [Real.log_pow]; exact_mod_cast h2
    have h4 : (1 : ℝ) / ρ < 2 ^ (⌊x⌋₊ + 1 : ℕ) :=
      (Real.log_lt_log_iff (by positivity) (by positivity)).mp h3
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (⌊x⌋₊ + 1 : ℕ))]
    rw [div_lt_iff₀ hρ0] at h4
    linarith
  refine le_trans (integral_bsKernelScalar_annulus_le hρ0 hNρ) ?_
  have hC : 0 ≤ 2 * (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi := by
    refine div_nonneg ?_ Real.pi_pos.le
    have hv : (0 : ℝ) ≤ (volume (Metric.ball (0 : Space) 1)).toReal :=
      ENNReal.toReal_nonneg
    linarith
  exact mul_le_mul_of_nonneg_left (by linarith) hC

/-!
## The `ρ = 1` endpoint of the Calderón–Zygmund splitting (certified, no `sorry`)

`exists_biotSavartKernelSplitting` asserts, in its "Satisfiability at both
endpoints" paragraph, that at `ρ = 1` its right-hand side already dominates
`‖∇u‖_∞` "by the `H³ ↪ C¹` embedding for `A` large".  That sentence was prose:
no `H³ ↪ C¹` gradient bound existed anywhere in this development —
`exists_agmonSupBound` embeds `H² ↪ L^∞` for the *field*, not for its
derivative, and the per-order dominations in `SobolevEmbedding` stop at the
integral level.

`exists_fderivSupBound_of_sobolevH3` below supplies it, kernel-clean.  The route
is entirely finite-dimensional bookkeeping on top of `exists_agmonSupBound`:

* the operator norm of `Du(x)` on the sup-normed `Space = Fin 3 → ℝ` is at most
  the sum of its three columns `Du(x)eⱼ` (`opNorm_le_sum_basisVector`);
* each column field `x ↦ Du(x)eⱼ` is itself a Schwartz velocity, namely
  `evalCLM eⱼ (fderivCLM u)`, so `exists_agmonSupBound` applies to it;
* its order-`n` derivative is dominated pointwise by the order-`(n+1)`
  derivative of `u` (`norm_iteratedFDeriv_fderiv`, composed with the
  norm-`≤ 1` evaluation map), so its `H²` energy is dominated by the `H³`
  energy of `u` with the index shift `Finset.sum_range_succ'`.

**What this does and does not do.**  It certifies the endpoint claim, and it
gives the BKM tower a reusable `‖∇u‖_∞ ≤ A‖u‖_{H³}` bound.  It does **not**
reduce `exists_biotSavartKernelSplitting`: that residual quantifies over *every*
`ρ ∈ (0,1]`.  Writing `a = A‖u‖_{H³}` and `b = B·Mω`, the `ρ`-dependent part
`a·ρ^{1/4} + b·(1 + log(1/ρ))` is minimised at `ρ = (4b/a)⁴`, where it equals
`b·(5 + 4 log(a/(4b)))` — logarithmic in `a`, hence smaller than `a` by an
arbitrary factor.  (Checked numerically: at `(a,b) = (10³,1), (10⁶,1),
(10²,10⁻²)` the minimum over `ρ` is `27.085844, 54.716865, 0.362962`, matching
`b(5 + 4 log(a/(4b)))` to six digits, with minimum/`a` equal to
`2.7·10⁻², 5.5·10⁻⁵, 3.6·10⁻³`.)  So the endpoint bound is exactly the `ρ = 1`
corner and nothing more: the genuine Biot–Savart singular-integral content —
the representation `∇u = PV(∇K ∗ ω)` — is untouched, and the residual's own
proof obligation stands.
-/

/-- The norm of a coordinate basis vector of the sup-normed `Space`. -/
private theorem norm_basisVector_eq_one (j : Fin 3) : ‖(basisVector j : Space)‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_) ?_
  · by_cases hi : i = j <;> simp [basisVector, hi]
  · simpa [basisVector] using norm_le_pi_norm (basisVector j : Space) j

/-- **Operator norm by columns.**  On the sup-normed `Space = Fin 3 → ℝ` the
operator norm of a continuous linear map is at most the sum of the norms of its
three columns. -/
private theorem opNorm_le_sum_basisVector (T : Space →L[ℝ] Space) :
    ‖T‖ ≤ ∑ i : Fin 3, ‖T (basisVector i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => norm_nonneg _) (fun v => ?_)
  have hbasis : v = ∑ i : Fin 3, v i • basisVector i := by
    simpa only [basisVector] using (pi_eq_sum_univ' v)
  calc ‖T v‖ = ‖T (∑ i : Fin 3, v i • basisVector i)‖ :=
        congrArg (fun X => ‖T X‖) hbasis
    _ = ‖∑ i : Fin 3, v i • T (basisVector i)‖ := by rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖v i • T (basisVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖T (basisVector i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖T (basisVector i)‖) * ‖v‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The `j`-th column field `x ↦ Du(x)eⱼ` of a Schwartz velocity, as a Schwartz
velocity in its own right. -/
private def columnField (u : SchwartzVelocity) (j : Fin 3) : SchwartzVelocity :=
  SchwartzMap.evalCLM ℝ Space Space (basisVector j) (SchwartzMap.fderivCLM ℝ Space Space u)

private theorem columnField_apply (u : SchwartzVelocity) (j : Fin 3) (x : Space) :
    (columnField u j) x = fderiv ℝ (⇑u) x (basisVector j) := by
  rw [columnField, SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply]

/-- **Order shift.**  Every iterated derivative of a column field is dominated
pointwise by the next-order iterated derivative of the field itself: the column
field is `ev ∘ (fderiv u)` with `‖ev‖ ≤ 1`, and
`norm_iteratedFDeriv_fderiv` converts `Dⁿ(Du)` into `D^{n+1}u`. -/
private theorem norm_iteratedFDeriv_columnField_le
    (u : SchwartzVelocity) (j : Fin 3) (n : ℕ) (y : Space) :
    ‖iteratedFDeriv ℝ n (⇑(columnField u j)) y‖ ≤ ‖iteratedFDeriv ℝ (n + 1) (⇑u) y‖ := by
  set du : SchwartzMap Space (Space →L[ℝ] Space) :=
    SchwartzMap.fderivCLM ℝ Space Space u with hdudef
  set ev : (Space →L[ℝ] Space) →L[ℝ] Space :=
    ContinuousLinearMap.apply ℝ Space (basisVector j) with hevdef
  have hevnorm : ‖ev‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => ?_)
    have hT := T.le_opNorm (basisVector j)
    rw [norm_basisVector_eq_one] at hT
    simpa [hevdef] using hT
  have hcomp : ⇑(columnField u j) = (ev : (Space →L[ℝ] Space) → Space) ∘ (⇑du) := by
    funext y
    simp [columnField, hdudef, hevdef, SchwartzMap.evalCLM_apply_apply,
      ContinuousLinearMap.apply_apply]
  have hducoe : (⇑du) = fderiv ℝ (⇑u) := by
    funext y; rw [hdudef, SchwartzMap.fderivCLM_apply]
  calc ‖iteratedFDeriv ℝ n (⇑(columnField u j)) y‖
      = ‖iteratedFDeriv ℝ n ((ev : (Space →L[ℝ] Space) → Space) ∘ (⇑du)) y‖ := by rw [hcomp]
    _ = ‖ev.compContinuousMultilinearMap (iteratedFDeriv ℝ n (⇑du) y)‖ := by
        rw [ContinuousLinearMap.iteratedFDeriv_comp_left ev (du.smooth ⊤).contDiffAt
          (by exact_mod_cast le_top)]
    _ ≤ ‖ev‖ * ‖iteratedFDeriv ℝ n (⇑du) y‖ := ev.norm_compContinuousMultilinearMap_le _
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (⇑du) y‖ :=
        mul_le_mul_of_nonneg_right hevnorm (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ n (fderiv ℝ (⇑u)) y‖ := by rw [one_mul, hducoe]
    _ = ‖iteratedFDeriv ℝ (n + 1) (⇑u) y‖ := norm_iteratedFDeriv_fderiv

/-- **`H²` of a column is dominated by `H³` of the field.**  The three `H²`
summands of a column field are the order-`1`, `2`, `3` summands of `u`'s `H³`
norm, so the omitted order-`0` summand is exactly the slack. -/
private theorem sobolevH2NormSq_columnField_le (u : SchwartzVelocity) (j : Fin 3) :
    sobolevH2NormSq (columnField u j) ≤ sobolevH3NormSq u := by
  have hstep : ∀ n ∈ Finset.range 3,
      (∫ x : Space, ‖iteratedFDeriv ℝ n (⇑(columnField u j)) x‖ ^ 2)
        ≤ ∫ x : Space, ‖iteratedFDeriv ℝ (n + 1) (⇑u) x‖ ^ 2 := by
    intro n _
    refine integral_mono (integrable_normSq_iteratedFDeriv_space (columnField u j) n)
      (integrable_normSq_iteratedFDeriv_space u (n + 1)) (fun x => ?_)
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_iteratedFDeriv_columnField_le u j n x) 2
  have hsum : sobolevH2NormSq (columnField u j)
      ≤ ∑ n ∈ Finset.range 3, ∫ x : Space, ‖iteratedFDeriv ℝ (n + 1) (⇑u) x‖ ^ 2 :=
    Finset.sum_le_sum hstep
  have hshift : sobolevH3NormSq u
      = (∑ n ∈ Finset.range 3, ∫ x : Space, ‖iteratedFDeriv ℝ (n + 1) (⇑u) x‖ ^ 2)
        + ∫ x : Space, ‖iteratedFDeriv ℝ 0 (⇑u) x‖ ^ 2 := by
    rw [sobolevH3NormSq]
    exact Finset.sum_range_succ' _ 3
  have hnn : (0:ℝ) ≤ ∫ x : Space, ‖iteratedFDeriv ℝ 0 (⇑u) x‖ ^ 2 :=
    integral_nonneg (fun x => by positivity)
  rw [hshift]
  linarith

/-- **`H³(ℝ³) ↪ C¹` at the level of the gradient sup norm (certified, no
`sorry`).**  There is one constant `A > 0` with

  `‖∇u(x)‖ ≤ A·‖u‖_{H³}`   for every Schwartz velocity `u` and every `x`,

where `‖u‖_{H³} = √(sobolevH3NormSq u)`.  The constant is `3C` in the constant
`C` of `exists_agmonSupBound`, the factor `3` being the three columns of the
sup-normed `Space = Fin 3 → ℝ`.

This is the `ρ = 1` endpoint asserted in the satisfiability paragraph of
`exists_biotSavartKernelSplitting`, now certified rather than argued: taking
`A` at least this constant makes that residual's right-hand side dominate
`‖∇u(x)‖` at `ρ = 1`, so the residual is not the unsatisfiable pole.  No
divergence-freeness is used. -/
theorem exists_fderivSupBound_of_sobolevH3 :
    ∃ A : ℝ, 0 < A ∧
      ∀ (u : SchwartzVelocity) (x : Space),
        ‖fderiv ℝ (⇑u) x‖ ≤ A * Real.sqrt (sobolevH3NormSq u) := by
  obtain ⟨C, hCpos, hC⟩ := exists_agmonSupBound
  refine ⟨3 * C, by positivity, fun u x => ?_⟩
  have hcol : ∀ j : Fin 3,
      ‖fderiv ℝ (⇑u) x (basisVector j)‖ ≤ C * Real.sqrt (sobolevH3NormSq u) := by
    intro j
    have h1 : ‖fderiv ℝ (⇑u) x (basisVector j)‖
        ≤ C * Real.sqrt (sobolevH2NormSq (columnField u j)) := by
      rw [← columnField_apply u j x]; exact hC (columnField u j) x
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
    exact Real.sqrt_le_sqrt (sobolevH2NormSq_columnField_le u j)
  calc ‖fderiv ℝ (⇑u) x‖
      ≤ ∑ j : Fin 3, ‖fderiv ℝ (⇑u) x (basisVector j)‖ := opNorm_le_sum_basisVector _
    _ ≤ ∑ _j : Fin 3, C * Real.sqrt (sobolevH3NormSq u) :=
        Finset.sum_le_sum (fun j _ => hcol j)
    _ = 3 * C * Real.sqrt (sobolevH3NormSq u) := by
        simp [Finset.sum_const]; ring

end Navier.Analysis.BealeKatoMajda

#print axioms Navier.Analysis.BealeKatoMajda.besselFourierMajorant_zero
#print axioms Navier.Analysis.BealeKatoMajda.integral_bsKernelScalar_annulus_le_log
#print axioms Navier.Analysis.BealeKatoMajda.exists_agmonMorreyBound
#print axioms Navier.Analysis.BealeKatoMajda.exists_fderivSupBound_of_sobolevH3
#print axioms Navier.Analysis.BiotSavartKernel.bsVectorKernel_coordinateLine_hasDerivAt
#print axioms Navier.Analysis.BealeKatoMajda.bsVectorKernel_coordinateLine_hasDerivAt_gradKernel
#print axioms Navier.Analysis.BealeKatoMajda.bsKernelDistributionLocalTerm_trace
#print axioms Navier.Analysis.BealeKatoMajda.integral_bsGradKernel_testFactor_ibp_away
#print axioms Navier.Analysis.BealeKatoMajda.exists_staticCurlSchwartz_h2_le_h3
#print axioms Navier.Analysis.BealeKatoMajda.exists_biotSavartKernelSplit_of_curlH2
#print axioms Navier.Analysis.BealeKatoMajda.exists_biotSavartKernelSplitting
