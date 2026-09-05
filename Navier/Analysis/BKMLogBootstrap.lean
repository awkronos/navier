import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.BKMLogLeaves
import Navier.Analysis.UniformDecayDominated
import Navier.Analysis.BiotSavartKernel
import Navier.Analysis.BiotSavartCore
import Navier.Analysis.BiotSavartIntegrationByParts
import Navier.Analysis.BiotSavartNearBounds
import Navier.Analysis.BiotSavartGradientRecovery
import Navier.Analysis.BiotSavartPVAssembly
import Navier.Analysis.BiotSavartMorrey
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
  exact
    Navier.Analysis.BiotSavartPVAssembly.exists_gradient_bound_of_curlH2

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
