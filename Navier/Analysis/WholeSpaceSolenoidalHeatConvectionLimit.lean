import Navier.Analysis.WholeSpaceSolenoidalHeatConvectionIntegrability

/-!
# Convection limit for the whole-space solenoidal heat cutoff

This file passes the convection slot of the exact compact test
`curl (chi_R G_tau a)` to its cutoff-free backward-heat-curl limit.  The
dominating function is a fixed finite sum of the four product-rule terms and
is integrable using only the `SolvesBefore` finite-energy bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped BigOperators ContDiff Matrix
open MeasureTheory Filter

namespace Navier.Analysis.WholeSpaceSolenoidalHeatConvectionLimit

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.Vorticity
open Navier.Analysis.CurlIdentities
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.WholeSpaceCutoffLimit
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatConvectionIntegrability

/-- Mixed product rule in two coordinate directions. -/
theorem mixedDirectional_mul
    {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (first second : Fin 3) (x : Space) :
    fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun y : Space => f y * g y) z (basisVector first))
        x (basisVector second) =
      fderiv ℝ
          (fun z : Space => fderiv ℝ f z (basisVector first))
          x (basisVector second) * g x +
        fderiv ℝ f x (basisVector first) *
          fderiv ℝ g x (basisVector second) +
        fderiv ℝ f x (basisVector second) *
          fderiv ℝ g x (basisVector first) +
        f x *
          fderiv ℝ
            (fun z : Space => fderiv ℝ g z (basisVector first))
            x (basisVector second) := by
  have hfirst :
      (fun z : Space =>
          fderiv ℝ (fun y : Space => f y * g y) z (basisVector first)) =
        fun z : Space =>
          fderiv ℝ f z (basisVector first) * g z +
            f z * fderiv ℝ g z (basisVector first) := by
    funext z
    change (fderiv ℝ (f * g) z) (basisVector first) = _
    rw [fderiv_mul
      ((hf.differentiable (by norm_num)).differentiableAt)
      ((hg.differentiable (by norm_num)).differentiableAt)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfirst]
  have hDf : ContDiff ℝ ∞
      (fun z : Space => fderiv ℝ f z (basisVector first)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hf (basisVector first)
  have hDg : ContDiff ℝ ∞
      (fun z : Space => fderiv ℝ g z (basisVector first)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hg (basisVector first)
  change (fderiv ℝ
    (fun z : Space =>
      fderiv ℝ f z (basisVector first) * g z +
        f z * fderiv ℝ g z (basisVector first)) x)
      (basisVector second) = _
  rw [fderiv_fun_add
    ((hDf.mul hg).differentiable (by norm_num)).differentiableAt
    ((hf.mul hDg).differentiable (by norm_num)).differentiableAt]
  rw [fderiv_fun_mul
    (hDf.differentiable (by norm_num) x)
    (hg.differentiable (by norm_num) x)]
  rw [fderiv_fun_mul
    (hf.differentiable (by norm_num) x)
    (hDg.differentiable (by norm_num) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Every fixed mixed second derivative of the scaled cutoff tends to zero. -/
theorem tendsto_mixedDirectional_scaledCutoff_zero
    (first second : Fin 3) (x : Space) :
    Tendsto (fun R : ℝ =>
      fderiv ℝ
        (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector first))
        x (basisVector second)) atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_fderiv_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
    (basisVector first) (basisVector second)
  apply squeeze_zero_norm' (a := fun R : ℝ => R⁻¹ * R⁻¹ * M)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.norm_eq_abs]
    exact abs_fderiv_fderiv_scaled_le standardBump standardBump.contDiff
      hM hR x
  · have hzero : Tendsto (fun R : ℝ => R⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    simpa using (hzero.mul hzero).mul_const M

/-- Pointwise mixed-derivative convergence for `chi_R f`. -/
theorem tendsto_mixedDirectional_scaledCutoff_mul
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (first second : Fin 3) (x : Space) :
    Tendsto (fun R : ℝ =>
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun y : Space => scaledCutoff R y * f y) z
            (basisVector first))
        x (basisVector second)) atTop
      (nhds (fderiv ℝ
        (fun z : Space => fderiv ℝ f z (basisVector first))
        x (basisVector second))) := by
  have h0 := tendsto_mixedDirectional_scaledCutoff_zero first second x
  have h1 : Tendsto (fun R : ℝ =>
      fderiv ℝ (scaledCutoff R) x (basisVector first)) atTop (nhds 0) := by
    have hgrad := scaledCutoff_staticGradient_tendsto_zero x
    rw [tendsto_pi_nhds] at hgrad
    simpa only [staticGradient, Pi.zero_apply] using hgrad first
  have h2 : Tendsto (fun R : ℝ =>
      fderiv ℝ (scaledCutoff R) x (basisVector second)) atTop (nhds 0) := by
    have hgrad := scaledCutoff_staticGradient_tendsto_zero x
    rw [tendsto_pi_nhds] at hgrad
    simpa only [staticGradient, Pi.zero_apply] using hgrad second
  have hχ : Tendsto (fun R : ℝ => scaledCutoff R x) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [scaledCutoff_eventually_one x] with R hR
    simp [hR]
  simp_rw [mixedDirectional_mul (scaledCutoff_contDiff _) hf first second x]
  simpa using (((h0.mul_const (f x)).add
    (h1.mul_const (fderiv ℝ f x (basisVector second)))).add
    (h2.mul_const (fderiv ℝ f x (basisVector first)))).add
      (hχ.mul_const (fderiv ℝ
        (fun z : Space => fderiv ℝ f z (basisVector first))
        x (basisVector second)))

/-- Dominated convergence for a mixed derivative of `chi_R f` paired with
`g`.  `H` in the proof is independent of `R` and is assembled only from the
four cutoff-free product-rule pairings. -/
theorem tendsto_integral_mixedDirectional_scaledCutoff_mul
    (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (g : Space → ℝ) (hg : Continuous g)
    (first second : Fin 3)
    (hzero : Integrable (fun y : Space => f y * g y))
    (hfirst : Integrable (fun y : Space =>
      fderiv ℝ f y (basisVector first) * g y))
    (hsecond : Integrable (fun y : Space =>
      fderiv ℝ f y (basisVector second) * g y))
    (hmixed : Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
        (basisVector second) * g y)) :
    Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => scaledCutoff R w * f w) z
              (basisVector first))
          y (basisVector second) * g y)
      atTop (nhds (∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
          (basisVector second) * g y)) := by
  obtain ⟨M₁, hM₁, hDM₁⟩ := exists_fderiv_opNorm_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
  obtain ⟨M₂, hM₂, hDM₂⟩ := exists_fderiv_fderiv_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
    (basisVector first) (basisVector second)
  let H : Space → ℝ := fun y =>
    M₂ * ‖f y * g y‖ +
      M₁ * ‖fderiv ℝ f y (basisVector second) * g y‖ +
      M₁ * ‖fderiv ℝ f y (basisVector first) * g y‖ +
      ‖fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
        (basisVector second) * g y‖
  have hH : Integrable H := by
    exact (((hzero.norm.const_mul M₂).add
      (hsecond.norm.const_mul M₁)).add
      (hfirst.norm.const_mul M₁)).add hmixed.norm
  apply tendsto_integral_filter_of_dominated_convergence H
  · filter_upwards with R
    have hprod : ContDiff ℝ ∞ (fun w : Space => scaledCutoff R w * f w) :=
      (scaledCutoff_contDiff R).mul hf
    have hD := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        hprod (basisVector first)) (basisVector second)
    exact (hD.continuous.mul hg).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards with y
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hRinv : R⁻¹ ≤ 1 := (inv_le_one₀ hR0).2 hR
    have hDchi : ∀ direction : Fin 3,
        |fderiv ℝ (scaledCutoff R) y (basisVector direction)| ≤ M₁ := by
      intro direction
      have h := abs_fderiv_scaled_le standardBump standardBump.contDiff
        hDM₁ hR0 y (basisVector direction)
      rw [Navier.Analysis.CurlDerivativeBridge.norm_basisVector, mul_one] at h
      exact h.trans (mul_le_of_le_one_left hM₁ hRinv)
    have hD2chi :
        |fderiv ℝ
            (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector first))
            y (basisVector second)| ≤ M₂ := by
      have h := abs_fderiv_fderiv_scaled_le standardBump standardBump.contDiff
        hDM₂ hR0 y
      have hRinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
      exact h.trans <| by
        calc
          R⁻¹ * R⁻¹ * M₂ ≤ 1 * 1 * M₂ := by gcongr
          _ = M₂ := by ring
    have hchi : |scaledCutoff R y| ≤ 1 := by
      rw [abs_of_nonneg (scaledCutoff_nonneg R y)]
      exact scaledCutoff_le_one R y
    rw [mixedDirectional_mul (scaledCutoff_contDiff R) hf first second y]
    change ‖
      (fderiv ℝ
          (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector first))
          y (basisVector second) * f y +
        fderiv ℝ (scaledCutoff R) y (basisVector first) *
          fderiv ℝ f y (basisVector second) +
        fderiv ℝ (scaledCutoff R) y (basisVector second) *
          fderiv ℝ f y (basisVector first) +
        scaledCutoff R y *
          fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
            (basisVector second)) * g y‖ ≤ H y
    rw [show
      (fderiv ℝ
          (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector first))
          y (basisVector second) * f y +
        fderiv ℝ (scaledCutoff R) y (basisVector first) *
          fderiv ℝ f y (basisVector second) +
        fderiv ℝ (scaledCutoff R) y (basisVector second) *
          fderiv ℝ f y (basisVector first) +
        scaledCutoff R y *
          fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
            (basisVector second)) * g y =
      fderiv ℝ
          (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector first))
          y (basisVector second) * (f y * g y) +
        fderiv ℝ (scaledCutoff R) y (basisVector first) *
          (fderiv ℝ f y (basisVector second) * g y) +
        fderiv ℝ (scaledCutoff R) y (basisVector second) *
          (fderiv ℝ f y (basisVector first) * g y) +
        scaledCutoff R y *
          (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
            (basisVector second) * g y) by ring]
    calc
      ‖fderiv ℝ
          (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector first))
          y (basisVector second) * (f y * g y) +
        fderiv ℝ (scaledCutoff R) y (basisVector first) *
          (fderiv ℝ f y (basisVector second) * g y) +
        fderiv ℝ (scaledCutoff R) y (basisVector second) *
          (fderiv ℝ f y (basisVector first) * g y) +
        scaledCutoff R y *
          (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
            (basisVector second) * g y)‖ ≤
        ‖fderiv ℝ
          (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector first))
          y (basisVector second) * (f y * g y)‖ +
        ‖fderiv ℝ (scaledCutoff R) y (basisVector first) *
          (fderiv ℝ f y (basisVector second) * g y)‖ +
        ‖fderiv ℝ (scaledCutoff R) y (basisVector second) *
          (fderiv ℝ f y (basisVector first) * g y)‖ +
        ‖scaledCutoff R y *
          (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
            (basisVector second) * g y)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add ((norm_add_le _ _).trans
              (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ H y := by
        simp only [norm_mul, Real.norm_eq_abs, H]
        have hterm2 := mul_le_mul_of_nonneg_right hD2chi
          (mul_nonneg (abs_nonneg (f y)) (abs_nonneg (g y)))
        have htermFirst := mul_le_mul_of_nonneg_right (hDchi first)
          (mul_nonneg (abs_nonneg (fderiv ℝ f y (basisVector second)))
            (abs_nonneg (g y)))
        have htermSecond := mul_le_mul_of_nonneg_right (hDchi second)
          (mul_nonneg (abs_nonneg (fderiv ℝ f y (basisVector first)))
            (abs_nonneg (g y)))
        have hterm0 := mul_le_mul_of_nonneg_right hchi
          (mul_nonneg
            (abs_nonneg
              (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector first)) y
                (basisVector second))) (abs_nonneg (g y)))
        exact add_le_add
          (add_le_add
            (add_le_add hterm2 htermFirst) htermSecond)
          (by simpa only [one_mul] using hterm0)
  · exact hH
  · filter_upwards with y
    exact (tendsto_mixedDirectional_scaledCutoff_mul hf first second y).mul_const
      (g y)

/-- A bounded continuous scalar multiplier can be paired with any two
coordinates of a finite-energy solution slice. -/
private theorem SolvesBefore.integrable_boundedMultiplier_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    (F : Space → ℝ) (hF : Continuous F)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ y, |F y| ≤ K)
    (first second : Fin 3) :
    Integrable (fun y : Space => F y * u s y first * u s y second) := by
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hmajor : Integrable (fun y : Space => K * ‖u s y‖ ^ 2) :=
    (hsol.finite_energy s hs0 hsT).const_mul K
  apply hmajor.mono'
    (((hF.mul ((continuous_apply first).comp hu.continuous)).mul
      ((continuous_apply second).comp hu.continuous)).aestronglyMeasurable)
  filter_upwards with y
  have hu1 : |u s y first| ≤ ‖u s y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (u s y) first
  have hu2 : |u s y second| ≤ ‖u s y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (u s y) second
  change |F y * u s y first * u s y second| ≤ K * ‖u s y‖ ^ 2
  rw [abs_mul, abs_mul]
  calc
    |F y| * |u s y first| * |u s y second| ≤
        K * ‖u s y‖ * ‖u s y‖ := by
      exact mul_le_mul
        (mul_le_mul (hbound y) hu1 (abs_nonneg _) hK) hu2
        (abs_nonneg _) (mul_nonneg hK (norm_nonneg _))
    _ = K * ‖u s y‖ ^ 2 := by ring

private theorem SolvesBefore.integrable_heatKernel_translate_mul_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (first second : Fin 3) :
    Integrable (fun y : Space =>
      heatKernel κ τ (x₀ - y) * u s y first * u s y second) := by
  let P : ℝ := (4 * Real.pi * κ * τ) ^ (-(3 : ℝ) / 2)
  apply SolvesBefore.integrable_boundedMultiplier_velocityPair hsol hs0 hsT
    (fun y : Space => heatKernel κ τ (x₀ - y))
    ((heatKernel_translate_contDiff κ τ x₀).continuous) P
    (by simp only [P]; positivity) _ first second
  intro y
  rw [abs_of_nonneg (heatKernel_nonneg hκ hτ _)]
  simpa only [P] using heatKernel_translate_le_peak hκ hτ x₀ y

private theorem SolvesBefore.integrable_fderiv_heatKernel_translate_mul_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (derivative first second : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
        (basisVector derivative) * u s y first * u s y second) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_abs_fderiv_heatKernel_translate_le_doubled hκ hτ
  let P : ℝ := (4 * Real.pi * κ * (2 * τ)) ^ (-(3 : ℝ) / 2)
  let K : ℝ := C * P
  have hG : ContDiff ℝ ∞ (fun z : Space => heatKernel κ τ (x₀ - z)) :=
    heatKernel_translate_contDiff κ τ x₀
  have hDF : Continuous (fun y : Space =>
      fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
        (basisVector derivative)) :=
    (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hG (basisVector derivative)).continuous
  apply SolvesBefore.integrable_boundedMultiplier_velocityPair hsol hs0 hsT _ hDF K
    (by simp only [K, P]; positivity) _ first second
  intro y
  calc
    |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
        (basisVector derivative)| ≤
      C * heatKernel κ (2 * τ) (x₀ - y) * ‖(basisVector derivative : Space)‖ :=
        hbound x₀ y (basisVector derivative)
    _ = C * heatKernel κ (2 * τ) (x₀ - y) := by
      rw [Navier.Analysis.CurlDerivativeBridge.norm_basisVector, mul_one]
    _ ≤ C * P := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      simpa only [P] using heatKernel_translate_le_peak hκ
        (by positivity : 0 < 2 * τ) x₀ y
    _ = K := rfl

/-- The mixed second derivative of the scalar cutoff-Gaussian has the actual
finite-energy convection limit, for arbitrary derivative and velocity
coordinates. -/
theorem SolvesBefore.tendsto_integral_mixedDirectional_scaledCutoff_heatKernel_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (firstDerivative secondDerivative velocityOne velocityTwo : Fin 3) :
    Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun w : Space =>
            scaledCutoff R w * heatKernel κ τ (x₀ - w)) z
              (basisVector firstDerivative))
        y (basisVector secondDerivative) *
          u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstDerivative))
          y (basisVector secondDerivative) *
            u s y velocityOne * u s y velocityTwo)) := by
  let G : Space → ℝ := fun y => heatKernel κ τ (x₀ - y)
  let g : Space → ℝ := fun y => u s y velocityOne * u s y velocityTwo
  have hGs : ContDiff ℝ ∞ G := heatKernel_translate_contDiff κ τ x₀
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hg : Continuous g :=
    ((continuous_apply velocityOne).comp hu.continuous).mul
      ((continuous_apply velocityTwo).comp hu.continuous)
  have hzero : Integrable (fun y : Space => G y * g y) := by
    simpa only [G, g, mul_assoc] using
      SolvesBefore.integrable_heatKernel_translate_mul_velocityPair hsol
        hs0 hsT hκ hτ x₀ velocityOne velocityTwo
  have hfirst : Integrable (fun y : Space =>
      fderiv ℝ G y (basisVector firstDerivative) * g y) := by
    simpa only [G, g, mul_assoc] using
      SolvesBefore.integrable_fderiv_heatKernel_translate_mul_velocityPair
        hsol hs0 hsT hκ hτ x₀ firstDerivative velocityOne velocityTwo
  have hsecond : Integrable (fun y : Space =>
      fderiv ℝ G y (basisVector secondDerivative) * g y) := by
    simpa only [G, g, mul_assoc] using
      SolvesBefore.integrable_fderiv_heatKernel_translate_mul_velocityPair
        hsol hs0 hsT hκ hτ x₀ secondDerivative velocityOne velocityTwo
  have hmixed : Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => fderiv ℝ G z
        (basisVector firstDerivative)) y (basisVector secondDerivative) * g y) := by
    simpa only [G, g, mul_assoc] using
      SolvesBefore.integrable_secondHeatKernel_translate_mul_velocityPair hsol
        hs0 hsT hκ hτ x₀ firstDerivative secondDerivative
          velocityOne velocityTwo
  have hlim := tendsto_integral_mixedDirectional_scaledCutoff_mul G hGs g hg
    firstDerivative secondDerivative hzero hfirst hsecond hmixed
  simpa only [G, g, mul_assoc] using hlim

private theorem atTopCompactBackwardHeatCurlTest_component_zero
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y 0) =
    fun y : Space =>
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 1) * a 2 -
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 2) * a 1 := by
  funext y
  change staticCurl (fun z : Space =>
    scaledCutoff (max 1 R) z •
      (heatKernel κ τ (x₀ - z) • a)) y 0 = _
  rw [show (fun z : Space =>
      scaledCutoff (max 1 R) z • (heatKernel κ τ (x₀ - z) • a)) =
      (fun z : Space =>
        (scaledCutoff (max 1 R) z * heatKernel κ τ (x₀ - z)) • a) by
        funext z
        rw [smul_smul]]
  rw [staticCurl_smul]
  · simp [staticGradient, staticCurl, cross_apply, basisVector]
  · exact (((scaledCutoff_contDiff (max 1 R)).mul
      (heatKernel_translate_contDiff κ τ x₀)).differentiable
        (by norm_num)).differentiableAt
  · exact differentiableAt_const a

private theorem atTopCompactBackwardHeatCurlTest_component_one
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y 1) =
    fun y : Space =>
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 2) * a 0 -
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 0) * a 2 := by
  funext y
  change staticCurl (fun z : Space =>
    scaledCutoff (max 1 R) z •
      (heatKernel κ τ (x₀ - z) • a)) y 1 = _
  rw [show (fun z : Space =>
      scaledCutoff (max 1 R) z • (heatKernel κ τ (x₀ - z) • a)) =
      (fun z : Space =>
        (scaledCutoff (max 1 R) z * heatKernel κ τ (x₀ - z)) • a) by
        funext z
        rw [smul_smul]]
  rw [staticCurl_smul]
  · simp [staticGradient, staticCurl, cross_apply, basisVector]
  · exact (((scaledCutoff_contDiff (max 1 R)).mul
      (heatKernel_translate_contDiff κ τ x₀)).differentiable
        (by norm_num)).differentiableAt
  · exact differentiableAt_const a

private theorem atTopCompactBackwardHeatCurlTest_component_two
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space =>
      (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field y 2) =
    fun y : Space =>
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 0) * a 1 -
      fderiv ℝ (fun w : Space =>
        scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) y
          (basisVector 1) * a 0 := by
  funext y
  change staticCurl (fun z : Space =>
    scaledCutoff (max 1 R) z •
      (heatKernel κ τ (x₀ - z) • a)) y 2 = _
  rw [show (fun z : Space =>
      scaledCutoff (max 1 R) z • (heatKernel κ τ (x₀ - z) • a)) =
      (fun z : Space =>
        (scaledCutoff (max 1 R) z * heatKernel κ τ (x₀ - z)) • a) by
        funext z
        rw [smul_smul]]
  rw [staticCurl_smul]
  · simp [staticGradient, staticCurl, cross_apply, basisVector]
  · exact (((scaledCutoff_contDiff (max 1 R)).mul
      (heatKernel_translate_contDiff κ τ x₀)).differentiable
        (by norm_num)).differentiableAt
  · exact differentiableAt_const a

private theorem backwardHeatCurlField_component_zero
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 0) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 1) * a 2 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 2) * a 1 := by
  funext y
  rw [Navier.Analysis.WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

private theorem backwardHeatCurlField_component_one
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 1) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 2) * a 0 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 0) * a 2 := by
  funext y
  rw [Navier.Analysis.WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

private theorem backwardHeatCurlField_component_two
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 2) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 0) * a 1 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 1) * a 0 := by
  funext y
  rw [Navier.Analysis.WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

private theorem directional_constLinearCombination
    {F H : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    (c d : ℝ) (direction : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => F y * c - H y * d) x
        (basisVector direction) =
      fderiv ℝ F x (basisVector direction) * c -
        fderiv ℝ H x (basisVector direction) * d := by
  rw [fderiv_fun_sub]
  · change (fderiv ℝ (F * fun _ : Space => c) x -
      fderiv ℝ (H * fun _ : Space => d) x) (basisVector direction) = _
    rw [fderiv_mul
        ((hF.differentiable (by norm_num)).differentiableAt)
        (differentiableAt_const c),
      fderiv_mul
        ((hH.differentiable (by norm_num)).differentiableAt)
        (differentiableAt_const d)]
    simp only [sub_apply, add_apply, smul_apply, fderiv_const_apply,
      zero_apply, mul_zero, smul_eq_mul]
    ring
  · exact ((hF.mul contDiff_const).differentiable
      (by norm_num)).differentiableAt
  · exact ((hH.mul contDiff_const).differentiable
      (by norm_num)).differentiableAt

private theorem SolvesBefore.integrable_cutoffHeat_mixed_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {R : ℝ} (hR : 0 < R) {κ τ : ℝ} (x₀ : Space)
    (firstDerivative secondDerivative velocityOne velocityTwo : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun w : Space =>
            scaledCutoff R w * heatKernel κ τ (x₀ - w)) z
              (basisVector firstDerivative))
        y (basisVector secondDerivative) *
          u s y velocityOne * u s y velocityTwo) := by
  let F : Space → ℝ := fun w =>
    scaledCutoff R w * heatKernel κ τ (x₀ - w)
  have hF : ContDiff ℝ ∞ F :=
    (scaledCutoff_contDiff R).mul (heatKernel_translate_contDiff κ τ x₀)
  have hD := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hF (basisVector firstDerivative)) (basisVector secondDerivative)
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hsuppF : HasCompactSupport F :=
    (scaledCutoff_hasCompactSupport hR).mul_right
  have hsuppD := (hsuppF.fderiv_apply ℝ (basisVector firstDerivative)).fderiv_apply
    ℝ (basisVector secondDerivative)
  have hsupp : HasCompactSupport (fun y : Space =>
      fderiv ℝ
        (fun z : Space => fderiv ℝ F z (basisVector firstDerivative))
        y (basisVector secondDerivative) *
          u s y velocityOne * u s y velocityTwo) :=
    hsuppD.mul_right.mul_right
  exact (((hD.continuous.mul
    ((continuous_apply velocityOne).comp hu.continuous)).mul
      ((continuous_apply velocityTwo).comp hu.continuous)).integrable_of_hasCompactSupport
        hsupp)

private theorem SolvesBefore.tendsto_integral_cutoffHeatCurlPair_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (firstA firstB direction velocityOne velocityTwo : Fin 3) (c d : ℝ) :
    Tendsto (fun R : ℝ => ∫ y : Space,
      (fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space =>
              scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
                (basisVector firstA))
          y (basisVector direction) * c -
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space =>
              scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
                (basisVector firstB))
          y (basisVector direction) * d) *
            u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        (fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstA))
            y (basisVector direction) * c -
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstB))
            y (basisVector direction) * d) *
              u s y velocityOne * u s y velocityTwo)) := by
  have hA0 :=
    SolvesBefore.tendsto_integral_mixedDirectional_scaledCutoff_heatKernel_velocityPair
      hsol hs0 hsT hκ hτ x₀ firstA direction velocityOne velocityTwo
  have hB0 :=
    SolvesBefore.tendsto_integral_mixedDirectional_scaledCutoff_heatKernel_velocityPair
      hsol hs0 hsT hκ hτ x₀ firstB direction velocityOne velocityTwo
  have hA : Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun w : Space =>
            scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
              (basisVector firstA))
        y (basisVector direction) * u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstA))
          y (basisVector direction) * u s y velocityOne * u s y velocityTwo)) := by
    apply hA0.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    rw [max_eq_right hR]
  have hB : Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun w : Space =>
            scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
              (basisVector firstB))
        y (basisVector direction) * u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstB))
          y (basisVector direction) * u s y velocityOne * u s y velocityTwo)) := by
    apply hB0.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    rw [max_eq_right hR]
  have hcomb := (hA.const_mul c).sub (hB.const_mul d)
  have htarget :
      (∫ y : Space,
        (fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstA))
            y (basisVector direction) * c -
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstB))
            y (basisVector direction) * d) *
              u s y velocityOne * u s y velocityTwo) =
      c * (∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstA))
          y (basisVector direction) * u s y velocityOne * u s y velocityTwo) -
      d * (∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstB))
          y (basisVector direction) * u s y velocityOne * u s y velocityTwo) := by
    have hi := (SolvesBefore.integrable_secondHeatKernel_translate_mul_velocityPair
      hsol hs0 hsT hκ hτ x₀ firstA direction velocityOne velocityTwo).const_mul c
    have hj := (SolvesBefore.integrable_secondHeatKernel_translate_mul_velocityPair
      hsol hs0 hsT hκ hτ x₀ firstB direction velocityOne velocityTwo).const_mul d
    rw [show (fun y : Space =>
      (fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstA)) y (basisVector direction) * c -
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstB)) y (basisVector direction) * d) *
          u s y velocityOne * u s y velocityTwo) =
      (fun y : Space => c *
        (fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstA)) y (basisVector direction) *
                u s y velocityOne * u s y velocityTwo) - d *
        (fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector firstB)) y (basisVector direction) *
                u s y velocityOne * u s y velocityTwo)) by funext y; ring,
      integral_sub hi hj, integral_const_mul, integral_const_mul]

  rw [htarget]
  apply hcomb.congr'
  filter_upwards with R
  have hRpos : 0 < max 1 R := lt_of_lt_of_le zero_lt_one (le_max_left 1 R)
  have hi := (SolvesBefore.integrable_cutoffHeat_mixed_velocityPair hsol
    hs0 hsT hRpos (κ := κ) (τ := τ) x₀ firstA direction
      velocityOne velocityTwo).const_mul c
  have hj := (SolvesBefore.integrable_cutoffHeat_mixed_velocityPair hsol
    hs0 hsT hRpos (κ := κ) (τ := τ) x₀ firstB direction
      velocityOne velocityTwo).const_mul d
  rw [show (fun y : Space =>
      (fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space =>
              scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
                (basisVector firstA)) y (basisVector direction) * c -
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space =>
              scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
                (basisVector firstB)) y (basisVector direction) * d) *
          u s y velocityOne * u s y velocityTwo) =
      (fun y : Space => c *
        (fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space =>
              scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
                (basisVector firstA)) y (basisVector direction) *
                  u s y velocityOne * u s y velocityTwo) - d *
        (fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space =>
              scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
                (basisVector firstB)) y (basisVector direction) *
                  u s y velocityOne * u s y velocityTwo)) by funext y; ring,
      integral_sub hi hj, integral_const_mul, integral_const_mul]

private theorem SolvesBefore.tendsto_integral_directional_cutoffHeatCurlPair_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (firstA firstB direction velocityOne velocityTwo : Fin 3) (c d : ℝ) :
    Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun w : Space =>
            scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
              (basisVector firstA) * c -
          fderiv ℝ (fun w : Space =>
            scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) z
              (basisVector firstB) * d)
        y (basisVector direction) *
          u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstA) * c -
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstB) * d)
          y (basisVector direction) *
            u s y velocityOne * u s y velocityTwo)) := by
  have hpair := SolvesBefore.tendsto_integral_cutoffHeatCurlPair_velocityPair
    hsol hs0 hsT hκ hτ x₀ firstA firstB direction velocityOne velocityTwo c d
  have hG : ContDiff ℝ ∞
      (fun w : Space => heatKernel κ τ (x₀ - w)) :=
    heatKernel_translate_contDiff κ τ x₀
  have hDA := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hG (basisVector firstA)
  have hDB := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hG (basisVector firstB)
  have htarget :
      (∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstA) * c -
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstB) * d)
          y (basisVector direction) *
            u s y velocityOne * u s y velocityTwo) =
      (∫ y : Space,
        (fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstA)) y (basisVector direction) * c -
          fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector firstB)) y (basisVector direction) * d) *
              u s y velocityOne * u s y velocityTwo) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [directional_constLinearCombination hDA hDB]
  rw [htarget]
  apply hpair.congr'
  filter_upwards with R
  have hprod : ContDiff ℝ ∞ (fun w : Space =>
      scaledCutoff (max 1 R) w * heatKernel κ τ (x₀ - w)) :=
    (scaledCutoff_contDiff (max 1 R)).mul hG
  have hPA := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hprod (basisVector firstA)
  have hPB := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hprod (basisVector firstB)
  apply integral_congr_ae
  filter_upwards with y
  rw [directional_constLinearCombination hPA hPB]

/-- One basis-direction component of the actual compact solenoidal test has
the cutoff-free convection limit. -/
theorem SolvesBefore.tendsto_integral_directional_compactBackwardHeatCurlTest_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityOne velocityTwo : Fin 3) :
    Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z fieldComponent)
        y (basisVector direction) *
          u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (basisVector direction) *
            u s y velocityOne * u s y velocityTwo)) := by
  fin_cases fieldComponent
  · change Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 0)
        y (basisVector direction) *
          u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 0)
          y (basisVector direction) *
            u s y velocityOne * u s y velocityTwo))
    simpa only [atTopCompactBackwardHeatCurlTest_component_zero,
      backwardHeatCurlField_component_zero] using
      SolvesBefore.tendsto_integral_directional_cutoffHeatCurlPair_velocityPair
        hsol hs0 hsT hκ hτ x₀ 1 2 direction velocityOne velocityTwo
          (a 2) (a 1)
  · change Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 1)
        y (basisVector direction) *
          u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 1)
          y (basisVector direction) *
            u s y velocityOne * u s y velocityTwo))
    simpa only [atTopCompactBackwardHeatCurlTest_component_one,
      backwardHeatCurlField_component_one] using
      SolvesBefore.tendsto_integral_directional_cutoffHeatCurlPair_velocityPair
        hsol hs0 hsT hκ hτ x₀ 2 0 direction velocityOne velocityTwo
          (a 0) (a 2)
  · change Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z 2)
        y (basisVector direction) *
          u s y velocityOne * u s y velocityTwo)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 2)
          y (basisVector direction) *
            u s y velocityOne * u s y velocityTwo))
    simpa only [atTopCompactBackwardHeatCurlTest_component_two,
      backwardHeatCurlField_component_two] using
      SolvesBefore.tendsto_integral_directional_cutoffHeatCurlPair_velocityPair
        hsol hs0 hsT hκ hτ x₀ 0 1 direction velocityOne velocityTwo
          (a 1) (a 0)

private theorem SolvesBefore.integrable_compactTest_directional_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    (φ : CompactSolenoidalTest)
    (direction fieldComponent velocityOne velocityTwo : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => φ.field z fieldComponent) y
        (basisVector direction) * u s y velocityOne * u s y velocityTwo) := by
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hD := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    (φ.smooth fieldComponent) (basisVector direction)
  have hsupp := (φ.compact fieldComponent).fderiv_apply ℝ (basisVector direction)
  exact (((hD.continuous.mul
    ((continuous_apply velocityOne).comp hu.continuous)).mul
      ((continuous_apply velocityTwo).comp hu.continuous)).integrable_of_hasCompactSupport
        hsupp.mul_right.mul_right)

/-- The actual convection integral for one field component converges: the
derivative direction is `u(s,y)`, exactly as in `lerayWeakRhs`. -/
theorem SolvesBefore.tendsto_integral_compactBackwardHeatCurlTest_convectionComponent
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (fieldComponent : Fin 3) :
    Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z fieldComponent)
        y (u s y) * u s y fieldComponent)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (u s y) * u s y fieldComponent)) := by
  have hdirs : ∀ direction : Fin 3, Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ
        (fun z : Space =>
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z fieldComponent)
        y (basisVector direction) * u s y direction * u s y fieldComponent)
      atTop (nhds (∫ y : Space,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (basisVector direction) * u s y direction * u s y fieldComponent)) :=
    fun direction =>
      SolvesBefore.tendsto_integral_directional_compactBackwardHeatCurlTest_velocityPair
        hsol hs0 hsT hκ hτ x₀ a direction fieldComponent direction fieldComponent
  have hsum := tendsto_finsetSum Finset.univ (fun direction _ => hdirs direction)
  have htarget :
      (∫ y : Space,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (u s y) * u s y fieldComponent) =
      ∑ direction : Fin 3, ∫ y : Space,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (basisVector direction) * u s y direction * u s y fieldComponent := by
    rw [show (fun y : Space =>
      fderiv ℝ
        (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
        y (u s y) * u s y fieldComponent) =
      (fun y : Space => ∑ direction : Fin 3,
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (basisVector direction) * u s y direction * u s y fieldComponent) by
        funext y
        rw [Navier.Analysis.CutoffIntegrationByParts.fderiv_apply_eq_sum_basis]
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro direction _
        ring]
    apply integral_finsetSum
    intro direction _
    exact SolvesBefore.integrable_directional_backwardHeatCurlField_mul_velocityPair
      hsol hs0 hsT hκ hτ x₀ a direction fieldComponent direction fieldComponent
  rw [htarget]
  apply hsum.congr'
  filter_upwards with R
  let φ := atTopCompactBackwardHeatCurlTest R κ τ x₀ a
  have hsource :
      (∫ y : Space,
        fderiv ℝ (fun z : Space => φ.field z fieldComponent) y (u s y) *
          u s y fieldComponent) =
      ∑ direction : Fin 3, ∫ y : Space,
        fderiv ℝ (fun z : Space => φ.field z fieldComponent) y
          (basisVector direction) * u s y direction * u s y fieldComponent := by
    rw [show (fun y : Space =>
      fderiv ℝ (fun z : Space => φ.field z fieldComponent) y (u s y) *
        u s y fieldComponent) =
      (fun y : Space => ∑ direction : Fin 3,
        fderiv ℝ (fun z : Space => φ.field z fieldComponent) y
          (basisVector direction) * u s y direction * u s y fieldComponent) by
        funext y
        rw [Navier.Analysis.CutoffIntegrationByParts.fderiv_apply_eq_sum_basis]
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro direction _
        ring]
    apply integral_finsetSum
    intro direction _
    exact SolvesBefore.integrable_compactTest_directional_velocityPair hsol
      hs0 hsT φ direction fieldComponent direction fieldComponent
  exact hsource.symm

/-- The cutoff-free convection slot associated with the backward-heat curl. -/
def backwardHeatCurlConvectionRhs
    (κ τ : ℝ) (x₀ a : Space) (u : VelocityEvolution) (s : ℝ) : ℝ :=
  ∑ fieldComponent : Fin 3, ∫ y : Space,
    fderiv ℝ
      (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
      y (u s y) * u s y fieldComponent

/-- **Actual compact-test convection limit.**  The whole convection sum in
the compact solenoidal `lerayWeakRhs` converges to the cutoff-free
backward-heat-curl convection slot on every preterminal `SolvesBefore` slice.
-/
theorem SolvesBefore.tendsto_compactBackwardHeatCurlTest_convection
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    Tendsto (fun R : ℝ =>
      ∑ fieldComponent : Fin 3, ∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z
              fieldComponent)
          y (u s y) * u s y fieldComponent)
      atTop (nhds (backwardHeatCurlConvectionRhs κ τ x₀ a u s)) := by
  unfold backwardHeatCurlConvectionRhs
  exact tendsto_finsetSum Finset.univ (fun fieldComponent _ =>
    SolvesBefore.tendsto_integral_compactBackwardHeatCurlTest_convectionComponent
      hsol hs0 hsT hκ hτ x₀ a fieldComponent)

/-- The exact weak evolution for the same compact test is packaged with its
now-closed convection cutoff limit. -/
theorem solvesBefore_compactBackwardHeatCurlEvolution_with_convectionLimit
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a₀ : Space)
    {a b s : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hs0 : 0 ≤ s) (hsT : s < T) :
    (∀ R : ℝ,
      testedMomentum (atTopCompactBackwardHeatCurlTest R κ τ x₀ a₀) u b -
          testedMomentum (atTopCompactBackwardHeatCurlTest R κ τ x₀ a₀) u a =
        ∫ t in a..b,
          lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a₀) u t) ∧
    Tendsto (fun R : ℝ =>
      ∑ fieldComponent : Fin 3, ∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a₀).field z
              fieldComponent)
          y (u s y) * u s y fieldComponent)
      atTop (nhds (backwardHeatCurlConvectionRhs κ τ x₀ a₀ u s)) := by
  refine ⟨?_, SolvesBefore.tendsto_compactBackwardHeatCurlTest_convection
    hsol hs0 hsT hκ hτ x₀ a₀⟩
  intro R
  exact solvesBefore_compactBackwardHeatCurlEvolution hT hsol
    (R := max 1 R) (lt_of_lt_of_le zero_lt_one (le_max_left 1 R))
      κ τ x₀ a₀ ha0 hab hbT

end Navier.Analysis.WholeSpaceSolenoidalHeatConvectionLimit
