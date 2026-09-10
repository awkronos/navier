import Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit

/-!
# Vanishing viscous cutoff-gradient correction

For the compact solenoidal test
`curl (χ_R G_τ a) = ∇χ_R × (G_τ a) + χ_R curl (G_τ a)`, this module
removes the first summand from the spatial viscous pairing.  Two diagonal
derivatives of that summand contain first, second, and third derivatives of
`χ_R`; their `R⁻¹`, `R⁻²`, and `R⁻³` rates are paired only with the Gaussian
and its first two derivatives.  Finite energy supplies every resulting
integrable envelope on the exact `SolvesBefore` carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Matrix
open MeasureTheory Filter

namespace Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit
open Navier.Analysis.HeatSemigroupSmoothing

/-- Every fixed mixed second derivative of `χ_R` tends to zero. -/
theorem tendsto_mixedSecondDirectional_scaledCutoff_zero
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

/-- Every fixed coordinate third derivative of `χ_R` tends to zero. -/
theorem tendsto_thirdDirectional_scaledCutoff_zero
    (first second third : Fin 3) (x : Space) :
    Tendsto (fun R : ℝ => thirdDirectional (scaledCutoff R)
      (basisVector first) (basisVector second) (basisVector third) x)
      atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_thirdDirectional_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
    (basisVector first) (basisVector second) (basisVector third)
  apply squeeze_zero_norm' (a := fun R : ℝ => R⁻¹ * R⁻¹ * R⁻¹ * M)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.norm_eq_abs]
    exact abs_thirdDirectional_scaled_le standardBump standardBump.contDiff
      hM hR x
  · have hzero : Tendsto (fun R : ℝ => R⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    simpa using ((hzero.mul hzero).mul hzero).mul_const M

/-- The differentiated cutoff factor times a smooth scalar tends pointwise
to zero after two further derivatives. -/
theorem tendsto_secondDirectional_cutoffDirectional_mul_zero
    (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (cutoffDirection direction : Fin 3) (x : Space) :
    Tendsto (fun R : ℝ =>
      fderiv ℝ
        (fun z : Space => fderiv ℝ
          (fun y : Space =>
            fderiv ℝ (scaledCutoff R) y (basisVector cutoffDirection) * f y)
          z (basisVector direction))
        x (basisVector direction)) atTop (nhds 0) := by
  have hq : ∀ R : ℝ, ContDiff ℝ ∞ (fun y : Space =>
      fderiv ℝ (scaledCutoff R) y (basisVector cutoffDirection)) := fun R =>
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      (scaledCutoff_contDiff R) (basisVector cutoffDirection)
  have h0 : Tendsto (fun R : ℝ =>
      fderiv ℝ (scaledCutoff R) x (basisVector cutoffDirection))
      atTop (nhds 0) := by
    have hgrad := scaledCutoff_staticGradient_tendsto_zero x
    rw [tendsto_pi_nhds] at hgrad
    simpa only [staticGradient, Pi.zero_apply] using hgrad cutoffDirection
  have h1 := tendsto_mixedSecondDirectional_scaledCutoff_zero
    cutoffDirection direction x
  have h2 := tendsto_thirdDirectional_scaledCutoff_zero
    cutoffDirection direction direction x
  simp_rw [secondDirectional_mul (hq _) hf direction x]
  have hfirst := h2.mul_const (f x)
  have hmiddle := (h1.mul_const
    (fderiv ℝ f x (basisVector direction))).const_mul 2
  have hlast := h0.mul_const
    (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction))
      x (basisVector direction))
  convert (hfirst.add hmiddle).add hlast using 1 <;> simp [thirdDirectional]

/-- The three cutoff-free pairings dominate the full second derivative of
`(D_k χ_R) f`, uniformly for `R ≥ 1`, and its integral tends to zero. -/
theorem tendsto_integral_secondDirectional_cutoffDirectional_mul_zero
    (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (g : Space → ℝ) (hg : Continuous g)
    (cutoffDirection direction : Fin 3)
    (hzero : Integrable (fun y : Space => f y * g y))
    (hone : Integrable (fun y : Space =>
      fderiv ℝ f y (basisVector direction) * g y))
    (htwo : Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction)) y
        (basisVector direction) * g y)) :
    Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ
          (fun z : Space => fderiv ℝ
            (fun w : Space =>
              fderiv ℝ (scaledCutoff R) w (basisVector cutoffDirection) * f w)
            z (basisVector direction))
          y (basisVector direction) * g y)
      atTop (nhds 0) := by
  obtain ⟨M₁, hM₁, hDM₁⟩ := exists_fderiv_opNorm_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
  obtain ⟨M₂, hM₂, hDM₂⟩ := exists_fderiv_fderiv_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
    (basisVector cutoffDirection) (basisVector direction)
  obtain ⟨M₃, hM₃, hDM₃⟩ := exists_thirdDirectional_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
    (basisVector cutoffDirection) (basisVector direction) (basisVector direction)
  let H : Space → ℝ := fun y =>
    M₃ * ‖f y * g y‖ +
      (2 * M₂) * ‖fderiv ℝ f y (basisVector direction) * g y‖ +
      M₁ * ‖fderiv ℝ (fun z : Space =>
        fderiv ℝ f z (basisVector direction)) y
          (basisVector direction) * g y‖
  have hH : Integrable H := by
    exact ((hzero.norm.const_mul M₃).add
      (hone.norm.const_mul (2 * M₂))).add (htwo.norm.const_mul M₁)
  have hlim : Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ
          (fun z : Space => fderiv ℝ
            (fun w : Space =>
              fderiv ℝ (scaledCutoff R) w (basisVector cutoffDirection) * f w)
            z (basisVector direction))
          y (basisVector direction) * g y)
      atTop (nhds (∫ _y : Space, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence H
    · filter_upwards with R
      have hq : ContDiff ℝ ∞ (fun w : Space =>
          fderiv ℝ (scaledCutoff R) w (basisVector cutoffDirection)) :=
        Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
          (scaledCutoff_contDiff R) (basisVector cutoffDirection)
      have hprod := hq.mul hf
      have hD := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
          hprod (basisVector direction)) (basisVector direction)
      exact (hD.continuous.mul hg).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      filter_upwards with y
      have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
      have hRinv : R⁻¹ ≤ 1 := (inv_le_one₀ hR0).2 hR
      have hq0 :
          |fderiv ℝ (scaledCutoff R) y (basisVector cutoffDirection)| ≤ M₁ := by
        have h := abs_fderiv_scaled_le standardBump standardBump.contDiff
          hDM₁ hR0 y (basisVector cutoffDirection)
        rw [Navier.Analysis.CurlDerivativeBridge.norm_basisVector, mul_one] at h
        exact h.trans (mul_le_of_le_one_left hM₁ hRinv)
      have hq1 :
          |fderiv ℝ
            (fun z : Space => fderiv ℝ (scaledCutoff R) z
              (basisVector cutoffDirection)) y (basisVector direction)| ≤ M₂ := by
        have h := abs_fderiv_fderiv_scaled_le standardBump standardBump.contDiff
          hDM₂ hR0 y
        have hRinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
        exact h.trans <| by
          calc
            R⁻¹ * R⁻¹ * M₂ ≤ 1 * 1 * M₂ := by gcongr
            _ = M₂ := by ring
      have hq2 :
          |thirdDirectional (scaledCutoff R) (basisVector cutoffDirection)
            (basisVector direction) (basisVector direction) y| ≤ M₃ := by
        have h := abs_thirdDirectional_scaled_le standardBump
          standardBump.contDiff hDM₃ hR0 y
        have hRinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
        exact h.trans <| by
          calc
            R⁻¹ * R⁻¹ * R⁻¹ * M₃ ≤ 1 * 1 * 1 * M₃ := by gcongr
            _ = M₃ := by ring
      have hqSmooth : ContDiff ℝ ∞ (fun w : Space =>
          fderiv ℝ (scaledCutoff R) w (basisVector cutoffDirection)) :=
        Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
          (scaledCutoff_contDiff R) (basisVector cutoffDirection)
      rw [secondDirectional_mul hqSmooth hf direction y]
      change ‖
        (thirdDirectional (scaledCutoff R) (basisVector cutoffDirection)
            (basisVector direction) (basisVector direction) y * f y +
          2 * (fderiv ℝ
            (fun z : Space => fderiv ℝ (scaledCutoff R) z
              (basisVector cutoffDirection)) y (basisVector direction) *
            fderiv ℝ f y (basisVector direction)) +
          fderiv ℝ (scaledCutoff R) y (basisVector cutoffDirection) *
            fderiv ℝ (fun z : Space => fderiv ℝ f z
              (basisVector direction)) y (basisVector direction)) * g y‖ ≤ H y
      rw [show
        (thirdDirectional (scaledCutoff R) (basisVector cutoffDirection)
            (basisVector direction) (basisVector direction) y * f y +
          2 * (fderiv ℝ
            (fun z : Space => fderiv ℝ (scaledCutoff R) z
              (basisVector cutoffDirection)) y (basisVector direction) *
            fderiv ℝ f y (basisVector direction)) +
          fderiv ℝ (scaledCutoff R) y (basisVector cutoffDirection) *
            fderiv ℝ (fun z : Space => fderiv ℝ f z
              (basisVector direction)) y (basisVector direction)) * g y =
        thirdDirectional (scaledCutoff R) (basisVector cutoffDirection)
            (basisVector direction) (basisVector direction) y * (f y * g y) +
          (2 * fderiv ℝ
            (fun z : Space => fderiv ℝ (scaledCutoff R) z
              (basisVector cutoffDirection)) y (basisVector direction)) *
            (fderiv ℝ f y (basisVector direction) * g y) +
          fderiv ℝ (scaledCutoff R) y (basisVector cutoffDirection) *
            (fderiv ℝ (fun z : Space => fderiv ℝ f z
              (basisVector direction)) y (basisVector direction) * g y) by ring]
      calc
        ‖thirdDirectional (scaledCutoff R) (basisVector cutoffDirection)
              (basisVector direction) (basisVector direction) y * (f y * g y) +
            (2 * fderiv ℝ
              (fun z : Space => fderiv ℝ (scaledCutoff R) z
                (basisVector cutoffDirection)) y (basisVector direction)) *
              (fderiv ℝ f y (basisVector direction) * g y) +
            fderiv ℝ (scaledCutoff R) y (basisVector cutoffDirection) *
              (fderiv ℝ (fun z : Space => fderiv ℝ f z
                (basisVector direction)) y (basisVector direction) * g y)‖ ≤
          ‖thirdDirectional (scaledCutoff R) (basisVector cutoffDirection)
              (basisVector direction) (basisVector direction) y * (f y * g y)‖ +
            ‖(2 * fderiv ℝ
              (fun z : Space => fderiv ℝ (scaledCutoff R) z
                (basisVector cutoffDirection)) y (basisVector direction)) *
              (fderiv ℝ f y (basisVector direction) * g y)‖ +
            ‖fderiv ℝ (scaledCutoff R) y (basisVector cutoffDirection) *
              (fderiv ℝ (fun z : Space => fderiv ℝ f z
                (basisVector direction)) y (basisVector direction) * g y)‖ := by
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ H y := by
          simp only [norm_mul, Real.norm_eq_abs, H]
          have h2 := mul_le_mul_of_nonneg_right hq2 (norm_nonneg (f y * g y))
          have h1 :
              |(2 : ℝ)| * |fderiv ℝ
                  (fun z : Space => fderiv ℝ (scaledCutoff R) z
                    (basisVector cutoffDirection)) y (basisVector direction)| *
                  ‖fderiv ℝ f y (basisVector direction) * g y‖ ≤
                (2 * M₂) * ‖fderiv ℝ f y (basisVector direction) * g y‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            norm_num
            exact hq1
          have h0 := mul_le_mul_of_nonneg_right hq0
            (norm_nonneg (fderiv ℝ (fun z : Space =>
              fderiv ℝ f z (basisVector direction)) y
                (basisVector direction) * g y))
          simpa only [Real.norm_eq_abs, abs_mul] using add_le_add (add_le_add h2 h1) h0
    · exact hH
    · filter_upwards with y
      simpa only [zero_mul] using
        (tendsto_secondDirectional_cutoffDirectional_mul_zero
          f hf cutoffDirection direction y).mul_const (g y)
  simpa using hlim

/-- A first derivative of a positive-time Gaussian translate is integrable
against every velocity component of a finite-energy solution slice. -/
theorem SolvesBefore.integrable_fderiv_heatKernel_translate_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (derivative velocityComponent : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
        (basisVector derivative) * u s y velocityComponent) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_abs_fderiv_heatKernel_translate_le_doubled hκ hτ
  have hpair := Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit.SolvesBefore.integrable_heatKernel_translate_mul_velocityNorm hsol
    hs0 hsT hκ (by positivity : 0 < 2 * τ) x₀
  have hmajor : Integrable (fun y : Space =>
      D * (heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖)) :=
    hpair.const_mul D
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hG : ContDiff ℝ ∞ (fun z : Space => heatKernel κ τ (x₀ - z)) :=
    Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff κ τ x₀
  have hDG := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hG (basisVector derivative)
  apply hmajor.mono'
    (hDG.continuous.mul
      ((continuous_apply velocityComponent).comp hu.continuous)).aestronglyMeasurable
  filter_upwards with y
  have hderiv := hbound x₀ y (basisVector derivative)
  rw [Navier.Analysis.CurlDerivativeBridge.norm_basisVector, mul_one] at hderiv
  have hucomp : |u s y velocityComponent| ≤ ‖u s y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (u s y) velocityComponent
  change |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
      (basisVector derivative) * u s y velocityComponent| ≤ _
  rw [abs_mul]
  calc
    |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
        (basisVector derivative)| * |u s y velocityComponent| ≤
      (D * heatKernel κ (2 * τ) (x₀ - y)) * ‖u s y‖ :=
        mul_le_mul hderiv hucomp (abs_nonneg _)
          (mul_nonneg hD.le
            (heatKernel_nonneg hκ (mul_pos (by norm_num) hτ) _))
    _ = D * (heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖) := by ring

/-- The scalar building block of the cutoff-gradient correction vanishes
after the two viscous derivatives and finite-energy pairing. -/
theorem SolvesBefore.tendsto_integral_secondDirectional_cutoffDirectional_heatKernel_mul_velocity_zero
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (cutoffDirection direction velocityComponent : Fin 3) :
    Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ
          (fun z : Space => fderiv ℝ
            (fun w : Space =>
              fderiv ℝ (scaledCutoff R) w (basisVector cutoffDirection) *
                heatKernel κ τ (x₀ - w))
            z (basisVector direction))
          y (basisVector direction) * u s y velocityComponent)
      atTop (nhds 0) := by
  apply tendsto_integral_secondDirectional_cutoffDirectional_mul_zero
    (fun y : Space => heatKernel κ τ (x₀ - y))
    (Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff κ τ x₀)
    (fun y : Space => u s y velocityComponent)
    ((continuous_apply velocityComponent).comp
      (contDiff_iff_contDiffAt.mpr (fun y =>
        Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
          hsol.classical.1 hs0 hsT y)).continuous)
    cutoffDirection direction
  · have hbase :=
      Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit.SolvesBefore.integrable_heatKernel_translate_mul_velocityNorm
        hsol hs0 hsT hκ hτ x₀
    apply hbase.mono'
      (((Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff
        κ τ x₀).continuous.mul
          ((continuous_apply velocityComponent).comp
            (contDiff_iff_contDiffAt.mpr (fun y =>
              Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
                hsol.classical.1 hs0 hsT y)).continuous)).aestronglyMeasurable)
    filter_upwards with y
    have hucomp : |u s y velocityComponent| ≤ ‖u s y‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (u s y) velocityComponent
    change |heatKernel κ τ (x₀ - y) * u s y velocityComponent| ≤
      heatKernel κ τ (x₀ - y) * ‖u s y‖
    rw [abs_mul,
      abs_of_nonneg (heatKernel_nonneg hκ hτ _)]
    exact mul_le_mul_of_nonneg_left hucomp (heatKernel_nonneg hκ hτ _)
  · exact Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit.SolvesBefore.integrable_fderiv_heatKernel_translate_mul_velocity hsol
      hs0 hsT hκ hτ x₀ direction velocityComponent
  · exact Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit.SolvesBefore.integrable_secondHeatKernel_translate_mul_velocity hsol
      hs0 hsT hκ hτ x₀ direction direction velocityComponent

/-- At positive radius the scalar correction integrand is integrable.  This
is used only to distribute the finite componentwise cross-product sum. -/
private theorem integrable_secondDirectional_cutoffDirectional_mul_of_pos
    (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (g : Space → ℝ) (hg : Continuous g)
    {R : ℝ} (hR : 0 < R) (cutoffDirection direction : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
        (fun z : Space => fderiv ℝ
          (fun w : Space =>
            fderiv ℝ (scaledCutoff R) w (basisVector cutoffDirection) * f w)
          z (basisVector direction))
        y (basisVector direction) * g y) := by
  let q : Space → ℝ := fun w =>
    fderiv ℝ (scaledCutoff R) w (basisVector cutoffDirection)
  have hq : ContDiff ℝ ∞ q :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      (scaledCutoff_contDiff R) (basisVector cutoffDirection)
  have hqsupp : HasCompactSupport q := by
    exact (scaledCutoff_hasCompactSupport hR).fderiv_apply ℝ
      (basisVector cutoffDirection)
  have hprod : ContDiff ℝ ∞ (fun w : Space => q w * f w) := hq.mul hf
  have hsupp : HasCompactSupport (fun w : Space => q w * f w) :=
    hqsupp.mul_right
  have hsuppD2 := (hsupp.fderiv_apply ℝ (basisVector direction)).fderiv_apply ℝ
    (basisVector direction)
  have hD2 := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hprod (basisVector direction)) (basisVector direction)
  exact (hD2.continuous.mul hg).integrable_of_hasCompactSupport hsuppD2.mul_right

private theorem secondDirectional_constLinearCombination
    {F H : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    (c d : ℝ) (direction : Fin 3) (x : Space) :
    fderiv ℝ (fun z : Space => fderiv ℝ
      (fun y : Space => F y * c - H y * d) z (basisVector direction))
      x (basisVector direction) =
      fderiv ℝ (fun z : Space => fderiv ℝ F z (basisVector direction))
        x (basisVector direction) * c -
      fderiv ℝ (fun z : Space => fderiv ℝ H z (basisVector direction))
        x (basisVector direction) * d := by
  have hfirst : (fun z : Space => fderiv ℝ
      (fun y : Space => F y * c - H y * d) z (basisVector direction)) =
      fun z : Space => fderiv ℝ F z (basisVector direction) * c -
        fderiv ℝ H z (basisVector direction) * d := by
    funext z
    rw [fderiv_fun_sub]
    · change (fderiv ℝ (F * fun _ : Space => c) z -
          fderiv ℝ (H * fun _ : Space => d) z) (basisVector direction) = _
      rw [fderiv_mul
          ((hF.differentiable (by norm_num)).differentiableAt)
          (differentiableAt_const c),
        fderiv_mul
          ((hH.differentiable (by norm_num)).differentiableAt)
          (differentiableAt_const d)]
      simp only [sub_apply, add_apply, smul_apply, fderiv_const_apply,
        zero_apply, mul_zero, smul_eq_mul]
      ring
    · exact ((hF.mul contDiff_const).differentiable (by norm_num)).differentiableAt
    · exact ((hH.mul contDiff_const).differentiable (by norm_num)).differentiableAt
  rw [hfirst]
  have hDF := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hF (basisVector direction)
  have hDH := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hH (basisVector direction)
  rw [fderiv_fun_sub]
  · change (fderiv ℝ
        ((fun z : Space => fderiv ℝ F z (basisVector direction)) *
          fun _ : Space => c) x -
      fderiv ℝ
        ((fun z : Space => fderiv ℝ H z (basisVector direction)) *
          fun _ : Space => d) x) (basisVector direction) = _
    rw [fderiv_mul
        ((hDF.differentiable (by norm_num)).differentiableAt)
        (differentiableAt_const c),
      fderiv_mul
        ((hDH.differentiable (by norm_num)).differentiableAt)
        (differentiableAt_const d)]
    simp only [sub_apply, add_apply, smul_apply, fderiv_const_apply,
      zero_apply, mul_zero, smul_eq_mul]
    ring
  · exact ((hDF.mul contDiff_const).differentiable (by norm_num)).differentiableAt
  · exact ((hDH.mul contDiff_const).differentiable (by norm_num)).differentiableAt

private theorem cutoffGradientCrossPotential_component_zero
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => (staticGradient (scaledCutoff R) y ⨯₃
      backwardHeatPotential κ τ x₀ a y) 0) = fun y : Space =>
        (fderiv ℝ (scaledCutoff R) y (basisVector 1) *
          heatKernel κ τ (x₀ - y)) * a 2 -
        (fderiv ℝ (scaledCutoff R) y (basisVector 2) *
          heatKernel κ τ (x₀ - y)) * a 1 := by
  funext y
  simp [staticGradient, backwardHeatPotential, cross_apply, basisVector] <;> ring_nf

private theorem cutoffGradientCrossPotential_component_one
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => (staticGradient (scaledCutoff R) y ⨯₃
      backwardHeatPotential κ τ x₀ a y) 1) = fun y : Space =>
        (fderiv ℝ (scaledCutoff R) y (basisVector 2) *
          heatKernel κ τ (x₀ - y)) * a 0 -
        (fderiv ℝ (scaledCutoff R) y (basisVector 0) *
          heatKernel κ τ (x₀ - y)) * a 2 := by
  funext y
  simp [staticGradient, backwardHeatPotential, cross_apply, basisVector] <;> ring_nf

private theorem cutoffGradientCrossPotential_component_two
    (R κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => (staticGradient (scaledCutoff R) y ⨯₃
      backwardHeatPotential κ τ x₀ a y) 2) = fun y : Space =>
        (fderiv ℝ (scaledCutoff R) y (basisVector 0) *
          heatKernel κ τ (x₀ - y)) * a 1 -
        (fderiv ℝ (scaledCutoff R) y (basisVector 1) *
          heatKernel κ τ (x₀ - y)) * a 0 := by
  funext y
  simp [staticGradient, backwardHeatPotential, cross_apply, basisVector] <;> ring_nf

/-- A two-coordinate cutoff-gradient combination has vanishing viscous
pairing.  This is the exact scalar shape of each cross-product component. -/
private theorem SolvesBefore.tendsto_integral_secondDirectional_cutoffDirectionalPair_heatKernel_mul_velocity_zero
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (first second direction velocityComponent : Fin 3) (c d : ℝ) :
    Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space =>
            (fderiv ℝ (scaledCutoff R) w (basisVector first) *
              heatKernel κ τ (x₀ - w)) * c -
            (fderiv ℝ (scaledCutoff R) w (basisVector second) *
              heatKernel κ τ (x₀ - w)) * d)
          z (basisVector direction)) y (basisVector direction) *
            u s y velocityComponent)
      atTop (nhds 0) := by
  let K : Space → ℝ := fun y => heatKernel κ τ (x₀ - y)
  have hK : ContDiff ℝ ∞ K :=
    Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff κ τ x₀
  have hu : Continuous (fun y : Space => u s y velocityComponent) :=
    (continuous_apply velocityComponent).comp
      (contDiff_iff_contDiffAt.mpr (fun y =>
        Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
          hsol.classical.1 hs0 hsT y)).continuous
  let I : Fin 3 → ℝ → ℝ := fun k R => ∫ y : Space,
    fderiv ℝ (fun z : Space => fderiv ℝ
      (fun w : Space => fderiv ℝ (scaledCutoff R) w (basisVector k) * K w)
      z (basisVector direction)) y (basisVector direction) *
        u s y velocityComponent
  have hfirst : Tendsto (I first) atTop (nhds 0) :=
    Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit.SolvesBefore.tendsto_integral_secondDirectional_cutoffDirectional_heatKernel_mul_velocity_zero
      hsol hs0 hsT hκ hτ x₀ first direction velocityComponent
  have hsecond : Tendsto (I second) atTop (nhds 0) :=
    Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit.SolvesBefore.tendsto_integral_secondDirectional_cutoffDirectional_heatKernel_mul_velocity_zero
      hsol hs0 hsT hκ hτ x₀ second direction velocityComponent
  have hEq : (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space =>
          (fderiv ℝ (scaledCutoff R) w (basisVector first) * K w) * c -
          (fderiv ℝ (scaledCutoff R) w (basisVector second) * K w) * d)
        z (basisVector direction)) y (basisVector direction) *
          u s y velocityComponent) =ᶠ[atTop]
      (fun R => c * I first R - d * I second R) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hint : ∀ k : Fin 3, Integrable (fun y : Space =>
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => fderiv ℝ (scaledCutoff R) w (basisVector k) * K w)
          z (basisVector direction)) y (basisVector direction) *
            u s y velocityComponent) := fun k =>
      integrable_secondDirectional_cutoffDirectional_mul_of_pos
        K hK (fun y : Space => u s y velocityComponent) hu hR k direction
    simp_rw [secondDirectional_constLinearCombination
      ((Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        (scaledCutoff_contDiff R) (basisVector first)).mul hK)
      ((Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        (scaledCutoff_contDiff R) (basisVector second)).mul hK)
      c d direction]
    rw [show (fun y : Space =>
        (fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => fderiv ℝ (scaledCutoff R) w (basisVector first) * K w)
            z (basisVector direction)) y (basisVector direction) * c -
          fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => fderiv ℝ (scaledCutoff R) w (basisVector second) * K w)
            z (basisVector direction)) y (basisVector direction) * d) *
              u s y velocityComponent) = fun y =>
        c * (fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => fderiv ℝ (scaledCutoff R) w (basisVector first) * K w)
            z (basisVector direction)) y (basisVector direction) *
              u s y velocityComponent) -
        d * (fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => fderiv ℝ (scaledCutoff R) w (basisVector second) * K w)
            z (basisVector direction)) y (basisVector direction) *
              u s y velocityComponent) by funext y; ring]
    rw [integral_sub ((hint first).const_mul c) ((hint second).const_mul d),
      integral_const_mul, integral_const_mul]
  have hcomb := (hfirst.const_mul c).sub (hsecond.const_mul d)
  have hcomb0 : Tendsto (fun R => c * I first R - d * I second R)
      atTop (nhds 0) := by simpa using hcomb
  exact hcomb0.congr' hEq.symm

/-- **Actual viscous correction limit.**  Both spatial derivatives of the
`∇χ_R × (G_τ a)` branch may be passed through the integral, and the branch
vanishes against every component of every preterminal finite-energy velocity
slice. -/
theorem SolvesBefore.tendsto_integral_secondDirectional_cutoffGradientCrossPotential_mul_velocity_zero
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityComponent : Fin 3) :
    Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => (staticGradient (scaledCutoff R) w ⨯₃
            backwardHeatPotential κ τ x₀ a w) fieldComponent)
          z (basisVector direction)) y (basisVector direction) *
            u s y velocityComponent)
      atTop (nhds 0) := by
  fin_cases fieldComponent
  · change Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => (staticGradient (scaledCutoff R) w ⨯₃
          backwardHeatPotential κ τ x₀ a w) 0)
        z (basisVector direction)) y (basisVector direction) *
          u s y velocityComponent) atTop (nhds 0)
    simp_rw [cutoffGradientCrossPotential_component_zero]
    exact tendsto_integral_secondDirectional_cutoffDirectionalPair_heatKernel_mul_velocity_zero hsol
      hs0 hsT hκ hτ x₀ 1 2 direction velocityComponent (a 2) (a 1)
  · change Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => (staticGradient (scaledCutoff R) w ⨯₃
          backwardHeatPotential κ τ x₀ a w) 1)
        z (basisVector direction)) y (basisVector direction) *
          u s y velocityComponent) atTop (nhds 0)
    simp_rw [cutoffGradientCrossPotential_component_one]
    exact tendsto_integral_secondDirectional_cutoffDirectionalPair_heatKernel_mul_velocity_zero hsol
      hs0 hsT hκ hτ x₀ 2 0 direction velocityComponent (a 0) (a 2)
  · change Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => (staticGradient (scaledCutoff R) w ⨯₃
          backwardHeatPotential κ τ x₀ a w) 2)
        z (basisVector direction)) y (basisVector direction) *
          u s y velocityComponent) atTop (nhds 0)
    simp_rw [cutoffGradientCrossPotential_component_two]
    exact tendsto_integral_secondDirectional_cutoffDirectionalPair_heatKernel_mul_velocity_zero hsol
      hs0 hsT hκ hτ x₀ 0 1 direction velocityComponent (a 1) (a 0)

end Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit
