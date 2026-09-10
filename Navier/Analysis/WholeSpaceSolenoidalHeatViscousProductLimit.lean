import Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit
import Navier.Analysis.WholeSpaceSolenoidalHeatConvectionIntegrability

/-!
# Dominated limit for the surviving whole-space viscous cutoff product

The viscous part of the compact solenoidal heat test contains the product
`chi_R * curl (G a)`.  Its diagonal second derivative has three terms.  This
module proves that, whenever those three cutoff-free pairings are integrable,
the integral of the full product converges to the integral of the surviving
second derivative.  The proof supplies the uniform integrable envelope that
was left explicit in `WholeSpaceSolenoidalHeatViscousCutoffLimit`.

This closes the limit for the `chi_R * curl (G a)` branch on the exact
`SolvesBefore` carrier.  The separate `grad chi_R x (G a)` correction and the
time-integrated limit remain distinct obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff
open MeasureTheory Filter

namespace Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatConvectionIntegrability
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.OfficialABEncoding

/-- A positive-time Gaussian translate times the norm of an actual
finite-energy velocity slice is integrable. -/
theorem SolvesBefore.integrable_heatKernel_translate_mul_velocityNorm
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space) :
    Integrable (fun y : Space => heatKernel κ τ (x₀ - y) * ‖u s y‖) := by
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have huNormMeas : Measurable (fun y : Space => ‖u s y‖) :=
    hu.continuous.norm.measurable
  have huNormPow : Integrable (fun y : Space => |‖u s y‖| ^ (2 : ℝ)) := by
    apply (hsol.finite_energy s hs0 hsT).congr
    filter_upwards with y
    rw [abs_of_nonneg (norm_nonneg _), Real.rpow_two]
  exact Navier.Analysis.HeatSemigroupSmoothing.integrable_heatKernel_mul_of_integrable_rpow
    hκ hτ (by norm_num : (1 : ℝ) < 2) huNormPow huNormMeas x₀

/-- Every component of the uncut backward-heat curl is integrable against
every component of an actual finite-energy velocity slice. -/
theorem SolvesBefore.integrable_backwardHeatCurlField_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (fieldComponent velocityComponent : Fin 3) :
    Integrable (fun y : Space =>
      backwardHeatCurlField κ τ x₀ a y fieldComponent * u s y velocityComponent) := by
  obtain ⟨D, hD, hgrad⟩ :=
    Navier.Analysis.HeatSemigroupSmoothing.exists_abs_fderiv_heatKernel_translate_le_doubled
      hκ hτ
  have hpair := integrable_heatKernel_translate_mul_velocityNorm hsol hs0 hsT
    hκ (by positivity : 0 < 2 * τ) x₀
  have hmajor : Integrable (fun y : Space =>
      (Real.sqrt 3 * D * officialEuclideanNorm a) *
        (heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖)) :=
    hpair.const_mul (Real.sqrt 3 * D * officialEuclideanNorm a)
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  apply hmajor.mono'
    (((continuous_apply fieldComponent).comp
      (backwardHeatCurlField_contDiff κ τ x₀ a).continuous).mul
      ((continuous_apply velocityComponent).comp hu.continuous)).aestronglyMeasurable
  filter_upwards with y
  have hG : 0 ≤ heatKernel κ (2 * τ) (x₀ - y) :=
    Navier.Analysis.HeatSemigroupSmoothing.heatKernel_nonneg hκ (by positivity) _
  have hgradNorm : officialEuclideanNorm
      (staticGradient (fun z : Space => heatKernel κ τ (x₀ - z)) y) ≤
        Real.sqrt 3 * (D * heatKernel κ (2 * τ) (x₀ - y)) := by
    refine (Navier.Analysis.OfficialABEncoding.officialEuclideanNorm_le _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 3)
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hD.le hG)).2
    intro i
    simpa [staticGradient, Real.norm_eq_abs,
      Navier.Analysis.CurlDerivativeBridge.norm_basisVector] using
        hgrad x₀ y (basisVector i)
  have hcurl : officialEuclideanNorm (backwardHeatCurlField κ τ x₀ a y) ≤
      Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
        officialEuclideanNorm a := by
    rw [Navier.Analysis.WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
    exact (Navier.Analysis.CurlDerivativeBridge.officialEuclideanNorm_cross_le _ _).trans <| by
      calc
        officialEuclideanNorm
              (staticGradient (fun z : Space => heatKernel κ τ (x₀ - z)) y) *
            officialEuclideanNorm a ≤
          (Real.sqrt 3 * (D * heatKernel κ (2 * τ) (x₀ - y))) *
            officialEuclideanNorm a :=
              mul_le_mul_of_nonneg_right hgradNorm
                (officialEuclideanNorm_nonneg _)
        _ = Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
              officialEuclideanNorm a := by ring
  have hfield : |backwardHeatCurlField κ τ x₀ a y fieldComponent| ≤
      officialEuclideanNorm (backwardHeatCurlField κ τ x₀ a y) := by
    have hsup : |backwardHeatCurlField κ τ x₀ a y fieldComponent| ≤
        ‖backwardHeatCurlField κ τ x₀ a y‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (backwardHeatCurlField κ τ x₀ a y) fieldComponent
    exact hsup.trans
      (Navier.Analysis.OfficialABEncoding.norm_le_officialEuclideanNorm _)
  have hucomp : |u s y velocityComponent| ≤ ‖u s y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (u s y) velocityComponent
  change |backwardHeatCurlField κ τ x₀ a y fieldComponent *
    u s y velocityComponent| ≤ _
  rw [abs_mul]
  calc
    |backwardHeatCurlField κ τ x₀ a y fieldComponent| *
        |u s y velocityComponent| ≤
      officialEuclideanNorm (backwardHeatCurlField κ τ x₀ a y) * ‖u s y‖ :=
        mul_le_mul hfield hucomp (abs_nonneg _) (officialEuclideanNorm_nonneg _)
    _ ≤ (Real.sqrt 3 * D * heatKernel κ (2 * τ) (x₀ - y) *
          officialEuclideanNorm a) * ‖u s y‖ :=
      mul_le_mul_of_nonneg_right hcurl (norm_nonneg _)
    _ = (Real.sqrt 3 * D * officialEuclideanNorm a) *
          (heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖) := by ring

/-- Mixed second derivatives of a positive-time Gaussian are dominated by
two wider positive-time Gaussians, uniformly in the coordinate pair. -/
theorem exists_abs_second_heatKernel_le_gaussians
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (x : Space) (i j : Fin 3),
      |fderiv ℝ
          (fun y : Space =>
            fderiv ℝ (fun z : Space => heatKernel κ τ z) y (basisVector i))
          x (basisVector j)| ≤
        A * heatKernel κ (4 * τ) x + B * heatKernel κ τ x := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_abs_coordinate_mul_heatKernel_le_doubled hκ hτ
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_abs_coordinate_mul_heatKernel_le_doubled hκ
      (by positivity : 0 < 2 * τ)
  let c : ℝ := -(4 * κ * τ)⁻¹ * 2
  let A : ℝ := |c| ^ 2 * C₁ * C₂
  let B : ℝ := |c|
  have hc : 0 < |c| := by
    apply abs_pos.mpr
    simp only [c]
    exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by positivity))) (by norm_num)
  refine ⟨A, B, by simp only [A]; positivity, by simpa only [B], ?_⟩
  intro x i j
  have hG : 0 ≤ heatKernel κ τ x := heatKernel_nonneg hκ hτ x
  have hquad : |x j * x i| * heatKernel κ τ x ≤
      C₁ * C₂ * heatKernel κ (4 * τ) x := by
    calc
      |x j * x i| * heatKernel κ τ x =
          |x j| * (|x i| * heatKernel κ τ x) := by rw [abs_mul]; ring
      _ ≤ |x j| * (C₁ * heatKernel κ (2 * τ) x) :=
        mul_le_mul_of_nonneg_left (h₁ x i) (abs_nonneg _)
      _ = C₁ * (|x j| * heatKernel κ (2 * τ) x) := by ring
      _ ≤ C₁ * (C₂ * heatKernel κ (2 * (2 * τ)) x) :=
        mul_le_mul_of_nonneg_left (h₂ x j) hC₁.le
      _ = C₁ * C₂ * heatKernel κ (4 * τ) x := by
        rw [show 2 * (2 * τ) = 4 * τ by ring]
        ring
  rw [Navier.Analysis.WholeSpaceHeatThirdDerivative.fderiv_fderiv_heatKernel_space_apply_mixed]
  change |heatKernel κ τ x * (c * x j * (c * x i) + c * basisVector j i)| ≤ _
  rw [abs_mul, abs_of_nonneg hG]
  have hbasis : |basisVector j i| ≤ 1 := by
    simp only [basisVector, Pi.single_apply]
    split <;> simp
  calc
    heatKernel κ τ x * |c * x j * (c * x i) + c * basisVector j i| ≤
        heatKernel κ τ x * (|c| ^ 2 * |x j * x i| + |c|) := by
      apply mul_le_mul_of_nonneg_left _ hG
      calc
        |c * x j * (c * x i) + c * basisVector j i| ≤
            |c * x j * (c * x i)| + |c * basisVector j i| := abs_add_le _ _
        _ = |c| ^ 2 * |x j * x i| + |c| * |basisVector j i| := by
          simp only [abs_mul]
          ring
        _ ≤ |c| ^ 2 * |x j * x i| + |c| * 1 := by
          gcongr
        _ = |c| ^ 2 * |x j * x i| + |c| := by ring
    _ = |c| ^ 2 * (|x j * x i| * heatKernel κ τ x) +
          |c| * heatKernel κ τ x := by ring
    _ ≤ |c| ^ 2 * (C₁ * C₂ * heatKernel κ (4 * τ) x) +
          |c| * heatKernel κ τ x :=
      add_le_add (mul_le_mul_of_nonneg_left hquad (sq_nonneg _)) le_rfl
    _ = A * heatKernel κ (4 * τ) x + B * heatKernel κ τ x := by
      simp only [A, B]
      ring

/-- A translated mixed second Gaussian derivative is integrable against any
velocity component on an actual finite-energy slice. -/
theorem SolvesBefore.integrable_secondHeatKernel_translate_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (derivativeOne derivativeTwo velocityComponent : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector derivativeOne))
          y (basisVector derivativeTwo) * u s y velocityComponent) := by
  obtain ⟨A, B, hA, hB, henv⟩ :=
    exists_abs_second_heatKernel_le_gaussians hκ hτ
  have hG4 := integrable_heatKernel_translate_mul_velocityNorm hsol hs0 hsT
    hκ (by positivity : 0 < 4 * τ) x₀
  have hG1 := integrable_heatKernel_translate_mul_velocityNorm hsol hs0 hsT
    hκ hτ x₀
  have hmajor : Integrable (fun y : Space =>
      A * (heatKernel κ (4 * τ) (x₀ - y) * ‖u s y‖) +
        B * (heatKernel κ τ (x₀ - y) * ‖u s y‖)) :=
    (hG4.const_mul A).add (hG1.const_mul B)
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hG : ContDiff ℝ ∞ (fun w : Space => heatKernel κ τ (x₀ - w)) :=
    Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff κ τ x₀
  have hD1 := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hG (basisVector derivativeOne)
  have hD2 := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hD1 (basisVector derivativeTwo)
  apply hmajor.mono'
    (hD2.continuous.mul
      ((continuous_apply velocityComponent).comp hu.continuous)).aestronglyMeasurable
  filter_upwards with y
  have hderiv :
      |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector derivativeOne))
          y (basisVector derivativeTwo)| ≤
        A * heatKernel κ (4 * τ) (x₀ - y) +
          B * heatKernel κ τ (x₀ - y) := by
    rw [fderiv_fderiv_heatKernel_translate_apply]
    exact henv (x₀ - y) derivativeOne derivativeTwo
  have hucomp : |u s y velocityComponent| ≤ ‖u s y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (u s y) velocityComponent
  change |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector derivativeOne))
          y (basisVector derivativeTwo) * u s y velocityComponent| ≤ _
  rw [abs_mul]
  calc
    |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector derivativeOne))
          y (basisVector derivativeTwo)| * |u s y velocityComponent| ≤
      (A * heatKernel κ (4 * τ) (x₀ - y) + B * heatKernel κ τ (x₀ - y)) *
        ‖u s y‖ :=
      mul_le_mul hderiv hucomp (abs_nonneg _)
        (add_nonneg
          (mul_nonneg hA.le (heatKernel_nonneg hκ (by positivity) _))
          (mul_nonneg hB.le (heatKernel_nonneg hκ hτ _)))
    _ = A * (heatKernel κ (4 * τ) (x₀ - y) * ‖u s y‖) +
        B * (heatKernel κ τ (x₀ - y) * ‖u s y‖) := by ring

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

/-- The first derivative of the uncut backward-heat curl is integrable against
every velocity component on an actual finite-energy slice. -/
theorem SolvesBefore.integrable_directional_backwardHeatCurlField_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityComponent : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (basisVector direction) * u s y velocityComponent) := by
  have hG : ContDiff ℝ ∞
      (fun z : Space => heatKernel κ τ (x₀ - z)) :=
    Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff κ τ x₀
  have hDG : ∀ i : Fin 3, ContDiff ℝ ∞ (fun y : Space =>
      fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
        (basisVector i)) := fun i =>
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hG (basisVector i)
  have combine : ∀ (i j : Fin 3) (c d : ℝ),
      Integrable (fun y : Space =>
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector i))
            y (basisVector direction) * c * u s y velocityComponent -
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector j))
            y (basisVector direction) * d * u s y velocityComponent) := by
    intro i j c d
    have hi := (integrable_secondHeatKernel_translate_mul_velocity
      hsol hs0 hsT hκ hτ x₀ i direction velocityComponent).const_mul c
    have hj := (integrable_secondHeatKernel_translate_mul_velocity
      hsol hs0 hsT hκ hτ x₀ j direction velocityComponent).const_mul d
    apply (hi.sub hj).congr
    filter_upwards with y
    change c *
          (fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector i))
            y (basisVector direction) * u s y velocityComponent) -
        d *
          (fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector j))
            y (basisVector direction) * u s y velocityComponent) = _
    ring
  fin_cases fieldComponent
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 0)
          y (basisVector direction) * u s y velocityComponent)
    rw [backwardHeatCurlField_component_zero]
    apply (combine 1 2 (a 2) (a 1)).congr
    filter_upwards with y
    rw [directional_constLinearCombination (hDG 1) (hDG 2)]
    ring
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 1)
          y (basisVector direction) * u s y velocityComponent)
    rw [backwardHeatCurlField_component_one]
    apply (combine 2 0 (a 0) (a 2)).congr
    filter_upwards with y
    rw [directional_constLinearCombination (hDG 2) (hDG 0)]
    ring
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 2)
          y (basisVector direction) * u s y velocityComponent)
    rw [backwardHeatCurlField_component_two]
    apply (combine 0 1 (a 1) (a 0)).congr
    filter_upwards with y
    rw [directional_constLinearCombination (hDG 0) (hDG 1)]
    ring

/-- Dominated convergence for the diagonal second derivative of
`scaledCutoff R * f`, paired with an integrable multiplier `g`.

The three hypotheses are exactly the cutoff-free product-rule terms:
`f*g`, `(D_i f)*g`, and `(D_i^2 f)*g`.  No spatial bound on `g` is used. -/
theorem tendsto_integral_secondDirectional_scaledCutoff_mul
    (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (g : Space → ℝ) (hg : Continuous g)
    (direction : Fin 3)
    (hzero : Integrable (fun y : Space => f y * g y))
    (hone : Integrable (fun y : Space =>
      fderiv ℝ f y (basisVector direction) * g y))
    (htwo : Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction)) y
        (basisVector direction) * g y)) :
    Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => scaledCutoff R w * f w) z
                (basisVector direction))
            y (basisVector direction) * g y)
      atTop
      (nhds (∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction)) y
          (basisVector direction) * g y)) := by
  obtain ⟨M₁, hM₁, hDM₁⟩ := exists_fderiv_opNorm_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
  obtain ⟨M₂, hM₂, hDM₂⟩ := exists_fderiv_fderiv_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
    (basisVector direction) (basisVector direction)
  let H : Space → ℝ := fun y =>
    M₂ * ‖f y * g y‖ +
      (2 * M₁) * ‖fderiv ℝ f y (basisVector direction) * g y‖ +
      ‖fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction)) y
        (basisVector direction) * g y‖
  have hH : Integrable H := by
    exact ((hzero.norm.const_mul M₂).add (hone.norm.const_mul (2 * M₁))).add htwo.norm
  apply tendsto_integral_filter_of_dominated_convergence H
  · filter_upwards with R
    have hprod : ContDiff ℝ ∞ (fun w : Space => scaledCutoff R w * f w) :=
      (scaledCutoff_contDiff R).mul hf
    have hD := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        hprod (basisVector direction)) (basisVector direction)
    exact (hD.continuous.mul hg).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards with y
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hRinv : R⁻¹ ≤ 1 := (inv_le_one₀ hR0).2 hR
    have hDchi :
        |fderiv ℝ (scaledCutoff R) y (basisVector direction)| ≤ M₁ := by
      have h := abs_fderiv_scaled_le standardBump standardBump.contDiff
        hDM₁ hR0 y (basisVector direction)
      rw [Navier.Analysis.CurlDerivativeBridge.norm_basisVector, mul_one] at h
      exact h.trans (mul_le_of_le_one_left hM₁ hRinv)
    have hD2chi :
        |fderiv ℝ
            (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector direction))
            y (basisVector direction)| ≤ M₂ := by
      have h := abs_fderiv_fderiv_scaled_le standardBump standardBump.contDiff
        hDM₂ hR0 y
      have hRinv0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR0.le
      exact h.trans <| by
        calc
          R⁻¹ * R⁻¹ * M₂ ≤ 1 * 1 * M₂ := by
            gcongr
          _ = M₂ := by ring
    have hchi : |scaledCutoff R y| ≤ 1 := by
      rw [abs_of_nonneg (scaledCutoff_nonneg R y)]
      exact scaledCutoff_le_one R y
    rw [secondDirectional_mul (scaledCutoff_contDiff R) hf direction y]
    change ‖
        (fderiv ℝ
              (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector direction))
              y (basisVector direction) * f y +
            2 * (fderiv ℝ (scaledCutoff R) y (basisVector direction) *
              fderiv ℝ f y (basisVector direction)) +
            scaledCutoff R y *
              fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction))
                y (basisVector direction)) * g y‖ ≤ H y
    rw [show
      (fderiv ℝ
              (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector direction))
              y (basisVector direction) * f y +
            2 * (fderiv ℝ (scaledCutoff R) y (basisVector direction) *
              fderiv ℝ f y (basisVector direction)) +
            scaledCutoff R y *
              fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction))
                y (basisVector direction)) * g y =
        (fderiv ℝ
              (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector direction))
              y (basisVector direction) * (f y * g y)) +
          (2 * fderiv ℝ (scaledCutoff R) y (basisVector direction)) *
            (fderiv ℝ f y (basisVector direction) * g y) +
          scaledCutoff R y *
            (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction))
              y (basisVector direction) * g y) by ring]
    calc
      ‖(fderiv ℝ
              (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector direction))
              y (basisVector direction) * (f y * g y)) +
          (2 * fderiv ℝ (scaledCutoff R) y (basisVector direction)) *
            (fderiv ℝ f y (basisVector direction) * g y) +
          scaledCutoff R y *
            (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction))
              y (basisVector direction) * g y)‖ ≤
        ‖fderiv ℝ
              (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector direction))
              y (basisVector direction) * (f y * g y)‖ +
          ‖(2 * fderiv ℝ (scaledCutoff R) y (basisVector direction)) *
            (fderiv ℝ f y (basisVector direction) * g y)‖ +
          ‖scaledCutoff R y *
            (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction))
              y (basisVector direction) * g y)‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ H y := by
        simp only [norm_mul, Real.norm_eq_abs, H]
        have h2 :
            |fderiv ℝ
                (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector direction))
                y (basisVector direction)| * ‖f y * g y‖ ≤
              M₂ * ‖f y * g y‖ :=
          mul_le_mul_of_nonneg_right hD2chi (norm_nonneg _)
        have h1 :
            |(2 : ℝ)| * |fderiv ℝ (scaledCutoff R) y (basisVector direction)| *
                ‖fderiv ℝ f y (basisVector direction) * g y‖ ≤
              (2 * M₁) *
                ‖fderiv ℝ f y (basisVector direction) * g y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          norm_num
          exact hDchi
        have h0 :
            |scaledCutoff R y| *
                ‖fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction)) y
                  (basisVector direction) * g y‖ ≤
              ‖fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction)) y
                (basisVector direction) * g y‖ := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hchi (norm_nonneg _)
        simpa only [norm_mul, Real.norm_eq_abs, abs_mul, H] using
          add_le_add (add_le_add h2 h1) h0
  · exact hH
  · filter_upwards with y
    exact (tendsto_secondDirectional_scaledCutoff_mul hf direction y).mul_const (g y)

/-- **Actual surviving viscous cutoff limit.**  On the native whole-space
`SolvesBefore` carrier, the diagonal second derivative of
`chi_R * curl (G a)` converges after pairing with every velocity component.
All three product-rule integrability inputs are derived from finite energy and
positive-time Gaussian estimates. -/
theorem SolvesBefore.tendsto_integral_secondDirectional_scaledCutoff_backwardHeatCurlField_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityComponent : Fin 3) :
    Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => scaledCutoff R w *
                backwardHeatCurlField κ τ x₀ a w fieldComponent) z
                (basisVector direction))
            y (basisVector direction) * u s y velocityComponent)
      atTop
      (nhds (∫ y : Space,
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ
                (fun w : Space => backwardHeatCurlField κ τ x₀ a w fieldComponent)
                z (basisVector direction))
            y (basisVector direction) * u s y velocityComponent)) := by
  apply tendsto_integral_secondDirectional_scaledCutoff_mul
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y fieldComponent)
    ((contDiff_apply ℝ ℝ fieldComponent).comp
      (backwardHeatCurlField_contDiff κ τ x₀ a))
    (fun y : Space => u s y velocityComponent)
    ((continuous_apply velocityComponent).comp
      (contDiff_iff_contDiffAt.mpr (fun y =>
        Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
          hsol.classical.1 hs0 hsT y)).continuous)
    direction
  · exact integrable_backwardHeatCurlField_mul_velocity
      hsol hs0 hsT hκ hτ x₀ a fieldComponent velocityComponent
  · exact integrable_directional_backwardHeatCurlField_mul_velocity
      hsol hs0 hsT hκ hτ x₀ a direction fieldComponent velocityComponent
  · exact Navier.Analysis.WholeSpaceSolenoidalHeatViscousIntegrability.SolvesBefore.integrable_secondDirectional_backwardHeatCurlField_mul_velocity
      hsol hs0 hsT hκ hτ x₀ a direction fieldComponent velocityComponent

end Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit
