import Navier.Analysis.WholeSpaceSolenoidalHeatViscousIntegrability

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff Matrix
open MeasureTheory

namespace Navier.Analysis.WholeSpaceSolenoidalHeatConvectionIntegrability

open Navier
open Navier.Analysis
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.WholeSpaceSolenoidalHeatDomination
open Navier.Analysis.WholeSpaceHeatThirdDerivative
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination

/-- Every mixed second spatial derivative of a positive-time heat kernel is
uniformly bounded, with one bound for all coordinate pairs.  This is the
`L^∞` Gaussian input required to pair the first derivative of the uncut
backward-heat curl with the quadratic finite-energy convection term. -/
theorem exists_abs_second_heatKernel_le_constant
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    ∃ K : ℝ, 0 < K ∧ ∀ (x : Space) (i j : Fin 3),
      |fderiv ℝ
          (fun y : Space =>
            fderiv ℝ (fun z : Space => heatKernel ν t z) y (basisVector i))
          x (basisVector j)| ≤ K := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    exists_abs_coordinate_mul_heatKernel_le_doubled hν ht
  obtain ⟨C₂, hC₂, h₂⟩ :=
    exists_abs_coordinate_mul_heatKernel_le_doubled hν
      (by positivity : 0 < 2 * t)
  let c : ℝ := -(4 * ν * t)⁻¹ * 2
  let P₁ : ℝ := (4 * Real.pi * ν * t) ^ (-(3 : ℝ) / 2)
  let P₄ : ℝ := (4 * Real.pi * ν * (4 * t)) ^ (-(3 : ℝ) / 2)
  let K : ℝ := |c| ^ 2 * C₁ * C₂ * P₄ + |c| * P₁ + 1
  have hc : 0 < |c| := by
    apply abs_pos.mpr
    simp only [c]
    exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by positivity)))
      (by norm_num)
  have hP₁ : 0 < P₁ := by simp only [P₁]; positivity
  have hP₄ : 0 < P₄ := by simp only [P₄]; positivity
  refine ⟨K, by simp only [K]; positivity, ?_⟩
  intro x i j
  have hG : 0 ≤ heatKernel ν t x := heatKernel_nonneg hν ht x
  have hG2 : 0 ≤ heatKernel ν (2 * t) x :=
    heatKernel_nonneg hν (by positivity) x
  have hquad : |x j * x i| * heatKernel ν t x ≤ C₁ * C₂ * P₄ := by
    calc
      |x j * x i| * heatKernel ν t x =
          |x j| * (|x i| * heatKernel ν t x) := by rw [abs_mul]; ring
      _ ≤ |x j| * (C₁ * heatKernel ν (2 * t) x) :=
        mul_le_mul_of_nonneg_left (h₁ x i) (abs_nonneg _)
      _ = C₁ * (|x j| * heatKernel ν (2 * t) x) := by ring
      _ ≤ C₁ * (C₂ * heatKernel ν (4 * t) x) := by
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        simpa only [show 2 * (2 * t) = 4 * t by ring] using h₂ x j
      _ ≤ C₁ * (C₂ * P₄) := by
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        apply mul_le_mul_of_nonneg_left _ hC₂.le
        simpa only [P₄, sub_zero] using heatKernel_translate_le_peak hν
          (by positivity : 0 < 4 * t) x (0 : Space)
      _ = C₁ * C₂ * P₄ := by ring
  have hpeak : heatKernel ν t x ≤ P₁ := by
    simpa only [P₁, sub_zero] using
      heatKernel_translate_le_peak hν ht x (0 : Space)
  rw [fderiv_fderiv_heatKernel_space_apply_mixed]
  change |heatKernel ν t x *
    (c * x j * (c * x i) + c * basisVector j i)| ≤ K
  rw [abs_mul, abs_of_nonneg hG]
  have hbasis : |basisVector j i| ≤ 1 := by
    simp only [basisVector, Pi.single_apply]
    split <;> simp
  have hmainAbs : |c * x j * (c * x i)| = |c| ^ 2 * |x j * x i| := by
    simp only [abs_mul]
    ring
  have hbasisAbs : |c * basisVector j i| = |c| * |basisVector j i| := by
    exact abs_mul _ _
  calc
    heatKernel ν t x * |c * x j * (c * x i) + c * basisVector j i| ≤
        heatKernel ν t x *
          (|c| ^ 2 * |x j * x i| + |c|) := by
      apply mul_le_mul_of_nonneg_left _ hG
      calc
        |c * x j * (c * x i) + c * basisVector j i| ≤
            |c * x j * (c * x i)| + |c * basisVector j i| := abs_add_le _ _
        _ = |c| ^ 2 * |x j * x i| + |c| * |basisVector j i| := by
          rw [hmainAbs, hbasisAbs]
        _ ≤ |c| ^ 2 * |x j * x i| + |c| * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left hbasis (abs_nonneg c)) _
        _ = |c| ^ 2 * |x j * x i| + |c| := by ring
    _ = |c| ^ 2 * (|x j * x i| * heatKernel ν t x) +
          |c| * heatKernel ν t x := by ring
    _ ≤ |c| ^ 2 * (C₁ * C₂ * P₄) + |c| * P₁ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hquad (sq_nonneg _))
        (mul_le_mul_of_nonneg_left hpeak (abs_nonneg _))
    _ ≤ K := by simp only [K]; linarith

private theorem fderiv_const_sub_apply {f : Space → ℝ} {x₀ y v : Space}
    (hf : DifferentiableAt ℝ f (x₀ - y)) :
    fderiv ℝ (fun z : Space => f (x₀ - z)) y v =
      -fderiv ℝ f (x₀ - y) v := by
  have hsub : HasFDerivAt (fun z : Space => x₀ - z)
      (-(1 : Space →L[ℝ] Space)) y :=
    (hasFDerivAt_id y).const_sub x₀
  change fderiv ℝ (f ∘ fun z : Space => x₀ - z) y v = _
  rw [(hf.hasFDerivAt.comp y hsub).fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply]
  rw [map_neg]
  rfl

/-- Two spatial derivatives of a reflected translate have positive sign. -/
theorem fderiv_fderiv_heatKernel_translate_apply
    (ν t : ℝ) (x₀ : Space) (i j : Fin 3) (y : Space) :
    fderiv ℝ
        (fun y' : Space =>
          fderiv ℝ (fun w : Space => heatKernel ν t (x₀ - w)) y'
            (basisVector i))
        y (basisVector j) =
      fderiv ℝ
        (fun y' : Space =>
          fderiv ℝ (fun w : Space => heatKernel ν t w) y'
            (basisVector i))
        (x₀ - y) (basisVector j) := by
  let F : Space → ℝ := fun w => heatKernel ν t w
  let D₁ : Space → ℝ := fun z => fderiv ℝ F z (basisVector i)
  have hF : ContDiff ℝ ∞ F := by
    dsimp only [F]
    unfold heatKernel
    fun_prop
  have hD₁ : ContDiff ℝ ∞ D₁ :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hF (basisVector i)
  have hfirst :
      (fun z : Space =>
          fderiv ℝ (fun w : Space => heatKernel ν t (x₀ - w)) z
            (basisVector i)) =
        fun z : Space => -D₁ (x₀ - z) := by
    funext z
    exact fderiv_const_sub_apply
      ((hF.differentiable (by norm_num)).differentiableAt)
  rw [hfirst]
  simp only [fderiv_fun_neg, neg_apply]
  rw [fderiv_const_sub_apply
    ((hD₁.differentiable (by norm_num)).differentiableAt)]
  simp only [D₁, F, neg_neg]

/-- A mixed second derivative of the translated Gaussian can be multiplied
by any two velocity coordinates on an actual `SolvesBefore` slice.  This is
the finite-energy integrability leaf used by every component of the uncut
backward-heat-curl convection pairing. -/
theorem SolvesBefore.integrable_secondHeatKernel_translate_mul_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : CriticalControlDecomposition.SolvesBefore μ T u p)
    {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ : Space)
    (derivativeOne derivativeTwo velocityOne velocityTwo : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector derivativeOne))
          y (basisVector derivativeTwo) *
        u s y velocityOne * u s y velocityTwo) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_abs_second_heatKernel_le_constant hκ hτ
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hD : ContDiff ℝ ∞ (fun y : Space =>
      fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector derivativeOne))
          y (basisVector derivativeTwo)) := by
    have hG : ContDiff ℝ ∞
        (fun w : Space => heatKernel κ τ (x₀ - w)) :=
      WholeSpaceCutoffLimit.heatKernel_translate_contDiff κ τ x₀
    exact Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        hG (basisVector derivativeOne)) (basisVector derivativeTwo)
  have hmajor : Integrable (fun y : Space => K * ‖u s y‖ ^ 2) :=
    (hsol.finite_energy s hs0 hsT).const_mul K
  apply hmajor.mono' ((hD.continuous.mul
    ((continuous_apply velocityOne).comp hu.continuous)).mul
      ((continuous_apply velocityTwo).comp hu.continuous)).aestronglyMeasurable
  filter_upwards with y
  have hDbound :
      |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector derivativeOne))
          y (basisVector derivativeTwo)| ≤ K := by
    rw [fderiv_fderiv_heatKernel_translate_apply]
    exact hbound (x₀ - y) derivativeOne derivativeTwo
  have hu1 : |u s y velocityOne| ≤ ‖u s y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (u s y) velocityOne
  have hu2 : |u s y velocityTwo| ≤ ‖u s y‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (u s y) velocityTwo
  change |fderiv ℝ
      (fun z : Space =>
        fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
          (basisVector derivativeOne))
      y (basisVector derivativeTwo) *
        u s y velocityOne * u s y velocityTwo| ≤ K * ‖u s y‖ ^ 2
  rw [abs_mul, abs_mul]
  calc
    |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector derivativeOne))
          y (basisVector derivativeTwo)| *
          |u s y velocityOne| * |u s y velocityTwo| ≤
        K * ‖u s y‖ * ‖u s y‖ := by
      exact mul_le_mul
        (mul_le_mul hDbound hu1 (abs_nonneg _) hK.le) hu2
        (abs_nonneg _) (mul_nonneg hK.le (norm_nonneg _))
    _ = K * ‖u s y‖ ^ 2 := by ring

private theorem backwardHeatCurlField_component_zero
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 0) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 1) * a 2 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 2) * a 1 := by
  funext y
  rw [WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
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
  rw [WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
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
  rw [WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
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

/-- The first derivative of the actual uncut backward-heat curl, contracted
against any two velocity coordinates, is integrable on every preterminal
finite-energy solution slice.  These are exactly the basis-direction leaves
whose finite sum forms the convection part of the cutoff-free Leray test. -/
theorem SolvesBefore.integrable_directional_backwardHeatCurlField_mul_velocityPair
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : CriticalControlDecomposition.SolvesBefore μ T u p)
    {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityOne velocityTwo : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (basisVector direction) *
        u s y velocityOne * u s y velocityTwo) := by
  have hG : ContDiff ℝ ∞
      (fun z : Space => heatKernel κ τ (x₀ - z)) :=
    WholeSpaceCutoffLimit.heatKernel_translate_contDiff κ τ x₀
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
            y (basisVector direction) * c *
              u s y velocityOne * u s y velocityTwo -
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector j))
            y (basisVector direction) * d *
              u s y velocityOne * u s y velocityTwo) := by
    intro i j c d
    have hi := (SolvesBefore.integrable_secondHeatKernel_translate_mul_velocityPair
      hsol hs0 hsT hκ hτ x₀ i direction velocityOne velocityTwo).const_mul c
    have hj := (SolvesBefore.integrable_secondHeatKernel_translate_mul_velocityPair
      hsol hs0 hsT hκ hτ x₀ j direction velocityOne velocityTwo).const_mul d
    apply (hi.sub hj).congr
    filter_upwards with y
    change c *
          (fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector i))
            y (basisVector direction) * u s y velocityOne * u s y velocityTwo) -
        d *
          (fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                (basisVector j))
            y (basisVector direction) * u s y velocityOne * u s y velocityTwo) = _
    ring
  fin_cases fieldComponent
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 0)
          y (basisVector direction) *
        u s y velocityOne * u s y velocityTwo)
    rw [backwardHeatCurlField_component_zero]
    apply (combine 1 2 (a 2) (a 1)).congr
    filter_upwards with y
    rw [directional_constLinearCombination (hDG 1) (hDG 2)]
    ring
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 1)
          y (basisVector direction) *
        u s y velocityOne * u s y velocityTwo)
    rw [backwardHeatCurlField_component_one]
    apply (combine 2 0 (a 0) (a 2)).congr
    filter_upwards with y
    rw [directional_constLinearCombination (hDG 2) (hDG 0)]
    ring
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z 2)
          y (basisVector direction) *
        u s y velocityOne * u s y velocityTwo)
    rw [backwardHeatCurlField_component_two]
    apply (combine 0 1 (a 1) (a 0)).congr
    filter_upwards with y
    rw [directional_constLinearCombination (hDG 0) (hDG 1)]
    ring

/-- **Cutoff-free Leray convection integrand.**  The derivative direction is
the velocity itself, exactly as in `lerayWeakRhs`; basis expansion reduces it
to the three finite-energy leaves above. -/
theorem SolvesBefore.integrable_backwardHeatCurlField_convection
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : CriticalControlDecomposition.SolvesBefore μ T u p)
    {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (fieldComponent velocityComponent : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (u s y) * u s y velocityComponent) := by
  have hterms : ∀ direction : Fin 3, Integrable (fun y : Space =>
      u s y direction *
        fderiv ℝ
          (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
          y (basisVector direction) * u s y velocityComponent) := by
    intro direction
    apply (SolvesBefore.integrable_directional_backwardHeatCurlField_mul_velocityPair
      hsol hs0 hsT hκ hτ x₀ a direction fieldComponent direction
        velocityComponent).congr
    filter_upwards with y
    ring
  apply (integrable_finsetSum Finset.univ fun direction _ =>
    hterms direction).congr
  filter_upwards with y
  rw [Navier.Analysis.CutoffIntegrationByParts.fderiv_apply_eq_sum_basis,
    Finset.sum_mul]

end Navier.Analysis.WholeSpaceSolenoidalHeatConvectionIntegrability
