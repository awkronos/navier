import Navier.Analysis.WholeSpaceHeatThirdDerivative

/-!
# Viscous pairing for the whole-space solenoidal heat test

This file consumes the square-integrable third heat-kernel derivatives to
justify the cutoff-free viscous integrand attached to the actual field
`curl (G a)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal Topology ContDiff Matrix
open MeasureTheory Filter

namespace Navier.Analysis.WholeSpaceSolenoidalHeatViscousIntegrability

open Navier
open Navier.Analysis
open Navier.Analysis.Vorticity
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceHeatThirdDerivative

private theorem backwardHeatCurlField_component_zero
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 0) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y (basisVector 1) * a 2 -
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y (basisVector 2) * a 1 := by
  funext y
  rw [backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

private theorem backwardHeatCurlField_component_one
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 1) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y (basisVector 2) * a 0 -
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y (basisVector 0) * a 2 := by
  funext y
  rw [backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

private theorem backwardHeatCurlField_component_two
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 2) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y (basisVector 0) * a 1 -
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y (basisVector 1) * a 0 := by
  funext y
  rw [backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

/-- Two directional derivatives commute with a fixed scalar linear
combination.  This is the exact product-free algebra left after expanding the
curl of the constant-polarized Gaussian potential. -/
private theorem secondDirectional_constLinearCombination
    {F H : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    (c d : ℝ) (direction : Fin 3) (x : Space) :
    fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun y : Space => F y * c - H y * d) z
            (basisVector direction))
        x (basisVector direction) =
      fderiv ℝ
          (fun z : Space => fderiv ℝ F z (basisVector direction))
          x (basisVector direction) * c -
        fderiv ℝ
          (fun z : Space => fderiv ℝ H z (basisVector direction))
          x (basisVector direction) * d := by
  have hfirst :
      (fun z : Space =>
          fderiv ℝ (fun y : Space => F y * c - H y * d) z
            (basisVector direction)) =
        fun z : Space =>
          fderiv ℝ F z (basisVector direction) * c -
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
  have hDF : ContDiff ℝ ∞
      (fun z : Space => fderiv ℝ F z (basisVector direction)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hF (basisVector direction)
  have hDH : ContDiff ℝ ∞
      (fun z : Space => fderiv ℝ H z (basisVector direction)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
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

/-- **Actual cutoff-free viscous summand.**  Every diagonal second derivative
of every component of `curl (G_t(x₀-·) a)`, paired with any component of a
preterminal finite-energy velocity slice, is integrable.  Summing this theorem
over `direction` is precisely the spatial integrability required by the
viscous part of `lerayWeakRhs` after the cutoff is removed. -/
theorem SolvesBefore.integrable_secondDirectional_backwardHeatCurlField_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityComponent : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space =>
            fderiv ℝ
              (fun w : Space => backwardHeatCurlField κ τ x₀ a w fieldComponent)
              z (basisVector direction))
          y (basisVector direction) * u s y velocityComponent) := by
  let K : Space → ℝ := fun y => heatKernel κ τ (x₀ - y)
  have hK : ContDiff ℝ ∞ K := by
    exact Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff κ τ x₀
  have hDK : ∀ q : Fin 3, ContDiff ℝ ∞
      (fun y : Space => fderiv ℝ K y (basisVector q)) := fun q =>
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hK (basisVector q)
  have hpair : ∀ q : Fin 3, Integrable (fun y : Space =>
      fderiv ℝ
          (fun y' : Space =>
            fderiv ℝ (fun z : Space => fderiv ℝ K z (basisVector q))
              y' (basisVector direction))
          y (basisVector direction) * u s y velocityComponent) := fun q => by
    exact Navier.Analysis.WholeSpaceHeatThirdDerivative.SolvesBefore.integrable_thirdHeatKernel_translate_mul_velocity
      hsol hs0 hsT
        hκ hτ x₀ q direction direction velocityComponent
  fin_cases fieldComponent
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space =>
            fderiv ℝ
              (fun w : Space => backwardHeatCurlField κ τ x₀ a w 0)
              z (basisVector direction))
          y (basisVector direction) * u s y velocityComponent)
    have hcomb := secondDirectional_constLinearCombination
      (hDK 1) (hDK 2) (a 2) (a 1) direction
    have hint := ((hpair 1).const_mul (a 2)).sub ((hpair 2).const_mul (a 1))
    apply hint.congr
    filter_upwards with y
    rw [backwardHeatCurlField_component_zero]
    rw [hcomb]
    simp only [Pi.sub_apply]
    ring
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space =>
            fderiv ℝ
              (fun w : Space => backwardHeatCurlField κ τ x₀ a w 1)
              z (basisVector direction))
          y (basisVector direction) * u s y velocityComponent)
    have hcomb := secondDirectional_constLinearCombination
      (hDK 2) (hDK 0) (a 0) (a 2) direction
    have hint := ((hpair 2).const_mul (a 0)).sub ((hpair 0).const_mul (a 2))
    apply hint.congr
    filter_upwards with y
    rw [backwardHeatCurlField_component_one]
    rw [hcomb]
    simp only [Pi.sub_apply]
    ring
  · change Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space =>
            fderiv ℝ
              (fun w : Space => backwardHeatCurlField κ τ x₀ a w 2)
              z (basisVector direction))
          y (basisVector direction) * u s y velocityComponent)
    have hcomb := secondDirectional_constLinearCombination
      (hDK 0) (hDK 1) (a 1) (a 0) direction
    have hint := ((hpair 0).const_mul (a 1)).sub ((hpair 1).const_mul (a 0))
    apply hint.congr
    filter_upwards with y
    rw [backwardHeatCurlField_component_two]
    rw [hcomb]
    simp only [Pi.sub_apply]
    ring

end Navier.Analysis.WholeSpaceSolenoidalHeatViscousIntegrability
