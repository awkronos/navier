import Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit

/-!
# Full spatial viscous limit for the compact solenoidal heat test

This module combines the vanishing cutoff-gradient correction with the
surviving cutoff-times-curl limit at the exact field
`curl (χ_R G_τ a)` consumed by the compact weak evolution.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Matrix
open MeasureTheory Filter

namespace Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit

/-- Two diagonal directional derivatives distribute over a sum of smooth
scalar fields. -/
private theorem secondDirectional_add
    {F H : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    (direction : Fin 3) (x : Space) :
    fderiv ℝ (fun z : Space => fderiv ℝ (fun y : Space => F y + H y) z
      (basisVector direction)) x (basisVector direction) =
      fderiv ℝ (fun z : Space => fderiv ℝ F z (basisVector direction))
        x (basisVector direction) +
      fderiv ℝ (fun z : Space => fderiv ℝ H z (basisVector direction))
        x (basisVector direction) := by
  have hfirst : (fun z : Space => fderiv ℝ (fun y : Space => F y + H y) z
      (basisVector direction)) = fun z : Space =>
        fderiv ℝ F z (basisVector direction) +
          fderiv ℝ H z (basisVector direction) := by
    funext z
    rw [fderiv_fun_add
      ((hF.differentiable (by norm_num)).differentiableAt)
      ((hH.differentiable (by norm_num)).differentiableAt)]
    rfl
  rw [hfirst]
  have hDF := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hF (basisVector direction)
  have hDH := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    hH (basisVector direction)
  rw [fderiv_fun_add
    ((hDF.differentiable (by norm_num)).differentiableAt)
    ((hDH.differentiable (by norm_num)).differentiableAt)]
  rfl

/-- A smooth compactly supported scalar test remains integrable against a
continuous multiplier after two fixed directional derivatives. -/
private theorem integrable_secondDirectional_mul_of_smooth_compact
    (F : Space → ℝ) (hF : ContDiff ℝ ∞ F) (hSupp : HasCompactSupport F)
    (g : Space → ℝ) (hg : Continuous g) (direction : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => fderiv ℝ F z (basisVector direction)) y
        (basisVector direction) * g y) := by
  have hD2 := Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
    (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hF (basisVector direction)) (basisVector direction)
  have hSuppD2 := (hSupp.fderiv_apply ℝ (basisVector direction)).fderiv_apply ℝ
    (basisVector direction)
  exact (hD2.continuous.mul hg).integrable_of_hasCompactSupport
    hSuppD2.mul_right

/-- **Full spatial viscous cutoff limit at the original compact-test field.**
For the exact `solenoidalCutoffField R (backwardHeatPotential κ τ x₀ a)`,
the velocity pairing with every diagonal second derivative converges to the
uncut backward-heat curl pairing.  The proof combines both terms of the
kernel-checked curl product decomposition; no cutoff branch remains. -/
theorem SolvesBefore.tendsto_integral_secondDirectional_solenoidalCutoffField_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityComponent : Fin 3) :
    Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => solenoidalCutoffField R
            (backwardHeatPotential κ τ x₀ a) w fieldComponent)
          z (basisVector direction)) y (basisVector direction) *
            u s y velocityComponent)
      atTop
      (nhds (∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => backwardHeatCurlField κ τ x₀ a w fieldComponent)
          z (basisVector direction)) y (basisVector direction) *
            u s y velocityComponent)) := by
  let A : Space → Space := backwardHeatPotential κ τ x₀ a
  let C : ℝ → Space → ℝ := fun R w =>
    (staticGradient (scaledCutoff R) w ⨯₃ A w) fieldComponent
  let S : ℝ → Space → ℝ := fun R w =>
    scaledCutoff R w * backwardHeatCurlField κ τ x₀ a w fieldComponent
  let Q : ℝ → Space → ℝ := fun R w =>
    solenoidalCutoffField R A w fieldComponent
  have hA : ContDiff ℝ ∞ A := backwardHeatPotential_contDiff κ τ x₀ a
  have hcurl : ContDiff ℝ ∞ (fun w : Space =>
      backwardHeatCurlField κ τ x₀ a w fieldComponent) :=
    (contDiff_apply ℝ ℝ fieldComponent).comp
      (backwardHeatCurlField_contDiff κ τ x₀ a)
  have hS : ∀ R : ℝ, ContDiff ℝ ∞ (S R) := fun R =>
    (scaledCutoff_contDiff R).mul hcurl
  have hQ : ∀ R : ℝ, ContDiff ℝ ∞ (Q R) := fun R =>
    (contDiff_apply ℝ ℝ fieldComponent).comp
      (solenoidalCutoffField_contDiff R A hA)
  have hdecomp : ∀ R : ℝ, Q R = fun w => C R w + S R w := by
    intro R
    funext w
    simp only [Q, C, S]
    rw [solenoidalCutoffField_eq R A hA w]
    simp only [Pi.add_apply]
    rfl
  have hC : ∀ R : ℝ, ContDiff ℝ ∞ (C R) := by
    intro R
    have hshape : C R = fun w => Q R w - S R w := by
      funext w
      have hw := congrFun (hdecomp R) w
      exact (eq_sub_iff_add_eq).2 hw.symm
    rw [hshape]
    exact (hQ R).sub (hS R)
  have hcorr : Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ (C R) z
        (basisVector direction)) y (basisVector direction) *
          u s y velocityComponent) atTop (nhds 0) := by
    exact Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit.SolvesBefore.tendsto_integral_secondDirectional_cutoffGradientCrossPotential_mul_velocity_zero
      hsol hs0 hsT hκ hτ x₀ a direction fieldComponent velocityComponent
  have hsurv : Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ (S R) z
        (basisVector direction)) y (basisVector direction) *
          u s y velocityComponent) atTop
      (nhds (∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => backwardHeatCurlField κ τ x₀ a w fieldComponent)
          z (basisVector direction)) y (basisVector direction) *
            u s y velocityComponent)) := by
    exact Navier.Analysis.WholeSpaceSolenoidalHeatViscousProductLimit.SolvesBefore.tendsto_integral_secondDirectional_scaledCutoff_backwardHeatCurlField_mul_velocity
      hsol hs0 hsT hκ hτ x₀ a direction fieldComponent velocityComponent
  have hEq : (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ (Q R) z
        (basisVector direction)) y (basisVector direction) *
          u s y velocityComponent) =ᶠ[atTop]
    (fun R : ℝ =>
      (∫ y : Space, fderiv ℝ (fun z : Space => fderiv ℝ (C R) z
          (basisVector direction)) y (basisVector direction) *
            u s y velocityComponent) +
      ∫ y : Space, fderiv ℝ (fun z : Space => fderiv ℝ (S R) z
          (basisVector direction)) y (basisVector direction) *
            u s y velocityComponent) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hSSupp : HasCompactSupport (S R) := by
      exact (scaledCutoff_hasCompactSupport hR).mul_right
    have hQSupp : HasCompactSupport (Q R) := by
      exact (solenoidalCutoffField_hasCompactSupport hR A).comp_left
        (g := fun v : Space => v fieldComponent) (by simp)
    have hCshape : C R = fun w => Q R w - S R w := by
      funext w
      have hw := congrFun (hdecomp R) w
      exact (eq_sub_iff_add_eq).2 hw.symm
    have hCSupp : HasCompactSupport (C R) := by
      rw [hCshape]
      exact hQSupp.sub hSSupp
    have hCint := integrable_secondDirectional_mul_of_smooth_compact
      (C R) (hC R) hCSupp (fun y : Space => u s y velocityComponent)
      ((continuous_apply velocityComponent).comp
        (contDiff_iff_contDiffAt.mpr (fun y =>
          Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
            hsol.classical.1 hs0 hsT y)).continuous) direction
    have hSint := integrable_secondDirectional_mul_of_smooth_compact
      (S R) (hS R) hSSupp (fun y : Space => u s y velocityComponent)
      ((continuous_apply velocityComponent).comp
        (contDiff_iff_contDiffAt.mpr (fun y =>
          Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
            hsol.classical.1 hs0 hsT y)).continuous) direction
    rw [hdecomp R]
    simp_rw [secondDirectional_add (hC R) (hS R) direction]
    rw [show (fun y : Space =>
        (fderiv ℝ (fun z : Space => fderiv ℝ (C R) z
            (basisVector direction)) y (basisVector direction) +
          fderiv ℝ (fun z : Space => fderiv ℝ (S R) z
            (basisVector direction)) y (basisVector direction)) *
              u s y velocityComponent) = fun y =>
        fderiv ℝ (fun z : Space => fderiv ℝ (C R) z
            (basisVector direction)) y (basisVector direction) *
              u s y velocityComponent +
        fderiv ℝ (fun z : Space => fderiv ℝ (S R) z
            (basisVector direction)) y (basisVector direction) *
              u s y velocityComponent by funext y; ring]
    rw [integral_add hCint hSint]
  change Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ (Q R) z
        (basisVector direction)) y (basisVector direction) *
          u s y velocityComponent) atTop _
  have hsum := hcorr.add hsurv
  have hfinal := hsum.congr' hEq.symm
  simpa using hfinal

end Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit
