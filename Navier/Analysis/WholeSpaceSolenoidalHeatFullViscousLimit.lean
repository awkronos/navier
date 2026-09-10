import Navier.Analysis.WholeSpaceSolenoidalHeatViscousCorrectionLimit
import Navier.Analysis.WholeSpaceSolenoidalHeatConvectionLimit

/-!
# Full spatial limits for the compact solenoidal heat test

This module combines the vanishing cutoff-gradient correction with the
surviving cutoff-times-curl limit at the exact field
`curl (χ_R G_τ a)` consumed by the compact weak evolution.  It then assembles
the momentum, convection, and viscous limits at the exact fixed-time
`lerayWeakRhs`; only the interval-time limit remains between this result and a
cutoff-free weak evolution identity.
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
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatConvectionLimit
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
theorem integrable_secondDirectional_mul_of_smooth_compact
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

/-! ## Assembly of the exact fixed-time right-hand side -/

/-- The cutoff-free viscous slot obtained from the diagonal spatial
Laplacian in `lerayWeakRhs`. -/
def backwardHeatCurlViscousRhs
    (κ τ : ℝ) (x₀ a : Space) (u : VelocityEvolution) (s : ℝ) : ℝ :=
  ∑ fieldComponent : Fin 3, ∑ direction : Fin 3, ∫ y : Space,
    fderiv ℝ (fun z : Space => fderiv ℝ
      (fun w : Space => backwardHeatCurlField κ τ x₀ a w fieldComponent)
      z (basisVector direction)) y (basisVector direction) *
        u s y fieldComponent

/-- The full cutoff-free spatial right-hand side at a fixed time. -/
def backwardHeatCurlRhs
    (ν κ τ : ℝ) (x₀ a : Space) (u : VelocityEvolution) (s : ℝ) : ℝ :=
  backwardHeatCurlConvectionRhs κ τ x₀ a u s +
    ν * backwardHeatCurlViscousRhs κ τ x₀ a u s

/-- The exact compact-test `lerayWeakRhs` is the sum of its convection slot
and expanded viscous coordinate integrals. -/
theorem lerayWeakRhs_compactBackwardHeatCurlTest_eq
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore ν T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    (R κ τ : ℝ) (x₀ a : Space) :
    lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s =
      (∑ fieldComponent : Fin 3, ∫ y : Space,
        fderiv ℝ
          (fun z : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field z
              fieldComponent)
          y (u s y) * u s y fieldComponent) +
      ν * (∑ fieldComponent : Fin 3, ∑ direction : Fin 3, ∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w
              fieldComponent)
          z (basisVector direction)) y (basisVector direction) *
            u s y fieldComponent) := by
  let φ := atTopCompactBackwardHeatCurlTest R κ τ x₀ a
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      Navier.Analysis.ParabolicCaccioppoli.contDiffAt_spatial_slice_before
        hsol.classical.1 hs0 hsT y
  have hint : ∀ (fieldComponent direction : Fin 3), Integrable (fun y : Space =>
      fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => φ.field w fieldComponent)
        z (basisVector direction)) y (basisVector direction) *
          u s y fieldComponent) := by
    intro fieldComponent direction
    exact integrable_secondDirectional_mul_of_smooth_compact
      (fun w : Space => φ.field w fieldComponent)
      (φ.smooth fieldComponent) (φ.compact fieldComponent)
      (fun y : Space => u s y fieldComponent)
      ((continuous_apply fieldComponent).comp hu.continuous) direction
  have hinterchange : ∀ fieldComponent : Fin 3,
      (∫ y : Space, (∑ direction : Fin 3,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => φ.field w fieldComponent)
          z (basisVector direction)) y (basisVector direction)) *
            u s y fieldComponent) =
      ∑ direction : Fin 3, ∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space => φ.field w fieldComponent)
          z (basisVector direction)) y (basisVector direction) *
            u s y fieldComponent := by
    intro fieldComponent
    rw [show (fun y : Space =>
        (∑ direction : Fin 3,
          fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => φ.field w fieldComponent)
            z (basisVector direction)) y (basisVector direction)) *
              u s y fieldComponent) =
        (fun y : Space => ∑ direction : Fin 3,
          fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space => φ.field w fieldComponent)
            z (basisVector direction)) y (basisVector direction) *
              u s y fieldComponent) by
          funext y
          rw [Finset.sum_mul]]
    exact integral_finsetSum Finset.univ
      (fun direction _ => hint fieldComponent direction)
  change lerayWeakRhs ν φ u s = _
  unfold lerayWeakRhs
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro fieldComponent _
  rw [hinterchange fieldComponent]

private theorem tendsto_max_one_atTop :
    Tendsto (fun R : ℝ => max 1 R) atTop atTop := by
  have hid : Tendsto (fun R : ℝ => R) atTop atTop := Filter.tendsto_id
  apply Filter.tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun R : ℝ => le_max_right 1 R)
  exact hid

/-- **Full fixed-time spatial cutoff limit.**  On every actual preterminal
finite-energy solution slice, the exact compact-test right-hand side tends to
the cutoff-free convection plus viscous expression.  No additional analytic
hypothesis is introduced. -/
theorem SolvesBefore.tendsto_compactBackwardHeatCurlTest_lerayWeakRhs
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore ν T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    Tendsto (fun R : ℝ =>
      lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s)
      atTop (nhds (backwardHeatCurlRhs ν κ τ x₀ a u s)) := by
  have hconv := SolvesBefore.tendsto_compactBackwardHeatCurlTest_convection
    hsol hs0 hsT hκ hτ x₀ a
  have hvør : ∀ (fieldComponent direction : Fin 3),
      Tendsto (fun R : ℝ => ∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w
              fieldComponent)
          z (basisVector direction)) y (basisVector direction) *
            u s y fieldComponent)
        atTop
        (nhds (∫ y : Space,
          fderiv ℝ (fun z : Space => fderiv ℝ
            (fun w : Space =>
              backwardHeatCurlField κ τ x₀ a w fieldComponent)
            z (basisVector direction)) y (basisVector direction) *
              u s y fieldComponent)) := by
    intro fieldComponent direction
    have hbase :=
      SolvesBefore.tendsto_integral_secondDirectional_solenoidalCutoffField_mul_velocity
        hsol hs0 hsT hκ hτ x₀ a direction fieldComponent fieldComponent
    change Tendsto (fun R : ℝ => ∫ y : Space,
      fderiv ℝ (fun z : Space => fderiv ℝ
        (fun w : Space => solenoidalCutoffField (max 1 R)
          (backwardHeatPotential κ τ x₀ a) w fieldComponent)
        z (basisVector direction)) y (basisVector direction) *
          u s y fieldComponent) atTop _
    convert hbase.comp tendsto_max_one_atTop using 1
    all_goals rfl
  have hvisc : Tendsto (fun R : ℝ =>
      ∑ fieldComponent : Fin 3, ∑ direction : Fin 3, ∫ y : Space,
        fderiv ℝ (fun z : Space => fderiv ℝ
          (fun w : Space =>
            (atTopCompactBackwardHeatCurlTest R κ τ x₀ a).field w
              fieldComponent)
          z (basisVector direction)) y (basisVector direction) *
            u s y fieldComponent)
      atTop (nhds (backwardHeatCurlViscousRhs κ τ x₀ a u s)) := by
    unfold backwardHeatCurlViscousRhs
    exact tendsto_finsetSum Finset.univ (fun fieldComponent _ =>
      tendsto_finsetSum Finset.univ (fun direction _ => hvør fieldComponent direction))
  unfold backwardHeatCurlRhs
  have hsum := hconv.add (hvisc.const_mul ν)
  apply hsum.congr'
  filter_upwards with R
  rw [lerayWeakRhs_compactBackwardHeatCurlTest_eq hsol hs0 hsT]

/-- Both momentum endpoints of the exact compact weak evolution lose their
spatial cutoff.  This is the left-hand-side companion to the fixed-time
`lerayWeakRhs` limit. -/
theorem SolvesBefore.tendsto_compactBackwardHeatCurlTest_testedMomentum_sub
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore ν T u p)
    {ta tb : ℝ} (hta0 : 0 ≤ ta) (htaT : ta < T)
    (htb0 : 0 ≤ tb) (htbT : tb < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    Tendsto (fun R : ℝ =>
      testedMomentum (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u tb -
        testedMomentum (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u ta)
      atTop (nhds (
        backwardHeatCurlMomentum κ τ x₀ a u tb -
          backwardHeatCurlMomentum κ τ x₀ a u ta)) := by
  exact
    (solvesBefore_compactBackwardHeatCurlTestedMomentum_tendsto
      hsol htb0 htbT hκ hτ x₀ a).sub
    (solvesBefore_compactBackwardHeatCurlTestedMomentum_tendsto
      hsol hta0 htaT hκ hτ x₀ a)

end Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit

#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit.integrable_secondDirectional_mul_of_smooth_compact
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit.lerayWeakRhs_compactBackwardHeatCurlTest_eq
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit.SolvesBefore.tendsto_compactBackwardHeatCurlTest_lerayWeakRhs
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit.SolvesBefore.tendsto_compactBackwardHeatCurlTest_testedMomentum_sub
