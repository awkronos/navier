import Navier.Analysis.WholeSpaceSolenoidalHeatViscousIntegrability

/-!
# Pointwise viscous cutoff limit for the solenoidal heat test

This file removes the `χ_R curl A` portion of the finite-radius viscous
cutoff.  It proves the full second-order product rule and takes its pointwise
`R → ∞` limit using the native scaled-cutoff derivative rates.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators Topology ContDiff Matrix
open Filter
open MeasureTheory

namespace Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit

open Navier
open Navier.Breakdown
open Navier.Analysis
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination

/-- The exact diagonal second-derivative product rule used by the viscous
slot of `lerayWeakRhs`. -/
theorem secondDirectional_mul
    {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (direction : Fin 3) (x : Space) :
    fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun y : Space => f y * g y) z (basisVector direction))
        x (basisVector direction) =
      fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction))
          x (basisVector direction) * g x +
        2 * (fderiv ℝ f x (basisVector direction) *
          fderiv ℝ g x (basisVector direction)) +
        f x * fderiv ℝ
          (fun z : Space => fderiv ℝ g z (basisVector direction))
          x (basisVector direction) := by
  have hfirst :
      (fun z : Space =>
          fderiv ℝ (fun y : Space => f y * g y) z (basisVector direction)) =
        fun z : Space =>
          fderiv ℝ f z (basisVector direction) * g z +
            f z * fderiv ℝ g z (basisVector direction) := by
    funext z
    change (fderiv ℝ (f * g) z) (basisVector direction) = _
    rw [fderiv_mul
      ((hf.differentiable (by norm_num)).differentiableAt)
      ((hg.differentiable (by norm_num)).differentiableAt)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  rw [hfirst]
  have hDf : ContDiff ℝ ∞
      (fun z : Space => fderiv ℝ f z (basisVector direction)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hf (basisVector direction)
  have hDg : ContDiff ℝ ∞
      (fun z : Space => fderiv ℝ g z (basisVector direction)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hg (basisVector direction)
  change (fderiv ℝ
    (fun z : Space =>
      fderiv ℝ f z (basisVector direction) * g z +
        f z * fderiv ℝ g z (basisVector direction)) x)
      (basisVector direction) = _
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

/-- Each fixed diagonal second derivative of the scaled cutoff tends to zero. -/
theorem tendsto_secondDirectional_scaledCutoff_zero
    (direction : Fin 3) (x : Space) :
    Tendsto (fun R : ℝ =>
      fderiv ℝ
        (fun z : Space => fderiv ℝ (scaledCutoff R) z (basisVector direction))
        x (basisVector direction)) atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_fderiv_bound
    standardBump standardBump.contDiff standardBump.hasCompactSupport
    (basisVector direction) (basisVector direction)
  apply squeeze_zero_norm' (a := fun R : ℝ => R⁻¹ * R⁻¹ * M)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.norm_eq_abs]
    exact abs_fderiv_fderiv_scaled_le standardBump standardBump.contDiff
      hM hR x
  · have hzero : Tendsto (fun R : ℝ => R⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero
    simpa using (hzero.mul hzero).mul_const M

/-- **Surviving viscous product limit.**  For every smooth scalar field, the
diagonal second derivative of `χ_R f` converges pointwise to that of `f`.
Both cutoff-derivative errors are eliminated rather than postulated. -/
theorem tendsto_secondDirectional_scaledCutoff_mul
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (direction : Fin 3) (x : Space) :
    Tendsto (fun R : ℝ =>
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun y : Space => scaledCutoff R y * f y) z
            (basisVector direction))
        x (basisVector direction)) atTop
      (nhds (fderiv ℝ
        (fun z : Space => fderiv ℝ f z (basisVector direction))
        x (basisVector direction))) := by
  have hχ0 : Tendsto (fun R : ℝ => scaledCutoff R x) atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [scaledCutoff_eventually_one x] with R hR
    exact hR.symm
  have hDχ0 : Tendsto (fun R : ℝ =>
      fderiv ℝ (scaledCutoff R) x (basisVector direction)) atTop (nhds 0) := by
    have hgrad := scaledCutoff_staticGradient_tendsto_zero x
    rw [tendsto_pi_nhds] at hgrad
    simpa only [staticGradient, Pi.zero_apply] using hgrad direction
  have hD2χ0 := tendsto_secondDirectional_scaledCutoff_zero direction x
  simp_rw [secondDirectional_mul (scaledCutoff_contDiff _) hf direction x]
  have hfirst := hD2χ0.mul_const (f x)
  have hmiddle := (hDχ0.mul_const
    (fderiv ℝ f x (basisVector direction))).const_mul 2
  have hlast := hχ0.mul_const
    (fderiv ℝ (fun z : Space => fderiv ℝ f z (basisVector direction))
      x (basisVector direction))
  convert (hfirst.add hmiddle).add hlast using 1
  all_goals simp

/-- The preceding pointwise limit is instantiated on the actual cutoff-free
solenoidal Gaussian field used by the weak evolution consumer. -/
theorem tendsto_secondDirectional_scaledCutoff_backwardHeatCurlField
    (κ τ : ℝ) (x₀ a : Space) (direction fieldComponent : Fin 3) (x : Space) :
    Tendsto (fun R : ℝ =>
      fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun y : Space => scaledCutoff R y *
            backwardHeatCurlField κ τ x₀ a y fieldComponent) z
            (basisVector direction))
        x (basisVector direction)) atTop
      (nhds (fderiv ℝ
        (fun z : Space => fderiv ℝ
          (fun y : Space => backwardHeatCurlField κ τ x₀ a y fieldComponent)
          z (basisVector direction)) x (basisVector direction))) := by
  apply tendsto_secondDirectional_scaledCutoff_mul
  exact (contDiff_apply ℝ ℝ fieldComponent).comp
    (backwardHeatCurlField_contDiff κ τ x₀ a)

/-- **The two cutoff-free DCT inputs on the actual solution carrier.**  The
surviving viscous product has the required a.e. pointwise cutoff limit, and
its limit is integrable against every preterminal finite-energy velocity
slice.  What remains for spatial dominated convergence is one uniform
integrable envelope for the two cutoff-derivative errors; the separate
`∇χ_R × A` solenoidal correction is not folded into this statement. -/
theorem SolvesBefore.integrable_and_ae_tendsto_scaledCutoff_secondDirectional_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityComponent : Fin 3) :
    Integrable (fun y : Space =>
      fderiv ℝ
          (fun z : Space =>
            fderiv ℝ
              (fun w : Space =>
                backwardHeatCurlField κ τ x₀ a w fieldComponent)
              z (basisVector direction))
          y (basisVector direction) * u s y velocityComponent) ∧
      ∀ᵐ y : Space ∂volume,
        Tendsto (fun R : ℝ =>
          fderiv ℝ
              (fun z : Space =>
                fderiv ℝ
                  (fun w : Space => scaledCutoff R w *
                    backwardHeatCurlField κ τ x₀ a w fieldComponent)
                  z (basisVector direction))
              y (basisVector direction) * u s y velocityComponent)
          atTop
          (nhds (fderiv ℝ
              (fun z : Space =>
                fderiv ℝ
                  (fun w : Space =>
                    backwardHeatCurlField κ τ x₀ a w fieldComponent)
                  z (basisVector direction))
              y (basisVector direction) * u s y velocityComponent)) := by
  constructor
  · exact Navier.Analysis.WholeSpaceSolenoidalHeatViscousIntegrability.SolvesBefore.integrable_secondDirectional_backwardHeatCurlField_mul_velocity
      hsol hs0 hsT hκ hτ x₀ a direction fieldComponent velocityComponent
  · filter_upwards with y
    exact (tendsto_secondDirectional_scaledCutoff_backwardHeatCurlField
      κ τ x₀ a direction fieldComponent y).mul_const (u s y velocityComponent)

end Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit

#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit.secondDirectional_mul
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit.tendsto_secondDirectional_scaledCutoff_mul
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit.tendsto_secondDirectional_scaledCutoff_backwardHeatCurlField
#print axioms Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit.SolvesBefore.integrable_and_ae_tendsto_scaledCutoff_secondDirectional_mul_velocity
