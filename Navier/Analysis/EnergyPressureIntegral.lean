import Navier.Analysis.EnergyPressureCancellation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Whole-space pressure cancellation under explicit flux hypotheses

Coordinatewise whole-space integration by parts turns an integrable
divergence into zero.  Applied to the pressure flux, this upgrades the
pointwise identity to exact integral pressure-work cancellation.

No boundary term is hidden: both the flux and its coordinate derivatives are
required integrable.  The official classical-solution record does not yet
derive those pressure-flux hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.EnergyPressureIntegral

open Navier

/-- An everywhere differentiable vector field with coordinatewise integrable
components and coordinate derivatives has zero integral divergence. -/
theorem integral_staticDivergence_eq_zero
    (F : VelocityField)
    (hF : Differentiable ℝ F)
    (hF_integrable : ∀ i : Fin 3,
      Integrable (fun x => F x i) volume)
    (hderiv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => F y i) x (basisVector i)) volume) :
    ∫ x : Space, staticDivergence F x = 0 := by
  have hcoordDiff (i : Fin 3) :
      Differentiable ℝ (fun x => F x i) :=
    (differentiable_pi.mp hF) i
  have hcoord (i : Fin 3) (x : Space) :
      fderiv ℝ F x (basisVector i) i =
        fderiv ℝ (fun y => F y i) x (basisVector i) := by
    rw [fderiv_apply (hF x) i]
    rfl
  have hcomponent (i : Fin 3) :
      ∫ x : Space,
          fderiv ℝ (fun y => F y i) x (basisVector i) = 0 := by
    have h :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := volume)
        (f := fun _ : Space => (1 : ℝ))
        (g := fun x => F x i)
        (v := basisVector i)
        (by simp)
        (by simpa only [one_mul] using hderiv_integrable i)
        (by simpa only [one_mul] using hF_integrable i)
        (fun x _ => differentiableAt_const (c := (1 : ℝ)))
        (fun x _ => hcoordDiff i x)
    simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul,
      integral_zero, neg_zero] using h
  simp only [staticDivergence, hcoord]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun i _ => hderiv_integrable i)]
  exact Finset.sum_eq_zero (fun i _ => hcomponent i)

/-- Under explicit pressure-flux integrability, total pressure work vanishes
on all of `R^3`. -/
theorem integral_pressure_work_eq_zero
    (u : VelocityEvolution) (p : PressureEvolution)
    (t : ℝ) (ht : 0 ≤ t)
    (hu : Incompressible u)
    (hdu : Differentiable ℝ (u t))
    (hdp : Differentiable ℝ (p t))
    (hflux_integrable : ∀ i : Fin 3,
      Integrable (fun x => (p t x • u t x) i) volume)
    (hflux_deriv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => (p t y • u t y) i) x
            (basisVector i)) volume) :
    ∫ x : Space,
        ∑ i : Fin 3, pressureGradient p t x i * u t x i = 0 := by
  have hfluxDiff :
      Differentiable ℝ (fun y => p t y • u t y) :=
    hdp.smul hdu
  calc
    (∫ x : Space,
        ∑ i : Fin 3, pressureGradient p t x i * u t x i) =
        ∫ x : Space,
          staticDivergence (fun y => p t y • u t y) x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        pressure_work_eq_staticDivergence
          u p t ht x hu (hdu x) (hdp x))
    _ = 0 :=
      integral_staticDivergence_eq_zero
        (fun y => p t y • u t y)
        hfluxDiff hflux_integrable hflux_deriv_integrable

end Navier.Analysis.EnergyPressureIntegral
