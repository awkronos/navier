import Navier.Analysis.EnergyConvectionCancellation
import Navier.Analysis.EnergyPressureIntegral

/-!
# Whole-space convection cancellation under explicit flux hypotheses

The pointwise convection-work identity is upgraded to a whole-space integral
only when every coordinate of the kinetic-energy flux and its matching
coordinate derivative is integrable.  These hypotheses are stated directly:
no decay or integrability transport from smoothness is asserted here.

This file proves no full energy identity and performs no time integration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.EnergyConvectionIntegral

open Navier

/-- At a nonnegative time, a differentiable incompressible velocity slice
rewrites the convective-work integrand as divergence of kinetic-energy flux. -/
theorem convection_work_integrand_eq_staticDivergence
    (u : VelocityEvolution) (t : ℝ) (ht : 0 ≤ t)
    (hinc : Incompressible u) (hdu : Differentiable ℝ (u t)) :
    (fun x : Space =>
      ∑ i : Fin 3, convection u t x i * u t x i) =
      fun x : Space => staticDivergence (kineticEnergyFlux (u t)) x := by
  funext x
  exact convection_work_eq_staticDivergence_of_incompressible
    u t ht x (hdu x) hinc

/-- Convective work integrates to zero on all of `R^3` when the kinetic-energy
flux and its coordinate derivatives satisfy the explicit integrability
hypotheses of the whole-space divergence lemma. -/
theorem integral_convection_work_eq_zero
    (u : VelocityEvolution) (t : ℝ) (ht : 0 ≤ t)
    (hinc : Incompressible u) (hdu : Differentiable ℝ (u t))
    (hflux_integrable : ∀ i : Fin 3,
      Integrable (fun x => kineticEnergyFlux (u t) x i) volume)
    (hflux_deriv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => kineticEnergyFlux (u t) y i) x
            (basisVector i)) volume) :
    ∫ x : Space,
        ∑ i : Fin 3, convection u t x i * u t x i = 0 := by
  have henergyDiff : Differentiable ℝ (kineticEnergyDensity (u t)) :=
    fun x => differentiableAt_kineticEnergyDensity (u t) x (hdu x)
  have hfluxDiff : Differentiable ℝ (kineticEnergyFlux (u t)) := by
    unfold kineticEnergyFlux
    exact henergyDiff.smul hdu
  have hrewrite :=
    convection_work_integrand_eq_staticDivergence u t ht hinc hdu
  calc
    (∫ x : Space,
        ∑ i : Fin 3, convection u t x i * u t x i) =
        ∫ x : Space,
          staticDivergence (kineticEnergyFlux (u t)) x :=
      congrArg (fun g : Space → ℝ => ∫ x, g x) hrewrite
    _ = 0 :=
      Navier.Analysis.EnergyPressureIntegral.integral_staticDivergence_eq_zero
        (kineticEnergyFlux (u t)) hfluxDiff
        hflux_integrable hflux_deriv_integrable

end Navier.Analysis.EnergyConvectionIntegral
