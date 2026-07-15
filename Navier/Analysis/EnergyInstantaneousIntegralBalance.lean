import Navier.Analysis.EnergyTimeDerivative
import Navier.Analysis.EnergyPressureIntegral
import Navier.Analysis.EnergyConvectionIntegral
import Navier.Analysis.EnergyViscousIntegral

/-!
# Guarded instantaneous whole-space energy balance

For a zero-force classical solution, the pointwise kinetic-energy-density
time derivative is viscosity work minus pressure work minus convection work.
Under explicit whole-space integrability hypotheses for the three associated
fluxes, the pressure and convection terms integrate to zero and viscosity work
integrates to minus the nonnegative derivative-energy density.

This is an identity at one fixed nonnegative time.  Its left side is the
spatial integral of a pointwise `fderivWithin`; this file does **not** identify
that quantity with the time derivative of a spatial kinetic-energy integral,
and it performs no time integration.  The stated flux hypotheses are also not
claimed to follow from the repository's classical-solution record.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.EnergyInstantaneousIntegralBalance

open Navier
open EnergyConvectionIntegral
open EnergyPressureIntegral
open EnergyViscousDissipation
open EnergyViscousIntegral

/-- For a zero-force classical solution, the pointwise density time
derivative contains exactly viscosity, pressure, and convection work, with
the Navier--Stokes signs made explicit. -/
theorem kineticEnergyDensity_timeDerivative_eq_zeroForce_work
    {ν : ℝ} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1 =
      ν * (∑ i : Fin 3, laplacian u t x i * u t x i) -
      (∑ i : Fin 3, pressureGradient p t x i * u t x i) -
      (∑ i : Fin 3, convection u t x i * u t x i) := by
  simpa only [zeroForce, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero] using
    kineticEnergyDensity_timeDerivative_eq_work_of_classicalSolution
      hsol t ht x

/-- Integrability of the pressure-flux coordinate derivatives implies
integrability of pressure work.  Integrability of the flux components is only
needed later to make its whole-space integral vanish. -/
theorem integrable_pressure_work_of_flux
    (u : VelocityEvolution) (p : PressureEvolution)
    (t : ℝ) (ht : 0 ≤ t)
    (hinc : Incompressible u)
    (hdu : Differentiable ℝ (u t))
    (hdp : Differentiable ℝ (p t))
    (hflux_deriv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => (p t y • u t y) i) x
            (basisVector i)) volume) :
    Integrable
      (fun x => ∑ i : Fin 3,
        pressureGradient p t x i * u t x i) volume := by
  have hfluxDiff :
      Differentiable ℝ (fun y => p t y • u t y) :=
    hdp.smul hdu
  have hdiv_integrable :
      Integrable
        (fun x => staticDivergence (fun y => p t y • u t y) x) volume :=
    integrable_staticDivergence_of_coordinatewise
      (fun y => p t y • u t y) hfluxDiff hflux_deriv_integrable
  apply hdiv_integrable.congr
  exact Filter.Eventually.of_forall (fun x =>
    (pressure_work_eq_staticDivergence
      u p t ht x hinc (hdu x) (hdp x)).symm)

/-- Integrability of the kinetic-energy-flux coordinate derivatives implies
integrability of convection work.  Flux-component integrability remains the
separate boundary-removal hypothesis. -/
theorem integrable_convection_work_of_flux
    (u : VelocityEvolution) (t : ℝ) (ht : 0 ≤ t)
    (hinc : Incompressible u)
    (hdu : Differentiable ℝ (u t))
    (hflux_deriv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => kineticEnergyFlux (u t) y i) x
            (basisVector i)) volume) :
    Integrable
      (fun x => ∑ i : Fin 3,
        convection u t x i * u t x i) volume := by
  have henergyDiff : Differentiable ℝ (kineticEnergyDensity (u t)) :=
    fun x => differentiableAt_kineticEnergyDensity (u t) x (hdu x)
  have hfluxDiff : Differentiable ℝ (kineticEnergyFlux (u t)) := by
    unfold kineticEnergyFlux
    exact henergyDiff.smul hdu
  have hdiv_integrable :
      Integrable
        (fun x => staticDivergence (kineticEnergyFlux (u t)) x) volume :=
    integrable_staticDivergence_of_coordinatewise
      (kineticEnergyFlux (u t)) hfluxDiff hflux_deriv_integrable
  apply hdiv_integrable.congr
  have hrewrite :=
    convection_work_integrand_eq_staticDivergence u t ht hinc hdu
  exact Filter.Eventually.of_forall (fun x => (congrFun hrewrite x).symm)

/-- The three derivative-flux guards and derivative-energy integrability
derive integrability of the pointwise kinetic-energy-density time derivative.
No independent work-integrability or time-derivative-integrability hypothesis
is needed. -/
theorem integrable_kineticEnergyDensity_timeDerivative_of_zeroForce
    {ν : ℝ} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    (t : ℝ) (ht : 0 ≤ t)
    (hdu : Differentiable ℝ (u t))
    (hdp : Differentiable ℝ (p t))
    (hddu : ∀ j : Fin 3,
      Differentiable ℝ (coordinateDerivativeField (u t) j))
    (hpressure_flux_deriv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => (p t y • u t y) i) x
            (basisVector i)) volume)
    (hconvection_flux_deriv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => kineticEnergyFlux (u t) y i) x
            (basisVector i)) volume)
    (hviscous_flux_deriv_integrable : ∀ j : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => viscousEnergyFlux (u t) y j) x
            (basisVector j)) volume)
    (hdensity_integrable :
      Integrable (derivativeEnergyDensity (u t)) volume) :
    Integrable
      (fun x =>
        fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
          (Set.Ici 0) t 1) volume := by
  have hviscousWork :
      Integrable
        (fun x => ∑ i : Fin 3,
          laplacian u t x i * u t x i) volume :=
    integrable_laplacian_work_of_viscous_flux
      u t hdu hddu hviscous_flux_deriv_integrable hdensity_integrable
  have hpressureWork :
      Integrable
        (fun x => ∑ i : Fin 3,
          pressureGradient p t x i * u t x i) volume :=
    integrable_pressure_work_of_flux
      u p t ht hsol.incompressible hdu hdp
      hpressure_flux_deriv_integrable
  have hconvectionWork :
      Integrable
        (fun x => ∑ i : Fin 3,
          convection u t x i * u t x i) volume :=
    integrable_convection_work_of_flux
      u t ht hsol.incompressible hdu
      hconvection_flux_deriv_integrable
  apply (((hviscousWork.const_mul ν).sub hpressureWork).sub
    hconvectionWork).congr
  exact Filter.Eventually.of_forall (fun x =>
    (kineticEnergyDensity_timeDerivative_eq_zeroForce_work
      hsol t ht x).symm)

/-- Guarded instantaneous whole-space energy balance for a zero-force
classical solution.  This integrates the pointwise density derivative; it is
not a theorem differentiating `∫ x, kineticEnergyDensity (u t) x`, and it
contains no time integration. -/
theorem integral_kineticEnergyDensity_timeDerivative_eq_neg_viscousDissipation
    {ν : ℝ} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    (t : ℝ) (ht : 0 ≤ t)
    (hdu : Differentiable ℝ (u t))
    (hdp : Differentiable ℝ (p t))
    (hddu : ∀ j : Fin 3,
      Differentiable ℝ (coordinateDerivativeField (u t) j))
    (hpressure_flux_integrable : ∀ i : Fin 3,
      Integrable (fun x => (p t x • u t x) i) volume)
    (hpressure_flux_deriv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => (p t y • u t y) i) x
            (basisVector i)) volume)
    (hconvection_flux_integrable : ∀ i : Fin 3,
      Integrable (fun x => kineticEnergyFlux (u t) x i) volume)
    (hconvection_flux_deriv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => kineticEnergyFlux (u t) y i) x
            (basisVector i)) volume)
    (hviscous_flux_integrable : ∀ j : Fin 3,
      Integrable (fun x => viscousEnergyFlux (u t) x j) volume)
    (hviscous_flux_deriv_integrable : ∀ j : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => viscousEnergyFlux (u t) y j) x
            (basisVector j)) volume)
    (hdensity_integrable :
      Integrable (derivativeEnergyDensity (u t)) volume) :
    (∫ x : Space,
      fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1) =
      -ν * (∫ x : Space, derivativeEnergyDensity (u t) x) := by
  have hviscousWork :
      Integrable
        (fun x => ∑ i : Fin 3,
          laplacian u t x i * u t x i) volume :=
    integrable_laplacian_work_of_viscous_flux
      u t hdu hddu hviscous_flux_deriv_integrable hdensity_integrable
  have hpressureWork :
      Integrable
        (fun x => ∑ i : Fin 3,
          pressureGradient p t x i * u t x i) volume :=
    integrable_pressure_work_of_flux
      u p t ht hsol.incompressible hdu hdp
      hpressure_flux_deriv_integrable
  have hconvectionWork :
      Integrable
        (fun x => ∑ i : Fin 3,
          convection u t x i * u t x i) volume :=
    integrable_convection_work_of_flux
      u t ht hsol.incompressible hdu
      hconvection_flux_deriv_integrable
  calc
    (∫ x : Space,
      fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1) =
        ∫ x : Space,
          ((ν * (∑ i : Fin 3, laplacian u t x i * u t x i) -
            (∑ i : Fin 3, pressureGradient p t x i * u t x i)) -
            (∑ i : Fin 3, convection u t x i * u t x i)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        kineticEnergyDensity_timeDerivative_eq_zeroForce_work
          hsol t ht x)
    _ = (∫ x : Space,
          (ν * (∑ i : Fin 3, laplacian u t x i * u t x i) -
            (∑ i : Fin 3, pressureGradient p t x i * u t x i))) -
          ∫ x : Space,
            ∑ i : Fin 3, convection u t x i * u t x i :=
      MeasureTheory.integral_sub
        ((hviscousWork.const_mul ν).sub hpressureWork)
        hconvectionWork
    _ = ((∫ x : Space,
          ν * (∑ i : Fin 3, laplacian u t x i * u t x i)) -
          ∫ x : Space,
            ∑ i : Fin 3, pressureGradient p t x i * u t x i) -
          ∫ x : Space,
            ∑ i : Fin 3, convection u t x i * u t x i := by
      rw [MeasureTheory.integral_sub
        (hviscousWork.const_mul ν) hpressureWork]
    _ = (ν * (∫ x : Space,
          ∑ i : Fin 3, laplacian u t x i * u t x i) -
          ∫ x : Space,
            ∑ i : Fin 3, pressureGradient p t x i * u t x i) -
          ∫ x : Space,
            ∑ i : Fin 3, convection u t x i * u t x i := by
      rw [MeasureTheory.integral_const_mul]
    _ = -ν * (∫ x : Space,
          derivativeEnergyDensity (u t) x) := by
      rw [integral_laplacian_work_eq_neg_derivativeEnergy
        u t hdu hddu hviscous_flux_integrable
        hviscous_flux_deriv_integrable hdensity_integrable]
      rw [integral_pressure_work_eq_zero
        u p t ht hsol.incompressible hdu hdp
        hpressure_flux_integrable hpressure_flux_deriv_integrable]
      rw [integral_convection_work_eq_zero
        u t ht hsol.incompressible hdu
        hconvection_flux_integrable hconvection_flux_deriv_integrable]
      ring

end Navier.Analysis.EnergyInstantaneousIntegralBalance
