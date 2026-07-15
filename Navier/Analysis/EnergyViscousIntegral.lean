import Navier.Analysis.EnergyViscousDissipation
import Navier.Analysis.EnergyPressureIntegral

/-!
# Whole-space viscous dissipation under explicit flux hypotheses

This file upgrades the pointwise identity

`sum_i (Delta u)_i u_i = div(viscousEnergyFlux u)
  - derivativeEnergyDensity u`

to an identity of whole-space integrals.  Boundary removal is supplied by the
existing coordinatewise divergence theorem: every component of the viscous
flux and its matching coordinate derivative must be integrable.  These
hypotheses are intentionally explicit; they are not claimed to follow from the
repository's official classical-solution class.

The divergence is proved integrable from its coordinate-derivative hypotheses,
and Laplacian work is then proved integrable from the pointwise identity and
integrability of the nonnegative derivative-energy density.  No full kinetic
energy identity is asserted here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.EnergyViscousIntegral

open Navier
open EnergyViscousDissipation
open EnergyPressureIntegral

/-- The viscous energy flux is globally differentiable when the velocity and
all of its coordinate-derivative fields are globally differentiable. -/
theorem differentiable_viscousEnergyFlux
    (u : VelocityField)
    (hu : Differentiable ℝ u)
    (hdu : ∀ j : Fin 3,
      Differentiable ℝ (coordinateDerivativeField u j)) :
    Differentiable ℝ (viscousEnergyFlux u) := by
  intro x
  exact differentiableAt_viscousEnergyFlux u x (hu x)
    (fun j => hdu j x)

/-- Coordinatewise integrability of the matching scalar derivatives implies
integrability of the vector field's static divergence.  Thus callers need not
postulate divergence integrability separately. -/
theorem integrable_staticDivergence_of_coordinatewise
    (F : VelocityField)
    (hF : Differentiable ℝ F)
    (hderiv_integrable : ∀ i : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => F y i) x (basisVector i)) volume) :
    Integrable (fun x => staticDivergence F x) volume := by
  have hcoord (i : Fin 3) (x : Space) :
      fderiv ℝ F x (basisVector i) i =
        fderiv ℝ (fun y => F y i) x (basisVector i) := by
    rw [fderiv_apply (hF x) i]
    rfl
  simp only [staticDivergence, hcoord]
  exact MeasureTheory.integrable_finsetSum Finset.univ
    (fun i _ => hderiv_integrable i)

/-- Under the differentiability and integrability assumptions used by viscous
integration by parts, Laplacian work is integrable.  This is derived rather
than added as an independent hypothesis. -/
theorem integrable_laplacian_work_of_viscous_flux
    (u : VelocityEvolution) (t : ℝ)
    (hu : Differentiable ℝ (u t))
    (hdu : ∀ j : Fin 3,
      Differentiable ℝ (coordinateDerivativeField (u t) j))
    (hflux_deriv_integrable : ∀ j : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => viscousEnergyFlux (u t) y j) x
            (basisVector j)) volume)
    (hdensity_integrable :
      Integrable (derivativeEnergyDensity (u t)) volume) :
    Integrable
      (fun x => ∑ i : Fin 3, laplacian u t x i * u t x i) volume := by
  have hfluxDiff : Differentiable ℝ (viscousEnergyFlux (u t)) :=
    differentiable_viscousEnergyFlux (u t) hu hdu
  have hdiv_integrable :
      Integrable
        (fun x => staticDivergence (viscousEnergyFlux (u t)) x) volume :=
    integrable_staticDivergence_of_coordinatewise
      (viscousEnergyFlux (u t)) hfluxDiff hflux_deriv_integrable
  apply (hdiv_integrable.sub hdensity_integrable).congr
  exact Filter.Eventually.of_forall (fun x =>
    (laplacian_work_eq_divergence_sub_derivativeEnergy
      u t x (hu x) (fun j => hdu j x)).symm)

/-- Whole-space viscous integration by parts.  The integral of Laplacian work
is minus the integral of the pointwise nonnegative derivative-energy density.
The component and derivative integrability assumptions on `viscousEnergyFlux`
are the explicit boundary-removal guard; no decay is inferred from the
official solution class. -/
theorem integral_laplacian_work_eq_neg_derivativeEnergy
    (u : VelocityEvolution) (t : ℝ)
    (hu : Differentiable ℝ (u t))
    (hdu : ∀ j : Fin 3,
      Differentiable ℝ (coordinateDerivativeField (u t) j))
    (hflux_integrable : ∀ j : Fin 3,
      Integrable (fun x => viscousEnergyFlux (u t) x j) volume)
    (hflux_deriv_integrable : ∀ j : Fin 3,
      Integrable
        (fun x =>
          fderiv ℝ (fun y => viscousEnergyFlux (u t) y j) x
            (basisVector j)) volume)
    (hdensity_integrable :
      Integrable (derivativeEnergyDensity (u t)) volume) :
    (∫ x : Space,
        ∑ i : Fin 3, laplacian u t x i * u t x i) =
      -(∫ x : Space, derivativeEnergyDensity (u t) x) := by
  have hfluxDiff : Differentiable ℝ (viscousEnergyFlux (u t)) :=
    differentiable_viscousEnergyFlux (u t) hu hdu
  have hdiv_integrable :
      Integrable
        (fun x => staticDivergence (viscousEnergyFlux (u t)) x) volume :=
    integrable_staticDivergence_of_coordinatewise
      (viscousEnergyFlux (u t)) hfluxDiff hflux_deriv_integrable
  calc
    (∫ x : Space,
        ∑ i : Fin 3, laplacian u t x i * u t x i) =
        ∫ x : Space,
          (staticDivergence (viscousEnergyFlux (u t)) x -
            derivativeEnergyDensity (u t) x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        laplacian_work_eq_divergence_sub_derivativeEnergy
          u t x (hu x) (fun j => hdu j x))
    _ = (∫ x : Space, staticDivergence (viscousEnergyFlux (u t)) x) -
          ∫ x : Space, derivativeEnergyDensity (u t) x :=
      MeasureTheory.integral_sub hdiv_integrable hdensity_integrable
    _ = 0 - ∫ x : Space, derivativeEnergyDensity (u t) x := by
      rw [integral_staticDivergence_eq_zero
        (viscousEnergyFlux (u t)) hfluxDiff
        hflux_integrable hflux_deriv_integrable]
    _ = -(∫ x : Space, derivativeEnergyDensity (u t) x) :=
      zero_sub _

end Navier.Analysis.EnergyViscousIntegral
