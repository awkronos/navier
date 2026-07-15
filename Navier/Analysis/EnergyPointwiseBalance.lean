import Navier.Analysis.EnergyTimeDerivative
import Navier.Analysis.EnergyConvectionCancellation
import Navier.Analysis.EnergyViscousDissipation
import Navier.Analysis.EnergyPressureCancellation

/-!
# Zero-force pointwise local energy balance

The exact project momentum equation, coordinate kinetic-energy derivative,
viscous product rule, pressure flux identity, and convection flux identity
combine into the local balance

`partial_t e + nu * |grad u|^2
  = nu * div(viscousFlux) - div(p u) - div(energyFlux)`.

All derivatives use the repository's Frechet and right-within conventions.
This file performs no spatial or time integration and proves no global energy
identity.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff

namespace Navier.Analysis.EnergyPointwiseBalance

open Navier
open Navier.Analysis.EnergyViscousDissipation

/-- Smoothness on nonnegative spacetime restricts to smoothness of every
spatial velocity slice at a nonnegative time. -/
theorem contDiff_spatialSlice_of_smoothVelocity
    (u : VelocityEvolution) (hu : SmoothVelocityOnNonnegativeTime u)
    (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (u t) := by
  have hparam : ContDiff ℝ ∞ (fun x : Space => (t, x)) := by
    fun_prop
  change ContDiff ℝ ∞
    ((fun z : ℝ × Space => u z.1 z.2) ∘ fun x : Space => (t, x))
  exact hu.comp_contDiff hparam (fun x => ⟨ht, Set.mem_univ x⟩)

/-- Smoothness on nonnegative spacetime restricts to smoothness of every
spatial pressure slice at a nonnegative time. -/
theorem contDiff_spatialSlice_of_smoothPressure
    (p : PressureEvolution) (hp : SmoothPressureOnNonnegativeTime p)
    (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (p t) := by
  have hparam : ContDiff ℝ ∞ (fun x : Space => (t, x)) := by
    fun_prop
  change ContDiff ℝ ∞
    ((fun z : ℝ × Space => p z.1 z.2) ∘ fun x : Space => (t, x))
  exact hp.comp_contDiff hparam (fun x => ⟨ht, Set.mem_univ x⟩)

/-- A smooth velocity field has differentiable first coordinate-derivative
fields.  This supplies the genuine second-spatial-derivative hypothesis used
by the pointwise viscous identity. -/
theorem differentiable_coordinateDerivativeField_of_contDiff
    (u : VelocityField) (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    Differentiable ℝ (coordinateDerivativeField u j) := by
  have hregularity : (1 : ℕ∞ω) + 1 ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
    exact WithTop.coe_le_coe.mpr le_top
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right hregularity
  have hcoordinate :
      ContDiff ℝ 1 (coordinateDerivativeField u j) := by
    unfold coordinateDerivativeField
    exact hfderiv.clm_apply contDiff_const
  exact hcoordinate.differentiable one_ne_zero

/-- Exact zero-force pointwise local energy balance under the derivative,
incompressibility, and equation hypotheses consumed by its component
identities. -/
theorem zeroForce_pointwise_energy_balance
    (ν : ℝ) (u : VelocityEvolution) (p : PressureEvolution)
    (t : ℝ) (ht : 0 ≤ t) (x : Space)
    (htime : DifferentiableWithinAt ℝ
      (fun s : ℝ => u s x) (Set.Ici 0) t)
    (hspace : DifferentiableAt ℝ (u t) x)
    (hsecond : ∀ j : Fin 3,
      DifferentiableAt ℝ (coordinateDerivativeField (u t) j) x)
    (hpressure : DifferentiableAt ℝ (p t) x)
    (hinc : Incompressible u)
    (hEquation : SatisfiesNavierStokes ν zeroForce u p) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1 +
        ν * derivativeEnergyDensity (u t) x =
      ν * staticDivergence (viscousEnergyFlux (u t)) x -
        staticDivergence (fun y => p t y • u t y) x -
        staticDivergence (kineticEnergyFlux (u t)) x := by
  have htimeWork :=
    kineticEnergyDensity_timeDerivative_eq_work
      ν zeroForce u p t ht x htime hEquation
  have hvisc :=
    laplacian_work_eq_divergence_sub_derivativeEnergy
      u t x hspace hsecond
  have hpressureWork :=
    pressure_work_eq_staticDivergence
      u p t ht x hinc hspace hpressure
  have hconvectionWork :=
    convection_work_eq_staticDivergence_of_incompressible
      u t ht x hspace hinc
  rw [htimeWork, hvisc, hpressureWork, hconvectionWork]
  simp only [zeroForce, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero]
  ring

/-- Every complete zero-force classical solution satisfies the pointwise
balance.  Its recorded spacetime smoothness genuinely supplies all time,
first-spatial, second-spatial, and pressure differentiability obligations. -/
theorem zeroForce_pointwise_energy_balance_of_classicalSolution
    {ν : ℝ} {u₀ : SchwartzVelocity}
    {u : VelocityEvolution} {p : PressureEvolution}
    (h : IsClassicalSolution ν zeroForce u₀ u p)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    fderivWithin ℝ (fun s : ℝ => kineticEnergyDensity (u s) x)
        (Set.Ici 0) t 1 +
        ν * derivativeEnergyDensity (u t) x =
      ν * staticDivergence (viscousEnergyFlux (u t)) x -
        staticDivergence (fun y => p t y • u t y) x -
        staticDivergence (kineticEnergyFlux (u t)) x := by
  have huSlice :=
    contDiff_spatialSlice_of_smoothVelocity u h.velocity_smooth t ht
  have hpSlice :=
    contDiff_spatialSlice_of_smoothPressure p h.pressure_smooth t ht
  exact zeroForce_pointwise_energy_balance ν u p t ht x
    (differentiableWithinAt_timeSlice_of_smoothVelocity
      u h.velocity_smooth t ht x)
    (huSlice.differentiable (by simp) x)
    (fun j =>
      differentiable_coordinateDerivativeField_of_contDiff
        (u t) huSlice j x)
    (hpSlice.differentiable (by simp) x)
    h.incompressible h.equation

end Navier.Analysis.EnergyPointwiseBalance
