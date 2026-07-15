import Navier.Analysis.VectorCalculus
import Navier.Analysis.EnergyConvectionCancellation

/-!
# Pointwise viscous dissipation identity

For a velocity slice with the stated first- and second-differentiability
hypotheses, componentwise Laplacian work is the divergence of the viscous
energy flux minus the squared coordinate-derivative density:

`sum_i (Delta u)_i u_i = div(sum_i (partial_j u_i) u_i)_j
  - sum_{j,i} (partial_j u_i)^2`.

This is a pointwise product-rule identity in the repository's exact Frechet
derivative and Laplacian conventions.  It takes no spatial integral and hides
no boundary argument.  Any whole-space consequence still requires explicit
integrability of the flux, its divergence, and the derivative-energy density,
together with a justified removal of the boundary flux.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Analysis.EnergyViscousDissipation

open Navier

/-- The first spatial derivative field in coordinate direction `j`. -/
def coordinateDerivativeField
    (u : VelocityField) (j : Fin 3) : VelocityField :=
  fun x => fderiv ℝ u x (basisVector j)

/-- The pointwise sum of squares of all coordinate derivatives of a velocity
field. -/
def derivativeEnergyDensity (u : VelocityField) (x : Space) : ℝ :=
  ∑ j : Fin 3, ∑ i : Fin 3,
    (coordinateDerivativeField u j x i) ^ 2

/-- The coordinate viscous-energy flux with `j`th component
`sum_i (partial_j u_i) u_i`. -/
def viscousEnergyFlux (u : VelocityField) (x : Space) : Space :=
  fun j => ∑ i : Fin 3,
    coordinateDerivativeField u j x i * u x i

/-- The coordinate derivative-energy density is pointwise nonnegative. -/
theorem derivativeEnergyDensity_nonneg (u : VelocityField) (x : Space) :
    0 ≤ derivativeEnergyDensity u x := by
  apply Finset.sum_nonneg
  intro j _
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The viscous flux is differentiable at a point when the velocity and every
first coordinate-derivative field are differentiable there. -/
theorem differentiableAt_viscousEnergyFlux
    (u : VelocityField) (x : Space)
    (hu : DifferentiableAt ℝ u x)
    (hdu : ∀ j : Fin 3,
      DifferentiableAt ℝ (coordinateDerivativeField u j) x) :
    DifferentiableAt ℝ (viscousEnergyFlux u) x := by
  rw [differentiableAt_pi]
  intro j
  apply DifferentiableAt.fun_sum
  intro i _
  exact (differentiableAt_pi.1 (hdu j) i).mul
    (differentiableAt_pi.1 hu i)

/-- Coordinate product rule for one component of the viscous flux. -/
theorem fderiv_viscousEnergyFlux_component
    (u : VelocityField) (x : Space) (j : Fin 3)
    (hu : DifferentiableAt ℝ u x)
    (hdu : DifferentiableAt ℝ (coordinateDerivativeField u j) x) :
    fderiv ℝ (fun y => viscousEnergyFlux u y j) x (basisVector j) =
      ∑ i : Fin 3,
        ((fderiv ℝ (coordinateDerivativeField u j) x
            (basisVector j)) i * u x i +
          (coordinateDerivativeField u j x i) ^ 2) := by
  have hfirst (i : Fin 3) :
      DifferentiableAt ℝ
        (fun y => coordinateDerivativeField u j y i) x :=
    differentiableAt_pi.1 hdu i
  have hcoord (i : Fin 3) :
      DifferentiableAt ℝ (fun y => u y i) x :=
    differentiableAt_pi.1 hu i
  change fderiv ℝ
      (fun y => ∑ i : Fin 3,
        coordinateDerivativeField u j y i * u y i)
      x (basisVector j) = _
  rw [fderiv_fun_sum]
  · simp only [sum_apply,
      fderiv_fun_mul (hfirst _) (hcoord _), add_apply, smul_apply,
      fderiv_apply hdu, fderiv_apply hu,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [coordinateDerivativeField]
    ring
  · intro i _
    exact (hfirst i).mul (hcoord i)

/-- Divergence of the viscous flux is second-derivative work plus the
derivative-energy density, before any rearrangement or integration. -/
theorem staticDivergence_viscousEnergyFlux
    (u : VelocityField) (x : Space)
    (hu : DifferentiableAt ℝ u x)
    (hdu : ∀ j : Fin 3,
      DifferentiableAt ℝ (coordinateDerivativeField u j) x) :
    staticDivergence (viscousEnergyFlux u) x =
      ∑ j : Fin 3, ∑ i : Fin 3,
        ((fderiv ℝ (coordinateDerivativeField u j) x
            (basisVector j)) i * u x i +
          (coordinateDerivativeField u j x i) ^ 2) := by
  have hflux := differentiableAt_viscousEnergyFlux u x hu hdu
  unfold staticDivergence
  apply Finset.sum_congr rfl
  intro j _
  have hcomponent :
      fderiv ℝ (viscousEnergyFlux u) x (basisVector j) j =
        fderiv ℝ (fun y => viscousEnergyFlux u y j) x
          (basisVector j) := by
    rw [fderiv_apply hflux j]
    rfl
  rw [hcomponent]
  exact fderiv_viscousEnergyFlux_component u x j hu (hdu j)

/-- The repository Laplacian work is exactly the sum of pure coordinate
second derivatives paired with the velocity. -/
theorem laplacian_work_eq_secondDerivative_sum
    (u : VelocityEvolution) (t : ℝ) (x : Space) :
    (∑ i : Fin 3, laplacian u t x i * u t x i) =
      ∑ j : Fin 3, ∑ i : Fin 3,
        (fderiv ℝ (coordinateDerivativeField (u t) j) x
          (basisVector j)) i * u t x i := by
  simp only [laplacian, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/-- Pointwise viscous integration by parts in coordinates.  Every required
first/second differentiability assumption is explicit; there is no integral
or boundary cancellation in this statement. -/
theorem laplacian_work_eq_divergence_sub_derivativeEnergy
    (u : VelocityEvolution) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (u t) x)
    (hdu : ∀ j : Fin 3,
      DifferentiableAt ℝ (coordinateDerivativeField (u t) j) x) :
    (∑ i : Fin 3, laplacian u t x i * u t x i) =
      staticDivergence (viscousEnergyFlux (u t)) x -
        derivativeEnergyDensity (u t) x := by
  rw [laplacian_work_eq_secondDerivative_sum]
  rw [staticDivergence_viscousEnergyFlux (u t) x hu hdu]
  simp only [derivativeEnergyDensity, Finset.sum_add_distrib]
  ring

/-- Equivalent additive form of the pointwise viscous identity. -/
theorem laplacian_work_add_derivativeEnergy_eq_divergence
    (u : VelocityEvolution) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (u t) x)
    (hdu : ∀ j : Fin 3,
      DifferentiableAt ℝ (coordinateDerivativeField (u t) j) x) :
    (∑ i : Fin 3, laplacian u t x i * u t x i) +
        derivativeEnergyDensity (u t) x =
      staticDivergence (viscousEnergyFlux (u t)) x := by
  rw [laplacian_work_eq_divergence_sub_derivativeEnergy u t x hu hdu]
  ring

end Navier.Analysis.EnergyViscousDissipation
