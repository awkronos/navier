import Navier.Analysis.VectorCalculus

/-!
# Pointwise convection-work cancellation

For a differentiable incompressible velocity field, the convective work
density is exactly the divergence of its kinetic-energy flux.  This is a
pointwise finite-dimensional identity.  No spatial integral, decay argument,
or boundary limit is asserted here.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier

/-- The pointwise kinetic-energy density `|u|^2 / 2` in coordinates. -/
def kineticEnergyDensity (u : VelocityField) (x : Space) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, u x i * u x i

/-- The spatial kinetic-energy flux. -/
def kineticEnergyFlux (u : VelocityField) (x : Space) : Space :=
  kineticEnergyDensity u x • u x

/-- Kinetic-energy density is differentiable wherever the velocity is. -/
theorem differentiableAt_kineticEnergyDensity
    (u : VelocityField) (x : Space) (hu : DifferentiableAt ℝ u x) :
    DifferentiableAt ℝ (kineticEnergyDensity u) x := by
  unfold kineticEnergyDensity
  apply DifferentiableAt.const_mul
  exact DifferentiableAt.fun_sum fun i _ =>
    ((differentiableAt_pi.1 hu i).mul (differentiableAt_pi.1 hu i))

/-- The Frechet derivative of kinetic-energy density is `u` paired with the
directional derivative of `u`. -/
theorem fderiv_kineticEnergyDensity
    (u : VelocityField) (x v : Space) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (kineticEnergyDensity u) x v =
      ∑ i, u x i * (fderiv ℝ u x v) i := by
  have hcoord : ∀ i : Fin 3,
      DifferentiableAt ℝ (fun y => u y i) x :=
    fun i => differentiableAt_pi.1 hu i
  have hsum : DifferentiableAt ℝ (fun y => ∑ i, u y i * u y i) x :=
    DifferentiableAt.fun_sum fun i _ => (hcoord i).mul (hcoord i)
  change fderiv ℝ (fun y => (1 / 2 : ℝ) * ∑ i, u y i * u y i) x v =
    ∑ i, u x i * (fderiv ℝ u x v) i
  rw [fderiv_const_mul hsum (1 / 2 : ℝ)]
  simp only [smul_apply, smul_eq_mul]
  rw [fderiv_fun_sum]
  · simp only [sum_apply,
      fderiv_fun_mul (hcoord _) (hcoord _), add_apply, smul_apply,
      fderiv_apply hu, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    rw [Finset.sum_add_distrib]
    ring_nf
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact (hcoord i).mul (hcoord i)

/-- Coordinate formula for the gradient of kinetic-energy density. -/
theorem staticGradient_kineticEnergyDensity
    (u : VelocityField) (x : Space) (hu : DifferentiableAt ℝ u x)
    (j : Fin 3) :
    staticGradient (kineticEnergyDensity u) x j =
      ∑ i, u x i * (fderiv ℝ u x (basisVector j)) i := by
  simpa only [staticGradient] using
    fderiv_kineticEnergyDensity u x (basisVector j) hu

/-- Pointwise convective work is the divergence of kinetic-energy flux when
the velocity is differentiable and divergence-free at the point. -/
theorem convection_work_eq_staticDivergence
    (u : VelocityEvolution) (t : ℝ) (x : Space)
    (hu : DifferentiableAt ℝ (u t) x)
    (hdiv : staticDivergence (u t) x = 0) :
    (∑ j, convection u t x j * u t x j) =
      staticDivergence (kineticEnergyFlux (u t)) x := by
  change (∑ j, convection u t x j * u t x j) =
    staticDivergence
      (fun y => kineticEnergyDensity (u t) y • u t y) x
  rw [staticDivergence_smul
    (kineticEnergyDensity (u t)) (u t) x
    (differentiableAt_kineticEnergyDensity (u t) x hu) hu]
  rw [hdiv, mul_zero, add_zero]
  rw [convection_eq_sum_coordinate_derivatives]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    spatialDerivative,
    staticGradient_kineticEnergyDensity (u t) x hu, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The pointwise convection cancellation specialized to an incompressible
velocity evolution at nonnegative time. -/
theorem convection_work_eq_staticDivergence_of_incompressible
    (u : VelocityEvolution) (t : ℝ) (ht : 0 ≤ t) (x : Space)
    (hu : DifferentiableAt ℝ (u t) x)
    (hinc : Incompressible u) :
    (∑ j, convection u t x j * u t x j) =
      staticDivergence (kineticEnergyFlux (u t)) x := by
  apply convection_work_eq_staticDivergence u t x hu
  simpa only [divergence, spatialDerivative, staticDivergence] using
    hinc t ht x

end Navier
