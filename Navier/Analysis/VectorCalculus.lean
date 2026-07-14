import Navier.Problem

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier

/-- The spatial gradient of a scalar field in the standard coordinates. -/
def staticGradient (f : PressureField) (x : Space) : Space :=
  fun i => fderiv ℝ f x (basisVector i)

/-- Coordinate divergence obeys the scalar-vector product rule. -/
theorem staticDivergence_smul
    (f : PressureField) (u : VelocityField) (x : Space)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) :
    staticDivergence (fun y => f y • u y) x =
      (∑ i, staticGradient f x i * u x i) + f x * staticDivergence u x := by
  simp only [staticDivergence, staticGradient, fderiv_fun_smul hf hu,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_comm _ _

/-- Divergence commutes with multiplication by a constant scalar. -/
theorem staticDivergence_const_smul
    (c : ℝ) (u : VelocityField) (x : Space)
    (hu : DifferentiableAt ℝ u x) :
    staticDivergence (fun y => c • u y) x = c * staticDivergence u x := by
  simpa only [staticGradient, fderiv_const_apply, zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add] using
    (staticDivergence_smul (fun _ : Space => c) u x
      (differentiableAt_const c) hu)

/-- The convective derivative is the coordinate-weighted sum of directional
derivatives along the standard basis. -/
theorem convection_eq_sum_coordinate_derivatives
    (u : VelocityEvolution) (t : ℝ) (x : Space) :
    convection u t x =
      ∑ i, (u t x i) • spatialDerivative u t x (basisVector i) := by
  rw [convection]
  have hbasis : u t x = ∑ i, (u t x i) • basisVector i := by
    simpa only [basisVector] using (pi_eq_sum_univ' (u t x))
  calc
    spatialDerivative u t x (u t x) =
        spatialDerivative u t x (∑ i, (u t x i) • basisVector i) :=
      congrArg (spatialDerivative u t x) hbasis
    _ = ∑ i, (u t x i) • spatialDerivative u t x (basisVector i) := by
      simp only [map_sum, map_smul]

end Navier
