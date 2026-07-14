import Navier.Problem

/-!
# Spatial dilation covariance

This module establishes only the spatial derivative and divergence identities
needed by later covariance work.  It does not state time scaling, pressure
scaling, force scaling, or full Navier--Stokes covariance.

The Frechet-derivative identity is universal: Mathlib's
`fderiv_comp_smul` and `fderiv_const_smul_field` include the `c = 0` case and
use the standard zero value of `fderiv` at nondifferentiability points.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.Covariance

open Navier

/-- The spatial derivative of `y |-> c * u(c * y)` scales by `c^2`.

No differentiability hypothesis is needed because the two Mathlib `fderiv`
scaling identities used here are valid universally, including at `c = 0`. -/
theorem fderiv_velocity_dilation (c : ℝ) (u : Space → Space) (x : Space) :
    fderiv ℝ (fun y : Space ↦ c • u (c • y)) x =
      c ^ 2 • fderiv ℝ u (c • x) := by
  rw [show (fun y : Space ↦ c • u (c • y)) =
      c • (fun y : Space ↦ u (c • y)) by rfl]
  rw [fderiv_const_smul_field]
  simp only [Pi.smul_apply, fderiv_comp_smul, smul_smul, pow_two]

/-- Static divergence scales by `c^2` under spatial velocity dilation. -/
theorem staticDivergence_dilation (c : ℝ) (u : Space → Space) (x : Space) :
    staticDivergence (fun y : Space ↦ c • u (c • y)) x =
      c ^ 2 * staticDivergence u (c • x) := by
  simp only [staticDivergence, fderiv_velocity_dilation,
    smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]

/-- Explicit boundary-case check: at `c = 0` the dilated field is identically
zero, so both its Frechet derivative and its static divergence vanish. -/
theorem zero_dilation_truth_check (u : Space → Space) (x : Space) :
    fderiv ℝ (fun y : Space ↦ (0 : ℝ) • u ((0 : ℝ) • y)) x = 0 ∧
      staticDivergence (fun y : Space ↦ (0 : ℝ) • u ((0 : ℝ) • y)) x = 0 := by
  simp [staticDivergence]

/-- The Schwartz velocity obtained from `u0` by `y |-> c * u0(c * y)`.

For `c = 0` this is the zero Schwartz map.  For `c != 0`, composition uses the
continuous linear equivalence given by scalar multiplication by the unit `c`.
-/
def scaledSchwartzVelocity (c : ℝ) (u₀ : SchwartzVelocity) : SchwartzVelocity :=
  if hc : c = 0 then
    0
  else
    c • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc) : Space ≃L[ℝ] Space) u₀

@[simp] theorem scaledSchwartzVelocity_apply
    (c : ℝ) (u₀ : SchwartzVelocity) (x : Space) :
    scaledSchwartzVelocity c u₀ x = c • u₀ (c • x) := by
  by_cases hc : c = 0
  · subst c
    simp [scaledSchwartzVelocity]
  · simp [scaledSchwartzVelocity, hc]

/-- Divergence-free Schwartz initial data remain divergence-free under the
spatial velocity dilation, for every real `c` (hence in particular `c > 0`). -/
theorem divergenceFreeInitial_scaled (c : ℝ) (u₀ : SchwartzVelocity)
    (hu₀ : DivergenceFreeInitial u₀) :
    DivergenceFreeInitial (scaledSchwartzVelocity c u₀) := by
  intro x
  have hfun : (fun y : Space ↦ scaledSchwartzVelocity c u₀ y) =
      (fun y : Space ↦ c • u₀ (c • y)) := by
    funext y
    exact scaledSchwartzVelocity_apply c u₀ y
  rw [hfun, staticDivergence_dilation, hu₀ (c • x), mul_zero]

end Navier.Analysis.Covariance
