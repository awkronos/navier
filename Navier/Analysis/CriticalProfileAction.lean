import Navier.Problem

/-!
# Translation-dilation action for critical profiles

Critical profile decompositions quotient loss of compactness by spatial
translations and Navier--Stokes dilations.  This file defines that exact
finite-dimensional action and proves its composition and inverse laws.

It does not extract profiles, prove weak convergence or norm decoupling,
construct an ancient solution, or supply a rigidity contradiction.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalProfileAction

open Navier

/-- Translate the profile center to `center`, dilate space by `lambda`, and
apply the critical velocity amplitude `lambda`. -/
def criticalProfileAction
    (lambda : ℝ) (center : Space) (f : Space → Space) : Space → Space :=
  fun x => lambda • f (lambda • (x - center))

/-- Unit scale and zero center act as the identity. -/
theorem criticalProfileAction_one_zero (f : Space → Space) :
    criticalProfileAction 1 0 f = f := by
  funext x
  simp [criticalProfileAction]

/-- Exact affine composition law for positive or negative nonzero outer
scale. -/
theorem criticalProfileAction_comp
    (lambda mu : ℝ) (center shift : Space) (f : Space → Space)
    (hLambda : lambda ≠ 0) :
    criticalProfileAction lambda center
        (criticalProfileAction mu shift f) =
      criticalProfileAction (lambda * mu)
        (center + lambda⁻¹ • shift) f := by
  funext x
  change
    lambda • (mu • f (mu • (lambda • (x - center) - shift))) =
      (lambda * mu) •
        f ((lambda * mu) • (x - (center + lambda⁻¹ • shift)))
  rw [smul_smul]
  congr 1
  apply congrArg f
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  field_simp [hLambda]
  ring

/-- The displayed reciprocal action is a left inverse. -/
theorem criticalProfileAction_inverse_left
    (lambda : ℝ) (center : Space) (f : Space → Space)
    (hLambda : lambda ≠ 0) :
    criticalProfileAction lambda⁻¹ (-lambda • center)
        (criticalProfileAction lambda center f) = f := by
  calc
    criticalProfileAction lambda⁻¹ (-lambda • center)
        (criticalProfileAction lambda center f) =
      criticalProfileAction (lambda⁻¹ * lambda)
        (-lambda • center + (lambda⁻¹)⁻¹ • center) f :=
      criticalProfileAction_comp lambda⁻¹ lambda
        (-lambda • center) center f (inv_ne_zero hLambda)
    _ = criticalProfileAction 1 0 f := by
      simp [hLambda]
    _ = f := criticalProfileAction_one_zero f

/-- The displayed reciprocal action is also a right inverse. -/
theorem criticalProfileAction_inverse_right
    (lambda : ℝ) (center : Space) (f : Space → Space)
    (hLambda : lambda ≠ 0) :
    criticalProfileAction lambda center
        (criticalProfileAction lambda⁻¹ (-lambda • center) f) = f := by
  calc
    criticalProfileAction lambda center
        (criticalProfileAction lambda⁻¹ (-lambda • center) f) =
      criticalProfileAction (lambda * lambda⁻¹)
        (center + lambda⁻¹ • (-lambda • center)) f :=
      criticalProfileAction_comp lambda lambda⁻¹ center
        (-lambda • center) f hLambda
    _ = criticalProfileAction 1 0 f := by
      simp [hLambda, smul_smul]
    _ = f := criticalProfileAction_one_zero f

/-- Conjugating one profile frame by another exposes the exact relative scale
and center used by parameter-orthogonality statements. -/
theorem criticalProfileAction_relative
    (lambda mu : ℝ) (center shift : Space) (f : Space → Space)
    (hLambda : lambda ≠ 0) :
    criticalProfileAction lambda⁻¹ (-lambda • center)
        (criticalProfileAction mu shift f) =
      criticalProfileAction (lambda⁻¹ * mu)
        (lambda • (shift - center)) f := by
  calc
    criticalProfileAction lambda⁻¹ (-lambda • center)
        (criticalProfileAction mu shift f) =
      criticalProfileAction (lambda⁻¹ * mu)
        (-lambda • center + (lambda⁻¹)⁻¹ • shift) f :=
      criticalProfileAction_comp lambda⁻¹ mu
        (-lambda • center) shift f (inv_ne_zero hLambda)
    _ = criticalProfileAction (lambda⁻¹ * mu)
        (lambda • (shift - center)) f := by
      congr 1
      ext i
      change
        -lambda * center i + (lambda⁻¹)⁻¹ * shift i =
          lambda * (shift i - center i)
      rw [inv_inv]
      ring

end Navier.Analysis.CriticalProfileAction
