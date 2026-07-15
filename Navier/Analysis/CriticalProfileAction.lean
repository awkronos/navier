import Navier.Analysis.CriticalLp
import Mathlib.MeasureTheory.Group.Measure

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

open MeasureTheory
open scoped ENNReal

namespace Navier.Analysis.CriticalProfileAction

open Navier
open Navier.Analysis.CriticalLp

/-- Pure spatial translation of a profile. -/
def criticalProfileTranslate
    (y : Space) (f : Space → Space) : Space → Space :=
  fun x => f (x - y)

/-- Translate the profile center to `center`, dilate space by `lambda`, and
apply the critical velocity amplitude `lambda`. -/
def criticalProfileAction
    (lambda : ℝ) (center : Space) (f : Space → Space) : Space → Space :=
  fun x => lambda • f (lambda • (x - center))

/-- The affine profile action is critical scaling after translating by the
scaled center. -/
theorem criticalProfileAction_eq_scale_translate
    (lambda : ℝ) (center : Space) (f : Space → Space) :
    criticalProfileAction lambda center f =
      criticalL3SpatialScale lambda
        (criticalProfileTranslate (lambda • center) f) := by
  funext x
  simp [criticalProfileAction, criticalL3SpatialScale,
    criticalProfileTranslate, smul_sub]

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

/-- Translation preserves genuine `MemLp` membership for every exponent. -/
theorem memLp_criticalProfileTranslate_iff
    (p : ℝ≥0∞) (y : Space) (f : Space → Space) :
    MemLp (criticalProfileTranslate y f) p volume ↔
      MemLp f p volume := by
  constructor
  · intro htranslated
    have hcomp :=
      htranslated.comp_measurePreserving
        (measurePreserving_add_right volume y)
    have heq :
        criticalProfileTranslate y f ∘ (fun x : Space => x + y) = f := by
      funext x
      simp [criticalProfileTranslate]
    rw [heq] at hcomp
    exact hcomp
  · intro hf
    have hcomp :=
      hf.comp_measurePreserving
        (measurePreserving_add_right volume (-y))
    have heq :
        f ∘ (fun x : Space => x + (-y)) =
          criticalProfileTranslate y f := by
      funext x
      simp [criticalProfileTranslate, sub_eq_add_neg]
    rw [heq] at hcomp
    exact hcomp

/-- Translation preserves the extended `Lp` seminorm of an a.e. strongly
measurable profile. -/
theorem eLpNorm_criticalProfileTranslate
    (p : ℝ≥0∞) (y : Space) (f : Space → Space)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (criticalProfileTranslate y f) p volume =
      eLpNorm f p volume := by
  have hcomp :=
    eLpNorm_comp_measurePreserving (p := p) hf
      (measurePreserving_add_right volume (-y))
  have heq :
      f ∘ (fun x : Space => x + (-y)) =
        criticalProfileTranslate y f := by
    funext x
    simp [criticalProfileTranslate, sub_eq_add_neg]
  rw [heq] at hcomp
  exact hcomp

/-- Positive critical profile actions preserve `L^3` membership. -/
theorem memLp_three_criticalProfileAction_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (center : Space) (f : Space → Space) :
    MemLp (criticalProfileAction lambda center f) 3 volume ↔
      MemLp f 3 volume := by
  rw [criticalProfileAction_eq_scale_translate]
  rw [memLp_three_criticalL3SpatialScale_iff lambda hLambda]
  exact memLp_criticalProfileTranslate_iff 3 (lambda • center) f

/-- Positive critical profile actions preserve the exact extended `L^3`
seminorm for genuine `MemLp` profiles. -/
theorem eLpNorm_three_criticalProfileAction
    (lambda : ℝ) (hLambda : 0 < lambda)
    (center : Space) (f : Space → Space)
    (hf : MemLp f 3 volume) :
    eLpNorm (criticalProfileAction lambda center f) 3 volume =
      eLpNorm f 3 volume := by
  have htranslated :
      MemLp (criticalProfileTranslate (lambda • center) f) 3 volume :=
    (memLp_criticalProfileTranslate_iff 3 (lambda • center) f).mpr hf
  calc
    eLpNorm (criticalProfileAction lambda center f) 3 volume =
        eLpNorm (criticalProfileTranslate (lambda • center) f) 3 volume := by
      rw [criticalProfileAction_eq_scale_translate]
      exact eLpNorm_three_criticalL3SpatialScale
        lambda hLambda (criticalProfileTranslate (lambda • center) f)
          htranslated
    _ = eLpNorm f 3 volume :=
      eLpNorm_criticalProfileTranslate 3 (lambda • center) f hf.1

end Navier.Analysis.CriticalProfileAction
