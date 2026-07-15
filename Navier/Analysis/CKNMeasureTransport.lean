import Navier.Analysis.CKNCylinderGeometry

/-!
# Integrability transport on parabolic cylinders

The anisotropic point map `(t,x) ↦ (λ²t,λx)` is a finite-dimensional
continuous linear equivalence for nonzero `λ`.  Its pushforward changes product
Haar measure by a finite nonzero scalar.  This module uses that fact to prove
exact `IntegrableOn` equivalences on the backward cylinders from
`CKNCylinderGeometry`.

Only integrability is transported here.  The determinant scalar is kept
abstract, and no formula for the value of an integral or normalized CKN
functional is asserted.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.CKNCylinder

open Navier

/-- Explicit product Haar measure on `(time, space)`. -/
def spaceTimeVolume : Measure SpaceTime :=
  (volume : Measure ℝ).prod (volume : Measure Space)

instance : Measure.IsAddHaarMeasure spaceTimeVolume := by
  unfold spaceTimeVolume
  infer_instance

/-- Composition with positive parabolic point scaling preserves and reflects
integrability on the corresponding preimage. -/
theorem integrableOn_comp_parabolicPointMap_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (g : SpaceTime → ℝ) (s : Set SpaceTime) :
    IntegrableOn (g ∘ parabolicPointMap lambda)
        (parabolicPointMap lambda ⁻¹' s) spaceTimeVolume ↔
      IntegrableOn g s spaceTimeVolume := by
  let e := parabolicPointEquiv lambda hLambda.ne'
  let c : ENNReal :=
    ENNReal.ofReal
      |(LinearMap.det (e : SpaceTime →ₗ[ℝ] SpaceTime))⁻¹|
  have hdet :
      LinearMap.det (e : SpaceTime →ₗ[ℝ] SpaceTime) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hmap :
      Measure.map (e : SpaceTime → SpaceTime) spaceTimeVolume =
        c • spaceTimeVolume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar
      spaceTimeVolume hdet
  have hc0 : c ≠ 0 := by
    exact ne_of_gt ((ENNReal.ofReal_pos).2
      (abs_pos.mpr (inv_ne_zero hdet)))
  have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    IntegrableOn (g ∘ parabolicPointMap lambda)
        (parabolicPointMap lambda ⁻¹' s) spaceTimeVolume ↔
        IntegrableOn (g ∘ e) (e ⁻¹' s) spaceTimeVolume := by
      rfl
    _ ↔ IntegrableOn g s (Measure.map e spaceTimeVolume) :=
      (integrableOn_map_equiv
        e.toHomeomorph.toMeasurableEquiv).symm
    _ ↔ IntegrableOn g s (c • spaceTimeVolume) := by rw [hmap]
    _ ↔ IntegrableOn g s spaceTimeVolume := by
      simp only [IntegrableOn, Measure.restrict_smul]
      exact integrable_smul_measure hc0 hcTop

/-- Multiplication by a nonzero amplitude and positive parabolic point scaling
preserve and reflect integrability on corresponding backward cylinders. -/
theorem integrableOn_const_mul_comp_backwardEuclideanCylinder_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (a : ℝ) (ha : a ≠ 0)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (hr : 0 < r)
    (g : SpaceTime → ℝ) :
    IntegrableOn (fun z => a * g (parabolicPointMap lambda z))
        (backwardEuclideanCylinder t₀ x₀ r) spaceTimeVolume ↔
      IntegrableOn g
        (backwardEuclideanCylinder
          (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r))
        spaceTimeVolume := by
  calc
    IntegrableOn (fun z => a * g (parabolicPointMap lambda z))
        (backwardEuclideanCylinder t₀ x₀ r) spaceTimeVolume ↔
      IntegrableOn (g ∘ parabolicPointMap lambda)
        (backwardEuclideanCylinder t₀ x₀ r) spaceTimeVolume :=
      integrable_const_mul_iff (isUnit_iff_ne_zero.mpr ha) _
    _ ↔ IntegrableOn g
        (backwardEuclideanCylinder
          (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r))
        spaceTimeVolume := by
      rw [← parabolicPointMap_preimage_backwardEuclideanCylinder
        lambda hLambda t₀ x₀ r hr]
      exact integrableOn_comp_parabolicPointMap_iff
        lambda hLambda g _

end Navier.Analysis.CKNCylinder
