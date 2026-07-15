import Navier.Analysis.Vorticity

/-!
# Backward Euclidean cylinders under parabolic dilation

This module defines the literal backward cylinders used by the
Caffarelli--Kohn--Nirenberg local theory, using the official Euclidean norm on
`Navier.Space`.  It proves exact image and preimage identities for positive
parabolic dilations.

These are finite-dimensional geometry statements.  They do not provide a
suitable weak solution, a local energy inequality, or an epsilon-regularity
theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CKNCylinder

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

/-- Spacetime points are ordered as `(time, space)`. -/
abbrev SpaceTime := ℝ × Space

/-- The point map `(t,x) ↦ (λ²t,λx)` underlying parabolic scaling. -/
def parabolicPointMap (lambda : ℝ) (z : SpaceTime) : SpaceTime :=
  (lambda ^ 2 * z.1, lambda • z.2)

/-- For nonzero `λ`, parabolic point scaling is a continuous linear
equivalence. -/
def parabolicPointEquiv (lambda : ℝ) (hLambda : lambda ≠ 0) :
    SpaceTime ≃L[ℝ] SpaceTime :=
  (ContinuousLinearEquiv.smulLeft
      (Units.mk0 (lambda ^ 2) (pow_ne_zero 2 hLambda)) :
      ℝ ≃L[ℝ] ℝ).prodCongr
    (ContinuousLinearEquiv.smulLeft (Units.mk0 lambda hLambda) :
      Space ≃L[ℝ] Space)

@[simp] theorem parabolicPointEquiv_apply
    (lambda : ℝ) (hLambda : lambda ≠ 0) (z : SpaceTime) :
    parabolicPointEquiv lambda hLambda z = parabolicPointMap lambda z := by
  rfl

/-- The backward cylinder `B_r(x₀) × (t₀-r²,t₀)`, with the spatial
ball measured using the official Euclidean norm. -/
def backwardEuclideanCylinder
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) : Set SpaceTime :=
  {z | t₀ - r ^ 2 < z.1 ∧ z.1 < t₀ ∧
    officialEuclideanNorm (z.2 - x₀) < r}

/-- A positive parabolic dilation has the expected exact cylinder preimage. -/
theorem parabolicPointMap_preimage_backwardEuclideanCylinder
    (lambda : ℝ) (hLambda : 0 < lambda)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (_hr : 0 < r) :
    parabolicPointMap lambda ⁻¹'
        backwardEuclideanCylinder
          (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r) =
      backwardEuclideanCylinder t₀ x₀ r := by
  ext z
  change
    (lambda ^ 2 * t₀ - (lambda * r) ^ 2 <
          lambda ^ 2 * z.1 ∧
        lambda ^ 2 * z.1 < lambda ^ 2 * t₀ ∧
        officialEuclideanNorm (lambda • z.2 - lambda • x₀) <
          lambda * r) ↔
      (t₀ - r ^ 2 < z.1 ∧ z.1 < t₀ ∧
        officialEuclideanNorm (z.2 - x₀) < r)
  have hsq : 0 < lambda ^ 2 := sq_pos_of_pos hLambda
  have hnorm :
      officialEuclideanNorm (lambda • z.2 - lambda • x₀) =
        lambda * officialEuclideanNorm (z.2 - x₀) := by
    rw [← smul_sub, officialEuclideanNorm_smul, abs_of_pos hLambda]
  rw [hnorm]
  constructor
  · rintro ⟨htLower, htUpper, hx⟩
    constructor
    · nlinarith
    constructor <;> nlinarith
  · rintro ⟨htLower, htUpper, hx⟩
    constructor
    · nlinarith
    constructor <;> nlinarith

/-- Nonzero parabolic point scaling is onto. -/
theorem parabolicPointMap_surjective
    (lambda : ℝ) (hLambda : lambda ≠ 0) :
    Function.Surjective (parabolicPointMap lambda) := by
  intro z
  refine ⟨(z.1 / lambda ^ 2, lambda⁻¹ • z.2), ?_⟩
  apply Prod.ext
  · dsimp [parabolicPointMap]
    field_simp
  · dsimp [parabolicPointMap]
    rw [smul_smul, mul_inv_cancel₀ hLambda, one_smul]

/-- A positive parabolic dilation maps a backward cylinder exactly onto the
correspondingly dilated cylinder. -/
theorem parabolicPointMap_image_backwardEuclideanCylinder
    (lambda : ℝ) (hLambda : 0 < lambda)
    (t₀ : ℝ) (x₀ : Space) (r : ℝ) (hr : 0 < r) :
    parabolicPointMap lambda ''
        backwardEuclideanCylinder t₀ x₀ r =
      backwardEuclideanCylinder
        (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hmem :
        y ∈ parabolicPointMap lambda ⁻¹'
          backwardEuclideanCylinder
            (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r) := by
      rw [parabolicPointMap_preimage_backwardEuclideanCylinder
        lambda hLambda t₀ x₀ r hr]
      exact hy
    exact hmem
  · intro hz
    obtain ⟨y, rfl⟩ :=
      parabolicPointMap_surjective lambda hLambda.ne' z
    refine ⟨y, ?_, rfl⟩
    have hmem :
        y ∈ parabolicPointMap lambda ⁻¹'
          backwardEuclideanCylinder
            (lambda ^ 2 * t₀) (lambda • x₀) (lambda * r) := hz
    rw [parabolicPointMap_preimage_backwardEuclideanCylinder
      lambda hLambda t₀ x₀ r hr] at hmem
    exact hmem

end Navier.Analysis.CKNCylinder
