import Navier.Analysis.BiotSavartKernel
import Navier.Analysis.CZNearField
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The shrinking Biot--Savart puncture

This file parameterizes the oriented boundary of a ball by spherical angles
and proves that its Biot--Savart flux converges to the local distributional
coefficient `(1/3) δᵢⱼ`.  It is the boundary term needed when the punctured
integration-by-parts identity is closed at the origin.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Interval

namespace Navier.Analysis.BiotSavartPuncture

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding

/-- Standard spherical parameterization of the unit sphere. -/
def unitSphereParam (θ ϕ : ℝ) : Space :=
  fun k => if k = 0 then Real.sin θ * Real.cos ϕ
    else if k = 1 then Real.sin θ * Real.sin ϕ
    else Real.cos θ

@[simp] theorem unitSphereParam_zero (θ ϕ : ℝ) :
    unitSphereParam θ ϕ 0 = Real.sin θ * Real.cos ϕ := rfl

@[simp] theorem unitSphereParam_one (θ ϕ : ℝ) :
    unitSphereParam θ ϕ 1 = Real.sin θ * Real.sin ϕ := rfl

@[simp] theorem unitSphereParam_two (θ ϕ : ℝ) :
    unitSphereParam θ ϕ 2 = Real.cos θ := rfl

/-- Product angular measure `dθ dϕ` on the standard spherical chart.
The surface Jacobian `sin θ` is included in `punctureAngularDensity`. -/
def sphereAngularMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Ioc 0 Real.pi)).prod
    (volume.restrict (Set.Ioc 0 (2 * Real.pi)))

/-- The `i,j` boundary-flux density after the powers of the radius cancel. -/
def punctureAngularDensity (i j : Fin 3) (p : ℝ × ℝ) : ℝ :=
  (1 / (4 * Real.pi)) * unitSphereParam p.1 p.2 i *
    unitSphereParam p.1 p.2 j * Real.sin p.1

/-- Boundary flux of the vector kernel against `φ` on the sphere of radius
`ε`, written in spherical coordinates. -/
def punctureBoundary (ε : ℝ) (i j : Fin 3) (φ : Space → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, punctureAngularDensity i j p *
    φ (ε • unitSphereParam p.1 p.2) ∂sphereAngularMeasure

private theorem integral_sin_zero_pi :
    (∫ x : ℝ in (0 : ℝ)..Real.pi, Real.sin x) = 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := -Real.cos) (f' := Real.sin)
    (fun x _ => by simpa only [neg_neg] using (Real.hasDerivAt_cos x).neg)
    (Real.continuous_sin.intervalIntegrable 0 Real.pi)
  rw [h]
  norm_num

private theorem integral_cos_zero_twoPi :
    (∫ x : ℝ in (0 : ℝ)..2 * Real.pi, Real.cos x) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := Real.sin) (f' := Real.cos)
    (fun x _ => Real.hasDerivAt_sin x)
    (Real.continuous_cos.intervalIntegrable 0 (2 * Real.pi))
  simpa using h

private theorem integral_sin_zero_twoPi :
    (∫ x : ℝ in (0 : ℝ)..2 * Real.pi, Real.sin x) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := -Real.cos) (f' := Real.sin)
    (fun x _ => by simpa only [neg_neg] using (Real.hasDerivAt_cos x).neg)
    (Real.continuous_sin.intervalIntegrable 0 (2 * Real.pi))
  simpa using h

private theorem integral_sin_mul_cos_sq_zero_pi :
    (∫ x : ℝ in (0 : ℝ)..Real.pi,
      Real.sin x * Real.cos x ^ 2) = 2 / 3 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => (-(1 / 3 : ℝ)) * (Real.cos ^ 3) y)
        (Real.sin x * Real.cos x ^ 2) x := by
    intro x
    have hd := ((Real.hasDerivAt_cos x).pow 3).const_mul (-(1 / 3 : ℝ))
    rw [show Real.sin x * Real.cos x ^ 2 =
        (-(1 / 3 : ℝ)) *
          (3 * Real.cos x ^ (3 - 1) * (-Real.sin x)) by norm_num; ring]
    exact hd
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (-(1 / 3 : ℝ)) * (Real.cos ^ 3) x)
    (f' := fun x : ℝ => Real.sin x * Real.cos x ^ 2)
    (fun x _ => hderiv x)
    ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).intervalIntegrable
      0 Real.pi)
  rw [h]
  norm_num

private theorem integral_sin_sq_mul_cos_zero_pi :
    (∫ x : ℝ in (0 : ℝ)..Real.pi,
      Real.sin x ^ 2 * Real.cos x) = 0 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => (1 / 3 : ℝ) * (Real.sin ^ 3) y)
        (Real.sin x ^ 2 * Real.cos x) x := by
    intro x
    have hd := ((Real.hasDerivAt_sin x).pow 3).const_mul (1 / 3 : ℝ)
    rw [show Real.sin x ^ 2 * Real.cos x =
        (1 / 3 : ℝ) * (3 * Real.sin x ^ (3 - 1) * Real.cos x) by
      norm_num; ring]
    exact hd
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (1 / 3 : ℝ) * (Real.sin ^ 3) x)
    (f' := fun x : ℝ => Real.sin x ^ 2 * Real.cos x)
    (fun x _ => hderiv x)
    (((Real.continuous_sin.pow 2).mul Real.continuous_cos).intervalIntegrable
      0 Real.pi)
  simpa using h

private theorem integral_sin_cube_zero_pi :
    (∫ x : ℝ in (0 : ℝ)..Real.pi, Real.sin x ^ 3) = 4 / 3 := by
  let F : ℝ → ℝ := (-Real.cos) +
    fun x => (1 / 3 : ℝ) * (Real.cos ^ 3) x
  have hderiv : ∀ x : ℝ, HasDerivAt F (Real.sin x ^ 3) x := by
    intro x
    have hd := (Real.hasDerivAt_cos x).neg.add
      (((Real.hasDerivAt_cos x).pow 3).const_mul (1 / 3 : ℝ))
    have heq : Real.sin x ^ 3 =
        -(-Real.sin x) +
          (1 / 3 : ℝ) * (3 * Real.cos x ^ (3 - 1) * (-Real.sin x)) := by
      have hsq : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq x]
      rw [show Real.sin x ^ 3 = Real.sin x * Real.sin x ^ 2 by ring, hsq]
      norm_num
      ring
    rw [heq]
    exact hd
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := fun x : ℝ => Real.sin x ^ 3)
    (fun x _ => hderiv x)
    ((Real.continuous_sin.pow 3).intervalIntegrable 0 Real.pi)
  rw [h]
  simp [F]
  norm_num

private theorem integral_cos_sq_zero_twoPi :
    (∫ x : ℝ in (0 : ℝ)..2 * Real.pi, Real.cos x ^ 2) = Real.pi := by
  let F : ℝ → ℝ := (fun y : ℝ => (1 / 2 : ℝ) * id y) +
    fun y => (1 / 2 : ℝ) * (Real.sin * Real.cos) y
  let d : ℝ → ℝ := fun x =>
    (1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) *
      (Real.cos x * Real.cos x + Real.sin x * (-Real.sin x))
  have hderiv : ∀ x : ℝ, HasDerivAt F (d x) x := by
    intro x
    exact ((hasDerivAt_id x).const_mul (1 / 2 : ℝ)).add
      (((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)).const_mul
        (1 / 2 : ℝ))
  have hshape : (fun x : ℝ => Real.cos x ^ 2) = d := by
    funext x
    dsimp [d]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hshape]
  have hdint : IntervalIntegrable d volume 0 (2 * Real.pi) := by
    rw [← hshape]
    exact (Real.continuous_cos.pow 2).intervalIntegrable 0 (2 * Real.pi)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := d)
    (fun x _ => hderiv x)
    hdint
  rw [h]
  simp [F]

private theorem integral_sin_sq_zero_twoPi :
    (∫ x : ℝ in (0 : ℝ)..2 * Real.pi, Real.sin x ^ 2) = Real.pi := by
  let F : ℝ → ℝ := (fun y : ℝ => (1 / 2 : ℝ) * id y) -
    fun y => (1 / 2 : ℝ) * (Real.sin * Real.cos) y
  let d : ℝ → ℝ := fun x =>
    (1 / 2 : ℝ) * 1 - (1 / 2 : ℝ) *
      (Real.cos x * Real.cos x + Real.sin x * (-Real.sin x))
  have hderiv : ∀ x : ℝ, HasDerivAt F (d x) x := by
    intro x
    exact ((hasDerivAt_id x).const_mul (1 / 2 : ℝ)).sub
      (((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x)).const_mul
        (1 / 2 : ℝ))
  have hshape : (fun x : ℝ => Real.sin x ^ 2) = d := by
    funext x
    dsimp [d]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hshape]
  have hdint : IntervalIntegrable d volume 0 (2 * Real.pi) := by
    rw [← hshape]
    exact (Real.continuous_sin.pow 2).intervalIntegrable 0 (2 * Real.pi)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := d)
    (fun x _ => hderiv x)
    hdint
  rw [h]
  simp [F]

private theorem integral_sin_mul_cos_zero_twoPi :
    (∫ x : ℝ in (0 : ℝ)..2 * Real.pi,
      Real.sin x * Real.cos x) = 0 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * (Real.sin ^ 2) y)
        (Real.sin x * Real.cos x) x := by
    intro x
    have hd := ((Real.hasDerivAt_sin x).pow 2).const_mul (1 / 2 : ℝ)
    rw [show Real.sin x * Real.cos x =
        (1 / 2 : ℝ) * (2 * Real.sin x ^ (2 - 1) * Real.cos x) by
      norm_num; ring]
    exact hd
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => (1 / 2 : ℝ) * (Real.sin ^ 2) y)
    (f' := fun x : ℝ => Real.sin x * Real.cos x)
    (fun x _ => hderiv x)
    ((Real.continuous_sin.mul Real.continuous_cos).intervalIntegrable
      0 (2 * Real.pi))
  simpa using h

/-- Total angular mass of the `i,j` boundary-flux density. -/
def punctureAngularMass (i j : Fin 3) : ℝ :=
  ∫ p : ℝ × ℝ, punctureAngularDensity i j p ∂sphereAngularMeasure

private theorem integral_sphereAngular_mul (f g : ℝ → ℝ) :
    (∫ p : ℝ × ℝ, f p.1 * g p.2 ∂sphereAngularMeasure) =
      (∫ θ : ℝ in (0 : ℝ)..Real.pi, f θ) *
        (∫ ϕ : ℝ in (0 : ℝ)..2 * Real.pi, g ϕ) := by
  rw [sphereAngularMeasure, MeasureTheory.integral_prod_mul,
    intervalIntegral.integral_of_le Real.pi_pos.le,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

/-- The actual spherical boundary flux has angular tensor `(1/3)δᵢⱼ`.
This derives the local coefficient from the surface integral rather than
assigning it by definition. -/
theorem punctureAngularMass_eq (i j : Fin 3) :
    punctureAngularMass i j = (1 / 3 : ℝ) * basisVector i j := by
  classical
  fin_cases i <;> fin_cases j
  all_goals simp only [punctureAngularMass, punctureAngularDensity,
    basisVector]
  all_goals simp [unitSphereParam]
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.cos p.2) *
        (Real.sin p.1 * Real.cos p.2) * Real.sin p.1
      ∂sphereAngularMeasure) = 3⁻¹
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.cos p.2) *
          (Real.sin p.1 * Real.cos p.2) * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ * Real.sin p.1 ^ 3) *
          Real.cos p.2 ^ 2) by funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * Real.sin θ ^ 3)
      (fun ϕ => Real.cos ϕ ^ 2), intervalIntegral.integral_const_mul,
      integral_sin_cube_zero_pi, integral_cos_sq_zero_twoPi]
    field_simp [Real.pi_ne_zero]
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.cos p.2) *
        (Real.sin p.1 * Real.sin p.2) * Real.sin p.1
      ∂sphereAngularMeasure) = 0
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.cos p.2) *
          (Real.sin p.1 * Real.sin p.2) * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ * Real.sin p.1 ^ 3) *
          (Real.sin p.2 * Real.cos p.2)) by funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * Real.sin θ ^ 3)
      (fun ϕ => Real.sin ϕ * Real.cos ϕ), integral_sin_mul_cos_zero_twoPi]
    simp
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.cos p.2) *
        Real.cos p.1 * Real.sin p.1 ∂sphereAngularMeasure) = 0
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.cos p.2) *
          Real.cos p.1 * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ *
          (Real.sin p.1 ^ 2 * Real.cos p.1)) * Real.cos p.2) by
            funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * (Real.sin θ ^ 2 * Real.cos θ))
      Real.cos, intervalIntegral.integral_const_mul,
      integral_sin_sq_mul_cos_zero_pi]
    simp
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.sin p.2) *
        (Real.sin p.1 * Real.cos p.2) * Real.sin p.1
      ∂sphereAngularMeasure) = 0
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.sin p.2) *
          (Real.sin p.1 * Real.cos p.2) * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ * Real.sin p.1 ^ 3) *
          (Real.sin p.2 * Real.cos p.2)) by funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * Real.sin θ ^ 3)
      (fun ϕ => Real.sin ϕ * Real.cos ϕ), integral_sin_mul_cos_zero_twoPi]
    simp
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.sin p.2) *
        (Real.sin p.1 * Real.sin p.2) * Real.sin p.1
      ∂sphereAngularMeasure) = 3⁻¹
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.sin p.2) *
          (Real.sin p.1 * Real.sin p.2) * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ * Real.sin p.1 ^ 3) *
          Real.sin p.2 ^ 2) by funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * Real.sin θ ^ 3)
      (fun ϕ => Real.sin ϕ ^ 2), intervalIntegral.integral_const_mul,
      integral_sin_cube_zero_pi, integral_sin_sq_zero_twoPi]
    field_simp [Real.pi_ne_zero]
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.sin p.2) *
        Real.cos p.1 * Real.sin p.1 ∂sphereAngularMeasure) = 0
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * (Real.sin p.1 * Real.sin p.2) *
          Real.cos p.1 * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ *
          (Real.sin p.1 ^ 2 * Real.cos p.1)) * Real.sin p.2) by
            funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * (Real.sin θ ^ 2 * Real.cos θ))
      Real.sin, intervalIntegral.integral_const_mul,
      integral_sin_sq_mul_cos_zero_pi]
    simp
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * Real.cos p.1 *
        (Real.sin p.1 * Real.cos p.2) * Real.sin p.1
      ∂sphereAngularMeasure) = 0
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * Real.cos p.1 *
          (Real.sin p.1 * Real.cos p.2) * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ *
          (Real.sin p.1 ^ 2 * Real.cos p.1)) * Real.cos p.2) by
            funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * (Real.sin θ ^ 2 * Real.cos θ))
      Real.cos, intervalIntegral.integral_const_mul,
      integral_sin_sq_mul_cos_zero_pi]
    simp
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * Real.cos p.1 *
        (Real.sin p.1 * Real.sin p.2) * Real.sin p.1
      ∂sphereAngularMeasure) = 0
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * Real.cos p.1 *
          (Real.sin p.1 * Real.sin p.2) * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ *
          (Real.sin p.1 ^ 2 * Real.cos p.1)) * Real.sin p.2) by
            funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * (Real.sin θ ^ 2 * Real.cos θ))
      Real.sin, intervalIntegral.integral_const_mul,
      integral_sin_sq_mul_cos_zero_pi]
    simp
  · change (∫ p : ℝ × ℝ,
      Real.pi⁻¹ * 4⁻¹ * Real.cos p.1 * Real.cos p.1 * Real.sin p.1
      ∂sphereAngularMeasure) = 3⁻¹
    rw [show (fun p : ℝ × ℝ =>
        Real.pi⁻¹ * 4⁻¹ * Real.cos p.1 * Real.cos p.1 * Real.sin p.1) =
        (fun p => (Real.pi⁻¹ * 4⁻¹ *
          (Real.sin p.1 * Real.cos p.1 ^ 2)) * 1) by funext p; ring]
    rw [integral_sphereAngular_mul
      (fun θ => Real.pi⁻¹ * 4⁻¹ * (Real.sin θ * Real.cos θ ^ 2))
      (fun _ => 1), intervalIntegral.integral_const_mul,
      integral_sin_mul_cos_sq_zero_pi, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one, sub_zero]
    field_simp [Real.pi_ne_zero]
    norm_num

private theorem abs_unitSphereParam_coord_le_one (θ ϕ : ℝ) (i : Fin 3) :
    |unitSphereParam θ ϕ i| ≤ 1 := by
  unfold unitSphereParam
  split_ifs
  · rw [abs_mul]
    exact mul_le_one₀ (Real.abs_sin_le_one θ) (abs_nonneg _)
      (Real.abs_cos_le_one ϕ)
  · rw [abs_mul]
    exact mul_le_one₀ (Real.abs_sin_le_one θ) (abs_nonneg _)
      (Real.abs_sin_le_one ϕ)
  · exact Real.abs_cos_le_one θ

private theorem abs_punctureAngularDensity_le (i j : Fin 3) (p : ℝ × ℝ) :
    |punctureAngularDensity i j p| ≤ |1 / (4 * Real.pi)| := by
  rw [punctureAngularDensity, abs_mul, abs_mul, abs_mul]
  have hi := abs_unitSphereParam_coord_le_one p.1 p.2 i
  have hj := abs_unitSphereParam_coord_le_one p.1 p.2 j
  have hs := Real.abs_sin_le_one p.1
  have hc : 0 ≤ |1 / (4 * Real.pi)| := abs_nonneg _
  calc
    |1 / (4 * Real.pi)| * |unitSphereParam p.1 p.2 i| *
          |unitSphereParam p.1 p.2 j| * |Real.sin p.1| ≤
        |1 / (4 * Real.pi)| * 1 * 1 * 1 := by
          gcongr
    _ = |1 / (4 * Real.pi)| := by ring

private theorem continuous_punctureAngularDensity (i j : Fin 3) :
    Continuous (punctureAngularDensity i j) := by
  unfold punctureAngularDensity unitSphereParam
  split_ifs <;> fun_prop

private theorem integrable_punctureAngularDensity (i j : Fin 3) :
    Integrable (punctureAngularDensity i j) sphereAngularMeasure := by
  let C : ℝ := |1 / (4 * Real.pi)|
  haveI : IsFiniteMeasure sphereAngularMeasure := by
    unfold sphereAngularMeasure
    infer_instance
  exact (integrable_const C).mono'
    (continuous_punctureAngularDensity i j).aestronglyMeasurable
    (ae_of_all _ fun p => by
      simpa only [Real.norm_eq_abs, abs_abs] using
        abs_punctureAngularDensity_le i j p)

private theorem continuous_unitSphereParam :
    Continuous (fun p : ℝ × ℝ => unitSphereParam p.1 p.2) := by
  apply continuous_pi
  intro k
  unfold unitSphereParam
  split_ifs <;> fun_prop

/-- For a bounded continuous test function, the shrinking spherical flux
converges to the local `(1/3)δᵢⱼ` term. -/
theorem tendsto_punctureBoundary (i j : Fin 3) (φ : Space → ℝ)
    (hφ : Continuous φ) (C : ℝ)
    (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    Tendsto (fun ε : ℝ => punctureBoundary ε i j φ) (nhds 0)
      (nhds ((1 / 3 : ℝ) * basisVector i j * φ 0)) := by
  let F : ℝ → (ℝ × ℝ) → ℝ := fun ε p =>
    punctureAngularDensity i j p * φ (ε • unitSphereParam p.1 p.2)
  let f : (ℝ × ℝ) → ℝ := fun p => punctureAngularDensity i j p * φ 0
  let bound : (ℝ × ℝ) → ℝ := fun p => C * ‖punctureAngularDensity i j p‖
  have hF_meas : ∀ ε : ℝ, AEStronglyMeasurable (F ε) sphereAngularMeasure := by
    intro ε
    apply Continuous.aestronglyMeasurable
    exact (continuous_punctureAngularDensity i j).mul
      (hφ.comp (by
        exact (continuous_const_smul ε).comp continuous_unitSphereParam))
  have hbound_ae : ∀ ε : ℝ, ∀ᵐ p ∂sphereAngularMeasure,
      ‖F ε p‖ ≤ bound p := by
    intro ε
    filter_upwards [] with p
    dsimp only [F, bound]
    rw [norm_mul]
    calc
      ‖punctureAngularDensity i j p‖ *
          ‖φ (ε • unitSphereParam p.1 p.2)‖ ≤
          ‖punctureAngularDensity i j p‖ * C :=
        mul_le_mul_of_nonneg_left (hφ_bound _) (norm_nonneg _)
      _ = C * ‖punctureAngularDensity i j p‖ := mul_comm _ _
  have hbound_int : Integrable bound sphereAngularMeasure := by
    exact (integrable_punctureAngularDensity i j).norm.const_mul C
  have hlim_ae : ∀ᵐ p ∂sphereAngularMeasure,
      Tendsto (fun ε : ℝ => F ε p) (nhds 0) (nhds (f p)) := by
    filter_upwards [] with p
    dsimp only [F, f]
    apply tendsto_const_nhds.mul
    have hc : Continuous (fun ε : ℝ =>
        φ (ε • unitSphereParam p.1 p.2)) := by
      fun_prop
    have hc0 : ContinuousAt (fun ε : ℝ =>
        φ (ε • unitSphereParam p.1 p.2)) 0 := hc.continuousAt
    change Tendsto (fun ε : ℝ => φ (ε • unitSphereParam p.1 p.2))
      (nhds 0) (nhds (φ ((0 : ℝ) • unitSphereParam p.1 p.2))) at hc0
    simpa only [zero_smul] using hc0
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := sphereAngularMeasure) (l := nhds (0 : ℝ))
    (F := F) (f := f) (bound := bound)
    (Eventually.of_forall hF_meas) (Eventually.of_forall hbound_ae)
    hbound_int hlim_ae
  have hterminal : (∫ p : ℝ × ℝ,
      punctureAngularDensity i j p * φ 0 ∂sphereAngularMeasure) =
      (1 / 3 : ℝ) * basisVector i j * φ 0 := by
    rw [integral_mul_const, ← punctureAngularMass, punctureAngularMass_eq]
  simpa only [punctureBoundary, F, f, hterminal] using hlim

/-- Schwartz test functions satisfy the boundedness hypothesis of the
shrinking-puncture theorem by their zeroth seminorm. -/
theorem tendsto_punctureBoundary_schwartz (i j : Fin 3)
    (φ : SchwartzMap Space ℝ) :
    Tendsto (fun ε : ℝ => punctureBoundary ε i j φ) (nhds 0)
      (nhds ((1 / 3 : ℝ) * basisVector i j * φ 0)) := by
  apply tendsto_punctureBoundary i j φ φ.continuous
    ((SchwartzMap.seminorm ℝ 0 0) φ)
  intro x
  simpa using φ.norm_iteratedFDeriv_le_seminorm ℝ 0 x

/-- Integral over the complement of the closed Euclidean ball of radius
`ε`.  This is the truncation used in the principal value. -/
def exteriorIntegral (ε : ℝ) (g : Space → ℝ) : ℝ :=
  ∫ x : Space, Set.indicator
    {x : Space | ε < officialEuclideanNorm x} g x

private theorem continuous_officialEuclideanNorm :
    Continuous officialEuclideanNorm := by
  rw [show officialEuclideanNorm = fun x : Space =>
      Real.sqrt (∑ k : Fin 3, |x k| ^ 2) by
    funext x
    exact officialEuclideanNorm_eq_sqrt_sum_sq x]
  fun_prop

/-- Removing a Euclidean ball whose radius tends to zero does not change the
integral of an integrable function that vanishes at the origin. -/
theorem tendsto_exteriorIntegral {g : Space → ℝ} (hg : Integrable g)
    (hg0 : g 0 = 0) :
    Tendsto (fun ε : ℝ => exteriorIntegral ε g)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x : Space, g x)) := by
  let F : ℝ → Space → ℝ := fun ε x => Set.indicator
    {y : Space | ε < officialEuclideanNorm y} g x
  have hset : ∀ ε : ℝ, MeasurableSet
      {x : Space | ε < officialEuclideanNorm x} := by
    intro ε
    exact (isOpen_lt continuous_const continuous_officialEuclideanNorm).measurableSet
  have hF_meas : ∀ ε : ℝ, AEStronglyMeasurable (F ε) := by
    intro ε
    exact hg.aestronglyMeasurable.indicator (hset ε)
  have hbound : ∀ ε : ℝ, ∀ᵐ x : Space, ‖F ε x‖ ≤ ‖g x‖ := by
    intro ε
    filter_upwards [] with x
    by_cases hx : ε < officialEuclideanNorm x
    · simp [F, hx]
    · simp [F, hx]
  have hpoint : ∀ᵐ x : Space,
      Tendsto (fun ε : ℝ => F ε x) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (g x)) := by
    filter_upwards [] with x
    by_cases hx : x = 0
    · subst x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε at hε
      have hnot : ¬ε < officialEuclideanNorm (0 : Space) := by
        simpa [officialEuclideanNorm, officialEuclideanPoint] using
          (not_lt_of_ge hε.le)
      simp [F, hnot, hg0]
    · have hn0 : officialEuclideanNorm x ≠ 0 := by
        intro hn
        apply hx
        apply norm_eq_zero.mp
        have hnorm := norm_le_officialEuclideanNorm x
        rw [hn] at hnorm
        exact le_antisymm hnorm (norm_nonneg x)
      have hpos : 0 < officialEuclideanNorm x :=
        lt_of_le_of_ne (officialEuclideanNorm_nonneg x) (Ne.symm hn0)
      refine tendsto_const_nhds.congr' ?_
      have hev : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
          ε < officialEuclideanNorm x :=
        (show ∀ᶠ ε : ℝ in nhds 0, ε < officialEuclideanNorm x from
          Iio_mem_nhds hpos).filter_mono inf_le_left
      filter_upwards [hev] with ε hε
      simp [F, hε]
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := nhdsWithin 0 (Set.Ioi 0))
    (F := F) (f := g) (bound := fun x => ‖g x‖)
    (Eventually.of_forall hF_meas) (Eventually.of_forall hbound)
    hg.norm hpoint
  simpa only [exteriorIntegral, F] using hlim

/-- The principal-value part of the `i,j` Biot--Savart gradient tensor. -/
def puncturedGradientIntegral (ε : ℝ) (i j : Fin 3)
    (φ : Space → ℝ) : ℝ :=
  exteriorIntegral ε (fun z =>
    (1 / (4 * Real.pi)) * bsGradKernel i j z * φ z)

/-- A value is the principal value of the Biot--Savart gradient tensor when
the exterior-ball truncations converge to it through positive radii. -/
def HasBiotSavartPrincipalValue (i j : Fin 3) (φ : Space → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun ε : ℝ => puncturedGradientIntegral ε i j φ)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

/-- Closing the punctured integration-by-parts identity adds exactly the
origin-supported `(1/3)δᵢⱼ` term.  The only geometric input required here is
the finite-radius punctured identity; the preceding theorems prove both
limits appearing in its closure. -/
theorem biotSavartPrincipalValue_identity
    (i j : Fin 3) (φ : Space → ℝ) (L C : ℝ)
    (hφ : Continuous φ) (hφ_bound : ∀ x, ‖φ x‖ ≤ C)
    (hintDerivative : Integrable (fun z : Space =>
      bsVectorKernel z j * fderiv ℝ φ z (basisVector i)))
    (hpv : HasBiotSavartPrincipalValue i j φ L)
    (hpunctured : ∀ ε : ℝ, 0 < ε →
      -(exteriorIntegral ε (fun z : Space =>
          bsVectorKernel z j * fderiv ℝ φ z (basisVector i))) =
        puncturedGradientIntegral ε i j φ +
          punctureBoundary ε i j φ) :
    -(∫ z : Space, bsVectorKernel z j *
        fderiv ℝ φ z (basisVector i)) =
      L + (1 / 3 : ℝ) * basisVector i j * φ 0 := by
  let derivativeIntegrand : Space → ℝ := fun z =>
    bsVectorKernel z j * fderiv ℝ φ z (basisVector i)
  have hd0 : derivativeIntegrand 0 = 0 := by
    simp [derivativeIntegrand, bsVectorKernel, bsKernelScalar]
  have hleft := (tendsto_exteriorIntegral hintDerivative hd0).neg
  have hsource : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 := inf_le_left
  have hboundary : Tendsto (fun ε : ℝ => punctureBoundary ε i j φ)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((1 / 3 : ℝ) * basisVector i j * φ 0)) :=
    (tendsto_punctureBoundary i j φ hφ C hφ_bound).mono_left hsource
  have hright := hpv.add hboundary
  have heq : (fun ε : ℝ => -(exteriorIntegral ε derivativeIntegrand))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun ε => puncturedGradientIntegral ε i j φ +
        punctureBoundary ε i j φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hpunctured ε hε
  have hleft' := hleft.congr' heq
  exact tendsto_nhds_unique hleft' hright

end Navier.Analysis.BiotSavartPuncture
