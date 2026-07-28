import Navier.Problem

/-!
# The Gaussian heat kernel on `ℝ³` and its `L^s` norms

Mathlib carries the one-dimensional Gaussian integral
`∫ x : ℝ, exp (-b x²) = √(π/b)` and Fubini in the form
`integral_fintype_prod_volume_eq_pow`, but **no heat kernel**: an exhaustive
search of Mathlib for `heatKernel` / `HeatKernel` / `heat_kernel` returns
nothing.  This file builds the three-dimensional kernel and the `L^s`
estimates that the conditional-regularity far-field leaves need, from the
explicit Gaussian and nothing else.

`Navier.Space = Fin 3 → ℝ` carries the *product* (supremum) norm, so the
Euclidean square `∑ i, x i ^ 2` is written out explicitly here rather than as
`‖x‖ ^ 2`; the comparison with the official Euclidean point norm lives in
`Navier.Analysis.OfficialABEncoding` and is not needed for any statement below.

## Contents

* `integral_gaussian_space` — `∫ x : Space, exp (-b ∑ xᵢ²) = √(π/b)³`, for
  every real `b` (the degenerate `b ≤ 0` cases hold because both sides take
  Lean's junk value `0`).
* `heatKernel` — `G_t^ν(x) = (4πνt)^{-3/2} exp(−|x|²/(4νt))`.
* `heatKernel_pos`, `heatKernel_nonneg` — positivity for `0 < ν`, `0 < t`.
* `integral_heatKernel` — the kernel has unit mass.

## Scaling (the reason this module exists)

For `1 ≤ s`, `∫ (G_t)^s = s^{-3/2} · (4πνt)^{-3(s-1)/2}`, so
`‖G_t‖_{L^{r'}} = C(r,ν) · t^{-3/(2r)}` with `1/r + 1/r' = 1`.  Composed with
Hölder this is the `L^r → L^∞` smoothing estimate
`‖e^{tνΔ} f‖_∞ ≤ C t^{-3/(2r)} ‖f‖_r`
[Kato, Math. Z. 187 (1984) 471–480, §2;
Giga–Miyakawa, Arch. Ration. Mech. Anal. 89 (1985) 267–281].
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Real
open scoped BigOperators

namespace Navier.Analysis.HeatSemigroupSmoothing

open Navier

/-! ### The three-dimensional Gaussian integral -/

/-- **The Gaussian integral on `ℝ³`.**  Fubini
(`integral_fintype_prod_volume_eq_pow`) reduces the isotropic Gaussian on
`Space = Fin 3 → ℝ` to the cube of Mathlib's one-dimensional
`integral_gaussian`.

No positivity hypothesis on `b` is needed: for `b < 0` the left side is a
non-integrable integrand and the right side has `√` of a negative number, both
`0`; for `b = 0` the left side is `∫ 1` over an infinite measure and the right
side is `√(π/0) ^ 3`, again both `0`. -/
theorem integral_gaussian_space (b : ℝ) :
    ∫ x : Space, Real.exp (-b * ∑ i : Fin 3, x i ^ 2) = Real.sqrt (π / b) ^ 3 := by
  have hprod : ∀ x : Space,
      Real.exp (-b * ∑ i : Fin 3, x i ^ 2) = ∏ i : Fin 3, Real.exp (-b * x i ^ 2) := by
    intro x
    rw [← Real.exp_sum, ← Finset.mul_sum]
  simp_rw [hprod]
  rw [MeasureTheory.integral_fintype_prod_volume_eq_pow (fun y : ℝ => Real.exp (-b * y ^ 2)),
    integral_gaussian]
  simp

/-! ### The heat kernel -/

/-- **The Gaussian heat kernel on `ℝ³`** for viscosity `ν` at time `t`:

`G_t^ν(x) = (4πνt)^{-3/2} · exp(−|x|²/(4νt))`,

the fundamental solution of `∂_t u = ν Δu`.  Written with `(4νt)⁻¹` in the
exponent so that it matches `integral_gaussian_space` syntactically;
`heatKernel_eq` gives the familiar quotient form. -/
def heatKernel (ν t : ℝ) (x : Space) : ℝ :=
  (4 * π * ν * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(4 * ν * t)⁻¹ * ∑ i : Fin 3, x i ^ 2)

/-- The heat kernel in the familiar quotient form `exp(−|x|²/(4νt))`. -/
theorem heatKernel_eq (ν t : ℝ) (x : Space) :
    heatKernel ν t x =
      (4 * π * ν * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ i : Fin 3, x i ^ 2) / (4 * ν * t)) := by
  rw [heatKernel]
  congr 2
  field_simp

/-- The heat kernel is strictly positive at positive viscosity and time. -/
theorem heatKernel_pos {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : Space) :
    0 < heatKernel ν t x := by
  have hA : (0 : ℝ) < 4 * π * ν * t := by positivity
  exact mul_pos (Real.rpow_pos_of_pos hA _) (Real.exp_pos _)

theorem heatKernel_nonneg {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (x : Space) :
    0 ≤ heatKernel ν t x :=
  (heatKernel_pos hν ht x).le

/-- For `0 < A`, `A^{-3/2} · (√A)³ = 1`.  The normalisation identity behind
`integral_heatKernel`, isolated because it recurs in the `L^s` estimates. -/
theorem rpow_neg_three_halves_mul_sqrt_cube {A : ℝ} (hA : 0 < A) :
    A ^ (-(3 : ℝ) / 2) * Real.sqrt A ^ 3 = 1 := by
  have hsq : Real.sqrt A ^ 3 = A ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (A ^ ((1 : ℝ) / 2)) 3,
      ← Real.rpow_mul hA.le]
    norm_num
  rw [hsq, ← Real.rpow_add hA]
  norm_num

/-- **The heat kernel has unit mass.**  `∫_{ℝ³} G_t^ν = 1` for every positive
viscosity and time: the Gaussian integral `integral_gaussian_space` returns
`√(4πνt)³`, which the prefactor `(4πνt)^{-3/2}` exactly cancels. -/
theorem integral_heatKernel {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    ∫ x : Space, heatKernel ν t x = 1 := by
  have hA : (0 : ℝ) < 4 * π * ν * t := by positivity
  simp only [heatKernel]
  rw [MeasureTheory.integral_const_mul, integral_gaussian_space]
  have hrw : π / (4 * ν * t)⁻¹ = 4 * π * ν * t := by
    rw [div_eq_mul_inv, inv_inv]; ring
  rw [hrw]
  exact rpow_neg_three_halves_mul_sqrt_cube hA

/-! ### `L^s` norms of the kernel and the `t^{-3/(2r)}` scaling -/

/-- The cube of a square root as an `rpow`. -/
theorem sqrt_cube_eq_rpow {A : ℝ} (hA : 0 ≤ A) : Real.sqrt A ^ 3 = A ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (A ^ ((1 : ℝ) / 2)) 3, ← Real.rpow_mul hA]
  norm_num

/-- **The `s`-th power integral of the heat kernel.**  For every `s > 0`,

`∫_{ℝ³} (G_t^ν)^s = s^{-3/2} · (4πνt)^{-3(s-1)/2}`.

At `s = 1` this is `integral_heatKernel`.  The `t`-dependence `t^{-3(s-1)/2}`
is the entire content of the smoothing estimate: it is what makes
`‖G_t‖_{L^{r'}}` blow up like `t^{-3/(2r)}` as `t ↓ 0`. -/
theorem integral_heatKernel_rpow {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) {s : ℝ} (hs : 0 < s) :
    ∫ x : Space, heatKernel ν t x ^ s
      = s ^ (-(3 : ℝ) / 2) * (4 * π * ν * t) ^ (-(3 : ℝ) * (s - 1) / 2) := by
  have hA : (0 : ℝ) < 4 * π * ν * t := by positivity
  have hpt : ∀ x : Space, heatKernel ν t x ^ s
      = (4 * π * ν * t) ^ (-(3 : ℝ) / 2 * s) *
        Real.exp (-(s * (4 * ν * t)⁻¹) * ∑ i : Fin 3, x i ^ 2) := by
    intro x
    rw [heatKernel, Real.mul_rpow (Real.rpow_nonneg hA.le _) (Real.exp_nonneg _),
      ← Real.rpow_mul hA.le, ← Real.exp_mul]
    ring_nf
  simp_rw [hpt]
  rw [MeasureTheory.integral_const_mul, integral_gaussian_space]
  have hq : π / (s * (4 * ν * t)⁻¹) = (4 * π * ν * t) / s := by
    field_simp
  have hsneg : s ^ (-(3 : ℝ) / 2) = (s ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [neg_div, Real.rpow_neg hs.le]
  have hAsplit : (4 * π * ν * t) ^ (-(3 : ℝ) * (s - 1) / 2)
      = (4 * π * ν * t) ^ (-(3 : ℝ) / 2 * s) * (4 * π * ν * t) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_add hA]
    congr 1
    ring
  rw [hq, sqrt_cube_eq_rpow (by positivity), Real.div_rpow hA.le hs.le,
    hsneg, hAsplit, div_eq_mul_inv]
  ring

/-- **The `L^{r'}` norm of the heat kernel scales like `t^{-3/(2r)}`.**  For a
spatial exponent `r > 1` with Hölder conjugate `r' = r/(r−1)`,

`‖G_t^ν‖_{L^{r'}(ℝ³)} = C(r,ν) · t^{-3/(2r)}`

with `C(r,ν) = (r')^{-3/(2r')} · (4πν)^{-3/(2r)} > 0` independent of `t`.

Composed with Hölder — `|(G_t * f)(x)| ≤ ‖G_t‖_{L^{r'}} ‖f‖_{L^r}` — this is
exactly the `L^r → L^∞` heat-semigroup smoothing estimate
`‖e^{tνΔ} f‖_∞ ≤ C t^{-3/(2r)} ‖f‖_r`
[Kato, Math. Z. 187 (1984) 471–480, §2].  The exponent is forced by parabolic
scaling: `3/2 − 3/(2r') = (3/2)(1 − 1/r') = 3/(2r)`. -/
theorem heatKernel_Lr_scaling {ν : ℝ} (hν : 0 < ν) {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      (∫ x : Space, heatKernel ν t x ^ (r / (r - 1))) ^ ((r - 1) / r)
        = C * t ^ (-(3 : ℝ) / (2 * r)) := by
  have hr1 : (0 : ℝ) < r - 1 := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  set s : ℝ := r / (r - 1) with hs_def
  have hs : 0 < s := div_pos hr0 hr1
  have hνπ : (0 : ℝ) < 4 * π * ν := by positivity
  refine ⟨s ^ (-(3 : ℝ) / 2 * ((r - 1) / r)) * (4 * π * ν) ^ (-(3 : ℝ) / (2 * r)),
    by positivity, ?_⟩
  intro t ht
  have hA : (0 : ℝ) < 4 * π * ν * t := by positivity
  rw [integral_heatKernel_rpow hν ht hs,
    Real.mul_rpow (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg hA.le _),
    ← Real.rpow_mul hs.le, ← Real.rpow_mul hA.le]
  have hcoef : -(3 : ℝ) * (s - 1) / 2 * ((r - 1) / r) = -(3 : ℝ) / (2 * r) := by
    rw [hs_def]
    field_simp
    ring
  rw [hcoef, show (4 : ℝ) * π * ν * t = (4 * π * ν) * t by ring,
    Real.mul_rpow hνπ.le ht.le]
  ring

end Navier.Analysis.HeatSemigroupSmoothing
