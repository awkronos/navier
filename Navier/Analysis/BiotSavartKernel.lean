import Navier.Analysis.Vorticity
import Navier.Analysis.OfficialABEncoding

/-!
# The Biot–Savart kernel and its elementary estimates

The Biot–Savart law recovers an incompressible velocity field from its
vorticity by convolution against the kernel

  `u(x) = -(4π)⁻¹ ∫_{ℝ³} ω(y) × (x − y) / |x − y|³ dy`,

so the velocity *gradient* is a Calderón–Zygmund singular integral of the
vorticity against the degree-`(−3)`-homogeneous kernel `∇K`.  This file builds
the genuinely Mathlib-absent kernel infrastructure: the definition, its
homogeneity, and the pointwise far-field `L²` decay bound that controls the
non-singular tail by `‖ω‖_{L²}`.  The deep Calderón–Zygmund near-field
cancellation theorem is named as an honest residual in
`SingularIntegralPrelims.lean`; the results here are unconditional real
analysis on `ℝ³` and carry axiom set `⊆ {propext, Classical.choice,
Quot.sound}`.

## Norm convention

`officialEuclideanNorm` is the `ℓ²` norm on `Space = Fin 3 → ℝ` (see
`OfficialABEncoding.lean`); it agrees with the standard Euclidean norm on `ℝ³`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped BigOperators

namespace Navier.Analysis.BiotSavartKernel

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding

/-- Local helper: the Euclidean norm is strictly positive off the origin. -/
private theorem officialEuclideanNorm_pos_of_ne_zero {x : Space} (hx : x ≠ 0) :
    0 < officialEuclideanNorm x := by
  by_contra h
  push_neg at h
  have heq : officialEuclideanNorm x = 0 :=
    le_antisymm h (officialEuclideanNorm_nonneg x)
  exact hx ((officialEuclideanNorm_eq_zero_iff x).mp heq)

/-!
## The scalar kernel magnitude
-/

/-- The Biot–Savart scalar kernel magnitude `1/(4π·|x|³)` off the origin,
defined as `0` at the origin (the origin value is irrelevant to every
convolution integral; the kernel is a distribution near `0`). -/
def bsKernelScalar (x : Space) : ℝ :=
  if x = 0 then 0 else 1 / (4 * Real.pi * officialEuclideanNorm x ^ 3)

/-- The scalar kernel is nonnegative. -/
theorem bsKernelScalar_nonneg (x : Space) :
    0 ≤ bsKernelScalar x := by
  rw [bsKernelScalar]
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (pow_nonneg (officialEuclideanNorm_nonneg _) _))

/-- Off the origin the scalar kernel equals `1/(4π|x|³)`. -/
theorem bsKernelScalar_apply_of_ne_zero {x : Space} (hx : x ≠ 0) :
    bsKernelScalar x = 1 / (4 * Real.pi * officialEuclideanNorm x ^ 3) := by
  rw [bsKernelScalar, if_neg hx]

/-- The scalar kernel is strictly positive off the origin. -/
theorem bsKernelScalar_pos_of_ne_zero {x : Space} (hx : x ≠ 0) :
    0 < bsKernelScalar x := by
  rw [bsKernelScalar_apply_of_ne_zero hx]
  exact div_pos (by norm_num)
    (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (pow_pos (officialEuclideanNorm_pos_of_ne_zero hx) _))

/-- The scalar kernel vanishes at the origin by definition. -/
theorem bsKernelScalar_zero : bsKernelScalar 0 = 0 := by
  rw [bsKernelScalar, if_pos rfl]

/-!
## The vector kernel and its off-origin derivative
-/

/-- The actual vector kernel `z/(4π|z|³)`, assigned the irrelevant value zero
at the singular point.  The velocity Biot--Savart integrand is obtained from
this by crossing with the vorticity. -/
def bsVectorKernel (x : Space) : Space :=
  bsKernelScalar x • x

/-- The squared Euclidean radius along a coordinate line has derivative
`2 xᵢ` at the line origin. -/
private theorem radiusSq_coordinateLine_hasDerivAt (x : Space) (i : Fin 3) :
    HasDerivAt
      (∑ k : Fin 3, (fun t : ℝ => x k + t * basisVector i k) ^ 2)
      (2 * x i) 0 := by
  classical
  have hsum := HasDerivAt.sum (x := (0 : ℝ)) (u := Finset.univ)
      (A := fun k : Fin 3 => (fun t : ℝ => x k + t * basisVector i k) ^ 2)
      (A' := fun k : Fin 3 => 2 * x k * basisVector i k)
      (fun k _ => by
        have hlin : HasDerivAt (fun t : ℝ => x k + t * basisVector i k)
            (basisVector i k) 0 := by
          simpa only [id_eq, mul_one, add_zero, mul_comm] using
            (hasDerivAt_id 0).mul_const (basisVector i k) |>.const_add (x k)
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, add_zero]
          using hlin.pow 2)
  have hd : (∑ k : Fin 3, 2 * x k * basisVector i k) = 2 * x i := by
    simp [basisVector, Pi.single_apply]
  rw [← hd]
  exact hsum

/-- Coordinate-line derivative of the official Euclidean radius away from
the origin: `d/dt |x+t eᵢ| at 0 = xᵢ/|x|`. -/
theorem officialEuclideanNorm_coordinateLine_hasDerivAt
    {x : Space} (hx : x ≠ 0) (i : Fin 3) :
    HasDerivAt
      (fun t : ℝ => officialEuclideanNorm (x + t • basisVector i))
      (x i / officialEuclideanNorm x) 0 := by
  have hq := (radiusSq_coordinateLine_hasDerivAt x i).sqrt ?_
  · have hfun : (fun t : ℝ => officialEuclideanNorm (x + t • basisVector i)) =
        (fun t : ℝ => Real.sqrt
          ((∑ k : Fin 3, (fun s : ℝ => x k + s * basisVector i k) ^ 2) t)) := by
      funext t
      rw [officialEuclideanNorm_eq_sqrt_sum_sq]
      congr 1
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sq_abs, Pi.pow_apply]
    rw [hfun]
    have hsum : (∑ k : Fin 3, x k ^ 2) = officialEuclideanNorm x ^ 2 := by
      rw [officialEuclideanNorm_eq_sqrt_sum_sq]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg |x k|)]
      simp only [sq_abs]
    convert hq using 1
    rw [show Real.sqrt ((∑ k : Fin 3,
          (fun s : ℝ => x k + s * basisVector i k) ^ 2) 0) =
          officialEuclideanNorm x by
      rw [Finset.sum_apply]
      simp only [Pi.pow_apply, zero_mul, add_zero]
      rw [hsum, Real.sqrt_sq (officialEuclideanNorm_nonneg x)]]
    have hr : officialEuclideanNorm x ≠ 0 :=
      (officialEuclideanNorm_eq_zero_iff x).not.mpr hx
    field_simp
  · rw [show ((∑ k : Fin 3,
        (fun s : ℝ => x k + s * basisVector i k) ^ 2) 0) =
        officialEuclideanNorm x ^ 2 by
      rw [Finset.sum_apply]
      simp only [Pi.pow_apply, zero_mul, add_zero]
      rw [officialEuclideanNorm_eq_sqrt_sum_sq]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg |x k|)]
      simp only [sq_abs]]
    exact pow_ne_zero 2 ((officialEuclideanNorm_eq_zero_iff x).not.mpr hx)

/-- **Off-origin Biot--Savart kernel derivative.**  The coordinate derivative
of `z ↦ zⱼ/(4π|z|³)` is the trace-free Calderón--Zygmund tensor
`(4π)⁻¹(δᵢⱼ|z|⁻³ - 3zᵢzⱼ|z|⁻⁵)`.  The missing value at the origin is the
separate distributional local term in the principal-value formula. -/
theorem bsVectorKernel_coordinateLine_hasDerivAt
    {x : Space} (hx : x ≠ 0) (i j : Fin 3) :
    HasDerivAt (fun t : ℝ => bsVectorKernel (x + t • basisVector i) j)
      ((1 / (4 * Real.pi)) *
        ((basisVector i j) / officialEuclideanNorm x ^ 3 -
          3 * x i * x j / officialEuclideanNorm x ^ 5)) 0 := by
  have hnorm := officialEuclideanNorm_coordinateLine_hasDerivAt hx i
  have hnorm3 := hnorm.pow 3
  have hr : officialEuclideanNorm x ≠ 0 :=
    (officialEuclideanNorm_eq_zero_iff x).not.mpr hx
  have hinv := hnorm3.inv (by simpa using pow_ne_zero 3 hr)
  have hcoord : HasDerivAt (fun t : ℝ => (x + t • basisVector i) j)
      (basisVector i j) 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq, mul_one,
      add_zero, mul_comm] using
      ((hasDerivAt_id 0).mul_const (basisVector i j)).const_add (x j)
  have hproduct := hcoord.mul hinv
  have hscaled := hproduct.const_mul (1 / (4 * Real.pi))
  have hlocal : ∀ᶠ t : ℝ in nhds 0, x + t • basisVector i ≠ 0 := by
    have hcont : ContinuousAt (fun t : ℝ => x + t • basisVector i) 0 := by
      fun_prop
    exact hcont.eventually_ne (by simpa using hx)
  have hsame :
      (fun t : ℝ => bsVectorKernel (x + t • basisVector i) j) =ᶠ[nhds 0]
        (fun t : ℝ => (1 / (4 * Real.pi)) *
          ((x + t • basisVector i) j *
            (officialEuclideanNorm (x + t • basisVector i) ^ 3)⁻¹)) := by
    filter_upwards [hlocal] with t ht
    rw [bsVectorKernel, Pi.smul_apply, smul_eq_mul,
      bsKernelScalar_apply_of_ne_zero ht]
    simp only [one_div]
    ring
  have hscaled' := hscaled.congr_of_eventuallyEq hsame
  dsimp at hscaled'
  have heq :
      (1 / (4 * Real.pi)) *
          ((basisVector i j) / officialEuclideanNorm x ^ 3 -
            3 * x i * x j / officialEuclideanNorm x ^ 5) =
        1 / (4 * Real.pi) *
          (basisVector i j * (officialEuclideanNorm x ^ 3)⁻¹ +
            x j * (-(3 * officialEuclideanNorm x ^ 2 *
                  (x i / officialEuclideanNorm x)) /
                (officialEuclideanNorm x ^ 3) ^ 2)) := by
    simp only [one_div]
    field_simp
    ring
  rw [heq]
  simpa only [zero_smul, add_zero, zero_mul] using hscaled'

/-!
## Homogeneity of degree −3
-/

/-- **Degree-`(−3)` homogeneity of the Biot–Savart scalar kernel.**
`bsKernelScalar (c • x) = |c|⁻³ · bsKernelScalar x` for `c ≠ 0`, `x ≠ 0`. -/
theorem bsKernelScalar_homogeneous (c : ℝ) (x : Space) (hc : c ≠ 0) (hx : x ≠ 0) :
    bsKernelScalar (c • x) = |c|⁻¹ ^ 3 * bsKernelScalar x := by
  rw [bsKernelScalar_apply_of_ne_zero (smul_ne_zero hc hx),
      bsKernelScalar_apply_of_ne_zero hx,
      officialEuclideanNorm_smul, mul_pow]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnx : 0 < officialEuclideanNorm x := officialEuclideanNorm_pos_of_ne_zero hx
  have habs : 0 < |c| := abs_pos.mpr hc
  field_simp

/-!
## Off-diagonal decay bound
-/

/-- **The off-diagonal decay rate.**  For `x ≠ 0`, the scalar kernel is at most
`1/(π·|x|³)` (absorbing the `4π` into a constant for downstream estimates). -/
theorem bsKernelScalar_le {x : Space} (hx : x ≠ 0) :
    bsKernelScalar x ≤ 1 / (Real.pi * officialEuclideanNorm x ^ 3) := by
  rw [bsKernelScalar_apply_of_ne_zero hx]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnx : 0 < officialEuclideanNorm x := officialEuclideanNorm_pos_of_ne_zero hx
  have hnx3 : 0 < officialEuclideanNorm x ^ 3 := pow_pos hnx _
  have hL : 0 < 4 * Real.pi * officialEuclideanNorm x ^ 3 :=
    mul_pos (mul_pos (by norm_num) hpi) hnx3
  have hR : 0 < Real.pi * officialEuclideanNorm x ^ 3 := mul_pos hpi hnx3
  rw [div_le_div_iff₀ hL hR]
  nlinarith [hpi, hnx3]

/-!
## Far-field `L²` decay (pointwise squared bound)
-/

/-- **Pointwise squared bound.** `bsKernelScalar(x)² ≤ 1/(16π²·|x|⁶)` off the
origin — the degree-`(−6)` far-field decay that makes the kernel tail
`L¹`-integrable at infinity (radial integral `∫_r^∞ ρ²/ρ⁶ dρ < ∞`). -/
theorem bsKernelScalar_sq_le {x : Space} (hx : x ≠ 0) :
    bsKernelScalar x ^ 2 ≤ 1 / (16 * Real.pi ^ 2 * officialEuclideanNorm x ^ 6) := by
  rw [bsKernelScalar_apply_of_ne_zero hx]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnx : 0 < officialEuclideanNorm x := officialEuclideanNorm_pos_of_ne_zero hx
  -- both sides are equal: (1/(4π|x|³))² = 1/((4π|x|³)²) = 1/(16π²|x|⁶)
  have heq : (1 / (4 * Real.pi * officialEuclideanNorm x ^ 3)) ^ 2 =
      1 / (16 * Real.pi ^ 2 * officialEuclideanNorm x ^ 6) := by
    field_simp
    ring
  rw [heq]

end Navier.Analysis.BiotSavartKernel
