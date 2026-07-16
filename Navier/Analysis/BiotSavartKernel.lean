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
