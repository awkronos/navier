import Navier.Analysis.BiotSavartKernel

/-!
# Calderón–Zygmund near-field cancellation: the Hörmander smoothness core

This file lands the first genuinely Mathlib-absent Calderón–Zygmund
infrastructure for homogeneous singular kernels on `ℝ³` (Stein, *Singular
Integrals and Differentiability Properties of Functions*, 1970, Ch. II §4;
Grafakos, *Classical Fourier Analysis*, §5.3): the **Hörmander smoothness
estimate** for the model degree-`(−3)` kernel and its consequence, the
**near-field cancellation bound** — the mechanism by which mean-zero data
converts the non-integrable `|x|⁻³` far-field decay of a Calderón–Zygmund
transform into the integrable `|x|⁻⁴` decay.

## Certified here (no sorry)

* `officialEuclideanNorm_add_le`, `officialEuclideanNorm_sub_le`,
  `abs_officialEuclideanNorm_sub_officialEuclideanNorm_le` — triangle-inequality
  API for the official Euclidean norm on `Space`.
* `cz_annulus_lower`, `cz_annulus_upper` — the far-field annulus geometry:
  `2|y| ≤ |x|` implies `|x|/2 ≤ |x−y| ≤ 3|x|/2`.
* `czScalarKernel` — the model scalar Calderón–Zygmund kernel `1/|x|³`, the
  magnitude envelope of the Biot–Savart *gradient* kernel
  `∂ᵢ(xⱼ/|x|³) = δᵢⱼ/|x|³ − 3xᵢxⱼ/|x|⁵` (every component is bounded in absolute
  value by `4·czScalarKernel`); its degree-`(−3)` homogeneity is certified.
* `czScalarKernel_hormander` — the **Hörmander / CZ smoothness condition**
  for the model kernel, with explicit constant:
  `|K(x−y) − K(x)| ≤ 38·|y|/|x|⁴` whenever `2|y| ≤ |x|`.
  The `|x|⁻⁴` decay is exactly what makes the Hörmander integral
  `∫_{|x| ≥ 2|y|} |K(x−y) − K(x)| dx` finite in dimension three
  (radial integral `∫ ρ²·ρ⁻⁴ dρ < ∞`).
* `cz_nearField_cancellation` — the **near-field cancellation estimate**:
  for integrable `f` with vanishing mean (`∫ f = 0`) supported in the ball
  `{|y − y₀| ≤ r}`, the model CZ transform
  `Tf(x) = ∫ K(x−y) f(y) dy` satisfies, at every `x` with `2r ≤ |x − y₀|`,

    `|Tf(x)| ≤ (38·r/|x−y₀|⁴)·‖f‖₁`.

  The mean-zero hypothesis is consumed exactly as in the classical proof:
  `Tf(x) = ∫ (K(x−y) − K(x−y₀)) f(y) dy`, upgrading the decay from
  `|x|⁻³` (not integrable at infinity on `ℝ³`) to `|x|⁻⁴` (integrable).
  Kernel-clean: the only hypotheses on `f` are integrability, mean zero,
  support, and the measurability/integrability side condition `hK_int`.

## Honest residual

Still open (genuinely Mathlib-absent): the Hörmander *integral* condition
`∫_{|x|≥2|y|} |K(x−y) − K(x)| dx ≤ C` via the annulus-shell argument
(the pointwise estimate here is its input), the weak-`(1,1)` bound, the
`L∞ → BMO` bound, and the Calderón–Zygmund stopping-time decomposition.
This file builds on `SingularIntegralPrelims.lean` /
`BiotSavartKernel.lean`, which name those residuals.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.CZNearField

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BiotSavartKernel

/-- Local helper: the Euclidean norm is strictly positive off the origin. -/
private theorem officialEuclideanNorm_pos_of_ne_zero {x : Space} (hx : x ≠ 0) :
    0 < officialEuclideanNorm x := by
  by_contra h
  push_neg at h
  have heq : officialEuclideanNorm x = 0 :=
    le_antisymm h (officialEuclideanNorm_nonneg x)
  exact hx ((officialEuclideanNorm_eq_zero_iff x).mp heq)

/-!
## Triangle-inequality API for the official Euclidean norm
-/

/-- Triangle inequality for the official Euclidean norm. -/
theorem officialEuclideanNorm_add_le (x y : Space) :
    officialEuclideanNorm (x + y) ≤ officialEuclideanNorm x + officialEuclideanNorm y := by
  have h : officialEuclideanPoint (x + y) =
      officialEuclideanPoint x + officialEuclideanPoint y := rfl
  rw [officialEuclideanNorm, officialEuclideanNorm, officialEuclideanNorm, h]
  exact norm_add_le _ _

/-- Subtraction form of the triangle inequality. -/
theorem officialEuclideanNorm_sub_le (x y : Space) :
    officialEuclideanNorm (x - y) ≤ officialEuclideanNorm x + officialEuclideanNorm y := by
  have h : officialEuclideanPoint (x - y) =
      officialEuclideanPoint x - officialEuclideanPoint y := rfl
  rw [officialEuclideanNorm, officialEuclideanNorm, officialEuclideanNorm, h]
  exact norm_sub_le _ _

/-- Reverse triangle inequality for the official Euclidean norm. -/
theorem abs_officialEuclideanNorm_sub_officialEuclideanNorm_le (x y : Space) :
    |officialEuclideanNorm x - officialEuclideanNorm y| ≤
      officialEuclideanNorm (x - y) := by
  have h : officialEuclideanPoint (x - y) =
      officialEuclideanPoint x - officialEuclideanPoint y := rfl
  rw [officialEuclideanNorm, officialEuclideanNorm, officialEuclideanNorm, h]
  exact abs_norm_sub_norm_le _ _

/-!
## The far-field annulus geometry
-/

/-- Lower annulus bound: if `2|y| ≤ |x|` then `|x|/2 ≤ |x−y|`. -/
theorem cz_annulus_lower {x y : Space}
    (h : 2 * officialEuclideanNorm y ≤ officialEuclideanNorm x) :
    officialEuclideanNorm x / 2 ≤ officialEuclideanNorm (x - y) := by
  have htri : officialEuclideanNorm x ≤
      officialEuclideanNorm (x - y) + officialEuclideanNorm y := by
    have h1 := officialEuclideanNorm_add_le (x - y) y
    rwa [sub_add_cancel] at h1
  linarith [officialEuclideanNorm_nonneg y]

/-- Upper annulus bound: if `2|y| ≤ |x|` then `|x−y| ≤ 3|x|/2`. -/
theorem cz_annulus_upper {x y : Space}
    (h : 2 * officialEuclideanNorm y ≤ officialEuclideanNorm x) :
    officialEuclideanNorm (x - y) ≤ 3 / 2 * officialEuclideanNorm x := by
  have h1 := officialEuclideanNorm_sub_le x y
  linarith [officialEuclideanNorm_nonneg y, officialEuclideanNorm_nonneg x]

/-!
## The model scalar Calderón–Zygmund kernel
-/

/-- The model scalar Calderón–Zygmund kernel `1/|x|³` off the origin
(`0` at the origin; the origin value is irrelevant to every convolution
integral).  This is the magnitude envelope of the Biot–Savart gradient
kernel `∂ᵢ(xⱼ/|x|³) = δᵢⱼ/|x|³ − 3xᵢxⱼ/|x|⁵`: each component of that matrix
kernel is bounded in absolute value by `4·czScalarKernel`. -/
def czScalarKernel (x : Space) : ℝ :=
  if x = 0 then 0 else 1 / officialEuclideanNorm x ^ 3

/-- Off the origin the model kernel equals `1/|x|³`. -/
theorem czScalarKernel_apply_of_ne_zero {x : Space} (hx : x ≠ 0) :
    czScalarKernel x = 1 / officialEuclideanNorm x ^ 3 := by
  rw [czScalarKernel, if_neg hx]

/-- The model kernel vanishes at the origin by definition. -/
theorem czScalarKernel_zero : czScalarKernel 0 = 0 := by
  rw [czScalarKernel, if_pos rfl]

/-- **Degree-`(−3)` homogeneity** of the model CZ kernel. -/
theorem czScalarKernel_homogeneous (c : ℝ) (x : Space) (hc : c ≠ 0) (hx : x ≠ 0) :
    czScalarKernel (c • x) = |c|⁻¹ ^ 3 * czScalarKernel x := by
  rw [czScalarKernel_apply_of_ne_zero (smul_ne_zero hc hx),
    czScalarKernel_apply_of_ne_zero hx, officialEuclideanNorm_smul, mul_pow]
  have hnx : 0 < officialEuclideanNorm x := officialEuclideanNorm_pos_of_ne_zero hx
  have habs : 0 < |c| := abs_pos.mpr hc
  field_simp

/-!
## The Hörmander smoothness estimate
-/

/-- **Hörmander smoothness of the model CZ kernel** (the Calderón–Zygmund
kernel condition of Stein 1970 Ch. II §4.2, Grafakos §5.3.1, for `1/|x|³`):
whenever `2|y| ≤ |x|`,

  `|K(x−y) − K(x)| ≤ 38·|y| / |x|⁴`.

The constant is explicit but crude; what matters is the `|x|⁻⁴` decay, one
power better than the kernel itself, which is precisely what makes the
Hörmander integral `∫_{|x|≥2|y|} |K(x−y) − K(x)| dx` finite on `ℝ³`. -/
theorem czScalarKernel_hormander {x y : Space}
    (h : 2 * officialEuclideanNorm y ≤ officialEuclideanNorm x) :
    |czScalarKernel (x - y) - czScalarKernel x| ≤
      38 * officialEuclideanNorm y / officialEuclideanNorm x ^ 4 := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hx0 : officialEuclideanNorm (0 : Space) = 0 :=
      (officialEuclideanNorm_eq_zero_iff 0).mpr rfl
    have hy : y = 0 := by
      by_contra hy
      have hpos := officialEuclideanNorm_pos_of_ne_zero hy
      rw [hx0] at h
      linarith
    subst hy
    simp [czScalarKernel_zero, sub_self, abs_zero, hx0]
  · have hxmy : x - y ≠ 0 := by
      intro hz
      have hz0 : officialEuclideanNorm (x - y) = 0 :=
        (officialEuclideanNorm_eq_zero_iff _).mpr hz
      have hlo := cz_annulus_lower h
      rw [hz0] at hlo
      have hpos := officialEuclideanNorm_pos_of_ne_zero hx
      linarith
    rw [czScalarKernel_apply_of_ne_zero hxmy, czScalarKernel_apply_of_ne_zero hx]
    set a := officialEuclideanNorm x with ha_def
    set b := officialEuclideanNorm (x - y) with hb_def
    have ha : 0 < a := officialEuclideanNorm_pos_of_ne_zero hx
    have hb_lo : a / 2 ≤ b := cz_annulus_lower h
    have hb : 0 < b := by linarith
    have hb_hi : b ≤ 3 / 2 * a := cz_annulus_upper h
    have hab : |a - b| ≤ officialEuclideanNorm y := by
      have h1 := abs_officialEuclideanNorm_sub_officialEuclideanNorm_le x (x - y)
      rwa [sub_sub_cancel] at h1
    have hsum_pos : 0 ≤ a ^ 2 + a * b + b ^ 2 := by positivity
    have hsum_le : a ^ 2 + a * b + b ^ 2 ≤ 19 / 4 * a ^ 2 := by
      nlinarith [ha.le, hb.le, mul_nonneg ha.le hb.le]
    have hnum : |a - b| * (a ^ 2 + a * b + b ^ 2) ≤
        officialEuclideanNorm y * (19 / 4 * a ^ 2) :=
      mul_le_mul hab hsum_le hsum_pos (officialEuclideanNorm_nonneg y)
    have hden_pos : 0 < a ^ 3 * b ^ 3 := by positivity
    have hb3 : (a / 2) ^ 3 ≤ b ^ 3 :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ a / 2) hb_lo 3
    have hden_lo : a ^ 6 / 8 ≤ a ^ 3 * b ^ 3 := by
      calc a ^ 6 / 8 = a ^ 3 * (a / 2) ^ 3 := by ring
        _ ≤ a ^ 3 * b ^ 3 :=
          mul_le_mul_of_nonneg_left hb3 (pow_nonneg ha.le 3)
    have ha3 : (a : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 ha.ne'
    have hb3' : (b : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hb.ne'
    have hdiff : 1 / b ^ 3 - 1 / a ^ 3 =
        (a - b) * (a ^ 2 + a * b + b ^ 2) / (a ^ 3 * b ^ 3) := by
      field_simp
      ring
    have habs : |1 / b ^ 3 - 1 / a ^ 3| =
        |a - b| * (a ^ 2 + a * b + b ^ 2) / (a ^ 3 * b ^ 3) := by
      rw [hdiff, abs_div, abs_mul, abs_of_nonneg hsum_pos, abs_of_pos hden_pos]
    rw [habs]
    have hnum'_nn : 0 ≤ officialEuclideanNorm y * (19 / 4 * a ^ 2) :=
      mul_nonneg (officialEuclideanNorm_nonneg y) (by positivity)
    have hstep : |a - b| * (a ^ 2 + a * b + b ^ 2) / (a ^ 3 * b ^ 3) ≤
        officialEuclideanNorm y * (19 / 4 * a ^ 2) / (a ^ 6 / 8) :=
      div_le_div₀ hnum'_nn hnum (by positivity) hden_lo
    refine hstep.trans (le_of_eq ?_)
    have ha6 : (a : ℝ) ^ 6 ≠ 0 := pow_ne_zero 6 ha.ne'
    field_simp
    ring

/-!
## Near-field cancellation
-/

/-- **Near-field cancellation for the model CZ kernel.**  Let `f` be
integrable with vanishing mean (`∫ f = 0`) and support in the ball
`{|y − y₀| ≤ r}`.  Then at every observation point `x` at distance at least
`2r` from the support center, the model Calderón–Zygmund transform
`Tf(x) = ∫ K(x−y) f(y) dy` satisfies

  `|Tf(x)| ≤ (38·r / |x−y₀|⁴)·∫ |f|`.

This is the classical mechanism (Stein 1970 Ch. II §4.4; Grafakos §5.3.2)
by which the mean-zero condition upgrades the far-field decay of a singular
integral from `|x|⁻³` — *not* integrable at infinity on `ℝ³` — to `|x|⁻⁴`,
which is.  The mean is consumed exactly once: `K(x−y₀)·∫ f = 0` lets the
transform be rewritten with the difference kernel `K(x−y) − K(x−y₀)`, to
which the Hörmander smoothness estimate applies. -/
theorem cz_nearField_cancellation
    {f : Space → ℝ} {y₀ : Space} {r : ℝ} (_hr : 0 ≤ r)
    (hf_int : Integrable f volume)
    (hf_mean : ∫ y, f y = 0)
    (hf_supp : ∀ y : Space, r < officialEuclideanNorm (y - y₀) → f y = 0)
    (hK_int : ∀ x : Space,
      Integrable (fun y => czScalarKernel (x - y) * f y) volume)
    {x : Space} (hx : 2 * r ≤ officialEuclideanNorm (x - y₀)) :
    |∫ y, czScalarKernel (x - y) * f y| ≤
      (38 * r / officialEuclideanNorm (x - y₀) ^ 4) * ∫ y, |f y| := by
  have hconst_int : Integrable (fun y => czScalarKernel (x - y₀) * f y) volume :=
    hf_int.const_mul _
  have hdiff_int :
      Integrable (fun y => (czScalarKernel (x - y) - czScalarKernel (x - y₀)) * f y)
        volume := by
    refine ((hK_int x).sub hconst_int).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    ring
  have hconst0 : ∫ y, czScalarKernel (x - y₀) * f y = 0 := by
    rw [integral_const_mul, hf_mean, mul_zero]
  have hsplit : ∫ y, czScalarKernel (x - y) * f y =
      ∫ y, (czScalarKernel (x - y) - czScalarKernel (x - y₀)) * f y := by
    have h1 : ∫ y, (czScalarKernel (x - y) - czScalarKernel (x - y₀)) * f y =
        ∫ y, (czScalarKernel (x - y) * f y - czScalarKernel (x - y₀) * f y) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [h1, integral_sub (hK_int x) hconst_int, hconst0, sub_zero]
  have hpoint : ∀ y : Space,
      |(czScalarKernel (x - y) - czScalarKernel (x - y₀)) * f y| ≤
        (38 * r / officialEuclideanNorm (x - y₀) ^ 4) * |f y| := by
    intro y
    by_cases hfy : f y = 0
    · simp [hfy]
    · have hyr : officialEuclideanNorm (y - y₀) ≤ r :=
        le_of_not_gt (fun hlt => hfy (hf_supp y hlt))
      have h2 : 2 * officialEuclideanNorm (y - y₀) ≤
          officialEuclideanNorm (x - y₀) := by linarith
      have hK := czScalarKernel_hormander (x := x - y₀) (y := y - y₀) h2
      rw [sub_sub_sub_cancel_right] at hK
      have hfac : 38 * officialEuclideanNorm (y - y₀) /
            officialEuclideanNorm (x - y₀) ^ 4 ≤
          38 * r / officialEuclideanNorm (x - y₀) ^ 4 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (by linarith)
          (inv_nonneg.mpr (pow_nonneg (officialEuclideanNorm_nonneg _) _))
      calc |(czScalarKernel (x - y) - czScalarKernel (x - y₀)) * f y|
          = |czScalarKernel (x - y) - czScalarKernel (x - y₀)| * |f y| :=
            abs_mul _ _
        _ ≤ (38 * r / officialEuclideanNorm (x - y₀) ^ 4) * |f y| :=
            mul_le_mul_of_nonneg_right (hK.trans hfac) (abs_nonneg _)
  calc |∫ y, czScalarKernel (x - y) * f y|
      = |∫ y, (czScalarKernel (x - y) - czScalarKernel (x - y₀)) * f y| := by
          rw [hsplit]
    _ ≤ ∫ y, |(czScalarKernel (x - y) - czScalarKernel (x - y₀)) * f y| := by
          have hnorm := norm_integral_le_integral_norm (μ := volume)
            (f := fun y => (czScalarKernel (x - y) - czScalarKernel (x - y₀)) * f y)
          simpa [Real.norm_eq_abs] using hnorm
    _ ≤ ∫ y, (38 * r / officialEuclideanNorm (x - y₀) ^ 4) * |f y| :=
          integral_mono_ae hdiff_int.abs (hf_int.abs.const_mul _)
            (Filter.Eventually.of_forall hpoint)
    _ = (38 * r / officialEuclideanNorm (x - y₀) ^ 4) * ∫ y, |f y| :=
          integral_const_mul _ _

/-!
## The Biot–Savart gradient kernel and its envelope
-/

/-- Coordinate domination: each coordinate is bounded by the Euclidean norm. -/
theorem coord_abs_le_officialEuclideanNorm (x : Space) (i : Fin 3) :
    |x i| ≤ officialEuclideanNorm x := by
  rw [officialEuclideanNorm_eq_sqrt_sum_sq]
  have h : |x i| ^ 2 ≤ ∑ j : Fin 3, |x j| ^ 2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 3 => |x j| ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc |x i| = Real.sqrt (|x i| ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_abs]
    _ ≤ Real.sqrt (∑ j : Fin 3, |x j| ^ 2) := Real.sqrt_le_sqrt h

/-- The **Biot–Savart gradient kernel** components
`Kᵢⱼ(x) = δᵢⱼ/|x|³ − 3·xᵢxⱼ/|x|⁵` off the origin (`0` at the origin).  This is
the matrix Calderón–Zygmund kernel of the velocity-gradient Biot–Savart law
`∂ᵢuⱼ = Kᵢⱼ * ω`-type convolutions on `ℝ³` (up to the skew-symmetric
vorticity contraction); every component is homogeneous of degree `−3`. -/
def bsGradKernel (i j : Fin 3) (x : Space) : ℝ :=
  if x = 0 then 0
  else (if i = j then (1 : ℝ) else 0) / officialEuclideanNorm x ^ 3
    - 3 * x i * x j / officialEuclideanNorm x ^ 5

/-- Off the origin the gradient kernel components are
`δᵢⱼ/|x|³ − 3xᵢxⱼ/|x|⁵`. -/
theorem bsGradKernel_apply_of_ne_zero {i j : Fin 3} {x : Space} (hx : x ≠ 0) :
    bsGradKernel i j x =
      (if i = j then (1 : ℝ) else 0) / officialEuclideanNorm x ^ 3
        - 3 * x i * x j / officialEuclideanNorm x ^ 5 := by
  rw [bsGradKernel, if_neg hx]

/-- **The gradient kernel is enveloped by the model CZ kernel**: every
component satisfies `|Kᵢⱼ(x)| ≤ 4·czScalarKernel(x)`.  This is the size
condition `|K(x)| ≤ A/|x|³` of the Calderón–Zygmund kernel hypotheses
(Stein 1970 Ch. II §4.2) for the Biot–Savart gradient kernel. -/
theorem bsGradKernel_abs_le (i j : Fin 3) (x : Space) :
    |bsGradKernel i j x| ≤ 4 * czScalarKernel x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [bsGradKernel, czScalarKernel_zero]
  · rw [bsGradKernel_apply_of_ne_zero hx, czScalarKernel_apply_of_ne_zero hx]
    set a := officialEuclideanNorm x with ha_def
    have ha : 0 < a := officialEuclideanNorm_pos_of_ne_zero hx
    have hi := coord_abs_le_officialEuclideanNorm x i
    have hj := coord_abs_le_officialEuclideanNorm x j
    have hδ1 : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by
      by_cases hij : i = j <;> simp [hij]
    have hδ : |(if i = j then (1 : ℝ) else 0) / a ^ 3| ≤ 1 / a ^ 3 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < a ^ 3)]
      exact div_le_div₀ (by norm_num) hδ1 (by positivity) le_rfl
    have hmul : |3 * x i * x j| = 3 * |x i| * |x j| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have h2 : 3 * |x i| * |x j| ≤ 3 * a * a :=
      mul_le_mul (by linarith) hj (abs_nonneg _) (by positivity)
    have hterm2 : |3 * x i * x j / a ^ 5| ≤ 3 / a ^ 3 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < a ^ 5), hmul]
      calc 3 * |x i| * |x j| / a ^ 5 ≤ 3 * a * a / a ^ 5 :=
            div_le_div₀ (by positivity) h2 (by positivity) le_rfl
        _ = 3 / a ^ 3 := by
            field_simp
    calc |(if i = j then (1 : ℝ) else 0) / a ^ 3 - 3 * x i * x j / a ^ 5|
        = |(if i = j then (1 : ℝ) else 0) / a ^ 3 + -(3 * x i * x j / a ^ 5)| :=
            congrArg abs (sub_eq_add_neg _ _)
      _ ≤ |(if i = j then (1 : ℝ) else 0) / a ^ 3| +
            |-(3 * x i * x j / a ^ 5)| := abs_add_le _ _
      _ = |(if i = j then (1 : ℝ) else 0) / a ^ 3| + |3 * x i * x j / a ^ 5| := by
            rw [abs_neg]
      _ ≤ 1 / a ^ 3 + 3 / a ^ 3 := add_le_add hδ hterm2
      _ = 4 * (1 / a ^ 3) := by ring

end Navier.Analysis.CZNearField
