import Navier.Analysis.RegularUniqueness

/-!
# The `L⁴` interpolation inequality `‖∇g‖⁴_{L⁴} ≤ 14 ‖g‖²_∞ ‖∇²g‖²_{L²}`

For a smooth scalar field `g` on `ℝ³` with `|g| ≤ G`, `∇g ∈ L² ∩ L⁴` and `∇²g ∈ L²`:

`∫ S² ≤ 14 G² ∑ᵢⱼ ∫ (∂ⱼ∂ᵢ g)²`,  `S = ∑ᵢ (∂ᵢ g)²`

(`l4_interpolation`).  Proof: one integration by parts,
`∫ S² = ∑ᵢ ∫ ∂ᵢg · (∂ᵢg S) = -∑ᵢ ∫ g ∂ᵢ(∂ᵢg S)`, the product rule
`∂ᵢ(∂ᵢg S) = ∂ᵢ∂ᵢg S + 2 ∂ᵢg ∑ⱼ ∂ⱼg ∂ᵢ∂ⱼg`, and pointwise AM–GM
`G |∂ᵢ(∂ᵢg S)|`-sum `≤ S²/2 + 7 G² ∑ (∂∂g)²`.

Applied to `g = ∂ₖuₗ` it gives `‖∇²u‖²_{L⁴} ≲ ‖∇u‖_∞ ‖∇³u‖_{L²}`, the middle-term bound of
the `H³` commutator estimate (damped `H³`, primitive 3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff

namespace Navier.Analysis.L4Interpolation

open Navier Navier.Analysis.RegularUniqueness

/-- First partials. -/
def a1 (g : Space → ℝ) (i : Fin 3) (x : Space) : ℝ := fderiv ℝ g x (basisVector i)

/-- Second partials `∂ⱼ∂ᵢ g`. -/
def b2 (g : Space → ℝ) (i j : Fin 3) (x : Space) : ℝ := fderiv ℝ (a1 g i) x (basisVector j)

/-- `S = |∇g|²`. -/
def S (g : Space → ℝ) (x : Space) : ℝ := ∑ i : Fin 3, a1 g i x ^ 2

/-- `H = |∇²g|²`. -/
def H (g : Space → ℝ) (x : Space) : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, b2 g i j x ^ 2

theorem S_nonneg (g : Space → ℝ) (x : Space) : 0 ≤ S g x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

theorem H_nonneg (g : Space → ℝ) (x : Space) : 0 ≤ H g x :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem sq_a1_le_S (g : Space → ℝ) (i : Fin 3) (x : Space) : a1 g i x ^ 2 ≤ S g x :=
  Finset.single_le_sum (f := fun i => a1 g i x ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)

theorem sq_b2_le_H (g : Space → ℝ) (i j : Fin 3) (x : Space) : b2 g i j x ^ 2 ≤ H g x := by
  unfold H
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j : Fin 3, b2 g i j x ^ 2)
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => b2 g i j x ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ j)

variable {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)

include hg in
theorem contDiff_a1 (i : Fin 3) : ContDiff ℝ ∞ (a1 g i) := cd_dir_s hg _

include hg in
theorem contDiff_S : ContDiff ℝ ∞ (S g) := by
  unfold S
  exact ContDiff.sum fun i _ => (contDiff_a1 hg i).pow 2

include hg in
theorem fderiv_S (i : Fin 3) (x : Space) :
    fderiv ℝ (S g) x (basisVector i) = ∑ j : Fin 3, 2 * a1 g j x * b2 g j i x := by
  have hd : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => a1 g j y ^ 2) x := fun j =>
    (((contDiff_a1 hg j).differentiable (by simp)) x).pow 2
  have e : S g = fun y => ∑ j : Fin 3, a1 g j y ^ 2 := rfl
  rw [e, fderiv_fun_sum (fun j _ => hd j), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_pow 2 (((contDiff_a1 hg j).differentiable (by simp)) x)]
  simp [b2]

include hg in
/-- The product rule for `∂ᵢ(∂ᵢg S)`. -/
theorem fderiv_aS (i : Fin 3) (x : Space) :
    fderiv ℝ (fun y => a1 g i y * S g y) x (basisVector i) =
      b2 g i i x * S g x + a1 g i x * ∑ j : Fin 3, 2 * a1 g j x * b2 g j i x := by
  rw [fderiv_fun_mul (((contDiff_a1 hg i).differentiable (by simp)) x)
    (((contDiff_S hg).differentiable (by simp)) x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fderiv_S hg i x]
  unfold b2
  ring

/-- The pointwise AM–GM budget. -/
theorem pointwise_budget {G : ℝ} (hG : 0 ≤ G) (x : Space) :
    G * ∑ i : Fin 3, |b2 g i i x * S g x + a1 g i x * ∑ j : Fin 3, 2 * a1 g j x * b2 g j i x|
      ≤ S g x ^ 2 / 2 + 7 * G ^ 2 * H g x := by
  have hS := S_nonneg g x
  have h1 : ∀ i : Fin 3, G * |b2 g i i x * S g x| ≤ S g x ^ 2 / 12 + 3 * G ^ 2 * b2 g i i x ^ 2 := by
    intro i
    rw [abs_mul, abs_of_nonneg hS]
    nlinarith [sq_nonneg (S g x / (2 * Real.sqrt 3) - Real.sqrt 3 * (G * |b2 g i i x|)),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), abs_nonneg (b2 g i i x), sq_abs (b2 g i i x),
      Real.sqrt_nonneg 3, sq_nonneg (S g x - 6 * G * |b2 g i i x|)]
  have h2 : ∀ i j : Fin 3, G * |a1 g i x * (2 * a1 g j x * b2 g j i x)| ≤
      (a1 g i x * a1 g j x) ^ 2 / 4 + 4 * G ^ 2 * b2 g j i x ^ 2 := by
    intro i j
    have e : |a1 g i x * (2 * a1 g j x * b2 g j i x)| = 2 * |a1 g i x * a1 g j x| * |b2 g j i x| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring
    rw [e]
    nlinarith [sq_nonneg (|a1 g i x * a1 g j x| / 2 - 2 * G * |b2 g j i x|),
      sq_abs (a1 g i x * a1 g j x), sq_abs (b2 g j i x)]
  have hSsq : ∑ i : Fin 3, ∑ j : Fin 3, (a1 g i x * a1 g j x) ^ 2 = S g x ^ 2 := by
    unfold S
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hdiag : ∑ i : Fin 3, b2 g i i x ^ 2 ≤ H g x := by
    unfold H
    refine Finset.sum_le_sum fun i _ => ?_
    exact Finset.single_le_sum (f := fun j => b2 g i j x ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hHswap : ∑ i : Fin 3, ∑ j : Fin 3, b2 g j i x ^ 2 = H g x := by
    unfold H; exact Finset.sum_comm
  calc G * ∑ i : Fin 3, |b2 g i i x * S g x + a1 g i x * ∑ j : Fin 3, 2 * a1 g j x * b2 g j i x|
      ≤ ∑ i : Fin 3, (G * |b2 g i i x * S g x| +
          ∑ j : Fin 3, G * |a1 g i x * (2 * a1 g j x * b2 g j i x)|) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.mul_sum, ← mul_add]
        refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) hG
        refine add_le_add le_rfl ?_
        rw [Finset.mul_sum]
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, ((S g x ^ 2 / 12 + 3 * G ^ 2 * b2 g i i x ^ 2) +
          ∑ j : Fin 3, ((a1 g i x * a1 g j x) ^ 2 / 4 + 4 * G ^ 2 * b2 g j i x ^ 2)) :=
        Finset.sum_le_sum fun i _ => add_le_add (h1 i) (Finset.sum_le_sum fun j _ => h2 i j)
    _ = S g x ^ 2 / 4 + 3 * G ^ 2 * ∑ i : Fin 3, b2 g i i x ^ 2 +
          (∑ i : Fin 3, ∑ j : Fin 3, (a1 g i x * a1 g j x) ^ 2) / 4 +
          4 * G ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, b2 g j i x ^ 2 := by
        simp only [Finset.sum_add_distrib, Fin.sum_univ_three]; ring
    _ ≤ S g x ^ 2 / 2 + 7 * G ^ 2 * H g x := by
        rw [hSsq, hHswap]
        nlinarith [hdiag, sq_nonneg G]

include hg in
/-- **The `L⁴` interpolation inequality.** -/
theorem l4_interpolation {G : ℝ} (hG0 : 0 ≤ G) (hG : ∀ x, |g x| ≤ G)
    (hS1 : Integrable (S g)) (hS2 : Integrable (fun x => S g x ^ 2))
    (hH : Integrable (H g)) :
    ∫ x, S g x ^ 2 ≤ 14 * G ^ 2 * ∫ x, H g x := by
  have hcg := hg.continuous
  have hca : ∀ i, Continuous (a1 g i) := fun i => (contDiff_a1 hg i).continuous
  have hcS : Continuous (S g) := (contDiff_S hg).continuous
  have hcb : ∀ i j, Continuous (b2 g i j) := fun i j => (cd_dir_s (contDiff_a1 hg i) _).continuous
  -- the integrand of the ibp
  set D : Fin 3 → Space → ℝ := fun i x =>
    b2 g i i x * S g x + a1 g i x * ∑ j : Fin 3, 2 * a1 g j x * b2 g j i x with hD
  have hcD : ∀ i, Continuous (D i) := fun i =>
    ((hcb i i).mul hcS).add ((hca i).mul (continuous_finsetSum _ fun j _ =>
      (continuous_const.mul (hca j)).mul (hcb j i)))
  have hDbound : ∀ i x, |D i x| ≤ S g x ^ 2 + 7 * H g x + S g x ^ 2 := by
    intro i x
    have hb := pointwise_budget (g := g) zero_le_one x
    have hle : |D i x| ≤ ∑ k : Fin 3, |D k x| :=
      Finset.single_le_sum (f := fun k => |D k x|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    simp only [one_mul, one_pow] at hb
    have := S_nonneg g x
    nlinarith [H_nonneg g x, sq_nonneg (S g x)]
  have hDint : ∀ i, Integrable (D i) := fun i =>
    (((hS2.add (hH.const_mul 7)).add hS2)).mono' (hcD i).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hDbound i x)
  have hgD : ∀ i, Integrable (fun x => g x * D i x) := fun i =>
    ((hDint i).norm.const_mul G).mono' (hcg.mul (hcD i)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hG x) (abs_nonneg _))
  have haaS : ∀ i, Integrable (fun x => a1 g i x * (a1 g i x * S g x)) := fun i =>
    hS2.mono' ((hca i).mul ((hca i).mul hcS)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, ← mul_assoc, ← sq, abs_of_nonneg (mul_nonneg (sq_nonneg _)
          (S_nonneg g x)), sq (S g x)]
        exact mul_le_mul_of_nonneg_right (sq_a1_le_S g i x) (S_nonneg g x))
  have hB : Integrable (fun x => G * ((S g x + S g x ^ 2) / 2)) :=
    ((hS1.add hS2).div_const 2).const_mul G
  have hgaS : ∀ i, Integrable (fun x => g x * (a1 g i x * S g x)) := fun i =>
    hB.mono' (hcg.mul ((hca i).mul hcS)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        show ‖g x * (a1 g i x * S g x)‖ ≤ G * ((S g x + S g x ^ 2) / 2)
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (S_nonneg g x)]
        have hS0 := S_nonneg g x
        refine mul_le_mul (hG x) ?_ (mul_nonneg (abs_nonneg _) hS0) hG0
        nlinarith [sq_a1_le_S g i x, sq_abs (a1 g i x), sq_nonneg (|a1 g i x| - S g x),
          abs_nonneg (a1 g i x)])
  -- the integration by parts
  have hibp : ∀ i, ∫ x, a1 g i x * (a1 g i x * S g x) = -∫ x, g x * D i x := by
    intro i
    have hd : ∀ x, fderiv ℝ (fun y => a1 g i y * S g y) x (basisVector i) = D i x :=
      fun x => fderiv_aS hg i x
    have h := ibp (f := g) (g := fun y => a1 g i y * S g y) (hg.of_le (by simp))
      (((contDiff_a1 hg i).mul (contDiff_S hg)).of_le (by simp)) (basisVector i) (haaS i)
      (by simp_rw [hd]; exact hgD i) (hgaS i)
    simp_rw [hd] at h
    rw [h, neg_neg]
    rfl
  have hsum : ∫ x, S g x ^ 2 = ∑ i : Fin 3, ∫ x, a1 g i x * (a1 g i x * S g x) := by
    rw [← integral_finsetSum _ fun i _ => haaS i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show S g x ^ 2 = ∑ i : Fin 3, a1 g i x * (a1 g i x * S g x)
    unfold S
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hn : ∀ i, Integrable (fun x => -(g x * D i x)) := fun i => (hgD i).neg
  have e : ∑ i : Fin 3, -∫ x, g x * D i x = ∫ x, ∑ i : Fin 3, -(g x * D i x) := by
    rw [integral_finsetSum _ fun i _ => hn i]
    simp_rw [integral_neg]
  have hbound : ∫ x, ∑ i : Fin 3, -(g x * D i x) ≤ ∫ x, (S g x ^ 2 / 2 + 7 * G ^ 2 * H g x) := by
    refine integral_mono ((integrable_finsetSum _ fun i _ => hn i))
      ((hS2.div_const 2).add (hH.const_mul _)) fun x => ?_
    have hb := pointwise_budget (g := g) hG0 x
    calc ∑ i : Fin 3, -(g x * D i x) ≤ ∑ i : Fin 3, G * |D i x| :=
          Finset.sum_le_sum fun i _ => by
            have h1 := neg_le_abs (g x * D i x)
            rw [abs_mul] at h1
            nlinarith [mul_le_mul_of_nonneg_right (hG x) (abs_nonneg (D i x))]
      _ = G * ∑ i : Fin 3, |D i x| := by rw [Finset.mul_sum]
      _ ≤ _ := hb
  have hX : ∫ x, S g x ^ 2 = ∑ i : Fin 3, -∫ x, g x * D i x :=
    hsum.trans (Finset.sum_congr rfl fun i _ => hibp i)
  have hB' : ∫ x, (S g x ^ 2 / 2 + 7 * G ^ 2 * H g x) =
      (∫ x, S g x ^ 2) / 2 + 7 * G ^ 2 * ∫ x, H g x := by
    rw [integral_add (hS2.div_const 2) (hH.const_mul _), integral_div, integral_const_mul]
  linarith [hbound, hX, hB', e]

end Navier.Analysis.L4Interpolation

set_option pp.fullNames true in
#print axioms Navier.Analysis.L4Interpolation.l4_interpolation
