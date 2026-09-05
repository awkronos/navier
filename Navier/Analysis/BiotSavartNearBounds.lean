import Navier.Analysis.BiotSavartKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Locally integrable cancellation weight for the Biot--Savart kernel

The degree `-3` scalar kernel becomes locally integrable after multiplication
by one power of the radius.  A dyadic shell decomposition gives the explicit
linear-in-radius bound used by sharp/smooth truncation comparison.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.BealeKatoMajda

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.OfficialABEncoding

private theorem continuous_officialEuclideanNorm :
    Continuous officialEuclideanNorm := by
  rw [show officialEuclideanNorm = fun x : Space =>
      Real.sqrt (∑ k : Fin 3, |x k| ^ 2) by
    funext x
    exact officialEuclideanNorm_eq_sqrt_sum_sq x]
  fun_prop

/-- The globally defined scalar Biot--Savart kernel is measurable. -/
theorem measurable_bsKernelScalar : Measurable bsKernelScalar := by
  have h : bsKernelScalar =
      fun z : Space => 1 / (4 * Real.pi * officialEuclideanNorm z ^ 3) := by
    funext z
    by_cases hz : z = 0
    · subst hz
      rw [bsKernelScalar_zero]
      simp [officialEuclideanNorm, officialEuclideanPoint]
    · rw [bsKernelScalar_apply_of_ne_zero hz]
  rw [h]
  exact measurable_const.div
    (measurable_const.mul ((continuous_officialEuclideanNorm.pow 3).measurable))

/-- **The actual Hölder-`1/4` near-field kernel is locally integrable.**

After Morrey cancellation, the singular factor is
`|z|^(1/4) |z|^(-3) = |z|^(-11/4)`.  Since `11/4 < 3`, the finite-dimensional
power-integrability criterion applies on every ball.  This is the precise
integrability input used when `exists_agmonMorreyBound` is paired with the
Biot–Savart kernel; the previously certified `|z|`-weighted estimate alone
does not imply this fractional endpoint near the origin. -/
theorem integrableOn_norm_rpow_oneFourth_mul_bsKernelScalar_ball (ρ : ℝ) :
    IntegrableOn
      (fun z : Space => ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z)
      (Metric.ball 0 ρ) volume := by
  apply integrableOn_ball_of_norm_le_rpow
    (E := Space) (F := ℝ) (C := 1 / (4 * Real.pi))
      (by simp) (by norm_num : (11 : ℝ) / 4 < Module.finrank ℝ Space)
  · filter_upwards with z
    by_cases hz : z = 0
    · subst z
      simp [bsKernelScalar_zero]
    · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hoge : ‖z‖ ≤ officialEuclideanNorm z := norm_le_officialEuclideanNorm z
      have hden : 4 * Real.pi * ‖z‖ ^ 3 ≤
          4 * Real.pi * officialEuclideanNorm z ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hoge 3) (by positivity)
      rw [Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _)
          (bsKernelScalar_nonneg z)), bsKernelScalar_apply_of_ne_zero hz]
      calc
        ‖z‖ ^ ((1 : ℝ) / 4) *
              (1 / (4 * Real.pi * officialEuclideanNorm z ^ 3)) ≤
            ‖z‖ ^ ((1 : ℝ) / 4) * (1 / (4 * Real.pi * ‖z‖ ^ 3)) :=
          mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (by positivity) hden)
            (Real.rpow_nonneg (norm_nonneg z) _)
        _ = (1 / (4 * Real.pi)) * ‖z‖ ^ (-((11 : ℝ) / 4)) := by
          rw [show ‖z‖ ^ (3 : ℕ) = ‖z‖ ^ (3 : ℝ) by
            exact (Real.rpow_natCast ‖z‖ 3).symm]
          calc
            ‖z‖ ^ ((1 : ℝ) / 4) *
                (1 / (4 * Real.pi * ‖z‖ ^ (3 : ℝ))) =
              (1 / (4 * Real.pi)) *
                (‖z‖ ^ ((1 : ℝ) / 4) * (‖z‖ ^ (3 : ℝ))⁻¹) := by ring
            _ = (1 / (4 * Real.pi)) * ‖z‖ ^ (-((11 : ℝ) / 4)) := by
              rw [← Real.rpow_neg hn.le, ← Real.rpow_add hn]
              norm_num
  · have hpowMeas : Measurable (fun z : Space => ‖z‖ ^ ((1 : ℝ) / 4)) :=
      (continuous_norm.rpow_const fun _ => Or.inr (by norm_num)).measurable
    exact (hpowMeas.mul measurable_bsKernelScalar).aestronglyMeasurable

/-- The fractional Morrey-weighted kernel is homogeneous of degree `-11/4`.
This is the scaling identity behind the sharp `ρ^(1/4)` near-field mass. -/
theorem norm_rpow_oneFourth_mul_bsKernelScalar_smul
    {ρ : ℝ} (hρ : 0 < ρ) (z : Space) :
    ‖ρ • z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar (ρ • z) =
      ρ ^ (-((11 : ℝ) / 4)) *
        (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
  by_cases hz : z = 0
  · subst z
    simp [bsKernelScalar_zero]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
      bsKernelScalar_homogeneous ρ z hρ.ne' hz, abs_of_pos hρ,
      Real.mul_rpow hρ.le (norm_nonneg z)]
    have hinv : ρ⁻¹ ^ (3 : ℕ) = ρ ^ (-(3 : ℝ)) := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hρ.le]
      norm_num
    rw [hinv]
    calc
      ρ ^ ((1 : ℝ) / 4) * ‖z‖ ^ ((1 : ℝ) / 4) *
          (ρ ^ (-(3 : ℝ)) * bsKernelScalar z) =
          (ρ ^ ((1 : ℝ) / 4) * ρ ^ (-(3 : ℝ))) *
            (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by ring
      _ = ρ ^ (-((11 : ℝ) / 4)) *
          (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
        rw [← Real.rpow_add hρ]
        norm_num

/-- **Sharp fractional near-field mass.**  The degree-`-11/4` weighted
Biot–Savart kernel has exactly the dimensionally predicted ball scaling
`I(ρ) = ρ^(1/4) I(1)`. -/
theorem integral_norm_rpow_oneFourth_mul_bsKernelScalar_ball_eq
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ z in Metric.ball (0 : Space) ρ,
        ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) =
      ρ ^ ((1 : ℝ) / 4) *
        ∫ z in Metric.ball (0 : Space) 1,
          ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z := by
  let f : Space → ℝ :=
    fun z => ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z
  have hchange := Measure.setIntegral_comp_smul_of_pos volume f
    (Metric.ball (0 : Space) 1) hρ
  rw [smul_unitBall_of_pos hρ] at hchange
  simp only [f, norm_rpow_oneFourth_mul_bsKernelScalar_smul hρ] at hchange
  rw [MeasureTheory.integral_const_mul] at hchange
  have hd : Module.finrank ℝ Space = 3 := by simp
  simp only [hd, smul_eq_mul] at hchange
  have hρ3 : ρ ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hρ.ne'
  have hcoeff : ρ ^ (3 : ℝ) * ρ ^ (-((11 : ℝ) / 4)) =
      ρ ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hρ]
    norm_num
  calc
    (∫ z in Metric.ball (0 : Space) ρ,
        ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) =
        ρ ^ (3 : ℕ) * ((ρ ^ (3 : ℕ))⁻¹ *
          ∫ z in Metric.ball (0 : Space) ρ,
            ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
          field_simp
    _ = ρ ^ (3 : ℕ) *
        (ρ ^ (-((11 : ℝ) / 4)) *
          ∫ z in Metric.ball (0 : Space) 1,
            ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
          rw [← hchange]
    _ = ρ ^ ((1 : ℝ) / 4) *
        ∫ z in Metric.ball (0 : Space) 1,
          ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z := by
          rw [show ρ ^ (3 : ℕ) = ρ ^ (3 : ℝ) by
            exact (Real.rpow_natCast ρ 3).symm]
          rw [← mul_assoc, hcoeff]

/-- **Hölder cancellation makes the Biot–Savart near-field convolution
integrable.**  This is the direct consumer form of
`integrableOn_norm_rpow_oneFourth_mul_bsKernelScalar_ball`: any strongly
measurable vector difference bounded by `H·|z|^(1/4)` can be multiplied by the
degree-`-3` kernel on a ball. -/
theorem integrableOn_bsKernelScalar_smul_of_holder
    (F : Space → Space) (H ρ : ℝ) (hH : 0 ≤ H)
    (hF : AEStronglyMeasurable F volume)
    (hholder : ∀ z, ‖F z‖ ≤ H * ‖z‖ ^ ((1 : ℝ) / 4)) :
    IntegrableOn (fun z => bsKernelScalar z • F z) (Metric.ball 0 ρ) volume := by
  have hbase :=
    (integrableOn_norm_rpow_oneFourth_mul_bsKernelScalar_ball ρ).const_mul H
  refine hbase.mono' ?_ ?_
  · exact (measurable_bsKernelScalar.aestronglyMeasurable.smul hF).restrict
  · filter_upwards with z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (bsKernelScalar_nonneg z)]
    have hknn := bsKernelScalar_nonneg z
    have hleft := mul_le_mul_of_nonneg_left (hholder z) hknn
    calc
      bsKernelScalar z * ‖F z‖ ≤
          bsKernelScalar z * (H * ‖z‖ ^ ((1 : ℝ) / 4)) := hleft
      _ = |H| * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
        rw [abs_of_nonneg hH]
        ring
      _ = H * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
        rw [abs_of_nonneg hH]

/-- **Quantitative Hölder near-field convolution bound.**  A vector
difference controlled by `H·|z|^(1/4)` contributes at most the universal
unit-ball weighted-kernel mass times `H·ρ^(1/4)`.  This is the precise
near-field estimate consumed by `exists_biotSavartKernelSplitting` once the
principal-value Biot–Savart representation supplies the difference. -/
theorem integral_norm_bsKernelScalar_smul_of_holder_le
    (F : Space → Space) (H : ℝ) {ρ : ℝ} (hH : 0 ≤ H) (hρ : 0 < ρ)
    (hF : AEStronglyMeasurable F volume)
    (hholder : ∀ z, ‖F z‖ ≤ H * ‖z‖ ^ ((1 : ℝ) / 4)) :
    (∫ z in Metric.ball (0 : Space) ρ,
        ‖bsKernelScalar z • F z‖) ≤
      H * ρ ^ ((1 : ℝ) / 4) *
        ∫ z in Metric.ball (0 : Space) 1,
          ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z := by
  have hleft : IntegrableOn (fun z => ‖bsKernelScalar z • F z‖)
      (Metric.ball (0 : Space) ρ) volume :=
    (integrableOn_bsKernelScalar_smul_of_holder F H ρ hH hF hholder).norm
  have hright : IntegrableOn
      (fun z : Space => H * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z))
      (Metric.ball (0 : Space) ρ) volume :=
    (integrableOn_norm_rpow_oneFourth_mul_bsKernelScalar_ball ρ).const_mul H
  calc
    (∫ z in Metric.ball (0 : Space) ρ,
        ‖bsKernelScalar z • F z‖) ≤
        ∫ z in Metric.ball (0 : Space) ρ,
          H * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
      refine setIntegral_mono_on hleft hright Metric.isOpen_ball.measurableSet ?_
      intro z _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (bsKernelScalar_nonneg z)]
      calc
        bsKernelScalar z * ‖F z‖ ≤
            bsKernelScalar z * (H * ‖z‖ ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (hholder z) (bsKernelScalar_nonneg z)
        _ = H * (‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by ring
    _ = H * (∫ z in Metric.ball (0 : Space) ρ,
          ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
      rw [MeasureTheory.integral_const_mul]
    _ = H * (ρ ^ ((1 : ℝ) / 4) *
          ∫ z in Metric.ball (0 : Space) 1,
            ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z) := by
      rw [integral_norm_rpow_oneFourth_mul_bsKernelScalar_ball_eq hρ]
    _ = H * ρ ^ ((1 : ℝ) / 4) *
          ∫ z in Metric.ball (0 : Space) 1,
            ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z := by ring


/-- The dyadic shell with radii in `(ρ/2^(k+1), ρ/2^k]`. -/
def czShell (ρ : ℝ) (k : ℕ) : Set Space :=
  Metric.ball 0 ρ ∩ {z : Space | ρ / 2 ^ (k + 1) < ‖z‖ ∧ ‖z‖ ≤ ρ / 2 ^ k}

theorem measurableSet_czShell (ρ : ℝ) (k : ℕ) : MeasurableSet (czShell ρ k) :=
  (Metric.isOpen_ball.measurableSet).inter
    ((measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const))

theorem czShell_disjoint {ρ : ℝ} (hρ : 0 < ρ) :
    Pairwise (Function.onFun Disjoint (czShell ρ)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · refine Set.disjoint_left.mpr fun z hzi hzj => ?_
    obtain ⟨-, hlo, -⟩ := hzi
    obtain ⟨-, -, hhi⟩ := hzj
    have hj : ρ / 2 ^ j ≤ ρ / 2 ^ (i + 1) := by
      apply div_le_div_of_nonneg_left hρ.le (by positivity)
      exact pow_le_pow_right₀ one_le_two (by omega)
    linarith
  · refine Set.disjoint_left.mpr fun z hzi hzj => ?_
    obtain ⟨-, -, hhi⟩ := hzi
    obtain ⟨-, hlo, -⟩ := hzj
    have hj : ρ / 2 ^ i ≤ ρ / 2 ^ (j + 1) := by
      apply div_le_div_of_nonneg_left hρ.le (by positivity)
      exact pow_le_pow_right₀ one_le_two (by omega)
    linarith

theorem ball_subset_iUnion_czShell {ρ : ℝ} (_hρ : 0 < ρ) :
    Metric.ball (0 : Space) ρ ⊆ insert 0 (⋃ k, czShell ρ k) := by
  classical
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    exact mem_insert 0 _
  · rw [mem_insert_iff]
    right
    rw [mem_iUnion]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hlt : ‖z‖ < ρ := by rwa [Metric.mem_ball, dist_zero_right] at hz
    obtain ⟨m, hm⟩ := add_one_pow_unbounded_of_pos (ρ / ‖z‖) one_pos
    rw [show (1 : ℝ) + 1 = 2 from one_add_one_eq_two] at hm
    have hex : ∃ n : ℕ, ρ / ‖z‖ < 2 ^ n := ⟨m, hm⟩
    have hspec : ρ / ‖z‖ < 2 ^ Nat.find hex := Nat.find_spec hex
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · exfalso
        rw [h, pow_zero] at hspec
        have hgt : 1 < ρ / ‖z‖ := by rwa [one_lt_div hn]
        linarith
      · exact h
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hle : 2 ^ k ≤ ρ / ‖z‖ := le_of_not_gt fun hcon => by
      have hmin := Nat.find_min' hex hcon
      omega
    refine ⟨k, ⟨hz, ?_, ?_⟩⟩
    · rw [hk] at hspec
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (k + 1))]
      rw [div_lt_iff₀ hn] at hspec
      rw [mul_comm]
      exact hspec
    · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)]
      rw [le_div_iff₀ hn] at hle
      rw [mul_comm]
      exact hle

theorem ball_eq_insert_iUnion_czShell {ρ : ℝ} (hρ : 0 < ρ) :
    Metric.ball (0 : Space) ρ = insert 0 (⋃ k, czShell ρ k) := by
  apply Subset.antisymm (ball_subset_iUnion_czShell hρ)
  rw [insert_subset_iff]
  refine ⟨Metric.mem_ball_self hρ, ?_⟩
  rw [iUnion_subset_iff]
  exact fun k z hz => hz.1

theorem czShell_pointwise_le {ρ : ℝ} (hρ : 0 < ρ) {k : ℕ} {z : Space}
    (hz : z ∈ czShell ρ k) :
    ‖z‖ * bsKernelScalar z ≤ 4 ^ k / (Real.pi * ρ ^ 2) := by
  obtain ⟨-, hlo, -⟩ := hz
  have hn : 0 < ‖z‖ := lt_trans (by positivity) hlo
  rw [bsKernelScalar_apply_of_ne_zero (norm_pos_iff.mp hn)]
  have hoge := norm_le_officialEuclideanNorm z
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
  have hle1 : ‖z‖ * (1 / (4 * Real.pi * officialEuclideanNorm z ^ 3))
      ≤ ‖z‖ * (1 / (4 * Real.pi * ‖z‖ ^ 3)) :=
    mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hoge 3) (by positivity)))
      hn.le
  have heq : ‖z‖ * (1 / (4 * Real.pi * ‖z‖ ^ 3)) =
      1 / (4 * Real.pi * ‖z‖ ^ 2) := by
    field_simp
  have hden : 4 * Real.pi * (ρ / 2 ^ (k + 1)) ^ 2 ≤
      4 * Real.pi * ‖z‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlo.le 2) (by positivity)
  calc
    ‖z‖ * (1 / (4 * Real.pi * officialEuclideanNorm z ^ 3))
        ≤ ‖z‖ * (1 / (4 * Real.pi * ‖z‖ ^ 3)) := hle1
    _ = 1 / (4 * Real.pi * ‖z‖ ^ 2) := heq
    _ ≤ 1 / (4 * Real.pi * (ρ / 2 ^ (k + 1)) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = 4 ^ k / (Real.pi * ρ ^ 2) := by
      have h42 : ((2 : ℝ) ^ (k + 1)) ^ 2 = 4 ^ (k + 1) := by
        rw [← pow_mul, show (k + 1) * 2 = 2 * (k + 1) from by ring, pow_mul]
        norm_num
      have h40 : (4 : ℝ) ^ (k + 1) ≠ 0 := by positivity
      rw [div_pow, h42]
      field_simp
      ring

theorem czShell_const_mul {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    (4 : ℝ) ^ k / (Real.pi * ρ ^ 2) * (ρ / 2 ^ k) ^ 3
      = (1 / 2) ^ k * ρ / Real.pi := by
  have h4 : (4 : ℝ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have e3 : (2 : ℝ) ^ (3 * k) = 2 ^ (2 * k) * 2 ^ k := by
    rw [show 3 * k = 2 * k + k by ring, pow_add]
  rw [div_pow, ← pow_mul, mul_comm k 3, e3, h4, one_div_pow]
  field_simp [hρ.ne', Real.pi_ne_zero, pow_ne_zero _ (two_ne_zero : (2 : ℝ) ≠ 0)]

theorem volume_czShell_le {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    volume (czShell ρ k) ≤
      ENNReal.ofReal ((ρ / 2 ^ k) ^ 3) * volume (Metric.ball (0 : Space) 1) := by
  have hd : Module.finrank ℝ Space = 3 := by simp
  calc
    volume (czShell ρ k) ≤ volume (Metric.closedBall (0 : Space) (ρ / 2 ^ k)) :=
      measure_mono fun z hz => mem_closedBall_zero_iff.mpr hz.2.2
    _ = ENNReal.ofReal ((ρ / 2 ^ k) ^ 3) *
          volume (Metric.closedBall (0 : Space) 1) := by
      have h := Measure.addHaar_closedBall_mul volume (0 : Space)
        (show (0 : ℝ) ≤ ρ / 2 ^ k by positivity) (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
      rw [mul_one, hd] at h
      exact h
    _ = ENNReal.ofReal ((ρ / 2 ^ k) ^ 3) * volume (Metric.ball (0 : Space) 1) := by
      rw [Measure.addHaar_closedBall_eq_addHaar_ball]

theorem setLIntegral_czShell_le {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    ∫⁻ z in czShell ρ k, ENNReal.ofReal (‖z‖ * bsKernelScalar z) ∂volume
      ≤ ENNReal.ofReal (4 ^ k / (Real.pi * ρ ^ 2)) * volume (czShell ρ k) :=
  calc
    ∫⁻ z in czShell ρ k, ENNReal.ofReal (‖z‖ * bsKernelScalar z) ∂volume
        ≤ ∫⁻ _ in czShell ρ k,
            ENNReal.ofReal (4 ^ k / (Real.pi * ρ ^ 2)) ∂volume :=
      setLIntegral_mono measurable_const fun _z hz =>
        ENNReal.ofReal_le_ofReal (czShell_pointwise_le hρ hz)
    _ = _ := setLIntegral_const _ _

theorem volume_singleton_zero_space : volume ({0} : Set Space) = 0 := by
  simp

theorem lintegral_norm_mul_bsKernelScalar_ball_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ z in Metric.ball (0 : Space) ρ,
        ENNReal.ofReal (‖z‖ * bsKernelScalar z) ∂volume
      ≤ ENNReal.ofReal (2 * ρ / Real.pi) * volume (Metric.ball (0 : Space) 1) := by
  have hdisj0 : Disjoint ({0} : Set Space) (⋃ k, czShell ρ k) := by
    rw [disjoint_singleton_left]
    simp only [mem_iUnion, not_exists]
    intro k hk
    obtain ⟨-, hlo, -⟩ := hk
    simp at hlo
    have hpos2 : (0 : ℝ) < ρ / 2 ^ (k + 1) := by positivity
    linarith
  rw [ball_eq_insert_iUnion_czShell hρ, insert_eq]
  rw [lintegral_union (MeasurableSet.iUnion (measurableSet_czShell ρ)) hdisj0]
  rw [lintegral_singleton, volume_singleton_zero_space, mul_zero, zero_add]
  rw [lintegral_iUnion (fun k => measurableSet_czShell ρ k) (czShell_disjoint hρ)]
  calc
    ∑' k, ∫⁻ z in czShell ρ k,
        ENNReal.ofReal (‖z‖ * bsKernelScalar z) ∂volume
        ≤ ∑' k, ENNReal.ofReal ((1 / 2) ^ k * ρ / Real.pi) *
            volume (Metric.ball (0 : Space) 1) := by
      apply ENNReal.tsum_le_tsum
      intro k
      calc
        ∫⁻ z in czShell ρ k, ENNReal.ofReal (‖z‖ * bsKernelScalar z) ∂volume
            ≤ ENNReal.ofReal (4 ^ k / (Real.pi * ρ ^ 2)) * volume (czShell ρ k) :=
          setLIntegral_czShell_le hρ k
        _ ≤ ENNReal.ofReal (4 ^ k / (Real.pi * ρ ^ 2)) *
              (ENNReal.ofReal ((ρ / 2 ^ k) ^ 3) *
                volume (Metric.ball (0 : Space) 1)) :=
          mul_le_mul_of_nonneg_left (volume_czShell_le hρ k) zero_le
        _ = ENNReal.ofReal ((1 / 2) ^ k * ρ / Real.pi) *
              volume (Metric.ball (0 : Space) 1) := by
          rw [← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          exact czShell_const_mul hρ k
    _ = ENNReal.ofReal (2 * ρ / Real.pi) * volume (Metric.ball (0 : Space) 1) := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      have hsumm : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k * (ρ / Real.pi) :=
        summable_geometric_two.mul_right _
      have hcongr : (fun k : ℕ => ENNReal.ofReal ((1 / 2) ^ k * ρ / Real.pi)) =
          fun k => ENNReal.ofReal ((1 / 2) ^ k * (ρ / Real.pi)) := by
        funext k
        rw [mul_div_assoc]
      rw [hcongr, ← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm]
      congr 1
      rw [tsum_mul_right, tsum_geometric_two, mul_div_assoc]

/-- The first-order cancellation factor makes the scalar kernel integrable on
every positive-radius ball. -/
theorem integrableOn_norm_mul_bsKernelScalar_ball {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun z : Space => ‖z‖ * bsKernelScalar z)
      (Metric.ball 0 ρ) volume := by
  have hfm : Measurable (fun z : Space => ‖z‖ * bsKernelScalar z) :=
    continuous_norm.measurable.mul measurable_bsKernelScalar
  have hnn : ∀ z : Space, 0 ≤ ‖z‖ * bsKernelScalar z :=
    fun z => mul_nonneg (norm_nonneg _) (bsKernelScalar_nonneg z)
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  exact lt_of_le_of_lt (lintegral_norm_mul_bsKernelScalar_ball_le hρ)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Space)) (r := 1)))

/-- Explicit linear mass bound for the cancellation-weighted kernel. -/
theorem integral_norm_mul_bsKernelScalar_ball_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ z in Metric.ball (0 : Space) ρ, ‖z‖ * bsKernelScalar z
      ≤ 2 * (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi * ρ := by
  have hnn : ∀ z : Space, 0 ≤ ‖z‖ * bsKernelScalar z :=
    fun z => mul_nonneg (norm_nonneg _) (bsKernelScalar_nonneg z)
  have hfm : Measurable (fun z : Space => ‖z‖ * bsKernelScalar z) :=
    continuous_norm.measurable.mul measurable_bsKernelScalar
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hnn) hfm.aestronglyMeasurable]
  have htop : (∫⁻ z in Metric.ball (0 : Space) ρ,
      ENNReal.ofReal (‖z‖ * bsKernelScalar z) ∂volume) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ball_lt_top (μ := volume) (x := (0 : Space)) (r := 1)).ne)
      (lintegral_norm_mul_bsKernelScalar_ball_le hρ)
  have htop2 : (ENNReal.ofReal (2 * ρ / Real.pi) *
      volume (Metric.ball (0 : Space) 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Space)) (r := 1)).ne
  have hle := (ENNReal.toReal_le_toReal htop htop2).mpr
    (lintegral_norm_mul_bsKernelScalar_ball_le hρ)
  refine le_trans hle ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  apply le_of_eq
  ring

end Navier.Analysis.BealeKatoMajda
