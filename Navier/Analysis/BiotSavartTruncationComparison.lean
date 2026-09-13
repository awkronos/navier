import Navier.Analysis.BiotSavartFiniteRadius
import Navier.Analysis.BiotSavartNearBounds

/-!
# Smooth versus sharp Biot--Savart truncations

The smooth exterior cutoff and the sharp exterior-ball cutoff differ only on
a shrinking annulus.  This file separates the constant angular mode, which
cancels exactly for the trace-free gradient kernel, from the first-order
Schwartz remainder, whose integral is `O(ε)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators

namespace Navier.Analysis.BiotSavartTruncationComparison

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartPuncture
open Navier.Analysis.BiotSavartFiniteRadius
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda

private theorem continuous_officialEuclideanNorm :
    Continuous officialEuclideanNorm := by
  rw [show officialEuclideanNorm = fun x : Space =>
      Real.sqrt (∑ k : Fin 3, |x k| ^ 2) by
    funext x
    exact officialEuclideanNorm_eq_sqrt_sum_sq x]
  fun_prop

/-- The scalar sharp cutoff used by `exteriorIntegral`. -/
def sharpExteriorCutoff (ε : ℝ) (x : Space) : ℝ :=
  if ε < officialEuclideanNorm x then 1 else 0

/-- Difference between the smooth and sharp exterior cutoffs. -/
def truncationDifferenceWeight (ε : ℝ) (x : Space) : ℝ :=
  smoothExteriorCutoff ε x - sharpExteriorCutoff ε x

/-- The error between smooth and sharp gradient truncations, written as one
integral over their shrinking annulus. -/
def smoothSharpCZError (ε : ℝ) (i j : Fin 3) (φ : Space → ℝ) : ℝ :=
  ∫ x : Space, truncationDifferenceWeight ε x *
    ((1 / (4 * Real.pi)) * bsGradKernel i j x) * φ x

theorem schwartz_sub_zero_norm_le (φ : SchwartzMap Space ℝ) (x : Space) :
    ‖φ x - φ 0‖ ≤ (SchwartzMap.seminorm ℝ 0 1) φ * ‖x‖ := by
  have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (f := (φ : Space → ℝ)) (C := (SchwartzMap.seminorm ℝ 0 1) φ)
    (x := (0 : Space)) (y := x)
    (fun y _ => φ.differentiableAt)
    (fun y _ => by
      rw [← norm_iteratedFDeriv_one]
      exact φ.norm_iteratedFDeriv_le_seminorm ℝ 1 y)
    (by simp) (by simp)
  simpa only [sub_zero] using h

private theorem smoothExteriorCutoff_eq_one_of_two_mul_le
    {ε : ℝ} (hε : 0 < ε) {x : Space}
    (hx : 2 * ε ≤ officialEuclideanNorm x) :
    smoothExteriorCutoff ε x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [radiusSq_eq_officialEuclideanNorm_sq]
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hx2raw : (2 * ε) ^ 2 ≤ officialEuclideanNorm x ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (by norm_num) hε.le)
      (officialEuclideanNorm_nonneg x)).2 hx
  have hx2 : 2 * ε ^ 2 ≤ officialEuclideanNorm x ^ 2 := by
    nlinarith
  rw [le_sub_iff_add_le]
  norm_num
  exact (le_div_iff₀ hεsq).2 hx2

private theorem truncationDifferenceWeight_eq_zero_of_outer
    {ε : ℝ} (hε : 0 < ε) {x : Space}
    (hx : 2 * ε ≤ officialEuclideanNorm x) :
    truncationDifferenceWeight ε x = 0 := by
  rw [truncationDifferenceWeight,
    smoothExteriorCutoff_eq_one_of_two_mul_le hε hx]
  have hsharp : sharpExteriorCutoff ε x = 1 := by
    rw [sharpExteriorCutoff, if_pos]
    linarith
  rw [hsharp]
  ring

private theorem abs_truncationDifferenceWeight_le_one
    (ε : ℝ) (x : Space) :
    |truncationDifferenceWeight ε x| ≤ 1 := by
  have hs0 : 0 ≤ smoothExteriorCutoff ε x :=
    Real.smoothTransition.nonneg _
  have hs1 : smoothExteriorCutoff ε x ≤ 1 :=
    Real.smoothTransition.le_one _
  have hh0 : 0 ≤ sharpExteriorCutoff ε x := by
    unfold sharpExteriorCutoff
    split_ifs <;> norm_num
  have hh1 : sharpExteriorCutoff ε x ≤ 1 := by
    unfold sharpExteriorCutoff
    split_ifs <;> norm_num
  rw [truncationDifferenceWeight, abs_le]
  constructor <;> linarith

private theorem czScalarKernel_eq_four_pi_mul_bsKernelScalar (x : Space) :
    czScalarKernel x = 4 * Real.pi * bsKernelScalar x := by
  by_cases hx : x = 0
  · subst x
    simp [czScalarKernel_zero, bsKernelScalar_zero]
  · rw [czScalarKernel_apply_of_ne_zero hx,
      bsKernelScalar_apply_of_ne_zero hx]
    have hr : officialEuclideanNorm x ≠ 0 := by
      intro hn
      apply hx
      apply norm_eq_zero.mp
      have hle := norm_le_officialEuclideanNorm x
      rw [hn] at hle
      exact le_antisymm hle (norm_nonneg x)
    field_simp

private theorem scaled_bsGradKernel_abs_le (i j : Fin 3) (x : Space) :
    |(1 / (4 * Real.pi)) * bsGradKernel i j x| ≤
      4 * bsKernelScalar x := by
  rw [abs_mul, abs_of_pos (by positivity : 0 < (1 / (4 * Real.pi) : ℝ))]
  have h := bsGradKernel_abs_le i j x
  rw [czScalarKernel_eq_four_pi_mul_bsKernelScalar] at h
  have hpi : 0 < Real.pi := Real.pi_pos
  calc
    1 / (4 * Real.pi) * |bsGradKernel i j x| ≤
        1 / (4 * Real.pi) *
          (4 * (4 * Real.pi * bsKernelScalar x)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4 * bsKernelScalar x := by field_simp

private theorem measurable_truncationDifferenceWeight (ε : ℝ) :
    Measurable (truncationDifferenceWeight ε) := by
  apply Measurable.sub (continuous_smoothExteriorCutoff ε).measurable
  unfold sharpExteriorCutoff
  exact Measurable.ite
    (measurableSet_lt measurable_const continuous_officialEuclideanNorm.measurable)
    measurable_const measurable_const

private theorem measurable_sharpExteriorCutoff (ε : ℝ) :
    Measurable (sharpExteriorCutoff ε) := by
  unfold sharpExteriorCutoff
  exact Measurable.ite
    (measurableSet_lt measurable_const continuous_officialEuclideanNorm.measurable)
    measurable_const measurable_const

private theorem measurable_bsGradKernel (i j : Fin 3) :
    Measurable (bsGradKernel i j) := by
  unfold bsGradKernel
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact (Measurable.sub
    (measurable_const.div (continuous_officialEuclideanNorm.measurable.pow_const 3))
    ((measurable_const.mul (measurable_pi_apply i)).mul (measurable_pi_apply j) |>.div
      (continuous_officialEuclideanNorm.measurable.pow_const 5)))

private theorem smoothSharpCZError_remainder_integrable
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Integrable (fun x : Space => truncationDifferenceWeight ε x *
      ((1 / (4 * Real.pi)) * bsGradKernel i j x) * (φ x - φ 0)) := by
  let M : ℝ := (SchwartzMap.seminorm ℝ 0 1) φ
  let ballWeight : Space → ℝ := fun x => Set.indicator
    (Metric.ball (0 : Space) (2 * ε))
    (fun y => 4 * M * (‖y‖ * bsKernelScalar y)) x
  have hballInt : Integrable ballWeight := by
    have hbase := integrableOn_norm_mul_bsKernelScalar_ball
      (show 0 < 2 * ε by positivity)
    have hscaled : IntegrableOn (fun y : Space =>
        4 * M * (‖y‖ * bsKernelScalar y))
        (Metric.ball (0 : Space) (2 * ε)) := hbase.const_mul (4 * M)
    exact hscaled.integrable_indicator measurableSet_ball
  apply hballInt.mono'
  · exact (((measurable_truncationDifferenceWeight ε).mul
      (measurable_const.mul (measurable_bsGradKernel i j))).mul
      (φ.continuous.measurable.sub measurable_const)).aestronglyMeasurable
  · filter_upwards [] with x
    by_cases hxouter : 2 * ε ≤ officialEuclideanNorm x
    · rw [truncationDifferenceWeight_eq_zero_of_outer hε hxouter]
      simp only [zero_mul, norm_zero]
      by_cases hxball : x ∈ Metric.ball (0 : Space) (2 * ε)
      · rw [show ballWeight x = 4 * M * (‖x‖ * bsKernelScalar x) by
          simp [ballWeight, hxball]]
        exact mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _))
          (mul_nonneg (norm_nonneg _) (bsKernelScalar_nonneg _))
      · simp [ballWeight, hxball]
    · have hxball : x ∈ Metric.ball (0 : Space) (2 * ε) := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (norm_le_officialEuclideanNorm x)
          (lt_of_not_ge hxouter)
      rw [show ballWeight x = 4 * M * (‖x‖ * bsKernelScalar x) by
        simp [ballWeight, hxball]]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hw := abs_truncationDifferenceWeight_le_one ε x
      have hk := scaled_bsGradKernel_abs_le i j x
      have hφ := schwartz_sub_zero_norm_le φ x
      have hφ' : |φ x - φ 0| ≤ M * ‖x‖ := by
        simpa only [M, Real.norm_eq_abs] using hφ
      have hM : 0 ≤ M := apply_nonneg _ _
      have hbs : 0 ≤ bsKernelScalar x := bsKernelScalar_nonneg x
      calc
        |truncationDifferenceWeight ε x| *
            |1 / (4 * Real.pi) * bsGradKernel i j x| * |φ x - φ 0| ≤
            1 * (4 * bsKernelScalar x) * (M * ‖x‖) := by
          gcongr
        _ = 4 * M * (‖x‖ * bsKernelScalar x) := by ring

theorem smoothSharpCZError_remainder_abs_le
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    |smoothSharpCZError ε i j (fun x => φ x - φ 0)| ≤
      16 * (SchwartzMap.seminorm ℝ 0 1) φ *
        (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi * ε := by
  let M : ℝ := (SchwartzMap.seminorm ℝ 0 1) φ
  let error : Space → ℝ := fun x => truncationDifferenceWeight ε x *
    ((1 / (4 * Real.pi)) * bsGradKernel i j x) * (φ x - φ 0)
  let ballWeight : Space → ℝ := fun x => Set.indicator
    (Metric.ball (0 : Space) (2 * ε))
    (fun y => 4 * M * (‖y‖ * bsKernelScalar y)) x
  have herr : Integrable error :=
    smoothSharpCZError_remainder_integrable hε i j φ
  have hballInt : Integrable ballWeight := by
    have hbase := integrableOn_norm_mul_bsKernelScalar_ball
      (show 0 < 2 * ε by positivity)
    have hscaled : IntegrableOn (fun y : Space =>
        4 * M * (‖y‖ * bsKernelScalar y))
        (Metric.ball (0 : Space) (2 * ε)) := hbase.const_mul (4 * M)
    exact hscaled.integrable_indicator measurableSet_ball
  have hpoint : ∀ x : Space, ‖error x‖ ≤ ballWeight x := by
    intro x
    by_cases hxouter : 2 * ε ≤ officialEuclideanNorm x
    · rw [show error x = 0 by
          dsimp only [error]
          rw [truncationDifferenceWeight_eq_zero_of_outer hε hxouter]
          ring]
      simp only [norm_zero]
      by_cases hxball : x ∈ Metric.ball (0 : Space) (2 * ε)
      · rw [show ballWeight x = 4 * M * (‖x‖ * bsKernelScalar x) by
          simp [ballWeight, hxball]]
        exact mul_nonneg (mul_nonneg (by norm_num) (apply_nonneg _ _))
          (mul_nonneg (norm_nonneg _) (bsKernelScalar_nonneg _))
      · simp [ballWeight, hxball]
    · have hxball : x ∈ Metric.ball (0 : Space) (2 * ε) := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (norm_le_officialEuclideanNorm x)
          (lt_of_not_ge hxouter)
      rw [show ballWeight x = 4 * M * (‖x‖ * bsKernelScalar x) by
        simp [ballWeight, hxball]]
      dsimp only [error]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have hw := abs_truncationDifferenceWeight_le_one ε x
      have hk := scaled_bsGradKernel_abs_le i j x
      have hφ := schwartz_sub_zero_norm_le φ x
      have hφ' : |φ x - φ 0| ≤ M * ‖x‖ := by
        simpa only [M, Real.norm_eq_abs] using hφ
      have hM : 0 ≤ M := apply_nonneg _ _
      have hbs : 0 ≤ bsKernelScalar x := bsKernelScalar_nonneg x
      calc
        |truncationDifferenceWeight ε x| *
            |1 / (4 * Real.pi) * bsGradKernel i j x| * |φ x - φ 0| ≤
            1 * (4 * bsKernelScalar x) * (M * ‖x‖) := by
          gcongr
        _ = 4 * M * (‖x‖ * bsKernelScalar x) := by ring
  change |∫ x : Space, error x| ≤ _
  calc
    |∫ x : Space, error x| = ‖∫ x : Space, error x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ x : Space, ballWeight x :=
      MeasureTheory.norm_integral_le_of_norm_le hballInt (ae_of_all _ hpoint)
    _ = 4 * M * ∫ x : Space in Metric.ball (0 : Space) (2 * ε),
        ‖x‖ * bsKernelScalar x := by
      rw [show ballWeight = Set.indicator (Metric.ball (0 : Space) (2 * ε))
          (fun x => 4 * M * (‖x‖ * bsKernelScalar x)) by rfl,
        MeasureTheory.integral_indicator measurableSet_ball,
        MeasureTheory.integral_const_mul]
    _ ≤ 4 * M *
        (2 * (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi *
          (2 * ε)) := by
      apply mul_le_mul_of_nonneg_left
        (integral_norm_mul_bsKernelScalar_ball_le
          (show 0 < 2 * ε by positivity))
      positivity
    _ = 16 * (SchwartzMap.seminorm ℝ 0 1) φ *
        (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi * ε := by
      dsimp only [M]
      ring

theorem tendsto_smoothSharpCZError_remainder
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Tendsto (fun ε : ℝ =>
      smoothSharpCZError ε i j (fun x => φ x - φ 0))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsource : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 := inf_le_left
  let C : ℝ := 16 * (SchwartzMap.seminorm ℝ 0 1) φ *
    (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [Real.norm_eq_abs, C, mul_assoc] using
      smoothSharpCZError_remainder_abs_le (i := i) (j := j) hε φ
  · have hc : Tendsto (fun _ : ℝ =>
        16 * ((SchwartzMap.seminorm ℝ 0 1) φ *
          (volume (Metric.ball (0 : Space) 1)).toReal) / Real.pi)
        (nhdsWithin 0 (Ioi 0))
        (nhds (16 * ((SchwartzMap.seminorm ℝ 0 1) φ *
          (volume (Metric.ball (0 : Space) 1)).toReal) / Real.pi)) :=
      tendsto_const_nhds
    simpa only [id_eq, mul_zero] using
      hc.mul (tendsto_id.mono_left hsource)

private abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)

private def euclideanCoordinateFlip (k : Fin 3) :
    EuclideanThree ≃ₗᵢ[ℝ] EuclideanThree :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun l : Fin 3 => if l = k then LinearIsometryEquiv.neg ℝ
      else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] private theorem euclideanCoordinateFlip_apply_same
    (k : Fin 3) (x : EuclideanThree) :
    euclideanCoordinateFlip k x k = -x k := by
  simp [euclideanCoordinateFlip]

@[simp] private theorem euclideanCoordinateFlip_apply_ne
    {k l : Fin 3} (h : l ≠ k) (x : EuclideanThree) :
    euclideanCoordinateFlip k x l = x l := by
  simp [euclideanCoordinateFlip, h]

private def euclideanCoordinatePerm (e : Equiv.Perm (Fin 3)) :
    EuclideanThree ≃ₗᵢ[ℝ] EuclideanThree :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

private def euclideanCZTensor (i j : Fin 3) (y : EuclideanThree) : ℝ :=
  if y = 0 then 0
  else (if i = j then (1 : ℝ) else 0) / ‖y‖ ^ 3 -
    3 * y i * y j / ‖y‖ ^ 5

private theorem euclideanCZTensor_flip_offDiag
    {i j : Fin 3} (hij : i ≠ j) (y : EuclideanThree) :
    euclideanCZTensor i j (euclideanCoordinateFlip i y) =
      -euclideanCZTensor i j y := by
  by_cases hy : y = 0
  · subst y
    simp [euclideanCZTensor]
  · have hflip : euclideanCoordinateFlip i y ≠ 0 := by
      simpa using (euclideanCoordinateFlip i).injective.ne hy
    rw [euclideanCZTensor, if_neg hflip, euclideanCZTensor, if_neg hy]
    simp only [hij, if_false, zero_div, zero_sub, norm_map,
      euclideanCoordinateFlip_apply_same,
      euclideanCoordinateFlip_apply_ne hij.symm]
    ring

private theorem euclideanCZTensor_perm_diagonal
    (i j : Fin 3) (y : EuclideanThree) :
    euclideanCZTensor j j (euclideanCoordinatePerm (Equiv.swap i j) y) =
      euclideanCZTensor i i y := by
  by_cases hy : y = 0
  · subst y
    simp [euclideanCZTensor]
  · have hperm : euclideanCoordinatePerm (Equiv.swap i j) y ≠ 0 := by
      simpa using (euclideanCoordinatePerm (Equiv.swap i j)).injective.ne hy
    rw [euclideanCZTensor, if_neg hperm, euclideanCZTensor, if_neg hy]
    simp [euclideanCoordinatePerm, norm_map]

private theorem euclideanCZTensor_trace (y : EuclideanThree) :
    (∑ i : Fin 3, euclideanCZTensor i i y) = 0 := by
  by_cases hy : y = 0
  · subst y
    simp [euclideanCZTensor]
  · simp only [euclideanCZTensor, if_neg hy, if_pos, Finset.sum_sub_distrib]
    have hnorm : ‖y‖ ^ 2 = ∑ i : Fin 3, (y i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have hone : (∑ _i : Fin 3, (1 : ℝ) / ‖y‖ ^ 3) =
        3 / ‖y‖ ^ 3 := by
      rw [Fin.sum_univ_three]
      ring
    have hcoord : (∑ i : Fin 3, 3 * y i * y i / ‖y‖ ^ 5) =
        3 * (∑ i : Fin 3, (y i) ^ 2) / ‖y‖ ^ 5 := by
      simp only [Fin.sum_univ_three]
      ring
    rw [hone, hcoord, ← hnorm]
    field_simp
    ring

private theorem integral_radial_euclideanCZTensor_offDiag
    (h : ℝ → ℝ) {i j : Fin 3} (hij : i ≠ j) :
    (∫ y : EuclideanThree, h ‖y‖ * euclideanCZTensor i j y) = 0 := by
  let flip := euclideanCoordinateFlip i
  let g : EuclideanThree → ℝ := fun y => h ‖y‖ * euclideanCZTensor i j y
  have hinv := (euclideanCoordinateFlip i).measurePreserving.integral_comp
    flip.toHomeomorph.measurableEmbedding g
  have hodd : (fun y => g (flip y)) = fun y => -g y := by
    funext y
    simp only [g, flip, norm_map, euclideanCZTensor_flip_offDiag hij]
    ring
  rw [hodd, integral_neg] at hinv
  change -(∫ y : EuclideanThree, g y) = ∫ y : EuclideanThree, g y at hinv
  linarith

private theorem integral_radial_euclideanCZTensor_diagonal_eq
    (h : ℝ → ℝ) (i j : Fin 3) :
    (∫ y : EuclideanThree, h ‖y‖ * euclideanCZTensor i i y) =
      ∫ y : EuclideanThree, h ‖y‖ * euclideanCZTensor j j y := by
  let swap := euclideanCoordinatePerm (Equiv.swap i j)
  let g : EuclideanThree → ℝ := fun y => h ‖y‖ * euclideanCZTensor j j y
  have hinv := (euclideanCoordinatePerm (Equiv.swap i j)).measurePreserving.integral_comp
    swap.toHomeomorph.measurableEmbedding g
  have hswap : (fun y => g (swap y)) =
      fun y => h ‖y‖ * euclideanCZTensor i i y := by
    funext y
    simp only [g, swap, norm_map, euclideanCZTensor_perm_diagonal]
  rw [hswap] at hinv
  exact hinv

private theorem integral_radial_euclideanCZTensor_diagonal_zero
    (h : ℝ → ℝ) (i : Fin 3) :
    (∫ y : EuclideanThree, h ‖y‖ * euclideanCZTensor i i y) = 0 := by
  let f : Fin 3 → EuclideanThree → ℝ := fun k y =>
    h ‖y‖ * euclideanCZTensor k k y
  by_cases hi : Integrable (f i)
  · have hint : ∀ k : Fin 3, Integrable (f k) := by
      intro k
      let swap := euclideanCoordinatePerm (Equiv.swap i k)
      have hiff := (euclideanCoordinatePerm (Equiv.swap i k)).measurePreserving.integrable_comp_emb
        swap.toHomeomorph.measurableEmbedding (g := f k)
      have hcomp : f k ∘ swap = f i := by
        funext y
        simp only [f, Function.comp_apply, swap, norm_map,
          euclideanCZTensor_perm_diagonal]
      rw [hcomp] at hiff
      exact hiff.mp hi
    have hsum := MeasureTheory.integral_finsetSum Finset.univ
      (fun k _ => hint k)
    have hpoint : (fun y : EuclideanThree => ∑ k : Fin 3, f k y) =
        fun _ => 0 := by
      funext y
      simp only [f, ← Finset.mul_sum, euclideanCZTensor_trace, mul_zero]
    have hzero : (∫ y : EuclideanThree, ∑ k : Fin 3, f k y) = 0 := by
      rw [hpoint]
      simp
    rw [hzero] at hsum
    have heq : ∀ k : Fin 3, (∫ y : EuclideanThree, f k y) =
        ∫ y : EuclideanThree, f i y := by
      intro k
      exact integral_radial_euclideanCZTensor_diagonal_eq h k i
    simp_rw [heq] at hsum
    simp only [Fin.sum_univ_three] at hsum
    change (∫ y : EuclideanThree, f i y) = 0
    linarith
  · exact integral_undef hi

private theorem integral_radial_euclideanCZTensor_zero
    (h : ℝ → ℝ) (i j : Fin 3) :
    (∫ y : EuclideanThree, h ‖y‖ * euclideanCZTensor i j y) = 0 := by
  by_cases hij : i = j
  · subst j
    exact integral_radial_euclideanCZTensor_diagonal_zero h i
  · exact integral_radial_euclideanCZTensor_offDiag h hij

private def radialTruncationDifference (ε r : ℝ) : ℝ :=
  Real.smoothTransition (r ^ 2 / ε ^ 2 - 1) -
    if ε < r then 1 else 0

private def spaceToEuclideanMeasurableEquiv : Space ≃ᵐ EuclideanThree :=
  MeasurableEquiv.mk (WithLp.equiv 2 Space).symm
    (by measurability)
    (by
      change Measurable (fun x : EuclideanThree => (fun i => x i : Space))
      fun_prop)

private theorem integral_space_comp_officialEuclideanPoint
    (g : EuclideanThree → ℝ) :
    (∫ x : Space, g (officialEuclideanPoint x)) =
      ∫ y : EuclideanThree, g y := by
  exact (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    spaceToEuclideanMeasurableEquiv.measurableEmbedding g

private theorem smoothSharpCZError_one_eq_euclidean
    (ε : ℝ) (i j : Fin 3) :
    smoothSharpCZError ε i j (fun _ => 1) =
      ∫ y : EuclideanThree,
        radialTruncationDifference ε ‖y‖ *
          ((1 / (4 * Real.pi)) * euclideanCZTensor i j y) := by
  let g : EuclideanThree → ℝ := fun y =>
    radialTruncationDifference ε ‖y‖ *
      ((1 / (4 * Real.pi)) * euclideanCZTensor i j y)
  have hpoint : ∀ x : Space,
      truncationDifferenceWeight ε x *
          ((1 / (4 * Real.pi)) * bsGradKernel i j x) * (1 : ℝ) =
        g (officialEuclideanPoint x) := by
    intro x
    by_cases hx : x = 0
    · subst x
      have hpoint0 : officialEuclideanPoint (0 : Space) = 0 := rfl
      simp [g, euclideanCZTensor, bsGradKernel, hpoint0]
    · have hy : officialEuclideanPoint x ≠ 0 := by
        intro hy
        apply hx
        funext k
        have hk := congrArg (fun y : EuclideanThree => y k) hy
        simpa using hk
      rw [truncationDifferenceWeight, smoothExteriorCutoff,
        radiusSq_eq_officialEuclideanNorm_sq, sharpExteriorCutoff,
        bsGradKernel_apply_of_ne_zero hx]
      dsimp only [g, radialTruncationDifference]
      rw [euclideanCZTensor, if_neg hy]
      simp only [officialEuclideanNorm, officialEuclideanPoint_apply, mul_one]
      congr 1
  rw [smoothSharpCZError]
  simp only [hpoint]
  exact integral_space_comp_officialEuclideanPoint g

/-- Exact cancellation of the constant angular mode in the smooth-minus-sharp
truncation error. -/
theorem smoothSharpCZError_one (ε : ℝ) (i j : Fin 3) :
    smoothSharpCZError ε i j (fun _ => 1) = 0 := by
  rw [smoothSharpCZError_one_eq_euclidean]
  have hzero := integral_radial_euclideanCZTensor_zero
    (fun r => radialTruncationDifference ε r * (1 / (4 * Real.pi))) i j
  convert hzero using 1
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- The trace-free Calderón--Zygmund tensor has zero integral on every
Euclidean annulus.  This is the exact constant-mode cancellation needed to
split a sharp principal value at a second positive radius. -/
theorem integral_scaled_bsGradKernel_euclideanAnnulus_eq_zero
    (ε ρ : ℝ) (i j : Fin 3) :
    (∫ z in {z : Space |
        ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ},
      (1 / (4 * Real.pi)) * bsGradKernel i j z) = 0 := by
  let h : ℝ → ℝ := fun r => if ε < r ∧ r < ρ then 1 else 0
  let g : EuclideanThree → ℝ := fun y =>
    h ‖y‖ * ((1 / (4 * Real.pi)) * euclideanCZTensor i j y)
  have hpoint : ∀ x : Space,
      Set.indicator {z : Space |
          ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ}
        (fun z => (1 / (4 * Real.pi)) * bsGradKernel i j z) x =
        g (officialEuclideanPoint x) := by
    intro x
    by_cases hs : x ∈ {z : Space |
        ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ}
    · rw [Set.indicator_of_mem hs]
      have hh : ε < ‖officialEuclideanPoint x‖ ∧
          ‖officialEuclideanPoint x‖ < ρ := by
        exact hs
      dsimp only [g, h]
      rw [if_pos hh, one_mul]
      by_cases hx : x = 0
      · subst x
        have hp : officialEuclideanPoint (0 : Space) = 0 := rfl
        rw [euclideanCZTensor, if_pos hp, bsGradKernel]
        simp
      · have hy : officialEuclideanPoint x ≠ 0 := by
          intro hy
          apply hx
          funext k
          have hk := congrArg (fun y : EuclideanThree => y k) hy
          simpa using hk
        rw [euclideanCZTensor, if_neg hy,
          bsGradKernel_apply_of_ne_zero hx]
        simp only [officialEuclideanNorm, officialEuclideanPoint_apply]
    · rw [Set.indicator_of_notMem hs]
      have hh : ¬(ε < ‖officialEuclideanPoint x‖ ∧
          ‖officialEuclideanPoint x‖ < ρ) := by
        exact hs
      simp [g, h, hh]
  have hset : {z : Space |
      ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ} =
      {z : Space | ε < officialEuclideanNorm z} ∩
        {z : Space | officialEuclideanNorm z < ρ} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  have hsmeas : MeasurableSet {z : Space |
      ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ} := by
    rw [hset]
    exact (measurableSet_lt measurable_const
      continuous_officialEuclideanNorm.measurable).inter
      (measurableSet_lt continuous_officialEuclideanNorm.measurable
        measurable_const)
  rw [← MeasureTheory.integral_indicator hsmeas]
  rw [show (fun x : Space =>
      Set.indicator {z : Space |
          ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ}
        (fun z => (1 / (4 * Real.pi)) * bsGradKernel i j z) x) =
      fun x => g (officialEuclideanPoint x) by
    funext x
    exact hpoint x]
  rw [integral_space_comp_officialEuclideanPoint]
  have hzero := integral_radial_euclideanCZTensor_zero
    (fun r => h r * (1 / (4 * Real.pi))) i j
  convert hzero using 1
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp only [g]
  ring

/-- With positive inner radius, the annular tensor in the cancellation theorem
is genuinely Bochner integrable. -/
theorem integrableOn_scaled_bsGradKernel_euclideanAnnulus
    {ε ρ : ℝ} (hε : 0 < ε) (i j : Fin 3) :
    IntegrableOn (fun z : Space =>
      (1 / (4 * Real.pi)) * bsGradKernel i j z)
      {z : Space |
        ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ} volume := by
  let s : Set Space := {z : Space |
    ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ}
  let C : ℝ := 1 / (Real.pi * ε ^ 3)
  have hsball : s ⊆ Metric.ball (0 : Space) ρ := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (norm_le_officialEuclideanNorm z) hz.2
  have hsfinite : volume s ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Space)) (r := ρ)).ne
      (measure_mono hsball)
  have hconst : IntegrableOn (fun _ : Space => C) s volume :=
    integrableOn_const hsfinite
  apply hconst.mono'
  · exact (measurable_const.mul (measurable_bsGradKernel i j)).aestronglyMeasurable.restrict
  · filter_upwards [self_mem_ae_restrict
      (show MeasurableSet s by
        dsimp only [s]
        have hset : {z : Space |
            ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ} =
            {z : Space | ε < officialEuclideanNorm z} ∩
              {z : Space | officialEuclideanNorm z < ρ} := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        rw [hset]
        exact (measurableSet_lt measurable_const
          continuous_officialEuclideanNorm.measurable).inter
          (measurableSet_lt continuous_officialEuclideanNorm.measurable
            measurable_const))] with z hz
    rw [Real.norm_eq_abs]
    have hz0 : z ≠ 0 := by
      intro hz0
      subst z
      have hzero : officialEuclideanNorm (0 : Space) = 0 := by
        simp [officialEuclideanNorm, officialEuclideanPoint]
      dsimp only [s, Set.mem_ofPred_eq] at hz
      rw [hzero] at hz
      linarith
    have hrpos : 0 < officialEuclideanNorm z := hε.trans hz.1
    have hpow : ε ^ 3 ≤ officialEuclideanNorm z ^ 3 :=
      pow_le_pow_left₀ hε.le hz.1.le 3
    calc
      |1 / (4 * Real.pi) * bsGradKernel i j z|
          ≤ 4 * bsKernelScalar z := scaled_bsGradKernel_abs_le i j z
      _ = 1 / (Real.pi * officialEuclideanNorm z ^ 3) := by
        rw [bsKernelScalar_apply_of_ne_zero hz0]
        field_simp
      _ ≤ 1 / (Real.pi * ε ^ 3) := by
        exact one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left hpow Real.pi_pos.le)
      _ = C := rfl

private theorem sharpExteriorCutoff_mul (ε : ℝ) (g : Space → ℝ) :
    (fun x => sharpExteriorCutoff ε x * g x) =
      Set.indicator {x : Space | ε < officialEuclideanNorm x} g := by
  funext x
  unfold sharpExteriorCutoff
  by_cases hx : ε < officialEuclideanNorm x <;> simp [hx]

theorem smoothPuncturedGradientIntegral_sub_puncturedGradientIntegral_eq_error
    {ε : ℝ} {i j : Fin 3} {φ : Space → ℝ}
    (hsmooth : Integrable (fun x : Space => smoothExteriorCutoff ε x *
      (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))))
    (hsharp : Integrable (Set.indicator
      {x : Space | ε < officialEuclideanNorm x}
      (fun x => (1 / (4 * Real.pi)) * bsGradKernel i j x * φ x))) :
    smoothPuncturedGradientIntegral ε i j φ -
      puncturedGradientIntegral ε i j φ = smoothSharpCZError ε i j φ := by
  rw [smoothPuncturedGradientIntegral, puncturedGradientIntegral,
    exteriorIntegral, ← integral_sub hsmooth hsharp, smoothSharpCZError]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← sharpExteriorCutoff_mul ε
    (fun x => (1 / (4 * Real.pi)) * bsGradKernel i j x * φ x)]
  unfold truncationDifferenceWeight
  ring

theorem smoothSharpCZError_eq_remainder
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (φ : SchwartzMap Space ℝ)
    (herror : Integrable (fun x : Space => truncationDifferenceWeight ε x *
      ((1 / (4 * Real.pi)) * bsGradKernel i j x) * φ x)) :
    smoothSharpCZError ε i j φ =
      smoothSharpCZError ε i j (fun x => φ x - φ 0) := by
  let remainder : Space → ℝ := fun x => truncationDifferenceWeight ε x *
    ((1 / (4 * Real.pi)) * bsGradKernel i j x) * (φ x - φ 0)
  let constantPart : Space → ℝ := fun x => φ 0 *
    (truncationDifferenceWeight ε x *
      ((1 / (4 * Real.pi)) * bsGradKernel i j x) * (1 : ℝ))
  have hrem : Integrable remainder :=
    smoothSharpCZError_remainder_integrable hε i j φ
  have hdecomp : (fun x : Space => truncationDifferenceWeight ε x *
      ((1 / (4 * Real.pi)) * bsGradKernel i j x) * φ x) =
      fun x => remainder x + constantPart x := by
    funext x
    dsimp only [remainder, constantPart]
    ring
  have hconst : Integrable constantPart := by
    have := herror.congr (ae_of_all _ fun x => congrFun hdecomp x)
    exact (this.sub hrem).congr (ae_of_all _ fun x => by
      dsimp only [constantPart, remainder]
      simp only [Pi.sub_apply]
      ring)
  rw [smoothSharpCZError, hdecomp, integral_add hrem hconst]
  have hconstIntegral : (∫ x : Space, constantPart x) = 0 := by
    dsimp only [constantPart]
    rw [MeasureTheory.integral_const_mul, ← smoothSharpCZError,
      smoothSharpCZError_one, mul_zero]
  rw [hconstIntegral, add_zero]
  rfl

/-- With the natural per-radius integrability of the two truncations, their
difference tends to zero for every Schwartz test function. -/
theorem tendsto_smoothPuncturedGradient_sub_puncturedGradient
    (i j : Fin 3) (φ : SchwartzMap Space ℝ)
    (hsmooth : ∀ ε : ℝ, 0 < ε → Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))))
    (hsharp : ∀ ε : ℝ, 0 < ε → Integrable (Set.indicator
      {x : Space | ε < officialEuclideanNorm x}
      (fun x => (1 / (4 * Real.pi)) * bsGradKernel i j x * φ x))) :
    Tendsto (fun ε : ℝ =>
      smoothPuncturedGradientIntegral ε i j φ -
        puncturedGradientIntegral ε i j φ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  apply (tendsto_smoothSharpCZError_remainder i j φ).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [smoothPuncturedGradientIntegral_sub_puncturedGradientIntegral_eq_error
      (hsmooth ε hε) (hsharp ε hε),
    smoothSharpCZError_eq_remainder hε i j φ]
  have herror : Integrable (fun x : Space => truncationDifferenceWeight ε x *
      ((1 / (4 * Real.pi)) * bsGradKernel i j x) * φ x) := by
    have hdifference := (hsmooth ε hε).sub (hsharp ε hε)
    exact hdifference.congr (ae_of_all _ fun x => by
      rw [← sharpExteriorCutoff_mul ε
        (fun x => (1 / (4 * Real.pi)) * bsGradKernel i j x * φ x)]
      simp only [Pi.sub_apply]
      unfold truncationDifferenceWeight
      ring)
  exact herror

/-- Multiplication by the smooth exterior cutoff converges to the identity on
an integrable function vanishing at the kernel pole. -/
theorem tendsto_smoothPuncturedDerivativeIntegral
    (i j : Fin 3) (φ : Space → ℝ)
    (hint : Integrable (fun x : Space =>
      fderiv ℝ φ x (basisVector i) * bsVectorKernel x j)) :
    Tendsto (fun ε : ℝ => smoothPuncturedDerivativeIntegral ε i j φ)
      (nhdsWithin 0 (Ioi 0))
      (nhds (∫ x : Space,
        fderiv ℝ φ x (basisVector i) * bsVectorKernel x j)) := by
  let g : Space → ℝ := fun x =>
    fderiv ℝ φ x (basisVector i) * bsVectorKernel x j
  let F : ℝ → Space → ℝ := fun ε x => smoothExteriorCutoff ε x * g x
  have hFmeas : ∀ ε : ℝ, AEStronglyMeasurable (F ε) := by
    intro ε
    exact (continuous_smoothExteriorCutoff ε).aestronglyMeasurable.mul
      hint.aestronglyMeasurable
  have hbound : ∀ ε : ℝ, ∀ᵐ x : Space, ‖F ε x‖ ≤ ‖g x‖ := by
    intro ε
    filter_upwards [] with x
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs]
    have hc0 : 0 ≤ smoothExteriorCutoff ε x := Real.smoothTransition.nonneg _
    have hc1 : smoothExteriorCutoff ε x ≤ 1 := Real.smoothTransition.le_one _
    rw [abs_of_nonneg hc0]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc1 (norm_nonneg (g x))
  have hpoint : ∀ᵐ x : Space,
      Tendsto (fun ε : ℝ => F ε x) (nhdsWithin 0 (Ioi 0)) (nhds (g x)) := by
    filter_upwards [] with x
    by_cases hx : x = 0
    · subst x
      have hg0 : g 0 = 0 := by
        simp [g, bsVectorKernel, bsKernelScalar]
      simp only [F, hg0, mul_zero]
      exact tendsto_const_nhds
    · have hrpos : 0 < officialEuclideanNorm x := by
        have hrne : officialEuclideanNorm x ≠ 0 := by
          intro hr
          apply hx
          apply norm_eq_zero.mp
          have hle := norm_le_officialEuclideanNorm x
          rw [hr] at hle
          exact le_antisymm hle (norm_nonneg x)
        exact lt_of_le_of_ne (officialEuclideanNorm_nonneg x) (Ne.symm hrne)
      have heps : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
          ε < officialEuclideanNorm x / 2 :=
        (show ∀ᶠ ε : ℝ in nhds 0, ε < officialEuclideanNorm x / 2 from
          Iio_mem_nhds (by positivity)).filter_mono inf_le_left
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin, heps] with ε hε hsmall
      have htwo : 2 * ε ≤ officialEuclideanNorm x := by linarith
      change g x = smoothExteriorCutoff ε x * g x
      rw [smoothExteriorCutoff_eq_one_of_two_mul_le hε htwo, one_mul]
  have hlim := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := nhdsWithin 0 (Ioi 0))
    (F := F) (f := g) (bound := fun x => ‖g x‖)
    (Eventually.of_forall hFmeas) (Eventually.of_forall hbound)
    hint.norm hpoint
  simpa only [smoothPuncturedDerivativeIntegral, F, g] using hlim

/-- A sharp exterior-ball principal value is also the limit of the smooth
radial truncations. -/
theorem tendsto_smoothPuncturedGradient_of_principalValue
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (L : ℝ)
    (hpv : HasBiotSavartPrincipalValue i j φ L)
    (hsmooth : ∀ ε : ℝ, 0 < ε → Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))))
    (hsharp : ∀ ε : ℝ, 0 < ε → Integrable (Set.indicator
      {x : Space | ε < officialEuclideanNorm x}
      (fun x => (1 / (4 * Real.pi)) * bsGradKernel i j x * φ x))) :
    Tendsto (fun ε : ℝ => smoothPuncturedGradientIntegral ε i j φ)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  have hdiff := tendsto_smoothPuncturedGradient_sub_puncturedGradient
    i j φ hsmooth hsharp
  have hadd := hdiff.add hpv
  have heq : (fun ε : ℝ =>
      smoothPuncturedGradientIntegral ε i j φ -
        puncturedGradientIntegral ε i j φ +
          puncturedGradientIntegral ε i j φ) =
      fun ε => smoothPuncturedGradientIntegral ε i j φ := by
    funext ε
    ring
  rw [heq, zero_add] at hadd
  exact hadd

/-- The smooth finite-radius identity, sharp/smooth comparison, and exact
one-third flux limit close the Biot--Savart principal-value identity without
assuming a sharp punctured divergence formula. -/
theorem biotSavartPrincipalValue_identity_of_smoothTruncation
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (L : ℝ)
    (hintDerivative : Integrable (fun x : Space =>
      fderiv ℝ φ x (basisVector i) * bsVectorKernel x j))
    (hpv : HasBiotSavartPrincipalValue i j φ L)
    (hsmoothGradient : ∀ ε : ℝ, 0 < ε → Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))))
    (hsharpGradient : ∀ ε : ℝ, 0 < ε → Integrable (Set.indicator
      {x : Space | ε < officialEuclideanNorm x}
      (fun x => (1 / (4 * Real.pi)) * bsGradKernel i j x * φ x)))
    (hflux : ∀ ε : ℝ, 0 < ε → Integrable (fun x : Space =>
      fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) *
        (φ * fun z : Space => bsVectorKernel z j) x))
    (hproduct : ∀ ε : ℝ, 0 < ε → Integrable (fun x : Space =>
      smoothExteriorCutoff ε x *
        (φ * fun z : Space => bsVectorKernel z j) x)) :
    -(∫ x : Space, fderiv ℝ φ x (basisVector i) * bsVectorKernel x j) =
      L + (1 / 3 : ℝ) * basisVector i j * φ 0 := by
  have hleft := (tendsto_smoothPuncturedDerivativeIntegral
    i j φ hintDerivative).neg
  have hgradient := tendsto_smoothPuncturedGradient_of_principalValue
    i j φ L hpv hsmoothGradient hsharpGradient
  have hfluxlim := tendsto_smoothPunctureFlux i j φ φ.continuous
    ((SchwartzMap.seminorm ℝ 0 0) φ)
    (fun x => by simpa using φ.norm_iteratedFDeriv_le_seminorm ℝ 0 x)
  have hright := hgradient.add hfluxlim
  have heq : (fun ε : ℝ => -smoothPuncturedDerivativeIntegral ε i j φ)
      =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun ε => smoothPuncturedGradientIntegral ε i j φ +
        smoothPunctureFlux ε i j φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply smoothPunctured_biotSavart_identity ε hε i j φ.differentiable
    · exact hintDerivative.bdd_mul
        (continuous_smoothExteriorCutoff ε).aestronglyMeasurable
        (ae_of_all _ fun x => by
          change |smoothExteriorCutoff ε x| ≤ 1
          have hc0 : 0 ≤ smoothExteriorCutoff ε x :=
            Real.smoothTransition.nonneg _
          rw [abs_of_nonneg hc0]
          exact Real.smoothTransition.le_one _)
    · exact hsmoothGradient ε hε
    · exact hflux ε hε
    · exact hproduct ε hε
  exact tendsto_nhds_unique (hleft.congr' heq) hright

private theorem measurable_bsKernelScalar : Measurable bsKernelScalar := by
  unfold bsKernelScalar
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact measurable_const.div
    (measurable_const.mul
      (continuous_officialEuclideanNorm.measurable.pow_const 3))

private theorem measurable_bsVectorKernel_coord (j : Fin 3) :
    Measurable (fun x : Space => bsVectorKernel x j) := by
  unfold bsVectorKernel
  simp only [Pi.smul_apply, smul_eq_mul]
  exact measurable_bsKernelScalar.mul (measurable_pi_apply j)

private theorem bsKernelScalar_le_of_radius
    {ε : ℝ} (hε : 0 < ε) {x : Space}
    (hx : ε ≤ officialEuclideanNorm x) :
    bsKernelScalar x ≤ 1 / (4 * Real.pi * ε ^ 3) := by
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    have : officialEuclideanNorm (0 : Space) = 0 := by
      simp [officialEuclideanNorm, officialEuclideanPoint]
    rw [this] at hx
    linarith
  rw [bsKernelScalar_apply_of_ne_zero hx0]
  have hrpos : 0 < officialEuclideanNorm x :=
    lt_of_lt_of_le hε hx
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

private theorem bsVectorKernel_coord_abs_le_of_radius
    {ε : ℝ} (hε : 0 < ε) {x : Space}
    (hx : ε ≤ officialEuclideanNorm x) (j : Fin 3) :
    |bsVectorKernel x j| ≤ 1 / (4 * Real.pi * ε ^ 2) := by
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    have : officialEuclideanNorm (0 : Space) = 0 := by
      simp [officialEuclideanNorm, officialEuclideanPoint]
    rw [this] at hx
    linarith
  rw [bsVectorKernel, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (bsKernelScalar_nonneg x),
    bsKernelScalar_apply_of_ne_zero hx0]
  have hrpos : 0 < officialEuclideanNorm x := lt_of_lt_of_le hε hx
  calc
    1 / (4 * Real.pi * officialEuclideanNorm x ^ 3) * |x j| ≤
        1 / (4 * Real.pi * officialEuclideanNorm x ^ 3) *
          officialEuclideanNorm x :=
      mul_le_mul_of_nonneg_left (coord_abs_le_officialEuclideanNorm x j)
        (by positivity)
    _ = 1 / (4 * Real.pi * officialEuclideanNorm x ^ 2) := by
      field_simp
    _ ≤ 1 / (4 * Real.pi * ε ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr

theorem integrable_smoothPuncturedGradient_schwartz
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Integrable (fun x : Space => smoothExteriorCutoff ε x *
      (φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))) := by
  let factor : Space → ℝ := fun x => smoothExteriorCutoff ε x *
    ((1 / (4 * Real.pi)) * bsGradKernel i j x)
  have hfactorMeas : AEStronglyMeasurable factor :=
    ((continuous_smoothExteriorCutoff ε).measurable.mul
      (measurable_const.mul (measurable_bsGradKernel i j))).aestronglyMeasurable
  have hfactorBound : ∀ᵐ x : Space, ‖factor x‖ ≤ 1 / (Real.pi * ε ^ 3) := by
    filter_upwards [] with x
    by_cases hx : officialEuclideanNorm x ≤ ε
    · rw [show factor x = 0 by
          dsimp only [factor]
          rw [smoothExteriorCutoff_eq_zero hε hx]
          ring]
      simp only [norm_zero]
      positivity
    · dsimp only [factor]
      rw [norm_mul, Real.norm_eq_abs]
      have hc0 : 0 ≤ smoothExteriorCutoff ε x := Real.smoothTransition.nonneg _
      rw [abs_of_nonneg hc0]
      have hc1 : smoothExteriorCutoff ε x ≤ 1 := Real.smoothTransition.le_one _
      have hk := scaled_bsGradKernel_abs_le i j x
      have hscalar := bsKernelScalar_le_of_radius hε (le_of_not_ge hx)
      calc
        smoothExteriorCutoff ε x *
            |1 / (4 * Real.pi) * bsGradKernel i j x| ≤
            1 * (4 * bsKernelScalar x) := by gcongr
        _ ≤ 1 * (4 * (1 / (4 * Real.pi * ε ^ 3))) := by gcongr
        _ = 1 / (Real.pi * ε ^ 3) := by field_simp
  have hint := φ.integrable.bdd_mul hfactorMeas hfactorBound
  exact hint.congr (ae_of_all _ fun x => by
    dsimp only [factor]
    ring)

theorem integrable_sharpPuncturedGradient_schwartz
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Integrable (Set.indicator {x : Space | ε < officialEuclideanNorm x}
      (fun x => (1 / (4 * Real.pi)) * bsGradKernel i j x * φ x)) := by
  let factor : Space → ℝ := fun x => sharpExteriorCutoff ε x *
    ((1 / (4 * Real.pi)) * bsGradKernel i j x)
  have hfactorMeas : AEStronglyMeasurable factor :=
    ((measurable_sharpExteriorCutoff ε).mul
      (measurable_const.mul (measurable_bsGradKernel i j))).aestronglyMeasurable
  have hfactorBound : ∀ᵐ x : Space, ‖factor x‖ ≤ 1 / (Real.pi * ε ^ 3) := by
    filter_upwards [] with x
    by_cases hx : ε < officialEuclideanNorm x
    · have hsharp : sharpExteriorCutoff ε x = 1 := by
        simp [sharpExteriorCutoff, hx]
      dsimp only [factor]
      rw [hsharp, one_mul, Real.norm_eq_abs]
      have hk := scaled_bsGradKernel_abs_le i j x
      have hscalar := bsKernelScalar_le_of_radius hε hx.le
      calc
        |1 / (4 * Real.pi) * bsGradKernel i j x| ≤
            4 * bsKernelScalar x := hk
        _ ≤ 4 * (1 / (4 * Real.pi * ε ^ 3)) := by gcongr
        _ = 1 / (Real.pi * ε ^ 3) := by field_simp
    · have hsharp : sharpExteriorCutoff ε x = 0 := by
        simp [sharpExteriorCutoff, hx]
      simp [factor, hsharp]
      positivity
  have hint := φ.integrable.bdd_mul hfactorMeas hfactorBound
  have hmul : Integrable (fun x : Space =>
      sharpExteriorCutoff ε x *
        ((1 / (4 * Real.pi)) * bsGradKernel i j x) * φ x) :=
    by simpa only [factor] using hint
  have hmul' : Integrable (fun x : Space =>
      sharpExteriorCutoff ε x *
        ((1 / (4 * Real.pi)) * bsGradKernel i j x * φ x)) :=
    hmul.congr (ae_of_all _ fun x => by ring)
  rw [sharpExteriorCutoff_mul ε
    (fun x => (1 / (4 * Real.pi)) * bsGradKernel i j x * φ x)] at hmul'
  exact hmul'

theorem integrable_smoothPuncturedProduct_schwartz
    {ε : ℝ} (hε : 0 < ε) (j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Integrable (fun x : Space => smoothExteriorCutoff ε x *
      (φ * fun z : Space => bsVectorKernel z j) x) := by
  let factor : Space → ℝ := fun x =>
    smoothExteriorCutoff ε x * bsVectorKernel x j
  have hfactorMeas : AEStronglyMeasurable factor :=
    ((continuous_smoothExteriorCutoff ε).measurable.mul
      (measurable_bsVectorKernel_coord j)).aestronglyMeasurable
  have hfactorBound : ∀ᵐ x : Space, ‖factor x‖ ≤
      1 / (4 * Real.pi * ε ^ 2) := by
    filter_upwards [] with x
    by_cases hx : officialEuclideanNorm x ≤ ε
    · rw [show factor x = 0 by
          dsimp only [factor]
          rw [smoothExteriorCutoff_eq_zero hε hx]
          ring]
      simp only [norm_zero]
      positivity
    · dsimp only [factor]
      rw [norm_mul, Real.norm_eq_abs]
      have hc0 : 0 ≤ smoothExteriorCutoff ε x := Real.smoothTransition.nonneg _
      rw [abs_of_nonneg hc0]
      calc
        smoothExteriorCutoff ε x * ‖bsVectorKernel x j‖ ≤
            1 * ‖bsVectorKernel x j‖ :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
            (norm_nonneg _)
        _ ≤ 1 * (1 / (4 * Real.pi * ε ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (by simpa only [Real.norm_eq_abs] using
              bsVectorKernel_coord_abs_le_of_radius hε (le_of_not_ge hx) j)
            (by norm_num)
        _ = 1 / (4 * Real.pi * ε ^ 2) := one_mul _
  have hint := φ.integrable.bdd_mul hfactorMeas hfactorBound
  exact hint.congr (ae_of_all _ fun x => by
    dsimp only [factor]
    simp only [Pi.mul_apply]
    ring)

/-- Schwartz decay supplies every sharp/smooth truncation integrability input;
only the compact derivative-layer flux remains explicit. -/
theorem biotSavartPrincipalValue_identity_schwartz
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (L : ℝ)
    (hintDerivative : Integrable (fun x : Space =>
      fderiv ℝ φ x (basisVector i) * bsVectorKernel x j))
    (hpv : HasBiotSavartPrincipalValue i j φ L)
    (hflux : ∀ ε : ℝ, 0 < ε → Integrable (fun x : Space =>
      fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) *
        (φ * fun z : Space => bsVectorKernel z j) x)) :
    -(∫ x : Space, fderiv ℝ φ x (basisVector i) * bsVectorKernel x j) =
      L + (1 / 3 : ℝ) * basisVector i j * φ 0 := by
  apply biotSavartPrincipalValue_identity_of_smoothTruncation
    i j φ L hintDerivative hpv
  · intro ε hε
    exact integrable_smoothPuncturedGradient_schwartz hε i j φ
  · intro ε hε
    exact integrable_sharpPuncturedGradient_schwartz hε i j φ
  · exact hflux
  · intro ε hε
    exact integrable_smoothPuncturedProduct_schwartz hε j φ

private theorem deriv_smoothTransition_eq_zero_of_lt_zero {t : ℝ} (ht : t < 0) :
    deriv Real.smoothTransition t = 0 := by
  have hs' : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hs : DifferentiableAt ℝ Real.smoothTransition t :=
    (hs'.differentiable (by norm_num)) t
  have heq : Real.smoothTransition =ᶠ[nhds t] fun _ : ℝ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  exact hs.hasDerivAt.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq)

private theorem deriv_smoothTransition_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have hs' : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hs : DifferentiableAt ℝ Real.smoothTransition t :=
    (hs'.differentiable (by norm_num)) t
  have heq : Real.smoothTransition =ᶠ[nhds t] fun _ : ℝ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  exact hs.hasDerivAt.unique ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq)

private theorem continuous_deriv_smoothTransition :
    Continuous (deriv Real.smoothTransition) := by
  have hs : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  exact hs.continuous_deriv (by norm_num)

private def smoothFluxIntegrand (ε : ℝ) (i j : Fin 3)
    (φ : Space → ℝ) (x : Space) : ℝ :=
  fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) *
    (φ * fun z : Space => bsVectorKernel z j) x

private theorem continuous_smoothFluxIntegrand
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Continuous (smoothFluxIntegrand ε i j φ) := by
  apply continuous_iff_continuousAt.2
  intro x
  by_cases hx : x = 0
  · subst x
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hevent : ∀ᶠ z : Space in nhds 0,
        ‖z‖ < ε / Real.sqrt 3 := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space) (div_pos hε hsqrt)] with z hz
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have hzero : smoothFluxIntegrand ε i j φ =ᶠ[nhds 0] fun _ => 0 := by
      filter_upwards [hevent] with z hz
      have hoff : officialEuclideanNorm z < ε := by
        calc
          officialEuclideanNorm z ≤ Real.sqrt 3 * ‖z‖ := officialEuclideanNorm_le z
          _ < Real.sqrt 3 * (ε / Real.sqrt 3) :=
            mul_lt_mul_of_pos_left hz hsqrt
          _ = ε := by field_simp
      have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
      have harg : radiusSq z / ε ^ 2 - 1 < 0 := by
        rw [radiusSq_eq_officialEuclideanNorm_sq, sub_lt_zero,
          div_lt_one hεsq]
        exact (sq_lt_sq₀ (officialEuclideanNorm_nonneg z) hε.le).2 hoff
      rw [smoothFluxIntegrand, smoothExteriorCutoff_fderiv_basis,
        deriv_smoothTransition_eq_zero_of_lt_zero harg]
      ring
    apply ContinuousAt.congr_of_eventuallyEq continuousAt_const hzero
  · change ContinuousAt (fun z : Space =>
      fderiv ℝ (smoothExteriorCutoff ε) z (basisVector i) *
        (φ z * bsVectorKernel z j)) x
    have hk : ContinuousAt (fun z : Space => bsVectorKernel z j) x :=
      (differentiableAt_bsVectorKernel_coord hx j).continuousAt
    have hcut : ContinuousAt (fun z : Space =>
        fderiv ℝ (smoothExteriorCutoff ε) z (basisVector i)) x := by
      rw [show (fun z : Space =>
          fderiv ℝ (smoothExteriorCutoff ε) z (basisVector i)) =
          fun z => deriv Real.smoothTransition (radiusSq z / ε ^ 2 - 1) *
            (2 * z i / ε ^ 2) by
        funext z
        exact smoothExteriorCutoff_fderiv_basis ε z i]
      have hradius : Continuous radiusSq := by
        unfold radiusSq
        fun_prop
      have hcoord : Continuous (fun z : Space => 2 * z i / ε ^ 2) := by
        exact (by fun_prop : Continuous (fun z : Space => 2 * z i)).div_const _
      exact (continuous_deriv_smoothTransition.comp
        ((hradius.div_const _).sub continuous_const)).continuousAt.mul
          hcoord.continuousAt
    exact hcut.mul (φ.continuous.continuousAt.mul hk)

private theorem hasCompactSupport_smoothFluxIntegrand
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    HasCompactSupport (smoothFluxIntegrand ε i j φ) := by
  let R : ℝ := Real.sqrt 2 * ε
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) R)
  intro x hx
  have hxnorm : R < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hoff : R < officialEuclideanNorm x :=
    lt_of_lt_of_le hxnorm (norm_le_officialEuclideanNorm x)
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hraw : R ^ 2 < officialEuclideanNorm x ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg hsqrt.le hε.le)
      (officialEuclideanNorm_nonneg x)).2 hoff
  have harg : 1 < radiusSq x / ε ^ 2 - 1 := by
    rw [radiusSq_eq_officialEuclideanNorm_sq, lt_sub_iff_add_lt]
    norm_num
    apply (lt_div_iff₀ hεsq).2
    dsimp only [R] at hraw
    nlinarith
  rw [smoothFluxIntegrand, smoothExteriorCutoff_fderiv_basis,
    deriv_smoothTransition_eq_zero_of_one_lt harg]
  ring

theorem integrable_smoothPunctureFlux_schwartz
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Integrable (fun x : Space =>
      fderiv ℝ (smoothExteriorCutoff ε) x (basisVector i) *
        (φ * fun z : Space => bsVectorKernel z j) x) := by
  exact (continuous_smoothFluxIntegrand hε i j φ).integrable_of_hasCompactSupport
    (hasCompactSupport_smoothFluxIntegrand hε i j φ)

/-- Truncation-discharged Schwartz form: a sharp principal value implies the
distributional Biot--Savart gradient identity with the exact local term. -/
theorem biotSavartPrincipalValue_identity_schwartz_full
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (L : ℝ)
    (hintDerivative : Integrable (fun x : Space =>
      fderiv ℝ φ x (basisVector i) * bsVectorKernel x j))
    (hpv : HasBiotSavartPrincipalValue i j φ L) :
    -(∫ x : Space, fderiv ℝ φ x (basisVector i) * bsVectorKernel x j) =
      L + (1 / 3 : ℝ) * basisVector i j * φ 0 := by
  apply biotSavartPrincipalValue_identity_schwartz i j φ L hintDerivative hpv
  intro ε hε
  exact integrable_smoothPunctureFlux_schwartz hε i j φ

end Navier.Analysis.BiotSavartTruncationComparison
