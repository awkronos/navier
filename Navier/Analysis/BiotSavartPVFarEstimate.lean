import Navier.Analysis.BiotSavartPVSplitEstimate
import Navier.Analysis.BiotSavartMorrey

/-!
# Quantitative far-field estimate for the Biot--Savart principal value

The sharp Euclidean far region is paired with the translated `L²` vorticity
by Cauchy--Schwarz.  The kernel square is integrable there by comparison with
the three-dimensional Bessel weight.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace Navier.Analysis.BiotSavartPVFarEstimate

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartPuncture
open Navier.Analysis.BiotSavartConvolution
open Navier.Analysis.BiotSavartPVSplitEstimate
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.Vorticity

private theorem continuous_officialEuclideanNorm :
    Continuous officialEuclideanNorm := by
  rw [show officialEuclideanNorm = fun x : Space =>
      Real.sqrt (∑ k : Fin 3, |x k| ^ 2) by
    funext x
    exact officialEuclideanNorm_eq_sqrt_sum_sq x]
  fun_prop

private theorem measurableSet_pvFarSet : MeasurableSet pvFarSet := by
  rw [pvFarSet]
  exact measurableSet_le measurable_const
    continuous_officialEuclideanNorm.measurable

/-- The scalar Biot--Savart majorant belongs to `L²` on the actual Euclidean
far region used by the principal-value split. -/
theorem integrableOn_bsKernelScalar_sq_pvFarSet :
    IntegrableOn (fun z : Space => bsKernelScalar z ^ 2) pvFarSet volume := by
  have hne : ∀ z : Space, z ∈ pvFarSet → z ≠ 0 := by
    intro z hz h0
    subst z
    rw [pvFarSet] at hz
    simp [officialEuclideanNorm_eq_sqrt_sum_sq] at hz
    norm_num at hz
  have hcontK : ContinuousOn bsKernelScalar pvFarSet := by
    have hbr : ContinuousOn
        (fun z : Space => 1 / (4 * Real.pi * officialEuclideanNorm z ^ 3))
        pvFarSet := by
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact continuousOn_const.mul
          (continuous_officialEuclideanNorm.continuousOn.pow 3)
      · intro z hz
        have hpos : (0 : ℝ) < officialEuclideanNorm z :=
          lt_of_lt_of_le one_pos hz
        exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
          (pow_ne_zero 3 hpos.ne')
    exact hbr.congr fun z hz => bsKernelScalar_apply_of_ne_zero (hne z hz)
  have haes : AEStronglyMeasurable (fun z : Space => bsKernelScalar z ^ 2)
      (volume.restrict pvFarSet) :=
    (hcontK.pow 2).aestronglyMeasurable measurableSet_pvFarSet
  have hg : Integrable (fun z : Space =>
      (125 / (16 * Real.pi ^ 2)) *
        (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹) :=
    integrable_inv_one_add_normSq_sq.const_mul _
  refine (hg.integrableOn).mono' haes ?_
  rw [ae_restrict_iff' measurableSet_pvFarSet]
  filter_upwards with z hz
  have he : (1 : ℝ) ≤ officialEuclideanNorm z := hz
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hprod : officialEuclideanNorm z ≤ 2 * ‖z‖ :=
    (officialEuclideanNorm_le z).trans
      (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg z))
  have hzhalf : (1 / 2 : ℝ) ≤ ‖z‖ := by linarith
  have hnormpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by norm_num) hzhalf
  have hker := bsKernelScalar_sq_le (hne z hz)
  have hoge : ‖z‖ ≤ officialEuclideanNorm z :=
    norm_le_officialEuclideanNorm z
  have hstep : (officialEuclideanNorm z ^ 6)⁻¹ ≤ (‖z‖ ^ 6)⁻¹ :=
    inv_anti₀ (pow_pos hnormpos 6)
      (pow_le_pow_left₀ (norm_nonneg z) hoge 6)
  have hw : (1 : ℝ) + ‖z‖ ^ 2 ≤ 5 * ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg ‖z‖]
  have hpow : ((1 : ℝ) + ‖z‖ ^ 2) ^ 3 ≤
      (5 * ‖z‖ ^ 2) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hw 3
  have hinv3 : ((5 * ‖z‖ ^ 2) ^ 3)⁻¹ ≤
      (((1 : ℝ) + ‖z‖ ^ 2) ^ 3)⁻¹ :=
    inv_anti₀ (by positivity) hpow
  have hbase : (1 : ℝ) ≤ 1 + ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg ‖z‖]
  have h32 : (((1 : ℝ) + ‖z‖ ^ 2) ^ 3)⁻¹ ≤
      (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hbase (by norm_num))
  have h6 : (‖z‖ ^ 6)⁻¹ ≤
      125 * (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    have heq : ((5 * ‖z‖ ^ 2) ^ 3)⁻¹ =
        (1 / 125) * (‖z‖ ^ 6)⁻¹ := by
      rw [show (5 * ‖z‖ ^ 2) ^ 3 = 125 * ‖z‖ ^ 6 by ring,
        mul_inv]
      norm_num
    rw [show (‖z‖ ^ 6)⁻¹ =
        125 * ((5 * ‖z‖ ^ 2) ^ 3)⁻¹ by rw [heq]; ring]
    exact mul_le_mul_of_nonneg_left (hinv3.trans h32) (by norm_num)
  have hbound : bsKernelScalar z ^ 2 ≤
      (125 / (16 * Real.pi ^ 2)) *
        (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ := by
    calc
      bsKernelScalar z ^ 2 ≤
          1 / (16 * Real.pi ^ 2 * officialEuclideanNorm z ^ 6) := hker
      _ = (1 / (16 * Real.pi ^ 2)) *
          (officialEuclideanNorm z ^ 6)⁻¹ := by ring
      _ ≤ (1 / (16 * Real.pi ^ 2)) * (‖z‖ ^ 6)⁻¹ :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ (1 / (16 * Real.pi ^ 2)) *
          (125 * (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      _ = (125 / (16 * Real.pi ^ 2)) *
          (((1 : ℝ) + ‖z‖ ^ 2) ^ 2)⁻¹ := by ring
  have hnn : 0 ≤ bsKernelScalar z ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact hbound

/-- Every curl component of the actual far PV convolution is controlled by
the stated full vorticity `L²` majorant. -/
theorem exists_pvFarCurlComponent_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (M₂ : ℝ),
        (∫ y : Space,
          officialEuclideanNorm (staticCurl (⇑u) y) ^ 2) ≤ M₂ →
        ∀ (x : Space) (i j k : Fin 3),
          |∫ z in pvFarSet,
            (1 / (4 * Real.pi)) * bsGradKernel i j z *
              curlComponentSchwartz u k (x - z)| ≤
            C * Real.sqrt M₂ := by
  let K : ℝ := Real.sqrt
    (∫ z in pvFarSet, (4 * bsKernelScalar z) ^ 2)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  refine ⟨K + 1, by linarith, ?_⟩
  intro u M₂ hM₂ x i j k
  let f : Space → ℝ := fun z =>
    (pvFarSet.indicator fun y => 4 * bsKernelScalar y) z
  let g : Space → ℝ := fun z =>
    officialEuclideanNorm (staticCurlSchwartz u (x - z))
  have hfcont : AEStronglyMeasurable f volume := by
    have hk : AEStronglyMeasurable (fun z : Space => 4 * bsKernelScalar z)
        volume := (measurable_const.mul measurable_bsKernelScalar).aestronglyMeasurable
    exact hk.indicator measurableSet_pvFarSet
  have hfSq : Integrable (fun z : Space => f z ^ 2) := by
    have hi : Integrable (pvFarSet.indicator
        (fun z : Space => bsKernelScalar z ^ 2)) :=
      (integrable_indicator_iff measurableSet_pvFarSet).mpr
        integrableOn_bsKernelScalar_sq_pvFarSet
    refine (hi.const_mul 16).congr (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ pvFarSet
    · simp [f, hz]
      ring
    · simp [f, hz]
  have hfmem : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq hfcont).mpr hfSq
  have hcurlInt : Integrable (fun y : Space =>
      officialEuclideanNorm (staticCurlSchwartz u y) ^ 2) := by
    have hbase := integrable_normSq_iteratedFDeriv_space
      (staticCurlSchwartz u) 0
    have hcont : Continuous (fun y : Space =>
        officialEuclideanNorm (staticCurlSchwartz u y) ^ 2) :=
      (continuous_officialEuclideanNorm.comp
        (staticCurlSchwartz u).continuous).pow 2
    refine (hbase.const_mul 4).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      norm_iteratedFDeriv_zero]
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have hnorm := officialEuclideanNorm_le (staticCurlSchwartz u y)
    have hle : officialEuclideanNorm (staticCurlSchwartz u y) ≤
        2 * ‖staticCurlSchwartz u y‖ :=
      hnorm.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _))
    nlinarith [officialEuclideanNorm_nonneg (staticCurlSchwartz u y),
      norm_nonneg (staticCurlSchwartz u y)]
  have hgSq : Integrable (fun z : Space => g z ^ 2) := by
    exact hcurlInt.comp_sub_left x
  have hgcont : AEStronglyMeasurable g volume := by
    exact (continuous_officialEuclideanNorm.comp
      ((staticCurlSchwartz u).continuous.comp (by fun_prop))).aestronglyMeasurable
  have hgmem : MemLp g 2 volume :=
    (memLp_two_iff_integrable_sq hgcont).mpr hgSq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume) (f := f) (g := g)
    (by rw [Real.holderConjugate_iff]; norm_num : Real.HolderConjugate 2 2)
    (Filter.Eventually.of_forall fun z => by
      change 0 ≤ (pvFarSet.indicator (fun y => 4 * bsKernelScalar y)) z
      by_cases hz : z ∈ pvFarSet <;> simp [hz, bsKernelScalar_nonneg])
    (Filter.Eventually.of_forall fun z => officialEuclideanNorm_nonneg _)
    (by simpa using hfmem) (by simpa using hgmem)
  have hgsqIntegral : (∫ z : Space, g z ^ 2) ≤ M₂ := by
    calc
      (∫ z : Space, g z ^ 2) =
          ∫ y : Space,
            officialEuclideanNorm (staticCurlSchwartz u y) ^ 2 := by
        simpa only [g] using
          (MeasureTheory.integral_sub_left_eq_self
            (fun y : Space =>
              officialEuclideanNorm (staticCurlSchwartz u y) ^ 2)
            volume x)
      _ = ∫ y : Space,
          officialEuclideanNorm (staticCurl (⇑u) y) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with y
        rw [staticCurlSchwartz_apply]
      _ ≤ M₂ := hM₂
  have hfIntegral : (∫ z : Space, f z ^ 2) =
      ∫ z in pvFarSet, (4 * bsKernelScalar z) ^ 2 := by
    rw [← MeasureTheory.integral_indicator measurableSet_pvFarSet]
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ pvFarSet <;> simp [f, hz]
  have hpoint : ∀ z : Space,
      ‖(pvFarSet.indicator (fun y =>
          (1 / (4 * Real.pi)) * bsGradKernel i j y *
            curlComponentSchwartz u k (x - y)) z)‖ ≤ f z * g z := by
    intro z
    by_cases hz : z ∈ pvFarSet
    · rw [Set.indicator_of_mem hz]
      dsimp only [f, g]
      rw [Set.indicator_of_mem hz, norm_mul, Real.norm_eq_abs]
      have hkern := scaled_bsGradKernel_abs_le i j z
      have hcoord : |curlComponentSchwartz u k (x - z)| ≤
          officialEuclideanNorm (staticCurlSchwartz u (x - z)) := by
        rw [curlComponentSchwartz_apply]
        exact coord_abs_le_officialEuclideanNorm _ k
      exact mul_le_mul hkern hcoord (abs_nonneg _)
        (mul_nonneg (by norm_num) (bsKernelScalar_nonneg z))
    · rw [Set.indicator_of_notMem hz]
      simp [f, hz]
  have hfgInt : Integrable (f * g) := hfmem.integrable_mul hgmem
  have hactual := integrable_piece (ε := (1 / 2 : ℝ)) (by norm_num)
    i j (curlComponentSchwartz u k) x measurableSet_pvFarSet
    (fun z hz => lt_of_lt_of_le (by norm_num : (1 / 2 : ℝ) < 1) hz)
  have hnorm := (MeasureTheory.norm_integral_le_integral_norm _).trans
    (integral_mono hactual.norm hfgInt (fun z => hpoint z))
  rw [← MeasureTheory.integral_indicator measurableSet_pvFarSet]
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans ?_
  calc
    (∫ z : Space, f z * g z) ≤
        Real.sqrt (∫ z : Space, f z ^ 2) *
          Real.sqrt (∫ z : Space, g z ^ 2) := by
      simpa [Real.sqrt_eq_rpow] using hholder
    _ ≤ K * Real.sqrt M₂ := by
      dsimp only [K]
      rw [hfIntegral]
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt hgsqIntegral) (Real.sqrt_nonneg _)
    _ ≤ (K + 1) * Real.sqrt M₂ :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

end Navier.Analysis.BiotSavartPVFarEstimate
