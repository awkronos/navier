import Navier.Analysis.LittlewoodPaleyBlock
import Navier.Analysis.LittlewoodPaleyPartition

/-!
# Physical Littlewood--Paley curl block estimate

This module joins the mechanical physical Fourier facts from
`LittlewoodPaleyBlock` to the normalized partition, kernel, and convolution
provider in `LittlewoodPaleyPartition`. It proves the scale-uniform LP3 block
bound under the actual pointwise vorticity bound. It does not assert the final
`GradSupLogHyp`, whose reconstruction and shell assembly remain separate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace Navier.Analysis.LittlewoodPaleyPhysical

open Navier Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.WienerGradLog
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.Vorticity (staticCurl)
open Navier.Analysis.LittlewoodPaleyBlock
open Navier.Analysis.LittlewoodPaleyPartition

/-- Every component of the unnormalized Fourier curl profile is integrable on
an actual represented Wiener datum. -/
theorem integrable_partitionCurlMoment
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    (r : Fin 3) : Integrable (partitionCurlMoment a r) := by
  fin_cases r
  · change Integrable (fun ξ : ES =>
      ((ξ 1 : ℝ) : ℂ) * a ξ 2 - ((ξ 2 : ℝ) : ℂ) * a ξ 1)
    exact (integrable_moment hr.datum 2 1).sub (integrable_moment hr.datum 1 2)
  · change Integrable (fun ξ : ES =>
      ((ξ 2 : ℝ) : ℂ) * a ξ 0 - ((ξ 0 : ℝ) : ℂ) * a ξ 2)
    exact (integrable_moment hr.datum 0 2).sub (integrable_moment hr.datum 2 0)
  · change Integrable (fun ξ : ES =>
      ((ξ 0 : ℝ) : ℂ) * a ξ 1 - ((ξ 1 : ℝ) : ℂ) * a ξ 0)
    exact (integrable_moment hr.datum 1 0).sub (integrable_moment hr.datum 0 1)

/-- Multiplication by the actual normalized annular Riesz symbol preserves
integrability. -/
theorem integrable_partitionAnnularRiesz_mul
    (q : ℤ) (i k : Fin 3) {f : ES → ℂ} (hf : Integrable f) :
    Integrable (fun ξ : ES => partitionAnnularRieszSymbol q i k ξ * f ξ) := by
  apply hf.bdd_mul
  · exact (partitionAnnularRieszSchwartz q i k).continuous.aestronglyMeasurable
  · filter_upwards [] with ξ
    simpa only [SchwartzMap.toBoundedContinuousFunction_apply,
      partitionAnnularRieszSchwartz_apply] using
      (partitionAnnularRieszSchwartz q i k).toBoundedContinuousFunction.norm_coe_le_norm ξ

/-- The inverse transform of each curl-moment component is pointwise bounded
by the physical vorticity supremum. The real part vanishes by Hermitian
symmetry; the imaginary part is the corresponding `staticCurl` coordinate. -/
theorem norm_fourierInv_partitionCurlMoment_le
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    {y : ℝ}
    (hω : ∀ x : Space,
      Navier.Analysis.OfficialABEncoding.officialEuclideanNorm (staticCurl v x) ≤ y)
    (r : Fin 3) (z : ES) :
    ‖FourierTransform.fourierInv (partitionCurlMoment a r) z‖ ≤ y := by
  obtain ⟨x, rfl⟩ := euclidPoint_surjective z
  fin_cases r
  · change ‖FourierTransform.fourierInv
      (fun ξ : ES => ((ξ 1 : ℝ) : ℂ) * a ξ 2 - ((ξ 2 : ℝ) : ℂ) * a ξ 1)
        (euclidPoint x)‖ ≤ y
    rw [fourierInv_sub_fn (integrable_moment hr.datum 2 1)
      (integrable_moment hr.datum 1 2)]
    have hre :
        (FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 1 : ℝ) : ℂ) * a ξ 2) (euclidPoint x) -
        FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 2 : ℝ) : ℂ) * a ξ 1) (euclidPoint x)).re = 0 := by
      rw [Complex.sub_re, moment_im hr.datum 2 1, moment_im hr.datum 1 2]
      simp
    have him :
        (FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 1 : ℝ) : ℂ) * a ξ 2) (euclidPoint x) -
        FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 2 : ℝ) : ℂ) * a ξ 1) (euclidPoint x)).im =
          staticCurl v x 0 := by
      rw [Complex.sub_im, ← hr.fderiv_coord_im x 2 1,
        ← hr.fderiv_coord_im x 1 2, staticCurl_comp_zero]
    rw [Complex.norm_def, Complex.normSq_apply, hre, him, zero_mul, zero_add,
      ← pow_two, Real.sqrt_sq_eq_abs]
    have hcoord : |staticCurl v x 0| ≤ ‖staticCurl v x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (staticCurl v x) 0
    exact (hcoord.trans
      (Navier.Analysis.OfficialABEncoding.norm_le_officialEuclideanNorm _)).trans (hω x)
  · change ‖FourierTransform.fourierInv
      (fun ξ : ES => ((ξ 2 : ℝ) : ℂ) * a ξ 0 - ((ξ 0 : ℝ) : ℂ) * a ξ 2)
        (euclidPoint x)‖ ≤ y
    rw [fourierInv_sub_fn (integrable_moment hr.datum 0 2)
      (integrable_moment hr.datum 2 0)]
    have hre :
        (FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 2 : ℝ) : ℂ) * a ξ 0) (euclidPoint x) -
        FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 0 : ℝ) : ℂ) * a ξ 2) (euclidPoint x)).re = 0 := by
      rw [Complex.sub_re, moment_im hr.datum 0 2, moment_im hr.datum 2 0]
      simp
    have him :
        (FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 2 : ℝ) : ℂ) * a ξ 0) (euclidPoint x) -
        FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 0 : ℝ) : ℂ) * a ξ 2) (euclidPoint x)).im =
          staticCurl v x 1 := by
      rw [Complex.sub_im, ← hr.fderiv_coord_im x 0 2,
        ← hr.fderiv_coord_im x 2 0, staticCurl_comp_one]
    rw [Complex.norm_def, Complex.normSq_apply, hre, him, zero_mul, zero_add,
      ← pow_two, Real.sqrt_sq_eq_abs]
    have hcoord : |staticCurl v x 1| ≤ ‖staticCurl v x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (staticCurl v x) 1
    exact (hcoord.trans
      (Navier.Analysis.OfficialABEncoding.norm_le_officialEuclideanNorm _)).trans (hω x)
  · change ‖FourierTransform.fourierInv
      (fun ξ : ES => ((ξ 0 : ℝ) : ℂ) * a ξ 1 - ((ξ 1 : ℝ) : ℂ) * a ξ 0)
        (euclidPoint x)‖ ≤ y
    rw [fourierInv_sub_fn (integrable_moment hr.datum 1 0)
      (integrable_moment hr.datum 0 1)]
    have hre :
        (FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 0 : ℝ) : ℂ) * a ξ 1) (euclidPoint x) -
        FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 1 : ℝ) : ℂ) * a ξ 0) (euclidPoint x)).re = 0 := by
      rw [Complex.sub_re, moment_im hr.datum 1 0, moment_im hr.datum 0 1]
      simp
    have him :
        (FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 0 : ℝ) : ℂ) * a ξ 1) (euclidPoint x) -
        FourierTransform.fourierInv
          (fun ξ : ES => ((ξ 1 : ℝ) : ℂ) * a ξ 0) (euclidPoint x)).im =
          staticCurl v x 2 := by
      rw [Complex.sub_im, ← hr.fderiv_coord_im x 1 0,
        ← hr.fderiv_coord_im x 0 1, staticCurl_comp_two]
    rw [Complex.norm_def, Complex.normSq_apply, hre, him, zero_mul, zero_add,
      ← pow_two, Real.sqrt_sq_eq_abs]
    have hcoord : |staticCurl v x 2| ≤ ‖staticCurl v x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (staticCurl v x) 2
    exact (hcoord.trans
      (Navier.Analysis.OfficialABEncoding.norm_le_officialEuclideanNorm _)).trans (hω x)

/-- **LP3.** Every normalized derivative block is bounded uniformly in the
dyadic scale by the pointwise physical vorticity bound. -/
theorem exists_uniform_partitionMomentBlock_le_curl
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    {y : ℝ} (hy : 0 ≤ y)
    (hω : ∀ x : Space,
      Navier.Analysis.OfficialABEncoding.officialEuclideanNorm (staticCurl v x) ≤ y)
    (i k : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℤ) (x : ES),
      ‖partitionMomentBlock a i k q x‖ ≤ C * y := by
  fin_cases i
  · obtain ⟨C₂, hC₂, h₂⟩ := partitionAnnularRiesz_young_uniform 2 k
    obtain ⟨C₁, hC₁, h₁⟩ := partitionAnnularRiesz_young_uniform 1 k
    refine ⟨C₂ + C₁, add_nonneg hC₂ hC₁, ?_⟩
    intro q x
    change ‖partitionMomentBlock a 0 k q x‖ ≤ (C₂ + C₁) * y
    rw [partitionMomentBlock_eq_rieszCurl hr x 0 k q, ← Real.fourierInv_eq]
    change ‖FourierTransform.fourierInv (fun ξ : ES =>
      partitionAnnularRieszSymbol q 2 k ξ * partitionCurlMoment a 1 ξ -
      partitionAnnularRieszSymbol q 1 k ξ * partitionCurlMoment a 2 ξ) x‖ ≤
        (C₂ + C₁) * y
    rw [fourierInv_sub_fn
      (integrable_partitionAnnularRiesz_mul q 2 k
        (integrable_partitionCurlMoment hr 1))
      (integrable_partitionAnnularRiesz_mul q 1 k
        (integrable_partitionCurlMoment hr 2))]
    calc
      ‖FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 2 k ξ *
            partitionCurlMoment a 1 ξ) x -
        FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 1 k ξ *
            partitionCurlMoment a 2 ξ) x‖
          ≤ ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 2 k ξ *
                partitionCurlMoment a 1 ξ) x‖ +
            ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 1 k ξ *
                partitionCurlMoment a 2 ξ) x‖ := norm_sub_le _ _
      _ ≤ C₂ * y + C₁ * y := add_le_add
        (h₂ q (integrable_partitionCurlMoment hr 1) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 1) x)
        (h₁ q (integrable_partitionCurlMoment hr 2) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 2) x)
      _ = (C₂ + C₁) * y := by ring
  · obtain ⟨C₀, hC₀, h₀⟩ := partitionAnnularRiesz_young_uniform 0 k
    obtain ⟨C₂, hC₂, h₂⟩ := partitionAnnularRiesz_young_uniform 2 k
    refine ⟨C₀ + C₂, add_nonneg hC₀ hC₂, ?_⟩
    intro q x
    change ‖partitionMomentBlock a 1 k q x‖ ≤ (C₀ + C₂) * y
    rw [partitionMomentBlock_eq_rieszCurl hr x 1 k q, ← Real.fourierInv_eq]
    change ‖FourierTransform.fourierInv (fun ξ : ES =>
      partitionAnnularRieszSymbol q 0 k ξ * partitionCurlMoment a 2 ξ -
      partitionAnnularRieszSymbol q 2 k ξ * partitionCurlMoment a 0 ξ) x‖ ≤
        (C₀ + C₂) * y
    rw [fourierInv_sub_fn
      (integrable_partitionAnnularRiesz_mul q 0 k
        (integrable_partitionCurlMoment hr 2))
      (integrable_partitionAnnularRiesz_mul q 2 k
        (integrable_partitionCurlMoment hr 0))]
    calc
      ‖FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 0 k ξ *
            partitionCurlMoment a 2 ξ) x -
        FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 2 k ξ *
            partitionCurlMoment a 0 ξ) x‖
          ≤ ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 0 k ξ *
                partitionCurlMoment a 2 ξ) x‖ +
            ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 2 k ξ *
                partitionCurlMoment a 0 ξ) x‖ := norm_sub_le _ _
      _ ≤ C₀ * y + C₂ * y := add_le_add
        (h₀ q (integrable_partitionCurlMoment hr 2) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 2) x)
        (h₂ q (integrable_partitionCurlMoment hr 0) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 0) x)
      _ = (C₀ + C₂) * y := by ring
  · obtain ⟨C₁, hC₁, h₁⟩ := partitionAnnularRiesz_young_uniform 1 k
    obtain ⟨C₀, hC₀, h₀⟩ := partitionAnnularRiesz_young_uniform 0 k
    refine ⟨C₁ + C₀, add_nonneg hC₁ hC₀, ?_⟩
    intro q x
    change ‖partitionMomentBlock a 2 k q x‖ ≤ (C₁ + C₀) * y
    rw [partitionMomentBlock_eq_rieszCurl hr x 2 k q, ← Real.fourierInv_eq]
    change ‖FourierTransform.fourierInv (fun ξ : ES =>
      partitionAnnularRieszSymbol q 1 k ξ * partitionCurlMoment a 0 ξ -
      partitionAnnularRieszSymbol q 0 k ξ * partitionCurlMoment a 1 ξ) x‖ ≤
        (C₁ + C₀) * y
    rw [fourierInv_sub_fn
      (integrable_partitionAnnularRiesz_mul q 1 k
        (integrable_partitionCurlMoment hr 0))
      (integrable_partitionAnnularRiesz_mul q 0 k
        (integrable_partitionCurlMoment hr 1))]
    calc
      ‖FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 1 k ξ *
            partitionCurlMoment a 0 ξ) x -
        FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 0 k ξ *
            partitionCurlMoment a 1 ξ) x‖
          ≤ ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 1 k ξ *
                partitionCurlMoment a 0 ξ) x‖ +
            ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 0 k ξ *
                partitionCurlMoment a 1 ξ) x‖ := norm_sub_le _ _
      _ ≤ C₁ * y + C₀ * y := add_le_add
        (h₁ q (integrable_partitionCurlMoment hr 0) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 0) x)
        (h₀ q (integrable_partitionCurlMoment hr 1) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 1) x)
      _ = (C₁ + C₀) * y := by ring

theorem norm_partitionMomentBlock_four_mul_add_le_H3
    (a : ES → ComplexSpace)
    (ha : Measurable a)
    (hH3 : Integrable (fun ξ : ES =>
      ‖ξ‖ ^ 6 * ∑ m : Fin 3, ‖a ξ m‖ ^ 2))
    (i k : Fin 3) (j : ℕ) (r : Fin 4) (x : ES) :
    ‖partitionMomentBlock a i k (4 * (j : ℤ) + (r : ℕ)) x‖ ≤
      (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) *
        ((1 : ℝ) / 4) ^ j := by
  have hs := norm_partitionMomentBlock_le_H3 a ha hH3 i k
    (4 * (j : ℤ) + (r : ℕ)) x
  have hfour : ((2 : ℝ) ^ (4 * (j : ℤ)))⁻¹ =
      (((1 : ℝ) / 4) ^ j) ^ 2 := by
    rw [zpow_mul, zpow_natCast]
    norm_num [div_pow]
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
    congr 1
    omega
  have hscale : ((2 : ℝ) ^ (4 * (j : ℤ) + (r : ℕ)))⁻¹ ≤
      (((1 : ℝ) / 4) ^ j) ^ 2 := by
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_inv_rev, hfour,
      zpow_natCast]
    have hr1 : ((2 : ℝ) ^ (r : ℕ))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    nlinarith [sq_nonneg (((1 : ℝ) / 4) ^ j)]
  have hweight : 0 ≤ ∫ ξ : ES, partitionHighWeight ξ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hsqrt :
      Real.sqrt (((2 : ℝ) ^ (4 * (j : ℤ) + (r : ℕ)))⁻¹ *
        ∫ ξ : ES, partitionHighWeight ξ ^ 2) ≤
      ((1 : ℝ) / 4) ^ j * partitionHighConstant := by
    calc
      Real.sqrt (((2 : ℝ) ^ (4 * (j : ℤ) + (r : ℕ)))⁻¹ *
          ∫ ξ : ES, partitionHighWeight ξ ^ 2)
          ≤ Real.sqrt (((((1 : ℝ) / 4) ^ j) ^ 2) *
            ∫ ξ : ES, partitionHighWeight ξ ^ 2) :=
              Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hscale hweight)
      _ = ((1 : ℝ) / 4) ^ j * partitionHighConstant := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) j)]
        rfl
  calc
    ‖partitionMomentBlock a i k (4 * (j : ℤ) + (r : ℕ)) x‖
        ≤ Real.sqrt (((2 : ℝ) ^ (4 * (j : ℤ) + (r : ℕ)))⁻¹ *
            ∫ ξ : ES, partitionHighWeight ξ ^ 2) *
              Navier.Analysis.WienerGradLog.profH3 a := hs
    _ ≤ (((1 : ℝ) / 4) ^ j * partitionHighConstant) *
          Navier.Analysis.WienerGradLog.profH3 a :=
      mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
    _ = (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) *
          ((1 : ℝ) / 4) ^ j := by ring

theorem tsum_int_split {f : ℤ → ℝ} (hf : Summable f) :
    (∑' q : ℤ, f q) = (∑' n : ℕ, f (n : ℤ)) +
      ∑' n : ℕ, f (Int.negSucc n) := by
  have hp : Summable (fun n : ℕ => f (n : ℤ)) :=
    hf.comp_injective (fun _ _ h => Int.ofNat_inj.mp h)
  have hn : Summable (fun n : ℕ => f (Int.negSucc n)) :=
    hf.comp_injective (fun _ _ h => Int.negSucc_inj.mp h)
  rw [← (Equiv.intEquivNatSumNat.symm.tsum_eq f)]
  exact hp.tsum_sum hn

theorem tsum_nonneg_partitionMomentBlock_le_high
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    (ha : Measurable a)
    (hH3 : Integrable (fun ξ : ES =>
      ‖ξ‖ ^ 6 * ∑ m : Fin 3, ‖a ξ m‖ ^ 2))
    (i k : Fin 3) (x : ES) {U : ℝ} (hU : 0 < U)
    (hunif : ∀ q : ℤ, ‖partitionMomentBlock a i k q x‖ ≤ U) :
    (∑' n : ℕ, ‖partitionMomentBlock a i k (n : ℤ) x‖) ≤
      32 * U * (1 + Real.log (1 +
        (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) / U)) := by
  let f : ℕ → ℝ := fun n => ‖partitionMomentBlock a i k (n : ℤ) x‖
  have hf : Summable f := by
    have hs := hasSum_partitionMomentBlock hr x i k
    exact hs.summable.norm.comp_injective (fun _ _ h => Int.ofNat_inj.mp h)
  rw [Nat.sumByResidueClasses hf 4]
  have hY : 0 ≤ partitionHighConstant *
      Navier.Analysis.WienerGradLog.profH3 a :=
    mul_nonneg partitionHighConstant_nonneg (Real.sqrt_nonneg _)
  have hj : ∀ j : ZMod 4,
      (∑' m : ℕ, f (j.val + 4 * m)) ≤
        8 * U * (1 + Real.log (1 +
          (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) / U)) := by
    intro j
    let g : ℕ → ℝ := fun m => min U
      ((partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) *
        ((1 : ℝ) / 4) ^ m)
    have hg : Summable g := by
      have hgeom : Summable (fun m : ℕ =>
          (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) *
            ((1 : ℝ) / 4) ^ m) :=
        Summable.mul_left _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      exact Summable.of_nonneg_of_le
        (fun m => le_min hU.le (mul_nonneg hY (pow_nonneg (by norm_num) m)))
        (fun m => min_le_right _ _) hgeom
    have hfm : Summable (fun m : ℕ => f (j.val + 4 * m)) :=
      hf.comp_injective (fun m n h => by omega)
    have hpoint : ∀ m : ℕ, f (j.val + 4 * m) ≤ g m := by
      intro m
      apply le_min
      · exact hunif _
      · dsimp [f, g]
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_comm,
          mul_comm] using
          norm_partitionMomentBlock_four_mul_add_le_H3
            a ha hH3 i k m (⟨j.val, j.val_lt⟩ : Fin 4) x
    exact (hfm.tsum_le_tsum hpoint hg).trans
      (blockEnvelopeLogBound hU hY)
  calc
    ∑ j : ZMod 4, ∑' m : ℕ, f (j.val + 4 * m)
        ≤ ∑ _j : ZMod 4, 8 * U * (1 + Real.log (1 +
          (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) / U)) :=
      Finset.sum_le_sum fun j _ => hj j
    _ = 32 * U * (1 + Real.log (1 +
          (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) / U)) := by
      simp
      ring

theorem tsum_negSucc_partitionMomentBlock_le_low
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    (i k : Fin 3) (x : ES) {U : ℝ} (hU : 0 < U)
    (hunif : ∀ q : ℤ, ‖partitionMomentBlock a i k q x‖ ≤ U) :
    (∑' n : ℕ, ‖partitionMomentBlock a i k (Int.negSucc n) x‖) ≤
      8 * U * (1 + Real.log (1 +
        (partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) / U)) := by
  let f : ℕ → ℝ := fun n => ‖partitionMomentBlock a i k (Int.negSucc n) x‖
  have hf : Summable f := by
    have hs := (hasSum_partitionMomentBlock hr x i k).summable.norm
    exact hs.comp_injective (fun _ _ h => Int.negSucc_inj.mp h)
  let g : ℕ → ℝ := fun n => min U
    ((partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) *
      ((1 : ℝ) / 4) ^ n)
  have hE : 0 ≤ partitionLowConstant *
      Navier.Analysis.WienerGradLog.profL2 a :=
    mul_nonneg partitionLowConstant_nonneg (Real.sqrt_nonneg _)
  have hg : Summable g := by
    have hgeom : Summable (fun n : ℕ =>
        (partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) *
          ((1 : ℝ) / 4) ^ n) :=
      Summable.mul_left _ (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    exact Summable.of_nonneg_of_le
      (fun n => le_min hU.le (mul_nonneg hE (pow_nonneg (by norm_num) n)))
      (fun n => min_le_right _ _) hgeom
  have hpoint : ∀ n : ℕ, f n ≤ g n := by
    intro n
    apply le_min
    · exact hunif _
    · dsimp [f, g]
      have hlow := norm_partitionMomentBlock_neg_le_L2 a hr.datum.meas
        hr.integrable_profL2_integrand i k (n + 1) x
      rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega]
      calc
        ‖partitionMomentBlock a i k (-((n + 1 : ℕ) : ℤ)) x‖
            ≤ (partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) *
              ((1 : ℝ) / 4) ^ (n + 1) := hlow
        _ ≤ (partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) *
              ((1 : ℝ) / 4) ^ n := by
          apply mul_le_mul_of_nonneg_left _ hE
          rw [pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n]
  exact (hf.tsum_le_tsum hpoint hg).trans
    (blockEnvelopeLogBound hU hE)

theorem exists_fourierInv_moment_le_shells
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    {y : ℝ} (hy : 0 < y)
    (hω : ∀ x : Space,
      Navier.Analysis.OfficialABEncoding.officialEuclideanNorm
        (Navier.Analysis.Vorticity.staticCurl v x) ≤ y)
    (x : ES) (i k : Fin 3) :
    ∃ A : ℝ, 1 ≤ A ∧
      ‖FourierTransform.fourierInv
        (fun ξ : ES => ((ξ k : ℝ) : ℂ) * a ξ i) x‖ ≤
        32 * (A * y) * (1 + Real.log (1 +
          (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) / (A * y))) +
        8 * (A * y) * (1 + Real.log (1 +
          (partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) / (A * y))) := by
  obtain ⟨C, hC, hblock⟩ :=
    exists_uniform_partitionMomentBlock_le_curl hr hy.le hω i k
  let A : ℝ := C + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hAy : 0 < A * y := mul_pos (lt_of_lt_of_le zero_lt_one hA) hy
  have hunif : ∀ q : ℤ, ‖partitionMomentBlock a i k q x‖ ≤ A * y := by
    intro q
    exact (hblock q x).trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) hy.le)
  have hs := hasSum_partitionMomentBlock hr x i k
  have hnorm := hs.summable.norm
  refine ⟨A, hA, ?_⟩
  calc
    ‖FourierTransform.fourierInv
        (fun ξ : ES => ((ξ k : ℝ) : ℂ) * a ξ i) x‖
        = ‖∑' q : ℤ, partitionMomentBlock a i k q x‖ := by rw [hs.tsum_eq]
    _ ≤ ∑' q : ℤ, ‖partitionMomentBlock a i k q x‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = (∑' n : ℕ, ‖partitionMomentBlock a i k (n : ℤ) x‖) +
        ∑' n : ℕ, ‖partitionMomentBlock a i k (Int.negSucc n) x‖ :=
      tsum_int_split hnorm
    _ ≤ 32 * (A * y) * (1 + Real.log (1 +
          (partitionHighConstant * Navier.Analysis.WienerGradLog.profH3 a) / (A * y))) +
        8 * (A * y) * (1 + Real.log (1 +
          (partitionLowConstant * Navier.Analysis.WienerGradLog.profL2 a) / (A * y))) :=
      add_le_add
        (tsum_nonneg_partitionMomentBlock_le_high hr hr.datum.meas
          hr.integrable_profH3_integrand i k x hAy hunif)
        (tsum_negSucc_partitionMomentBlock_le_low hr i k x hAy hunif)

theorem exists_global_partitionAnnularRiesz_young :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i k : Fin 3) (q : ℤ) {f : ES → ℂ}, Integrable f →
      ∀ (y : ℝ), 0 ≤ y →
        (∀ z : ES, ‖FourierTransform.fourierInv f z‖ ≤ y) →
        ∀ x : ES,
          ‖FourierTransform.fourierInv
            (fun ξ : ES => partitionAnnularRieszSymbol q i k ξ * f ξ) x‖ ≤
            C * y := by
  choose C hC hY using fun i k : Fin 3 => partitionAnnularRiesz_young_uniform i k
  let M : ℝ := ∑ i : Fin 3, ∑ k : Fin 3, C i k
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hC i k
  refine ⟨M, hM, ?_⟩
  intro i k q f hf y hy hfy x
  have hik : C i k ≤ M := by
    calc
      C i k ≤ ∑ k' : Fin 3, C i k' :=
        Finset.single_le_sum (fun k' _ => hC i k') (Finset.mem_univ k)
      _ ≤ ∑ i' : Fin 3, ∑ k' : Fin 3, C i' k' :=
        Finset.single_le_sum
          (fun i' _ => Finset.sum_nonneg fun k' _ => hC i' k')
          (Finset.mem_univ i)
  exact (hY i k q hf y hy hfy x).trans
    (mul_le_mul_of_nonneg_right hik hy)

/-- Global LP3 constant, selected before the represented field and datum. -/
theorem exists_global_partitionMomentBlock_le_curl :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {v : VelocityField} {a : ES → ComplexSpace}, Rep v a →
      ∀ {y : ℝ}, 0 ≤ y →
        (∀ x : Space,
          Navier.Analysis.OfficialABEncoding.officialEuclideanNorm (staticCurl v x) ≤ y) →
        ∀ (i k : Fin 3) (q : ℤ) (x : ES),
          ‖partitionMomentBlock a i k q x‖ ≤ C * y := by
  obtain ⟨M, hM, hY⟩ := exists_global_partitionAnnularRiesz_young
  refine ⟨2 * M, mul_nonneg (by norm_num) hM, ?_⟩
  intro v a hr y hy hω i k q x
  fin_cases i
  · change ‖partitionMomentBlock a 0 k q x‖ ≤ (2 * M) * y
    rw [partitionMomentBlock_eq_rieszCurl hr x 0 k q, ← Real.fourierInv_eq]
    change ‖FourierTransform.fourierInv (fun ξ : ES =>
      partitionAnnularRieszSymbol q 2 k ξ * partitionCurlMoment a 1 ξ -
      partitionAnnularRieszSymbol q 1 k ξ * partitionCurlMoment a 2 ξ) x‖ ≤
        (2 * M) * y
    rw [fourierInv_sub_fn
      (integrable_partitionAnnularRiesz_mul q 2 k
        (integrable_partitionCurlMoment hr 1))
      (integrable_partitionAnnularRiesz_mul q 1 k
        (integrable_partitionCurlMoment hr 2))]
    calc
      ‖FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 2 k ξ *
            partitionCurlMoment a 1 ξ) x -
        FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 1 k ξ *
            partitionCurlMoment a 2 ξ) x‖
          ≤ ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 2 k ξ *
                partitionCurlMoment a 1 ξ) x‖ +
            ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 1 k ξ *
                partitionCurlMoment a 2 ξ) x‖ := norm_sub_le _ _
      _ ≤ M * y + M * y := add_le_add
        (hY 2 k q (integrable_partitionCurlMoment hr 1) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 1) x)
        (hY 1 k q (integrable_partitionCurlMoment hr 2) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 2) x)
      _ = (2 * M) * y := by ring
  · change ‖partitionMomentBlock a 1 k q x‖ ≤ (2 * M) * y
    rw [partitionMomentBlock_eq_rieszCurl hr x 1 k q, ← Real.fourierInv_eq]
    change ‖FourierTransform.fourierInv (fun ξ : ES =>
      partitionAnnularRieszSymbol q 0 k ξ * partitionCurlMoment a 2 ξ -
      partitionAnnularRieszSymbol q 2 k ξ * partitionCurlMoment a 0 ξ) x‖ ≤
        (2 * M) * y
    rw [fourierInv_sub_fn
      (integrable_partitionAnnularRiesz_mul q 0 k
        (integrable_partitionCurlMoment hr 2))
      (integrable_partitionAnnularRiesz_mul q 2 k
        (integrable_partitionCurlMoment hr 0))]
    calc
      ‖FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 0 k ξ *
            partitionCurlMoment a 2 ξ) x -
        FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 2 k ξ *
            partitionCurlMoment a 0 ξ) x‖
          ≤ ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 0 k ξ *
                partitionCurlMoment a 2 ξ) x‖ +
            ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 2 k ξ *
                partitionCurlMoment a 0 ξ) x‖ := norm_sub_le _ _
      _ ≤ M * y + M * y := add_le_add
        (hY 0 k q (integrable_partitionCurlMoment hr 2) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 2) x)
        (hY 2 k q (integrable_partitionCurlMoment hr 0) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 0) x)
      _ = (2 * M) * y := by ring
  · change ‖partitionMomentBlock a 2 k q x‖ ≤ (2 * M) * y
    rw [partitionMomentBlock_eq_rieszCurl hr x 2 k q, ← Real.fourierInv_eq]
    change ‖FourierTransform.fourierInv (fun ξ : ES =>
      partitionAnnularRieszSymbol q 1 k ξ * partitionCurlMoment a 0 ξ -
      partitionAnnularRieszSymbol q 0 k ξ * partitionCurlMoment a 1 ξ) x‖ ≤
        (2 * M) * y
    rw [fourierInv_sub_fn
      (integrable_partitionAnnularRiesz_mul q 1 k
        (integrable_partitionCurlMoment hr 0))
      (integrable_partitionAnnularRiesz_mul q 0 k
        (integrable_partitionCurlMoment hr 1))]
    calc
      ‖FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 1 k ξ *
            partitionCurlMoment a 0 ξ) x -
        FourierTransform.fourierInv
          (fun ξ : ES => partitionAnnularRieszSymbol q 0 k ξ *
            partitionCurlMoment a 1 ξ) x‖
          ≤ ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 1 k ξ *
                partitionCurlMoment a 0 ξ) x‖ +
            ‖FourierTransform.fourierInv
              (fun ξ : ES => partitionAnnularRieszSymbol q 0 k ξ *
                partitionCurlMoment a 1 ξ) x‖ := norm_sub_le _ _
      _ ≤ M * y + M * y := add_le_add
        (hY 1 k q (integrable_partitionCurlMoment hr 0) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 0) x)
        (hY 0 k q (integrable_partitionCurlMoment hr 1) y hy
          (norm_fourierInv_partitionCurlMoment_le hr hω 1) x)
      _ = (2 * M) * y := by ring

/-- Fixed multiplier constants can be absorbed into the final logarithmic envelope. -/
theorem one_add_log_one_add_mul_le
    {P B t : ℝ} (hP : 0 ≤ P) (hPB : P ≤ B) (hB : 1 ≤ B) (ht : 0 ≤ t) :
    1 + Real.log (1 + P * t) ≤
      (1 + Real.log B) * (1 + Real.log (1 + t)) := by
  have harg : 1 + P * t ≤ B * (1 + t) := by
    have hmul := mul_le_mul_of_nonneg_right hPB ht
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 1 + P * t) harg
  rw [Real.log_mul (by linarith : B ≠ 0) (by positivity : 1 + t ≠ 0)] at hlog
  have hLB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hLt : 0 ≤ Real.log (1 + t) :=
    Real.log_nonneg (le_add_of_nonneg_right ht)
  nlinarith [mul_nonneg hLB hLt]

theorem gradSupLogHyp_proved : GradSupLogHyp := by
  obtain ⟨C, hC, hblock⟩ := exists_global_partitionMomentBlock_le_curl
  let A : ℝ := C + 1
  let B : ℝ := 1 + partitionHighConstant + partitionLowConstant
  let L : ℝ := 1 + Real.log B
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hPH : 0 ≤ partitionHighConstant := partitionHighConstant_nonneg
  have hPL : 0 ≤ partitionLowConstant := partitionLowConstant_nonneg
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hLB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hL : 0 ≤ L := by dsimp [L]; linarith
  refine ⟨40 * A * L, mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hL, ?_⟩
  intro v a hr y hy hω x i j
  by_cases hy0 : y = 0
  · subst y
    have hz := rep_curlfree_grad_zero hr hω x i j
    rw [hz]
    simp
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hAy : 0 < A * y := mul_pos (lt_of_lt_of_le zero_lt_one hA) hyp
  have hunif : ∀ q : ℤ,
      ‖partitionMomentBlock a i j q (euclidPoint x)‖ ≤ A * y := by
    intro q
    exact (hblock hr hy hω i j q (euclidPoint x)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) hy)
  have hs := hasSum_partitionMomentBlock hr (euclidPoint x) i j
  have hnorm := hs.summable.norm
  have hhigh := tsum_nonneg_partitionMomentBlock_le_high hr hr.datum.meas
    hr.integrable_profH3_integrand i j (euclidPoint x) hAy hunif
  have hlow := tsum_negSucc_partitionMomentBlock_le_low hr i j
    (euclidPoint x) hAy hunif
  have hmoment :
      ‖FourierTransform.fourierInv
        (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) (euclidPoint x)‖ ≤
      32 * (A * y) * (1 + Real.log (1 +
        (partitionHighConstant * profH3 a) / (A * y))) +
      8 * (A * y) * (1 + Real.log (1 +
        (partitionLowConstant * profL2 a) / (A * y))) := by
    calc
      ‖FourierTransform.fourierInv
          (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) (euclidPoint x)‖
          = ‖∑' q : ℤ, partitionMomentBlock a i j q (euclidPoint x)‖ := by
            rw [hs.tsum_eq]
      _ ≤ ∑' q : ℤ, ‖partitionMomentBlock a i j q (euclidPoint x)‖ :=
        norm_tsum_le_tsum_norm hnorm
      _ = (∑' n : ℕ, ‖partitionMomentBlock a i j (n : ℤ) (euclidPoint x)‖) +
          ∑' n : ℕ, ‖partitionMomentBlock a i j (Int.negSucc n) (euclidPoint x)‖ :=
        tsum_int_split hnorm
      _ ≤ _ := add_le_add hhigh hlow
  have hH : 0 ≤ profH3 a := Real.sqrt_nonneg _
  have hE : 0 ≤ profL2 a := Real.sqrt_nonneg _
  have hden : y ≤ A * y := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hy
  have hqH : profH3 a / (A * y) ≤ profH3 a / y :=
    div_le_div_of_nonneg_left hH hyp hden
  have hqE : profL2 a / (A * y) ≤ profL2 a / y :=
    div_le_div_of_nonneg_left hE hyp hden
  have hlogH :
      1 + Real.log (1 + (partitionHighConstant * profH3 a) / (A * y)) ≤
        L * (1 + Real.log (1 + profH3 a / y)) := by
    have harg : (partitionHighConstant * profH3 a) / (A * y) ≤
        partitionHighConstant * (profH3 a / y) := by
      calc
        (partitionHighConstant * profH3 a) / (A * y)
            = partitionHighConstant * (profH3 a / (A * y)) := by ring
        _ ≤ partitionHighConstant * (profH3 a / y) :=
          mul_le_mul_of_nonneg_left hqH hPH
    have hm := Real.log_le_log (by positivity : 0 < 1 +
      (partitionHighConstant * profH3 a) / (A * y)) (by linarith : 1 +
      (partitionHighConstant * profH3 a) / (A * y) ≤
        1 + partitionHighConstant * (profH3 a / y))
    calc
      1 + Real.log (1 + (partitionHighConstant * profH3 a) / (A * y))
          ≤ 1 + Real.log (1 + partitionHighConstant * (profH3 a / y)) :=
        add_le_add_right hm 1
      _ ≤ L * (1 + Real.log (1 + profH3 a / y)) := by
        simpa [L] using (one_add_log_one_add_mul_le hPH
          (by dsimp [B]; linarith) hB (div_nonneg hH hy))
  have hlogE :
      1 + Real.log (1 + (partitionLowConstant * profL2 a) / (A * y)) ≤
        L * (1 + Real.log (1 + profL2 a / y)) := by
    have harg : (partitionLowConstant * profL2 a) / (A * y) ≤
        partitionLowConstant * (profL2 a / y) := by
      calc
        (partitionLowConstant * profL2 a) / (A * y)
            = partitionLowConstant * (profL2 a / (A * y)) := by ring
        _ ≤ partitionLowConstant * (profL2 a / y) :=
          mul_le_mul_of_nonneg_left hqE hPL
    have hm := Real.log_le_log (by positivity : 0 < 1 +
      (partitionLowConstant * profL2 a) / (A * y)) (by linarith : 1 +
      (partitionLowConstant * profL2 a) / (A * y) ≤
        1 + partitionLowConstant * (profL2 a / y))
    calc
      1 + Real.log (1 + (partitionLowConstant * profL2 a) / (A * y))
          ≤ 1 + Real.log (1 + partitionLowConstant * (profL2 a / y)) :=
        add_le_add_right hm 1
      _ ≤ L * (1 + Real.log (1 + profL2 a / y)) := by
        simpa [L] using (one_add_log_one_add_mul_le hPL
          (by dsimp [B]; linarith) hB (div_nonneg hE hy))
  have hlogH0 : 0 ≤ Real.log (1 + profH3 a / y) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hH hy))
  have hlogE0 : 0 ≤ Real.log (1 + profL2 a / y) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hE hy))
  have hcoef : 0 ≤ A * y * L := mul_nonneg (mul_nonneg (by linarith) hy) hL
  rw [hr.fderiv_coord_im x i j]
  refine (Complex.abs_im_le_norm _).trans (hmoment.trans ?_)
  calc
    32 * (A * y) * (1 + Real.log (1 +
        (partitionHighConstant * profH3 a) / (A * y))) +
      8 * (A * y) * (1 + Real.log (1 +
        (partitionLowConstant * profL2 a) / (A * y)))
        ≤ 32 * (A * y) * (L * (1 + Real.log (1 + profH3 a / y))) +
          8 * (A * y) * (L * (1 + Real.log (1 + profL2 a / y))) := by
            gcongr <;> positivity
    _ ≤ 40 * A * L * y *
          (1 + Real.log (1 + profH3 a / y) + Real.log (1 + profL2 a / y)) := by
      have hSH : 1 + Real.log (1 + profH3 a / y) ≤
          1 + Real.log (1 + profH3 a / y) + Real.log (1 + profL2 a / y) := by linarith
      have hSE : 1 + Real.log (1 + profL2 a / y) ≤
          1 + Real.log (1 + profH3 a / y) + Real.log (1 + profL2 a / y) := by linarith
      calc
        32 * (A * y) * (L * (1 + Real.log (1 + profH3 a / y))) +
            8 * (A * y) * (L * (1 + Real.log (1 + profL2 a / y)))
            ≤ 32 * (A * y) * (L *
                (1 + Real.log (1 + profH3 a / y) + Real.log (1 + profL2 a / y))) +
              8 * (A * y) * (L *
                (1 + Real.log (1 + profH3 a / y) + Real.log (1 + profL2 a / y))) := by
              gcongr
        _ = _ := by ring

end Navier.Analysis.LittlewoodPaleyPhysical

set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.integrable_partitionCurlMoment
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.integrable_partitionAnnularRiesz_mul
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.norm_fourierInv_partitionCurlMoment_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.exists_uniform_partitionMomentBlock_le_curl
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.norm_partitionMomentBlock_four_mul_add_le_H3
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.tsum_int_split
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.tsum_nonneg_partitionMomentBlock_le_high
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.tsum_negSucc_partitionMomentBlock_le_low
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.exists_fourierInv_moment_le_shells
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.exists_global_partitionAnnularRiesz_young
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.exists_global_partitionMomentBlock_le_curl
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.one_add_log_one_add_mul_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyPhysical.gradSupLogHyp_proved
