import Navier.Analysis.BiotSavartPVSplitEstimate
import Navier.Analysis.BiotSavartMorrey

/-!
# Quantitative Morrey bound for the Biot--Savart PV near region

The cancellation remainder in the sharp principal-value split is bounded by
the fractional `|z|^(1/4)` kernel moment and the actual `H²` norm of the
Schwartz vorticity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.BiotSavartPVNearEstimate

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartConvolution
open Navier.Analysis.BiotSavartPVSplitEstimate
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda

private theorem measurableSet_pvNearSet (ε ρ : ℝ) :
    MeasurableSet (pvNearSet ε ρ) := by
  rw [pvNearSet]
  have hcont : Continuous officialEuclideanNorm := by
    rw [show officialEuclideanNorm = fun x : Space =>
        Real.sqrt (∑ k : Fin 3, |x k| ^ 2) by
      funext x
      exact officialEuclideanNorm_eq_sqrt_sum_sq x]
    fun_prop
  exact ((measurableSet_lt measurable_const hcont.measurable).inter
    (measurableSet_lt hcont.measurable measurable_const))

private theorem curlDifference_measurable
    (u : SchwartzVelocity) (x : Space) :
    AEStronglyMeasurable (fun z : Space =>
      staticCurlSchwartz u (x - z) - staticCurlSchwartz u x) volume :=
  ((staticCurlSchwartz u).continuous.comp (by fun_prop)).sub
    continuous_const |>.aestronglyMeasurable

/-- The actual inner PV remainder for a curl component has the sharp
`ρ^(1/4) sqrt(H₂)` bound, uniformly in the puncture radius and all tensor
indices. -/
theorem exists_pvNearCurlComponent_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (H₂ : ℝ),
        sobolevH2NormSq (staticCurlSchwartz u) ≤ H₂ →
        ∀ (x : Space) (i j k : Fin 3) (ε ρ : ℝ),
          0 < ε → ε < ρ →
          |∫ z in pvNearSet ε ρ,
            (1 / (4 * Real.pi)) * bsGradKernel i j z *
              (curlComponentSchwartz u k (x - z) -
                curlComponentSchwartz u k x)| ≤
            C * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ := by
  obtain ⟨CM, hCM, hmorrey⟩ := exists_agmonMorreyBound
  let I : ℝ := ∫ z in Metric.ball (0 : Space) 1,
    ‖z‖ ^ ((1 : ℝ) / 4) * bsKernelScalar z
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun z =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _)
        (bsKernelScalar_nonneg z)
  refine ⟨8 * CM * I + 1, by nlinarith, ?_⟩
  intro u H₂ hH₂ x i j k ε ρ hε hερ
  have hρ : 0 < ρ := hε.trans hερ
  let F : Space → Space := fun z =>
    staticCurlSchwartz u (x - z) - staticCurlSchwartz u x
  let H : ℝ := CM * Real.sqrt (sobolevH2NormSq (staticCurlSchwartz u))
  have hH : 0 ≤ H := mul_nonneg hCM.le (Real.sqrt_nonneg _)
  have hholder : ∀ z : Space,
      ‖F z‖ ≤ H * ‖z‖ ^ ((1 : ℝ) / 4) := by
    intro z
    have hm := hmorrey (staticCurlSchwartz u) (x - z) x
    simpa only [F, H, sub_sub_cancel_left, norm_neg] using hm
  have hFmeas : AEStronglyMeasurable F volume :=
    curlDifference_measurable u x
  have hvecInt := integrableOn_bsKernelScalar_smul_of_holder
    F H ρ hH hFmeas hholder
  let majorant : Space → ℝ := (Metric.ball (0 : Space) ρ).indicator
    (fun z => 8 * ‖bsKernelScalar z • F z‖)
  have hmajorant : Integrable majorant := by
    have hnorm : IntegrableOn (fun z : Space =>
        ‖bsKernelScalar z • F z‖) (Metric.ball (0 : Space) ρ) := hvecInt.norm
    have hscaled : IntegrableOn (fun z : Space =>
        8 * ‖bsKernelScalar z • F z‖) (Metric.ball (0 : Space) ρ) :=
      hnorm.const_mul 8
    exact hscaled.integrable_indicator measurableSet_ball
  let f : Space → ℝ := fun z => (pvNearSet ε ρ).indicator
    (fun y => (1 / (4 * Real.pi)) * bsGradKernel i j y *
      (curlComponentSchwartz u k (x - y) - curlComponentSchwartz u k x)) z
  have hfmeas : AEStronglyMeasurable f volume := by
    have hcomp : Continuous (fun z : Space =>
        curlComponentSchwartz u k (x - z) - curlComponentSchwartz u k x) :=
      ((curlComponentSchwartz u k).continuous.comp (by fun_prop)).sub continuous_const
    have hgrad : Measurable (bsGradKernel i j) := by
      unfold bsGradKernel
      have hcont : Continuous officialEuclideanNorm := by
        rw [show officialEuclideanNorm = fun y : Space =>
            Real.sqrt (∑ l : Fin 3, |y l| ^ 2) by
          funext y
          exact officialEuclideanNorm_eq_sqrt_sum_sq y]
        fun_prop
      apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
      exact (Measurable.sub
        (measurable_const.div (hcont.measurable.pow_const 3))
        ((measurable_const.mul (measurable_pi_apply i)).mul
          (measurable_pi_apply j) |>.div (hcont.measurable.pow_const 5)))
    exact (((measurable_const.mul hgrad).mul hcomp.measurable).indicator
      (measurableSet_pvNearSet ε ρ)).aestronglyMeasurable
  have hpoint : ∀ z : Space, ‖f z‖ ≤ majorant z := by
    intro z
    by_cases hz : z ∈ pvNearSet ε ρ
    · have hzball : z ∈ Metric.ball (0 : Space) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (norm_le_officialEuclideanNorm z) hz.2
      rw [show f z = (1 / (4 * Real.pi)) * bsGradKernel i j z *
          (curlComponentSchwartz u k (x - z) - curlComponentSchwartz u k x) by
        simp [f, hz],
        show majorant z = 8 * ‖bsKernelScalar z • F z‖ by
          simp [majorant, hzball]]
      rw [norm_mul, Real.norm_eq_abs]
      have hk := scaled_bsGradKernel_abs_le i j z
      have hcoord :
          |curlComponentSchwartz u k (x - z) - curlComponentSchwartz u k x| ≤
            2 * ‖F z‖ := by
        rw [show curlComponentSchwartz u k (x - z) -
            curlComponentSchwartz u k x = F z k by
          simp [F, curlComponentSchwartz_apply]]
        calc
          |F z k| ≤ officialEuclideanNorm (F z) :=
            coord_abs_le_officialEuclideanNorm (F z) k
          _ ≤ Real.sqrt 3 * ‖F z‖ := officialEuclideanNorm_le (F z)
          _ ≤ 2 * ‖F z‖ := by
            have hs : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
            exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
      rw [norm_smul]
      calc
        |1 / (4 * Real.pi) * bsGradKernel i j z| *
            |curlComponentSchwartz u k (x - z) - curlComponentSchwartz u k x| ≤
            (4 * bsKernelScalar z) * (2 * ‖F z‖) :=
          mul_le_mul hk hcoord (abs_nonneg _)
            (mul_nonneg (by norm_num) (bsKernelScalar_nonneg z))
        _ = 8 * (‖bsKernelScalar z‖ * ‖F z‖) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (bsKernelScalar_nonneg z)]
          ring
    · rw [show f z = 0 by simp [f, hz], norm_zero]
      dsimp only [majorant]
      by_cases hzball : z ∈ Metric.ball (0 : Space) ρ
      · rw [Set.indicator_of_mem hzball]
        positivity
      · rw [Set.indicator_of_notMem hzball]
  have hf : Integrable f :=
    hmajorant.mono' hfmeas (Filter.Eventually.of_forall hpoint)
  have hnormIntegral : ‖∫ z : Space, f z‖ ≤ ∫ z : Space, majorant z :=
    (MeasureTheory.norm_integral_le_integral_norm f).trans
      (integral_mono hf.norm hmajorant (fun z => hpoint z))
  have hmass := integral_norm_bsKernelScalar_smul_of_holder_le
    F H hH hρ hFmeas hholder
  have hsqrt : Real.sqrt (sobolevH2NormSq (staticCurlSchwartz u)) ≤
      Real.sqrt H₂ := Real.sqrt_le_sqrt hH₂
  have htarget : (∫ z : Space, majorant z) ≤
      8 * H * ρ ^ ((1 : ℝ) / 4) * I := by
    dsimp only [majorant]
    rw [MeasureTheory.integral_indicator measurableSet_ball,
      MeasureTheory.integral_const_mul]
    calc
      8 * (∫ z in Metric.ball (0 : Space) ρ,
          ‖bsKernelScalar z • F z‖) ≤
          8 * (H * ρ ^ ((1 : ℝ) / 4) * I) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = 8 * H * ρ ^ ((1 : ℝ) / 4) * I := by ring
  rw [← MeasureTheory.integral_indicator (measurableSet_pvNearSet ε ρ)]
  rw [Real.norm_eq_abs] at hnormIntegral
  change |∫ z : Space, f z| ≤ _
  calc
    |∫ z : Space, f z| ≤ ∫ z : Space, majorant z := hnormIntegral
    _ ≤ 8 * H * ρ ^ ((1 : ℝ) / 4) * I := htarget
    _ ≤ (8 * CM * I + 1) * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ := by
      dsimp only [H]
      have hp : 0 ≤ ρ ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hρ.le _
      have hbase : 0 ≤ 8 * CM * I := by positivity
      have hcoeff : 8 * CM * I ≤ 8 * CM * I + 1 := by linarith
      calc
        8 * (CM * Real.sqrt (sobolevH2NormSq (staticCurlSchwartz u))) *
            ρ ^ ((1 : ℝ) / 4) * I =
            (8 * CM * I) * ρ ^ ((1 : ℝ) / 4) *
              Real.sqrt (sobolevH2NormSq (staticCurlSchwartz u)) := by ring
        _ ≤ (8 * CM * I) * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ :=
          mul_le_mul_of_nonneg_left hsqrt (mul_nonneg hbase hp)
        _ ≤ (8 * CM * I + 1) * ρ ^ ((1 : ℝ) / 4) * Real.sqrt H₂ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoeff hp) (Real.sqrt_nonneg _)

end Navier.Analysis.BiotSavartPVNearEstimate
