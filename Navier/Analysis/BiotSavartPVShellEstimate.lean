import Navier.Analysis.BiotSavartPVSplitEstimate
import Navier.Analysis.BiotSavartMorrey

/-!
# Quantitative logarithmic shell estimate for the Biot--Savart principal value

The Euclidean PV shell is transported into a product-norm dyadic annulus.  Its
scalar kernel mass is finite and logarithmic, and hence each actual curl
component convolution is bounded by the stated vorticity supremum majorant.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.BiotSavartPVShellEstimate

open Navier
open Navier.Analysis.BiotSavartKernel
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

private theorem measurableSet_pvShellSet (ρ : ℝ) :
    MeasurableSet (pvShellSet ρ) := by
  rw [pvShellSet]
  exact ((measurableSet_le measurable_const
    continuous_officialEuclideanNorm.measurable).inter
    (measurableSet_lt continuous_officialEuclideanNorm.measurable
      measurable_const))

private theorem czShell_kernel_le_pv {k : ℕ} {z : Space}
    (hz : z ∈ czShell 1 k) :
    bsKernelScalar z ≤ 2 * 8 ^ k / Real.pi := by
  obtain ⟨-, hlo, -⟩ := hz
  have hpos : (0 : ℝ) < 1 / 2 ^ (k + 1) := by positivity
  have hn : 0 < ‖z‖ := lt_trans hpos hlo
  rw [bsKernelScalar_apply_of_ne_zero (norm_pos_iff.mp hn)]
  have hoge := norm_le_officialEuclideanNorm z
  have hle1 : (1 : ℝ) / (4 * Real.pi * officialEuclideanNorm z ^ 3)
      ≤ 1 / (4 * Real.pi * ‖z‖ ^ 3) :=
    one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hoge 3) (by positivity))
  have hden : 4 * Real.pi * ((1 : ℝ) / 2 ^ (k + 1)) ^ 3 ≤
      4 * Real.pi * ‖z‖ ^ 3 :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hlo.le 3) (by positivity)
  have hkey : (1 : ℝ) / (4 * Real.pi * (1 / 2 ^ (k + 1)) ^ 3)
      = 2 * 8 ^ k / Real.pi := by
    have h8 : ((2 : ℝ) ^ (k + 1)) ^ 3 = 8 * 8 ^ k := by
      rw [← pow_mul, mul_comm (k + 1) 3, pow_mul]
      norm_num [pow_succ, mul_comm]
    have hpi := Real.pi_ne_zero
    rw [div_pow, one_pow, h8]
    field_simp
    ring
  calc
    (1 : ℝ) / (4 * Real.pi * officialEuclideanNorm z ^ 3)
        ≤ 1 / (4 * Real.pi * ‖z‖ ^ 3) := hle1
    _ ≤ 1 / (4 * Real.pi * ((1 : ℝ) / 2 ^ (k + 1)) ^ 3) :=
      one_div_le_one_div_of_le (by positivity) hden
    _ = 2 * 8 ^ k / Real.pi := hkey

private theorem productAnnulus_subset_shells {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 1 / 2 ^ N < δ) :
    Metric.ball (0 : Space) 1 ∩ {z : Space | δ ≤ ‖z‖} ⊆
      ⋃ k ∈ Finset.range N, czShell 1 k := by
  intro z hz
  obtain ⟨hball, hlow⟩ := hz
  simp only [Set.mem_setOf_eq] at hlow
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hmem := ball_subset_iUnion_czShell (ρ := (1 : ℝ)) one_pos hball
  rw [mem_insert_iff] at hmem
  rcases hmem with h | h
  · exact absurd h hz0
  · rw [mem_iUnion] at h
    obtain ⟨k, hk⟩ := h
    have hhi : ‖z‖ ≤ 1 / 2 ^ k := hk.2.2
    have hkN : k < N := by
      by_contra hcon
      have hNk : N ≤ k := Nat.not_lt.mp hcon
      have hmono : (1 : ℝ) / 2 ^ k ≤ 1 / 2 ^ N :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ one_le_two hNk)
      linarith
    exact mem_biUnion (Finset.mem_range.mpr hkN) hk

private theorem setLIntegral_czShell_kernel_le_pv (k : ℕ) :
    ∫⁻ z in czShell 1 k, ENNReal.ofReal (bsKernelScalar z) ∂volume
      ≤ ENNReal.ofReal (2 / Real.pi) *
        volume (Metric.ball (0 : Space) 1) := by
  calc
    ∫⁻ z in czShell 1 k, ENNReal.ofReal (bsKernelScalar z) ∂volume
        ≤ ∫⁻ _ in czShell 1 k,
            ENNReal.ofReal (2 * 8 ^ k / Real.pi) ∂volume :=
      setLIntegral_mono measurable_const fun _z hz =>
        ENNReal.ofReal_le_ofReal (czShell_kernel_le_pv hz)
    _ = ENNReal.ofReal (2 * 8 ^ k / Real.pi) * volume (czShell 1 k) :=
      setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (2 * 8 ^ k / Real.pi) *
        (ENNReal.ofReal (((1 : ℝ) / 2 ^ k) ^ 3) *
          volume (Metric.ball (0 : Space) 1)) :=
      mul_le_mul_of_nonneg_left (volume_czShell_le one_pos k) zero_le
    _ = ENNReal.ofReal (2 / Real.pi) *
        volume (Metric.ball (0 : Space) 1) := by
      rw [← mul_assoc]
      congr 1
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have h8 : ((2 : ℝ) ^ k) ^ 3 = 8 ^ k := by
        rw [← pow_mul, mul_comm k 3, pow_mul]
        norm_num
      have hpi := Real.pi_ne_zero
      have h8k : ((8 : ℝ) ^ k) ≠ 0 := by positivity
      rw [div_pow, one_pow, h8]
      field_simp

private theorem lintegral_productAnnulus_kernel_le {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 1 / 2 ^ N < δ) :
    ∫⁻ z in Metric.ball (0 : Space) 1 ∩ {z : Space | δ ≤ ‖z‖},
        ENNReal.ofReal (bsKernelScalar z) ∂volume
      ≤ ENNReal.ofReal (2 * N / Real.pi) *
        volume (Metric.ball (0 : Space) 1) := by
  refine le_trans (lintegral_mono'
    (Measure.restrict_mono (productAnnulus_subset_shells hδ hN) le_rfl) le_rfl) ?_
  rw [lintegral_biUnion_finset ((czShell_disjoint one_pos).set_pairwise _)
    (fun b _ => measurableSet_czShell 1 b)]
  calc
    ∑ k ∈ Finset.range N,
        ∫⁻ z in czShell 1 k, ENNReal.ofReal (bsKernelScalar z) ∂volume
        ≤ ∑ _k ∈ Finset.range N,
            ENNReal.ofReal (2 / Real.pi) *
              volume (Metric.ball (0 : Space) 1) :=
      Finset.sum_le_sum fun k _ => setLIntegral_czShell_kernel_le_pv k
    _ = (N : ENNReal) * (ENNReal.ofReal (2 / Real.pi) *
          volume (Metric.ball (0 : Space) 1)) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ENNReal.ofReal (2 * N / Real.pi) *
        volume (Metric.ball (0 : Space) 1) := by
      rw [← mul_assoc]
      congr 1
      rw [← ENNReal.ofReal_natCast N,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

private theorem integral_productAnnulus_kernel_le {δ : ℝ} (hδ : 0 < δ)
    {N : ℕ} (hN : 1 / 2 ^ N < δ) :
    ∫ z in Metric.ball (0 : Space) 1 ∩ {z : Space | δ ≤ ‖z‖},
        bsKernelScalar z
      ≤ 2 * (volume (Metric.ball (0 : Space) 1)).toReal /
          Real.pi * N := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall bsKernelScalar_nonneg)
    measurable_bsKernelScalar.aestronglyMeasurable]
  have htop2 : (ENNReal.ofReal (2 * N / Real.pi) *
      volume (Metric.ball (0 : Space) 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Space)) (r := 1)).ne
  have htop : (∫⁻ z in Metric.ball (0 : Space) 1 ∩
      {z : Space | δ ≤ ‖z‖}, ENNReal.ofReal (bsKernelScalar z) ∂volume) ≠ ⊤ :=
    ne_top_of_le_ne_top htop2 (lintegral_productAnnulus_kernel_le hδ hN)
  refine le_trans ((ENNReal.toReal_le_toReal htop htop2).mpr
    (lintegral_productAnnulus_kernel_le hδ hN)) ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  apply le_of_eq
  ring

private theorem integral_productAnnulus_kernel_le_log {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ z in Metric.ball (0 : Space) 1 ∩ {z : Space | δ ≤ ‖z‖},
        bsKernelScalar z
      ≤ 2 * (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi *
          (1 + Real.log (1 / δ) / Real.log 2) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set q : ℝ := Real.log (1 / δ) / Real.log 2 with hqdef
  have hqnn : 0 ≤ q := by
    refine div_nonneg (Real.log_nonneg ?_) hl2.le
    rw [le_div_iff₀ hδ0]
    linarith
  have hqN : q < (⌊q⌋₊ + 1 : ℕ) := by
    have h := Nat.lt_floor_add_one q
    push_cast
    exact h
  have hNle : ((⌊q⌋₊ + 1 : ℕ) : ℝ) ≤ 1 + q := by
    have h := Nat.floor_le hqnn
    push_cast
    linarith
  have hNδ : 1 / 2 ^ (⌊q⌋₊ + 1 : ℕ) < δ := by
    have h2 : Real.log (1 / δ) <
        ((⌊q⌋₊ + 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [hqdef, div_lt_iff₀ hl2] at hqN
      exact hqN
    have h3 : Real.log (1 / δ) <
        Real.log ((2 : ℝ) ^ (⌊q⌋₊ + 1 : ℕ)) := by
      rw [Real.log_pow]
      exact_mod_cast h2
    have h4 : (1 : ℝ) / δ < 2 ^ (⌊q⌋₊ + 1 : ℕ) :=
      (Real.log_lt_log_iff (by positivity) (by positivity)).mp h3
    rw [div_lt_iff₀ (by positivity :
      (0 : ℝ) < 2 ^ (⌊q⌋₊ + 1 : ℕ))]
    rw [div_lt_iff₀ hδ0] at h4
    linarith
  refine le_trans (integral_productAnnulus_kernel_le hδ0 hNδ) ?_
  have hC : 0 ≤
      2 * (volume (Metric.ball (0 : Space) 1)).toReal / Real.pi := by
    exact div_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      Real.pi_pos.le
  exact mul_le_mul_of_nonneg_left (by linarith) hC

private theorem integrableOn_bsKernelScalar_productAnnulus
    {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn bsKernelScalar
      (Metric.ball (0 : Space) 1 ∩ {z : Space | δ ≤ ‖z‖}) volume := by
  let q : ℝ := Real.log (1 / δ) / Real.log 2
  let N : ℕ := ⌊q⌋₊ + 1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hqN : q < (N : ℕ) := by
    dsimp only [N]
    have h := Nat.lt_floor_add_one q
    push_cast
    exact h
  have hN : 1 / 2 ^ N < δ := by
    have hlog : Real.log (1 / δ) < (N : ℕ) * Real.log 2 := by
      rw [show Real.log (1 / δ) = q * Real.log 2 by
        dsimp only [q]
        field_simp]
      exact mul_lt_mul_of_pos_right hqN hl2
    have hp : (1 : ℝ) / δ < 2 ^ N :=
      (Real.log_lt_log_iff (by positivity)
        (by positivity : (0 : ℝ) < 2 ^ N)).mp (by
          rw [Real.log_pow]
          exact_mod_cast hlog)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)]
    rw [div_lt_iff₀ hδ] at hp
    nlinarith
  have hlin := lintegral_productAnnulus_kernel_le hδ hN
  have htop2 : (ENNReal.ofReal (2 * N / Real.pi) *
      volume (Metric.ball (0 : Space) 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Space)) (r := 1)).ne
  have hfinite : (∫⁻ z in Metric.ball (0 : Space) 1 ∩
      {z : Space | δ ≤ ‖z‖}, ‖bsKernelScalar z‖ₑ ∂volume) < ⊤ := by
    rw [show (fun z : Space => ‖bsKernelScalar z‖ₑ) =
        fun z => ENNReal.ofReal (bsKernelScalar z) by
      funext z
      rw [Real.enorm_eq_ofReal (bsKernelScalar_nonneg z)]]
    exact lt_of_le_of_lt hlin (lt_top_iff_ne_top.mpr htop2)
  have hmeas : AEStronglyMeasurable bsKernelScalar
      (volume.restrict (Metric.ball (0 : Space) 1 ∩
        {z : Space | δ ≤ ‖z‖})) :=
    measurable_bsKernelScalar.aestronglyMeasurable.restrict
  exact ⟨hmeas, hasFiniteIntegral_iff_enorm.mpr hfinite⟩

/-- The scalar kernel is genuinely integrable on every positive Euclidean PV
shell. -/
theorem integrableOn_bsKernelScalar_pvShellSet {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn bsKernelScalar (pvShellSet ρ) volume := by
  have hsub : pvShellSet ρ ⊆
      Metric.ball (0 : Space) 1 ∩ {z : Space | ρ / 2 ≤ ‖z‖} := by
    intro z hz
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have heprod : officialEuclideanNorm z ≤ 2 * ‖z‖ :=
      (officialEuclideanNorm_le z).trans
        (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg z))
    exact ⟨by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (norm_le_officialEuclideanNorm z) hz.2,
      by simp only [Set.mem_setOf_eq]; linarith [hz.1]⟩
  exact (integrableOn_bsKernelScalar_productAnnulus (by positivity : 0 < ρ / 2)).mono_set hsub

/-- Each actual curl-component convolution on the Euclidean PV shell obeys a
universal `Mω (1 + log(1/ρ))` bound. -/
theorem exists_pvShellCurlComponent_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (Mω : ℝ),
        (∀ y : Space,
          officialEuclideanNorm (staticCurl (⇑u) y) ≤ Mω) →
        ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
        ∀ (x : Space) (i j k : Fin 3),
          |∫ z in pvShellSet ρ,
            (1 / (4 * Real.pi)) * bsGradKernel i j z *
              curlComponentSchwartz u k (x - z)| ≤
            C * Mω * (1 + Real.log (1 / ρ)) := by
  let V : ℝ := (volume (Metric.ball (0 : Space) 1)).toReal
  let C : ℝ := 100 * V / (Real.pi * Real.log 2) + 1
  have hC : 0 < C := by
    dsimp only [C, V]
    have : 0 ≤ (volume (Metric.ball (0 : Space) 1)).toReal :=
      ENNReal.toReal_nonneg
    positivity
  refine ⟨C, hC, ?_⟩
  intro u Mω hMω ρ hρ hρ1 x i j k
  have hMω0 : 0 ≤ Mω :=
    (officialEuclideanNorm_nonneg (staticCurl (⇑u) 0)).trans (hMω 0)
  have hsub : pvShellSet ρ ⊆
      Metric.ball (0 : Space) 1 ∩ {z : Space | ρ / 2 ≤ ‖z‖} := by
    intro z hz
    have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    have heprod : officialEuclideanNorm z ≤ 2 * ‖z‖ :=
      (officialEuclideanNorm_le z).trans
        (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg z))
    exact ⟨by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (norm_le_officialEuclideanNorm z) hz.2,
      by simp only [Set.mem_setOf_eq]; linarith [hz.1]⟩
  have hδ : 0 < ρ / 2 := by positivity
  have hδ1 : ρ / 2 ≤ 1 := by linarith
  have hmass := integral_productAnnulus_kernel_le_log hδ hδ1
  let q : Space → ℝ := fun z =>
    (pvShellSet ρ).indicator (fun y =>
      (1 / (4 * Real.pi)) * bsGradKernel i j y *
        curlComponentSchwartz u k (x - y)) z
  let majorant : Space → ℝ := fun z =>
    (pvShellSet ρ).indicator (fun y => 4 * Mω * bsKernelScalar y) z
  have hmajorant : Integrable majorant := by
    have hi := (integrableOn_bsKernelScalar_pvShellSet hρ).const_mul (4 * Mω)
    exact (integrable_indicator_iff (measurableSet_pvShellSet ρ)).mpr hi
  have hqmeas : AEStronglyMeasurable q volume := by
    have hgrad : Measurable (bsGradKernel i j) := by
      unfold bsGradKernel
      apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
      exact (Measurable.sub
        (measurable_const.div
          (continuous_officialEuclideanNorm.measurable.pow_const 3))
        ((measurable_const.mul (measurable_pi_apply i)).mul
          (measurable_pi_apply j) |>.div
            (continuous_officialEuclideanNorm.measurable.pow_const 5)))
    have hcurl : Continuous (fun z : Space =>
        curlComponentSchwartz u k (x - z)) :=
      (curlComponentSchwartz u k).continuous.comp (by fun_prop)
    exact (((measurable_const.mul hgrad).mul hcurl.measurable).indicator
      (measurableSet_pvShellSet ρ)).aestronglyMeasurable
  have hpoint : ∀ z : Space, ‖q z‖ ≤ majorant z := by
    intro z
    by_cases hz : z ∈ pvShellSet ρ
    · rw [show q z = (1 / (4 * Real.pi)) * bsGradKernel i j z *
          curlComponentSchwartz u k (x - z) by simp [q, hz],
        show majorant z = 4 * Mω * bsKernelScalar z by simp [majorant, hz],
        norm_mul, Real.norm_eq_abs]
      have hkern := scaled_bsGradKernel_abs_le i j z
      have hcoord : |curlComponentSchwartz u k (x - z)| ≤ Mω := by
        rw [curlComponentSchwartz_apply]
        exact (coord_abs_le_officialEuclideanNorm _ k).trans
          (by simpa only [staticCurlSchwartz_apply] using hMω (x - z))
      calc
        |1 / (4 * Real.pi) * bsGradKernel i j z| *
            |curlComponentSchwartz u k (x - z)|
            ≤ (4 * bsKernelScalar z) * Mω :=
          mul_le_mul hkern hcoord (abs_nonneg _)
            (mul_nonneg (by norm_num) (bsKernelScalar_nonneg z))
        _ = 4 * Mω * bsKernelScalar z := by ring
    · simp [q, majorant, hz]
  have hq : Integrable q := hmajorant.mono' hqmeas
    (Filter.Eventually.of_forall hpoint)
  have hnorm : ‖∫ z : Space, q z‖ ≤ ∫ z : Space, majorant z := by
    exact (norm_integral_le_integral_norm q).trans
      (integral_mono hq.norm hmajorant hpoint)
  rw [← MeasureTheory.integral_indicator (measurableSet_pvShellSet ρ)]
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans ?_
  have hlogρ : 0 ≤ Real.log (1 / ρ) := by
    exact Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlogRewrite : Real.log (1 / (ρ / 2)) =
      Real.log 2 + Real.log (1 / ρ) := by
    rw [show 1 / (ρ / 2) = 2 * (1 / ρ) by field_simp,
      Real.log_mul (by norm_num) (by positivity)]
  calc
    (∫ z : Space, majorant z) =
        4 * Mω * ∫ z in pvShellSet ρ, bsKernelScalar z := by
      dsimp only [majorant]
      rw [MeasureTheory.integral_indicator (measurableSet_pvShellSet ρ),
        MeasureTheory.integral_const_mul]
    _ ≤ 4 * Mω * ∫ z in
          Metric.ball (0 : Space) 1 ∩ {z : Space | ρ / 2 ≤ ‖z‖},
          bsKernelScalar z := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hMω0)
      exact setIntegral_mono_set
        (integrableOn_bsKernelScalar_productAnnulus hδ)
        (Filter.Eventually.of_forall bsKernelScalar_nonneg)
        (Filter.Eventually.of_forall hsub)
    _ ≤ 4 * Mω *
        (2 * V / Real.pi *
          (1 + Real.log (1 / (ρ / 2)) / Real.log 2)) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num) hMω0)
    _ ≤ C * Mω * (1 + Real.log (1 / ρ)) := by
      dsimp only [C, V]
      rw [hlogRewrite]
      have hl2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2
      have hV : 0 ≤ (volume (Metric.ball (0 : Space) 1)).toReal :=
        ENNReal.toReal_nonneg
      have hMV : 0 ≤ Mω * (volume (Metric.ball (0 : Space) 1)).toReal :=
        mul_nonneg hMω0 hV
      have hMVlog2 : Mω * (volume (Metric.ball (0 : Space) 1)).toReal *
          Real.log 2 ≤ Mω * (volume (Metric.ball (0 : Space) 1)).toReal :=
        mul_le_of_le_one_right hMV hlog2le
      have hMVL : 0 ≤ Mω * (volume (Metric.ball (0 : Space) 1)).toReal *
          Real.log (1 / ρ) := mul_nonneg hMV hlogρ
      have hMpilog2 : 0 ≤ Mω * Real.pi * Real.log 2 :=
        mul_nonneg (mul_nonneg hMω0 Real.pi_pos.le) hlog2.le
      have hMpilog2L : 0 ≤ Mω * Real.pi * Real.log 2 *
          Real.log (1 / ρ) := mul_nonneg hMpilog2 hlogρ
      field_simp [hl2ne]
      ring_nf at hMVlog2 hMVL hMpilog2 hMpilog2L ⊢
      nlinarith

end Navier.Analysis.BiotSavartPVShellEstimate
