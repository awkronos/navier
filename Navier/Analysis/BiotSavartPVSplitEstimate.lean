import Navier.Analysis.BiotSavartConvolution
import Navier.Analysis.BiotSavartNearBounds

/-!
# Sharp principal-value near/shell/far decomposition

This file splits every sharp truncated Calderón--Zygmund convolution into an
inner cancellation remainder, a middle shell, and a far tail.  The inner
constant mode is removed by the exact Euclidean-annulus cancellation theorem.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators

namespace Navier.Analysis.BiotSavartPVSplitEstimate

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartPuncture
open Navier.Analysis.BiotSavartPrincipalValue
open Navier.Analysis.BiotSavartTruncationComparison
open Navier.Analysis.BiotSavartConvolution
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda

def pvNearSet (ε ρ : ℝ) : Set Space :=
  {z | ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ}

def pvShellSet (ρ : ℝ) : Set Space :=
  {z | ρ ≤ officialEuclideanNorm z ∧ officialEuclideanNorm z < 1}

def pvFarSet : Set Space :=
  {z | 1 ≤ officialEuclideanNorm z}

private theorem continuous_officialEuclideanNorm :
    Continuous officialEuclideanNorm := by
  rw [show officialEuclideanNorm = fun x : Space =>
      Real.sqrt (∑ k : Fin 3, |x k| ^ 2) by
    funext x
    exact officialEuclideanNorm_eq_sqrt_sum_sq x]
  fun_prop

private theorem measurableSet_pvNearSet (ε ρ : ℝ) :
    MeasurableSet (pvNearSet ε ρ) := by
  rw [pvNearSet]
  exact ((measurableSet_lt measurable_const
    continuous_officialEuclideanNorm.measurable).inter
    (measurableSet_lt continuous_officialEuclideanNorm.measurable
      measurable_const))

private theorem measurableSet_pvShellSet (ρ : ℝ) :
    MeasurableSet (pvShellSet ρ) := by
  rw [pvShellSet]
  exact ((measurableSet_le measurable_const
    continuous_officialEuclideanNorm.measurable).inter
    (measurableSet_lt continuous_officialEuclideanNorm.measurable
      measurable_const))

private theorem measurableSet_pvFarSet : MeasurableSet pvFarSet := by
  rw [pvFarSet]
  exact measurableSet_le measurable_const
    continuous_officialEuclideanNorm.measurable

private theorem measurable_bsGradKernel (i j : Fin 3) :
    Measurable (bsGradKernel i j) := by
  unfold bsGradKernel
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact (Measurable.sub
    (measurable_const.div (continuous_officialEuclideanNorm.measurable.pow_const 3))
    ((measurable_const.mul (measurable_pi_apply i)).mul (measurable_pi_apply j) |>.div
      (continuous_officialEuclideanNorm.measurable.pow_const 5)))

private theorem czScalarKernel_eq_four_pi_mul_bsKernelScalar (z : Space) :
    czScalarKernel z = 4 * Real.pi * bsKernelScalar z := by
  by_cases hz : z = 0
  · subst z
    simp [czScalarKernel_zero, bsKernelScalar_zero]
  · rw [czScalarKernel_apply_of_ne_zero hz,
      bsKernelScalar_apply_of_ne_zero hz]
    have hr : officialEuclideanNorm z ≠ 0 := by
      intro hr
      apply hz
      apply norm_eq_zero.mp
      have hle := norm_le_officialEuclideanNorm z
      rw [hr] at hle
      exact le_antisymm hle (norm_nonneg z)
    field_simp

theorem scaled_bsGradKernel_abs_le (i j : Fin 3) (z : Space) :
    |(1 / (4 * Real.pi)) * bsGradKernel i j z| ≤
      4 * bsKernelScalar z := by
  rw [abs_mul, abs_of_pos (by positivity : 0 < (1 / (4 * Real.pi) : ℝ))]
  have h := bsGradKernel_abs_le i j z
  rw [czScalarKernel_eq_four_pi_mul_bsKernelScalar] at h
  calc
    1 / (4 * Real.pi) * |bsGradKernel i j z| ≤
        1 / (4 * Real.pi) * (4 * (4 * Real.pi * bsKernelScalar z)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4 * bsKernelScalar z := by field_simp

private theorem pvRegions_union {ε ρ : ℝ} (hερ : ε < ρ) (hρ1 : ρ ≤ 1) :
    pvNearSet ε ρ ∪ pvShellSet ρ ∪ pvFarSet =
      {z : Space | ε < officialEuclideanNorm z} := by
  ext z
  simp only [pvNearSet, pvShellSet, pvFarSet, mem_union, mem_setOf_eq]
  constructor
  · rintro ((h | h) | h)
    · exact h.1
    · exact lt_of_lt_of_le hερ h.1
    · exact lt_of_lt_of_le hερ (hρ1.trans h)
  · intro hε
    by_cases hρ : officialEuclideanNorm z < ρ
    · exact Or.inl (Or.inl ⟨hε, hρ⟩)
    · by_cases h1 : officialEuclideanNorm z < 1
      · exact Or.inl (Or.inr ⟨le_of_not_gt hρ, h1⟩)
      · exact Or.inr (le_of_not_gt h1)

private theorem integrable_piece
    {ε : ℝ} (hε : 0 < ε) (i j : Fin 3)
    (φ : SchwartzMap Space ℝ) (x : Space)
    {s : Set Space} (hs : MeasurableSet s)
    (hsub : s ⊆ {z : Space | ε < officialEuclideanNorm z}) :
    Integrable (s.indicator (fun z =>
      (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z))) := by
  let ψ := reflectedTranslate φ x
  have hall := integrable_sharpPuncturedGradient_schwartz hε i j ψ
  apply hall.norm.mono'
  · exact (((measurable_const.mul (measurable_bsGradKernel i j)).mul
      ψ.continuous.measurable).indicator hs).aestronglyMeasurable
  · filter_upwards [] with z
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hsub hz)]
      change ‖(1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)‖ ≤
        ‖(1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)‖
      exact le_rfl
    · rw [Set.indicator_of_notMem hz]
      simpa only [norm_zero] using norm_nonneg
        ({z : Space | ε < officialEuclideanNorm z}.indicator
          (fun z => (1 / (4 * Real.pi)) * bsGradKernel i j z * ψ z) z)

/-- Exact three-region decomposition of every positive sharp truncation. -/
theorem puncturedGradientIntegral_eq_near_shell_far
    {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (hρ1 : ρ ≤ 1)
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    puncturedGradientIntegral ε i j (reflectedTranslate φ x) =
      (∫ z in pvNearSet ε ρ,
        (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)) +
      (∫ z in pvShellSet ρ,
        (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)) +
      (∫ z in pvFarSet,
        (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)) := by
  let f : Space → ℝ := fun z =>
    (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)
  have hnsub : pvNearSet ε ρ ⊆ {z : Space | ε < officialEuclideanNorm z} :=
    fun _ hz => hz.1
  have hssub : pvShellSet ρ ⊆ {z : Space | ε < officialEuclideanNorm z} := by
    intro z hz
    exact lt_of_lt_of_le hερ hz.1
  have hfsub : pvFarSet ⊆ {z : Space | ε < officialEuclideanNorm z} := by
    intro z hz
    exact lt_of_lt_of_le hερ (hρ1.trans hz)
  have hn := integrable_piece hε i j φ x (measurableSet_pvNearSet ε ρ) hnsub
  have hs := integrable_piece hε i j φ x (measurableSet_pvShellSet ρ) hssub
  have hf := integrable_piece hε i j φ x measurableSet_pvFarSet hfsub
  rw [puncturedGradientIntegral, exteriorIntegral]
  simp only [reflectedTranslate_apply]
  rw [← MeasureTheory.integral_indicator (μ := volume) (f := f)
      (measurableSet_pvNearSet ε ρ),
    ← MeasureTheory.integral_indicator (μ := volume) (f := f)
      (measurableSet_pvShellSet ρ),
    ← MeasureTheory.integral_indicator (μ := volume) (f := f)
      measurableSet_pvFarSet]
  rw [← pvRegions_union hερ hρ1]
  have hns : Disjoint (pvNearSet ε ρ) (pvShellSet ρ) := by
    rw [Set.disjoint_left]
    intro z hnz hsz
    exact (not_lt_of_ge hsz.1) hnz.2
  have hnf : Disjoint (pvNearSet ε ρ) pvFarSet := by
    rw [Set.disjoint_left]
    intro z hnz hfz
    exact (not_lt_of_ge (hρ1.trans hfz)) hnz.2
  have hsf : Disjoint (pvShellSet ρ) pvFarSet := by
    rw [Set.disjoint_left]
    intro z hsz hfz
    exact (not_lt_of_ge hfz) hsz.2
  have hind : (pvNearSet ε ρ ∪ pvShellSet ρ ∪ pvFarSet).indicator f =
      fun z => (pvNearSet ε ρ).indicator f z +
        (pvShellSet ρ).indicator f z + pvFarSet.indicator f z := by
    funext z
    by_cases hnz : z ∈ pvNearSet ε ρ
    · have hsz : z ∉ pvShellSet ρ := fun h =>
        (not_lt_of_ge h.1) hnz.2
      have hfz : z ∉ pvFarSet := fun h =>
        (not_lt_of_ge (hρ1.trans h)) hnz.2
      simp [hnz, hsz, hfz]
    · by_cases hsz : z ∈ pvShellSet ρ
      · have hfz : z ∉ pvFarSet := fun h =>
          (not_lt_of_ge h) hsz.2
        simp [hnz, hsz, hfz]
      · by_cases hfz : z ∈ pvFarSet
        · simp [hnz, hsz, hfz]
        · simp [hnz, hsz, hfz]
  rw [hind]
  change (∫ z : Space,
      ((pvNearSet ε ρ).indicator f z + (pvShellSet ρ).indicator f z) +
        pvFarSet.indicator f z) =
    ((∫ z : Space, (pvNearSet ε ρ).indicator f z) +
      ∫ z : Space, (pvShellSet ρ).indicator f z) +
      ∫ z : Space, pvFarSet.indicator f z
  calc
    (∫ z : Space,
        ((pvNearSet ε ρ).indicator f z + (pvShellSet ρ).indicator f z) +
          pvFarSet.indicator f z) =
        (∫ z : Space,
          (pvNearSet ε ρ).indicator f z + (pvShellSet ρ).indicator f z) +
          ∫ z : Space, pvFarSet.indicator f z :=
      integral_add (hn.add hs) hf
    _ = ((∫ z : Space, (pvNearSet ε ρ).indicator f z) +
          ∫ z : Space, (pvShellSet ρ).indicator f z) +
          ∫ z : Space, pvFarSet.indicator f z := by
      rw [integral_add hn hs]

private theorem integrable_near_remainder
    {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ)
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    Integrable ((pvNearSet ε ρ).indicator (fun z =>
      (1 / (4 * Real.pi)) * bsGradKernel i j z *
        (φ (x - z) - φ x))) := by
  let ψ := reflectedTranslate φ x
  let M : ℝ := (SchwartzMap.seminorm ℝ 0 1) ψ
  let majorant : Space → ℝ := (Metric.ball (0 : Space) ρ).indicator
    (fun z => 4 * M * (‖z‖ * bsKernelScalar z))
  have hρ : 0 < ρ := hε.trans hερ
  have hmajorant : Integrable majorant := by
    have hbase := integrableOn_norm_mul_bsKernelScalar_ball hρ
    have hscaled : IntegrableOn (fun z : Space =>
        4 * M * (‖z‖ * bsKernelScalar z))
        (Metric.ball (0 : Space) ρ) := hbase.const_mul (4 * M)
    exact hscaled.integrable_indicator measurableSet_ball
  apply hmajorant.mono'
  · exact ((((measurable_const.mul (measurable_bsGradKernel i j)).mul
      (ψ.continuous.measurable.sub measurable_const))).indicator
      (measurableSet_pvNearSet ε ρ)).aestronglyMeasurable
  · filter_upwards [] with z
    by_cases hz : z ∈ pvNearSet ε ρ
    · have hzball : z ∈ Metric.ball (0 : Space) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (norm_le_officialEuclideanNorm z) hz.2
      dsimp only [majorant]
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hzball,
        norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hk := scaled_bsGradKernel_abs_le i j z
      have hψ := schwartz_sub_zero_norm_le ψ z
      have hdiff : |φ (x - z) - φ x| ≤ M * ‖z‖ := by
        simpa only [ψ, reflectedTranslate_apply, sub_zero, M,
          Real.norm_eq_abs] using hψ
      have hk0 : 0 ≤ 4 * bsKernelScalar z :=
        mul_nonneg (by norm_num) (bsKernelScalar_nonneg z)
      calc
        |1 / (4 * Real.pi) * bsGradKernel i j z| *
            |φ (x - z) - φ x| ≤
            (4 * bsKernelScalar z) * (M * ‖z‖) :=
          mul_le_mul hk hdiff (abs_nonneg _) hk0
        _ = 4 * M * (‖z‖ * bsKernelScalar z) := by ring
    · rw [Set.indicator_of_notMem hz, norm_zero]
      dsimp only [majorant]
      by_cases hzball : z ∈ Metric.ball (0 : Space) ρ
      · rw [Set.indicator_of_mem hzball]
        exact mul_nonneg
          (mul_nonneg (by norm_num) (apply_nonneg _ _))
          (mul_nonneg (norm_nonneg _) (bsKernelScalar_nonneg _))
      · rw [Set.indicator_of_notMem hzball]

/-- Exact inner cancellation: on a positive annulus the convolution may be
written with `φ(x-z)-φ(x)`, because the constant tensor mode is integrable and
has zero integral. -/
theorem integral_pvNearSet_eq_remainder
    {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ)
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    (∫ z in pvNearSet ε ρ,
      (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)) =
    ∫ z in pvNearSet ε ρ,
      (1 / (4 * Real.pi)) * bsGradKernel i j z *
        (φ (x - z) - φ x) := by
  let f : Space → ℝ := fun z =>
    (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)
  let r : Space → ℝ := fun z =>
    (1 / (4 * Real.pi)) * bsGradKernel i j z * (φ (x - z) - φ x)
  let c : Space → ℝ := fun z =>
    φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j z)
  have hρ : 0 < ρ := hε.trans hερ
  have hf : IntegrableOn f (pvNearSet ε ρ) := by
    have hi := integrable_piece hε i j φ x
      (measurableSet_pvNearSet ε ρ) (fun _ hz => hz.1)
    exact (integrable_indicator_iff (measurableSet_pvNearSet ε ρ)).mp hi
  have hr : IntegrableOn r (pvNearSet ε ρ) := by
    exact (integrable_indicator_iff (measurableSet_pvNearSet ε ρ)).mp
      (integrable_near_remainder hε hερ i j φ x)
  have hc : IntegrableOn c (pvNearSet ε ρ) := by
    have hsub : pvNearSet ε ρ = {z : Space |
        ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ} := rfl
    rw [hsub]
    exact (integrableOn_scaled_bsGradKernel_euclideanAnnulus hε i j).const_mul (φ x)
  have hdecomp : ∀ z : Space, f z = r z + c z := by
    intro z
    dsimp only [f, r, c]
    ring
  calc
    (∫ z in pvNearSet ε ρ, f z) =
        ∫ z in pvNearSet ε ρ, r z + c z := by
      apply setIntegral_congr_fun (measurableSet_pvNearSet ε ρ)
      intro z _
      exact hdecomp z
    _ = (∫ z in pvNearSet ε ρ, r z) +
        ∫ z in pvNearSet ε ρ, c z := integral_add hr hc
    _ = (∫ z in pvNearSet ε ρ, r z) + 0 := by
      congr 1
      dsimp only [c]
      rw [MeasureTheory.integral_const_mul,
        show pvNearSet ε ρ = {z : Space |
          ε < officialEuclideanNorm z ∧ officialEuclideanNorm z < ρ} from rfl,
        integral_scaled_bsGradKernel_euclideanAnnulus_eq_zero, mul_zero]
    _ = ∫ z in pvNearSet ε ρ, r z := add_zero _

/-- The sharp truncation with its inner constant mode already removed. -/
theorem puncturedGradientIntegral_eq_remainder_shell_far
    {ε ρ : ℝ} (hε : 0 < ε) (hερ : ε < ρ) (hρ1 : ρ ≤ 1)
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    puncturedGradientIntegral ε i j (reflectedTranslate φ x) =
      (∫ z in pvNearSet ε ρ,
        (1 / (4 * Real.pi)) * bsGradKernel i j z *
          (φ (x - z) - φ x)) +
      (∫ z in pvShellSet ρ,
        (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)) +
      (∫ z in pvFarSet,
        (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)) := by
  rw [puncturedGradientIntegral_eq_near_shell_far hε hερ hρ1 i j φ x,
    integral_pvNearSet_eq_remainder hε hερ i j φ x]

/-- The actual translated principal value is the limit of the three-region
split with the cancellation remainder in the shrinking inner annulus. -/
theorem tendsto_principalValueConvolution_split
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    Tendsto (fun ε : ℝ =>
      (∫ z in pvNearSet ε ρ,
        (1 / (4 * Real.pi)) * bsGradKernel i j z *
          (φ (x - z) - φ x)) +
      (∫ z in pvShellSet ρ,
        (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)) +
      (∫ z in pvFarSet,
        (1 / (4 * Real.pi)) * bsGradKernel i j z * φ (x - z)))
      (nhdsWithin 0 (Ioi 0))
      (nhds (principalValueConvolution i j φ x)) := by
  have hpv := hasBiotSavartPrincipalValue_reflectedTranslate i j φ x
  apply hpv.congr'
  have hsmall : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < ρ :=
    (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
      (Iio_mem_nhds hρ)
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hερ
  exact puncturedGradientIntegral_eq_remainder_shell_far
    hε hερ hρ1 i j φ x

end Navier.Analysis.BiotSavartPVSplitEstimate
