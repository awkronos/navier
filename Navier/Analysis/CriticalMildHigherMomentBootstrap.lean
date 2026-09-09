import Navier.Analysis.CriticalMildFullPositiveTimeRegularity

/-!
# The next positive-time raw-carrier moment

This module begins the higher-moment bootstrap after full half-generator
regularity. It remains entirely on the raw complex mild carrier. Physical
Fourier normalization is supplied by a separate decoder.

The Gaussian layer first records the three-quarter-generator heat gain
`sum |k|^(3/2) ||u_k||`. For the actual nonlinear history, the derived
quarter-Hölder endpoint modulus supports the strict five-eighth-generator rung
`sum |k|^(5/4) ||u_k||`: its cancelling density behaves like
`(t-s)^(-7/8)`, which is integrable. The next endpoint is not claimed here.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set

namespace Navier.Analysis.CriticalMildHigherMomentBootstrap

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatCarrierAlgebra
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildObservationContinuity
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildQuantitativeRestart
open Navier.Analysis.CriticalMildInteriorTimeModulus
open Navier.Analysis.CriticalMildFullPositiveTimeRegularity
open Navier.Analysis.LeiLinPositiveRestartCancellation
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PeriodicDynamicCriticalTail

/-- The additional square-root frequency factor between the half-generator
and full-generator carrier moments. -/
def halfFrequencyWeight (k : LatticeMode) : ℝ :=
  Real.sqrt ‖complexFrequency (latticeFrequency k)‖

/-- The raw-carrier three-quarter-generator moment
`sum |k|^(3/2) ||u_k||`. -/
def heatThreeQuarterGeneratorMoment (u : WeightedLatticeBanach) : ℝ :=
  ∑' k : LatticeMode,
    halfFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖)

theorem heatThreeQuarterGeneratorMoment_nonneg (u : WeightedLatticeBanach) :
    0 ≤ heatThreeQuarterGeneratorMoment u := by
  unfold heatThreeQuarterGeneratorMoment
  exact tsum_nonneg fun k => mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A half-frequency Gaussian gain, with a simple explicit constant. -/
theorem sqrt_mul_exp_neg_mul_sq_le_inv_fourthRoot
    {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    Real.sqrt q * Real.exp (-(a * q * q)) ≤
      (Real.sqrt (Real.sqrt a))⁻¹ := by
  let s : ℝ := Real.sqrt a
  let y : ℝ := s * q
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 ha
  have hy : 0 ≤ y := mul_nonneg hs.le hq
  have hbase : Real.sqrt y * Real.exp (-(y * y)) ≤ 1 := by
    by_cases hy1 : y ≤ 1
    · have hsqrty : Real.sqrt y ≤ 1 := Real.sqrt_le_one.mpr hy1
      have hexp : Real.exp (-(y * y)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hy hy))
      exact (mul_le_mul hsqrty hexp (Real.exp_pos _).le (by positivity)).trans_eq
        (one_mul 1)
    · have hy1' : 1 ≤ y := le_of_not_ge hy1
      have hsqrty : Real.sqrt y ≤ y := (Real.sqrt_le_iff).2 ⟨hy, by nlinarith⟩
      refine (mul_le_mul_of_nonneg_right hsqrty (Real.exp_pos _).le).trans ?_
      have hone :=
        mul_exp_neg_mul_sq_le_inv_sqrt (a := (1 : ℝ)) (r := y) zero_lt_one
      norm_num at hone
      exact hone
  have hsqrtmul : Real.sqrt y = Real.sqrt s * Real.sqrt q := by
    dsimp [y]
    exact Real.sqrt_mul hs.le q
  have hsq : s * s = a := by dsimp [s]; exact Real.mul_self_sqrt ha.le
  have hrewrite :
      Real.sqrt q * Real.exp (-(a * q * q)) =
        (Real.sqrt s)⁻¹ * (Real.sqrt y * Real.exp (-(y * y))) := by
    rw [hsqrtmul]
    have hroots : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
    dsimp [y]
    rw [show -(s * q * (s * q)) = -(a * q * q) by
      calc
        -(s * q * (s * q)) = -((s * s) * (q * q)) := by ring
        _ = -(a * q * q) := by rw [hsq]; ring]
    field_simp
  rw [hrewrite]
  exact (mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq
    (mul_one _)

/-- Positive heat time gains one additional half-frequency on an existing
half-generator input. -/
theorem summable_threeQuarterGeneratorMoment_weightedHeatFlow
    (ν r : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (hhalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :
    Summable fun k : LatticeMode =>
      halfFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ *
          ‖weightedHeatFlow ν r hν.le hr.le u k‖) := by
  let C : ℝ := (Real.sqrt (Real.sqrt (ν * r)))⁻¹
  have hpoint : ∀ k : LatticeMode,
      halfFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            ‖weightedHeatFlow ν r hν.le hr.le u k‖) ≤
        C * (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) := by
    intro k
    rw [weightedHeatFlow_apply_of_divergenceFree ν r hν.le hr.le u hu k,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (complexHeatDecay_nonneg ν r (latticeFrequency k))]
    have hgain := sqrt_mul_exp_neg_mul_sq_le_inv_fourthRoot
      (mul_pos hν hr) (norm_nonneg (complexFrequency (latticeFrequency k)))
    have hdecay : complexHeatDecay ν r (latticeFrequency k) =
        Real.exp (-((ν * r) * ‖complexFrequency (latticeFrequency k)‖ *
          ‖complexFrequency (latticeFrequency k)‖)) := by
      unfold complexHeatDecay FrequencyHeatLeray.heatDecay
      rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
      congr 1
      ring
    rw [hdecay]
    dsimp [halfFrequencyWeight, C]
    calc
      Real.sqrt ‖complexFrequency (latticeFrequency k)‖ *
          (‖complexFrequency (latticeFrequency k)‖ *
            (Real.exp (-((ν * r) *
              ‖complexFrequency (latticeFrequency k)‖ *
                ‖complexFrequency (latticeFrequency k)‖)) * ‖u k‖)) =
        (Real.sqrt ‖complexFrequency (latticeFrequency k)‖ *
          Real.exp (-((ν * r) *
            ‖complexFrequency (latticeFrequency k)‖ *
              ‖complexFrequency (latticeFrequency k)‖))) *
            (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) := by ring
      _ ≤ (Real.sqrt (Real.sqrt (ν * r)))⁻¹ *
          (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :=
        mul_le_mul_of_nonneg_right hgain
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (hhalf.mul_left C).of_nonneg_of_le
    (fun k => mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hpoint

/-- Quantitative version of the half-frequency heat gain. -/
theorem heatThreeQuarterGeneratorMoment_weightedHeatFlow_le
    (ν r : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (hhalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :
    heatThreeQuarterGeneratorMoment
        (weightedHeatFlow ν r hν.le hr.le u) ≤
      (Real.sqrt (Real.sqrt (ν * r)))⁻¹ *
        heatHalfGeneratorMoment u := by
  let C : ℝ := (Real.sqrt (Real.sqrt (ν * r)))⁻¹
  have hpoint : ∀ k : LatticeMode,
      halfFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            ‖weightedHeatFlow ν r hν.le hr.le u k‖) ≤
        C * (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) := by
    intro k
    rw [weightedHeatFlow_apply_of_divergenceFree ν r hν.le hr.le u hu k,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (complexHeatDecay_nonneg ν r (latticeFrequency k))]
    have hgain := sqrt_mul_exp_neg_mul_sq_le_inv_fourthRoot
      (mul_pos hν hr) (norm_nonneg (complexFrequency (latticeFrequency k)))
    have hdecay : complexHeatDecay ν r (latticeFrequency k) =
        Real.exp (-((ν * r) * ‖complexFrequency (latticeFrequency k)‖ *
          ‖complexFrequency (latticeFrequency k)‖)) := by
      unfold complexHeatDecay FrequencyHeatLeray.heatDecay
      rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
      congr 1
      ring
    rw [hdecay]
    dsimp [halfFrequencyWeight, C]
    calc
      Real.sqrt ‖complexFrequency (latticeFrequency k)‖ *
          (‖complexFrequency (latticeFrequency k)‖ *
            (Real.exp (-((ν * r) *
              ‖complexFrequency (latticeFrequency k)‖ *
                ‖complexFrequency (latticeFrequency k)‖)) * ‖u k‖)) =
        (Real.sqrt ‖complexFrequency (latticeFrequency k)‖ *
          Real.exp (-((ν * r) *
            ‖complexFrequency (latticeFrequency k)‖ *
              ‖complexFrequency (latticeFrequency k)‖))) *
            (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) := by ring
      _ ≤ C * (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :=
        mul_le_mul_of_nonneg_right hgain
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  unfold heatThreeQuarterGeneratorMoment heatHalfGeneratorMoment
  have hleft := summable_threeQuarterGeneratorMoment_weightedHeatFlow
    ν r hν hr u hu hhalf
  have hright := hhalf.mul_left C
  calc
    (∑' k : LatticeMode,
      halfFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ *
          ‖weightedHeatFlow ν r hν.le hr.le u k‖)) ≤
        ∑' k : LatticeMode,
          C * (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :=
      hleft.tsum_le_tsum hpoint hright
    _ = C * ∑' k : LatticeMode,
        ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖ := tsum_mul_left

/-- Subtraction preserves the three-quarter-generator domain. -/
theorem summable_threeQuarterGeneratorMoment_sub
    (u v : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode => halfFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖))
    (hv : Summable fun k : LatticeMode => halfFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖)) :
    Summable fun k : LatticeMode => halfFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖(u - v) k‖) := by
  have hright := hu.add hv
  exact hright.of_nonneg_of_le
    (fun k => mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun k => by
      change halfFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * ‖u k - v k‖) ≤ _
      calc
        halfFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * ‖u k - v k‖) ≤
          halfFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * (‖u k‖ + ‖v k‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
            (Real.sqrt_nonneg _)
        _ = halfFrequencyWeight k *
              (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) +
            halfFrequencyWeight k *
              (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖) := by ring)

/-- The three-quarter moment of a sum is subadditive on its domain. -/
theorem heatThreeQuarterGeneratorMoment_add_le
    (u v : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode => halfFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖))
    (hv : Summable fun k : LatticeMode => halfFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖)) :
    heatThreeQuarterGeneratorMoment (u + v) ≤
      heatThreeQuarterGeneratorMoment u + heatThreeQuarterGeneratorMoment v := by
  unfold heatThreeQuarterGeneratorMoment
  have hpoint : ∀ k : LatticeMode,
      halfFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * ‖(u + v) k‖) ≤
        halfFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) +
          halfFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖) := by
    intro k
    change _ * (_ * ‖u k + v k‖) ≤ _
    calc
      halfFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * ‖u k + v k‖) ≤
        halfFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * (‖u k‖ + ‖v k‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
          (Real.sqrt_nonneg _)
      _ = _ := by ring
  exact Summable.tsum_le_tsum hpoint
    ((hu.add hv).of_nonneg_of_le
      (fun k => mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hpoint)
    (hu.add hv) |>.trans_eq (Summable.tsum_add hu hv)

set_option maxHeartbeats 800000 in
/-- A frozen-source difference gains three halves of a frequency power after
the existing half-generator cancellation is passed through one further
half-frequency heat gain. -/
theorem heatThreeQuarterGeneratorMoment_heatRegularizedSpectralOutput_sub_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v) :
    heatThreeQuarterGeneratorMoment
        (heatRegularizedSpectralOutput ν τ hν hτ u u hu -
          heatRegularizedSpectralOutput ν τ hν hτ v v hv) ≤
      (Real.sqrt (Real.sqrt (ν * (τ / 2))))⁻¹ *
        ((2 / (ν * (τ / 2))) * (‖u‖ + ‖v‖) * ‖u - v‖) := by
  let a : ℝ := τ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let zu := heatRegularizedSpectralOutput ν a hν ha u u hu
  let zv := heatRegularizedSpectralOutput ν a hν ha v v hv
  let z := zu - zv
  have hzu : LatticeDivergenceFree zu :=
    heatRegularizedSpectralOutput_divergenceFree ν a hν ha u u hu
  have hzv : LatticeDivergenceFree zv :=
    heatRegularizedSpectralOutput_divergenceFree ν a hν ha v v hv
  have hz : LatticeDivergenceFree z := hzu.sub hzv
  have hzuHalf := summable_halfGeneratorMoment_heatRegularizedSpectralOutput
    ν a hν ha u u hu
  have hzvHalf := summable_halfGeneratorMoment_heatRegularizedSpectralOutput
    ν a hν ha v v hv
  have hzHalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖z k‖ := by
    exact summable_halfGeneratorMoment_sub zu zv hzuHalf hzvHalf
  have haa : a + a = τ := by dsimp [a]; ring
  have hsemu := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha u u hu
  have hsemv := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha v v hv
  have hsemigroup : weightedHeatFlow ν a hν.le ha.le z =
      heatRegularizedSpectralOutput ν τ hν hτ u u hu -
        heatRegularizedSpectralOutput ν τ hν hτ v v hv := by
    dsimp [z, zu, zv]
    rw [← weightedHeatFlowCLM_apply, map_sub,
      weightedHeatFlowCLM_apply, weightedHeatFlowCLM_apply, hsemu, hsemv]
    simp only [haa]
  have hthree := heatThreeQuarterGeneratorMoment_weightedHeatFlow_le
    ν a hν ha z hz hzHalf
  have hhalf := heatHalfGeneratorMoment_heatRegularizedSpectralOutput_sub_le
    ν a hν ha u v hu hv
  rw [hsemigroup] at hthree
  refine hthree.trans ?_
  exact mul_le_mul_of_nonneg_left hhalf
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- The actual raw mild integrand inherits the three-quarter-generator
frozen-source cancellation at every strict terminal lag. -/
theorem heatThreeQuarterGeneratorMoment_criticalMildPathIntegrand_sub_frozen_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s < t) :
    heatThreeQuarterGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s -
          heatRegularizedSpectralOutput ν (t - s) hν (sub_pos.mpr hst)
            (u t) (u t) (hu t)) ≤
      (Real.sqrt (Real.sqrt (ν * ((t - s) / 2))))⁻¹ *
        ((2 / (ν * ((t - s) / 2))) *
          (‖u s‖ + ‖u t‖) * ‖u s - u t‖) := by
  have hlag : 0 < t - s := sub_pos.mpr hst
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
    ν hν (u s) (u s) (hu s) hlag]
  exact heatThreeQuarterGeneratorMoment_heatRegularizedSpectralOutput_sub_le
    ν (t - s) hν hlag (u s) (u t) (hu s) (hu t)

/-- Finite three-quarter moment sums pass through a Bochner integral. -/
theorem sum_heatThreeQuarterGeneratorMoment_integral_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (F : Finset LatticeMode) (f : α → WeightedLatticeBanach)
    (hf : IntegrableOn f S μ)
    (hfsum : ∀ᵐ s ∂μ.restrict S, Summable fun k : LatticeMode =>
      halfFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖))
    (hfM : IntegrableOn
      (fun s => heatThreeQuarterGeneratorMoment (f s)) S μ) :
    (∑ k ∈ F, halfFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ *
        ‖(∫ s in S, f s ∂μ) k‖)) ≤
      ∫ s in S, heatThreeQuarterGeneratorMoment (f s) ∂μ := by
  have hcoord (k : LatticeMode) :
      (∫ s in S, f s ∂μ) k = ∫ s in S, f s k ∂μ := by
    change (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k)
        (∫ s in S, f s ∂μ) = _
    exact (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integral_comp_comm hf |>.symm
  have hcoordInt (k : LatticeMode) : IntegrableOn (fun s => f s k) S μ :=
    (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integrable_comp hf
  have htermInt (k : LatticeMode) : IntegrableOn
      (fun s => halfFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖)) S μ :=
    ((hcoordInt k).norm.const_mul _).const_mul _
  calc
    ∑ k ∈ F, halfFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ *
          ‖(∫ s in S, f s ∂μ) k‖) ≤
      ∑ k ∈ F, halfFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ *
          (∫ s in S, ‖f s k‖ ∂μ)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hcoord k]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (norm_nonneg _)) (Real.sqrt_nonneg _)
    _ = ∫ s in S, ∑ k ∈ F, halfFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖) ∂μ := by
      rw [integral_finsetSum F (fun k _ => htermInt k)]
      simp_rw [integral_const_mul]
    _ ≤ ∫ s in S, heatThreeQuarterGeneratorMoment (f s) ∂μ := by
      apply integral_mono_ae
      · exact integrable_finsetSum F fun k _ => htermInt k
      · exact hfM
      · filter_upwards [hfsum] with s hs
        unfold heatThreeQuarterGeneratorMoment
        exact hs.sum_le_tsum F fun k _ => mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The full three-quarter moment passes through a Bochner integral whenever
the pointwise moments and their scalar integral are summable. -/
theorem heatThreeQuarterGeneratorMoment_integral_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (f : α → WeightedLatticeBanach) (hf : IntegrableOn f S μ)
    (hfsum : ∀ᵐ s ∂μ.restrict S, Summable fun k : LatticeMode =>
      halfFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖))
    (hfM : IntegrableOn
      (fun s => heatThreeQuarterGeneratorMoment (f s)) S μ) :
    heatThreeQuarterGeneratorMoment (∫ s in S, f s ∂μ) ≤
      ∫ s in S, heatThreeQuarterGeneratorMoment (f s) ∂μ := by
  unfold heatThreeQuarterGeneratorMoment
  apply Real.tsum_le_of_sum_le
  · intro k
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · intro F
    exact sum_heatThreeQuarterGeneratorMoment_integral_le_integral
      F f hf hfsum hfM

/-- The explicit coefficient left after combining the extra half-frequency
heat gain with the square-root endpoint modulus. -/
def threeQuarterDiniConstant (ν R C : ℝ) : ℝ :=
  (8 / ν) * R * C * (Real.sqrt (Real.sqrt (ν / 2)))⁻¹

/-- Exact reduction of the three-quarter cancellation density to the
integrable power `δ^(-3/4)`. -/
theorem threeQuarter_cancellation_density_eq
    { ν R C δ : ℝ } (hν : 0 < ν) (hδ : 0 < δ) :
    (Real.sqrt (Real.sqrt (ν * (δ / 2))))⁻¹ *
        ((2 / (ν * (δ / 2))) * (2 * R) * (C * Real.sqrt δ)) =
      threeQuarterDiniConstant ν R C * δ ^ (-(3 / 4 : ℝ)) := by
  have hν2 : 0 < ν / 2 := by positivity
  have hrootSplit : Real.sqrt (Real.sqrt ((ν / 2) * δ)) =
      Real.sqrt (Real.sqrt (ν / 2)) * Real.sqrt (Real.sqrt δ) := by
    rw [Real.sqrt_mul hν2.le, Real.sqrt_mul (Real.sqrt_nonneg (ν / 2))]
  have hrootδ : 0 < Real.sqrt (Real.sqrt δ) := by positivity
  have hrootν : 0 < Real.sqrt (Real.sqrt (ν / 2)) := by positivity
  have hsqrtδ : Real.sqrt δ =
      Real.sqrt (Real.sqrt δ) * Real.sqrt (Real.sqrt δ) := by
    rw [Real.mul_self_sqrt (Real.sqrt_nonneg δ)]
  have hinvrootδ : (Real.sqrt (Real.sqrt δ))⁻¹ * Real.sqrt δ =
      Real.sqrt (Real.sqrt δ) := by
    calc
      (Real.sqrt (Real.sqrt δ))⁻¹ * Real.sqrt δ =
          (Real.sqrt (Real.sqrt δ))⁻¹ *
            (Real.sqrt (Real.sqrt δ) * Real.sqrt (Real.sqrt δ)) :=
        congrArg (fun x => (Real.sqrt (Real.sqrt δ))⁻¹ * x) hsqrtδ
      _ = Real.sqrt (Real.sqrt δ) := by field_simp
  have hpow := inv_mul_sqrt_sqrt_eq_rpow_neg_three_fourths hδ
  rw [show ν * (δ / 2) = (ν / 2) * δ by ring, hrootSplit,
    mul_inv_rev, show 2 / ((ν / 2) * δ) = (4 / ν) * δ⁻¹ by
      field_simp [hν.ne', hδ.ne']; ring]
  calc
    (Real.sqrt (Real.sqrt δ))⁻¹ *
          (Real.sqrt (Real.sqrt (ν / 2)))⁻¹ *
            ((4 / ν) * δ⁻¹ * (2 * R) * (C * Real.sqrt δ)) =
        ((8 / ν) * R * C *
          (Real.sqrt (Real.sqrt (ν / 2)))⁻¹) *
            (δ⁻¹ * ((Real.sqrt (Real.sqrt δ))⁻¹ * Real.sqrt δ)) := by
      ring
    _ = ((8 / ν) * R * C *
          (Real.sqrt (Real.sqrt (ν / 2)))⁻¹) *
            (δ⁻¹ * Real.sqrt (Real.sqrt δ)) := by rw [hinvrootδ]
    _ = threeQuarterDiniConstant ν R C * δ ^ (-(3 / 4 : ℝ)) := by
      rw [hpow]
      rfl

/-! ## A strict fractional rung compatible with the quarter-Hölder endpoint -/

/-- The quarter-frequency factor used for the first strict bootstrap beyond
the half-generator domain. -/
def quarterFrequencyWeight (k : LatticeMode) : ℝ :=
  Real.sqrt (Real.sqrt ‖complexFrequency (latticeFrequency k)‖)

/-- The raw-carrier five-eighth-generator moment
`sum |k|^(5/4) ||u_k||`. -/
def heatFiveEighthGeneratorMoment (u : WeightedLatticeBanach) : ℝ :=
  ∑' k : LatticeMode, quarterFrequencyWeight k *
    (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖)

theorem heatFiveEighthGeneratorMoment_nonneg (u : WeightedLatticeBanach) :
    0 ≤ heatFiveEighthGeneratorMoment u := by
  unfold heatFiveEighthGeneratorMoment
  exact tsum_nonneg fun k => mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- A quarter-frequency Gaussian gain at the sharp parabolic eighth-root
scale. -/
theorem fourthRoot_mul_exp_neg_mul_sq_le_inv_eighthRoot
    {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) :
    Real.sqrt (Real.sqrt q) * Real.exp (-(a * q * q)) ≤
      (Real.sqrt (Real.sqrt (Real.sqrt a)))⁻¹ := by
  let s : ℝ := Real.sqrt a
  let y : ℝ := s * q
  have hs : 0 < s := by dsimp [s]; exact Real.sqrt_pos.2 ha
  have hy : 0 ≤ y := mul_nonneg hs.le hq
  have hbase : Real.sqrt (Real.sqrt y) * Real.exp (-(y * y)) ≤ 1 := by
    by_cases hy1 : y ≤ 1
    · have hroot : Real.sqrt (Real.sqrt y) ≤ 1 :=
        Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr hy1)
      have hexp : Real.exp (-(y * y)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hy hy))
      exact (mul_le_mul hroot hexp (Real.exp_pos _).le (by positivity)).trans_eq
        (one_mul 1)
    · have hy1' : 1 ≤ y := le_of_not_ge hy1
      have hsqrty : Real.sqrt y ≤ y := (Real.sqrt_le_iff).2 ⟨hy, by nlinarith⟩
      have hfourth : Real.sqrt (Real.sqrt y) ≤ Real.sqrt y :=
        (Real.sqrt_le_iff).2 ⟨Real.sqrt_nonneg y, by
          rw [Real.sq_sqrt hy]
          exact hsqrty⟩
      refine (mul_le_mul_of_nonneg_right (hfourth.trans hsqrty)
        (Real.exp_pos _).le).trans ?_
      have hone :=
        mul_exp_neg_mul_sq_le_inv_sqrt (a := (1 : ℝ)) (r := y) zero_lt_one
      norm_num at hone
      exact hone
  have hsqrtmul : Real.sqrt y = Real.sqrt s * Real.sqrt q := by
    dsimp [y]
    exact Real.sqrt_mul hs.le q
  have hfourthmul : Real.sqrt (Real.sqrt y) =
      Real.sqrt (Real.sqrt s) * Real.sqrt (Real.sqrt q) := by
    rw [hsqrtmul, Real.sqrt_mul (Real.sqrt_nonneg s)]
  have hsq : s * s = a := by dsimp [s]; exact Real.mul_self_sqrt ha.le
  have hrewrite :
      Real.sqrt (Real.sqrt q) * Real.exp (-(a * q * q)) =
        (Real.sqrt (Real.sqrt s))⁻¹ *
          (Real.sqrt (Real.sqrt y) * Real.exp (-(y * y))) := by
    rw [hfourthmul]
    have hroots : Real.sqrt (Real.sqrt s) ≠ 0 := by positivity
    dsimp [y]
    rw [show -(s * q * (s * q)) = -(a * q * q) by
      calc
        -(s * q * (s * q)) = -((s * s) * (q * q)) := by ring
        _ = -(a * q * q) := by rw [hsq]; ring]
    field_simp
  rw [hrewrite]
  exact (mul_le_mul_of_nonneg_left hbase
    (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (mul_one _)

/-- Positive heat puts half-generator data in the five-eighth-generator
domain. -/
theorem summable_fiveEighthGeneratorMoment_weightedHeatFlow
    (ν r : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (hhalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ *
        ‖weightedHeatFlow ν r hν.le hr.le u k‖) := by
  have hthree := summable_threeQuarterGeneratorMoment_weightedHeatFlow
    ν r hν hr u hu hhalf
  apply hthree.of_nonneg_of_le
  · intro k
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · intro k
    have hweight : quarterFrequencyWeight k ≤ halfFrequencyWeight k := by
      by_cases hk : k = 0
      · subst k
        unfold quarterFrequencyWeight halfFrequencyWeight
        change Real.sqrt (Real.sqrt (latticeModeSize 0)) ≤
          Real.sqrt (latticeModeSize 0)
        rw [latticeModeSize_zero]
        simp
      · have hq : 1 ≤ ‖complexFrequency (latticeFrequency k)‖ :=
          one_le_latticeModeSize_of_ne_zero hk
        dsimp [quarterFrequencyWeight, halfFrequencyWeight]
        exact (Real.sqrt_le_iff).2 ⟨Real.sqrt_nonneg _, by
          rw [Real.sq_sqrt (norm_nonneg _)]
          exact (Real.sqrt_le_iff).2 ⟨norm_nonneg _, by nlinarith⟩⟩
    exact mul_le_mul_of_nonneg_right hweight
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Every strict nonlinear heat output is in the five-eighth-generator
domain, without higher-moment assumptions on its inputs. -/
theorem summable_fiveEighthGeneratorMoment_heatRegularizedSpectralOutput
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ *
        ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu k‖) := by
  let a : ℝ := τ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let z := heatRegularizedSpectralOutput ν a hν ha u v hu
  have hz : LatticeDivergenceFree z :=
    heatRegularizedSpectralOutput_divergenceFree ν a hν ha u v hu
  have hzHalf := summable_halfGeneratorMoment_heatRegularizedSpectralOutput
    ν a hν ha u v hu
  have hs := summable_fiveEighthGeneratorMoment_weightedHeatFlow
    ν a hν ha z hz hzHalf
  have hsemigroup := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha u v hu
  have haa : a + a = τ := by dsimp [a]; ring
  have hsemigroup' : weightedHeatFlow ν a hν.le ha.le z =
      heatRegularizedSpectralOutput ν τ hν hτ u v hu := by
    dsimp [z]
    simpa only [haa] using hsemigroup
  rw [hsemigroup'] at hs
  exact hs

/-- Subtraction preserves the five-eighth-generator domain. -/
theorem summable_fiveEighthGeneratorMoment_sub
    (u v : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖))
    (hv : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖)) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖(u - v) k‖) := by
  have hright := hu.add hv
  exact hright.of_nonneg_of_le
    (fun k => mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun k => by
      change quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * ‖u k - v k‖) ≤ _
      calc
        quarterFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * ‖u k - v k‖) ≤
          quarterFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * (‖u k‖ + ‖v k‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
            (Real.sqrt_nonneg _)
        _ = quarterFrequencyWeight k *
              (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) +
            quarterFrequencyWeight k *
              (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖) := by ring)

/-- Positive heat gains a quarter frequency on half-generator data. -/
theorem heatFiveEighthGeneratorMoment_weightedHeatFlow_le
    (ν r : ℝ) (hν : 0 < ν) (hr : 0 < r)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (hhalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :
    heatFiveEighthGeneratorMoment
        (weightedHeatFlow ν r hν.le hr.le u) ≤
      (Real.sqrt (Real.sqrt (Real.sqrt (ν * r))))⁻¹ *
        heatHalfGeneratorMoment u := by
  let C : ℝ := (Real.sqrt (Real.sqrt (Real.sqrt (ν * r))))⁻¹
  have hpoint : ∀ k : LatticeMode,
      quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            ‖weightedHeatFlow ν r hν.le hr.le u k‖) ≤
        C * (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) := by
    intro k
    rw [weightedHeatFlow_apply_of_divergenceFree ν r hν.le hr.le u hu k,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (complexHeatDecay_nonneg ν r (latticeFrequency k))]
    have hgain := fourthRoot_mul_exp_neg_mul_sq_le_inv_eighthRoot
      (mul_pos hν hr) (norm_nonneg (complexFrequency (latticeFrequency k)))
    have hdecay : complexHeatDecay ν r (latticeFrequency k) =
        Real.exp (-((ν * r) * ‖complexFrequency (latticeFrequency k)‖ *
          ‖complexFrequency (latticeFrequency k)‖)) := by
      unfold complexHeatDecay FrequencyHeatLeray.heatDecay
      rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
      congr 1
      ring
    rw [hdecay]
    dsimp [quarterFrequencyWeight, C]
    calc
      Real.sqrt (Real.sqrt ‖complexFrequency (latticeFrequency k)‖) *
          (‖complexFrequency (latticeFrequency k)‖ *
            (Real.exp (-((ν * r) *
              ‖complexFrequency (latticeFrequency k)‖ *
                ‖complexFrequency (latticeFrequency k)‖)) * ‖u k‖)) =
        (Real.sqrt (Real.sqrt ‖complexFrequency (latticeFrequency k)‖) *
          Real.exp (-((ν * r) *
            ‖complexFrequency (latticeFrequency k)‖ *
              ‖complexFrequency (latticeFrequency k)‖))) *
            (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) := by ring
      _ ≤ C * (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :=
        mul_le_mul_of_nonneg_right hgain
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  unfold heatFiveEighthGeneratorMoment heatHalfGeneratorMoment
  have hright := hhalf.mul_left C
  have hleft := hright.of_nonneg_of_le
    (fun k => mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hpoint
  calc
    (∑' k : LatticeMode, quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ *
        ‖weightedHeatFlow ν r hν.le hr.le u k‖)) ≤
      ∑' k : LatticeMode,
        C * (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :=
      hleft.tsum_le_tsum hpoint hright
    _ = C * ∑' k : LatticeMode,
        ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖ := tsum_mul_left

set_option maxHeartbeats 800000 in
/-- The frozen-source difference at the strict five-eighth-generator rung. -/
theorem heatFiveEighthGeneratorMoment_heatRegularizedSpectralOutput_sub_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v) :
    heatFiveEighthGeneratorMoment
        (heatRegularizedSpectralOutput ν τ hν hτ u u hu -
          heatRegularizedSpectralOutput ν τ hν hτ v v hv) ≤
      (Real.sqrt (Real.sqrt (Real.sqrt (ν * (τ / 2)))))⁻¹ *
        ((2 / (ν * (τ / 2))) * (‖u‖ + ‖v‖) * ‖u - v‖) := by
  let a : ℝ := τ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let zu := heatRegularizedSpectralOutput ν a hν ha u u hu
  let zv := heatRegularizedSpectralOutput ν a hν ha v v hv
  let z := zu - zv
  have hzu : LatticeDivergenceFree zu :=
    heatRegularizedSpectralOutput_divergenceFree ν a hν ha u u hu
  have hzv : LatticeDivergenceFree zv :=
    heatRegularizedSpectralOutput_divergenceFree ν a hν ha v v hv
  have hz : LatticeDivergenceFree z := hzu.sub hzv
  have hzuHalf := summable_halfGeneratorMoment_heatRegularizedSpectralOutput
    ν a hν ha u u hu
  have hzvHalf := summable_halfGeneratorMoment_heatRegularizedSpectralOutput
    ν a hν ha v v hv
  have hzHalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖z k‖ :=
    summable_halfGeneratorMoment_sub zu zv hzuHalf hzvHalf
  have haa : a + a = τ := by dsimp [a]; ring
  have hsemu := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha u u hu
  have hsemv := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha v v hv
  have hsemigroup : weightedHeatFlow ν a hν.le ha.le z =
      heatRegularizedSpectralOutput ν τ hν hτ u u hu -
        heatRegularizedSpectralOutput ν τ hν hτ v v hv := by
    dsimp [z, zu, zv]
    rw [← weightedHeatFlowCLM_apply, map_sub,
      weightedHeatFlowCLM_apply, weightedHeatFlowCLM_apply, hsemu, hsemv]
    simp only [haa]
  have hfive := heatFiveEighthGeneratorMoment_weightedHeatFlow_le
    ν a hν ha z hz hzHalf
  have hhalf := heatHalfGeneratorMoment_heatRegularizedSpectralOutput_sub_le
    ν a hν ha u v hu hv
  rw [hsemigroup] at hfive
  refine hfive.trans ?_
  exact mul_le_mul_of_nonneg_left hhalf
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

/-- Five-eighth-generator cancellation for the actual raw mild integrand. -/
theorem heatFiveEighthGeneratorMoment_criticalMildPathIntegrand_sub_frozen_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s < t) :
    heatFiveEighthGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s -
          heatRegularizedSpectralOutput ν (t - s) hν (sub_pos.mpr hst)
            (u t) (u t) (hu t)) ≤
      (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
        ((2 / (ν * ((t - s) / 2))) *
          (‖u s‖ + ‖u t‖) * ‖u s - u t‖) := by
  have hlag : 0 < t - s := sub_pos.mpr hst
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
    ν hν (u s) (u s) (hu s) hlag]
  exact heatFiveEighthGeneratorMoment_heatRegularizedSpectralOutput_sub_le
    ν (t - s) hν hlag (u s) (u t) (hu s) (hu t)

/-- The five-eighth moment passes through a Bochner integral. -/
theorem heatFiveEighthGeneratorMoment_integral_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (f : α → WeightedLatticeBanach) (hf : IntegrableOn f S μ)
    (hfsum : ∀ᵐ s ∂μ.restrict S, Summable fun k : LatticeMode =>
      quarterFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖))
    (hfM : IntegrableOn
      (fun s => heatFiveEighthGeneratorMoment (f s)) S μ) :
    heatFiveEighthGeneratorMoment (∫ s in S, f s ∂μ) ≤
      ∫ s in S, heatFiveEighthGeneratorMoment (f s) ∂μ := by
  unfold heatFiveEighthGeneratorMoment
  apply Real.tsum_le_of_sum_le
  · intro k
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · intro F
    have hcoord (k : LatticeMode) :
        (∫ s in S, f s ∂μ) k = ∫ s in S, f s k ∂μ := by
      change (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k)
          (∫ s in S, f s ∂μ) = _
      exact (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integral_comp_comm hf |>.symm
    have hcoordInt (k : LatticeMode) : IntegrableOn (fun s => f s k) S μ :=
      (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integrable_comp hf
    have htermInt (k : LatticeMode) : IntegrableOn
        (fun s => quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖)) S μ :=
      ((hcoordInt k).norm.const_mul _).const_mul _
    calc
      ∑ k ∈ F, quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            ‖(∫ s in S, f s ∂μ) k‖) ≤
        ∑ k ∈ F, quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            (∫ s in S, ‖f s k‖ ∂μ)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [hcoord k]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
            (norm_nonneg _)) (Real.sqrt_nonneg _)
      _ = ∫ s in S, ∑ k ∈ F, quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖) ∂μ := by
        rw [integral_finsetSum F (fun k _ => htermInt k)]
        simp_rw [integral_const_mul]
      _ ≤ ∫ s in S, heatFiveEighthGeneratorMoment (f s) ∂μ := by
        apply integral_mono_ae
        · exact integrable_finsetSum F fun k _ => htermInt k
        · exact hfM
        · filter_upwards [hfsum] with s hs
          unfold heatFiveEighthGeneratorMoment
          exact hs.sum_le_tsum F fun k _ => mul_nonneg (Real.sqrt_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Finite five-eighth moment sums admit the same Bochner bound; this is the
monotone input used to prove summability of the integrated history. -/
theorem sum_heatFiveEighthGeneratorMoment_integral_le_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    (F : Finset LatticeMode) (f : α → WeightedLatticeBanach)
    (hf : IntegrableOn f S μ)
    (hfsum : ∀ᵐ s ∂μ.restrict S, Summable fun k : LatticeMode =>
      quarterFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖))
    (hfM : IntegrableOn
      (fun s => heatFiveEighthGeneratorMoment (f s)) S μ) :
    (∑ k ∈ F, quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ *
        ‖(∫ s in S, f s ∂μ) k‖)) ≤
      ∫ s in S, heatFiveEighthGeneratorMoment (f s) ∂μ := by
  have hcoord (k : LatticeMode) :
      (∫ s in S, f s ∂μ) k = ∫ s in S, f s k ∂μ := by
    change (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k)
        (∫ s in S, f s ∂μ) = _
    exact (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integral_comp_comm hf |>.symm
  have hcoordInt (k : LatticeMode) : IntegrableOn (fun s => f s k) S μ :=
    (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integrable_comp hf
  have htermInt (k : LatticeMode) : IntegrableOn
      (fun s => quarterFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖)) S μ :=
    ((hcoordInt k).norm.const_mul _).const_mul _
  calc
    ∑ k ∈ F, quarterFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ *
          ‖(∫ s in S, f s ∂μ) k‖) ≤
      ∑ k ∈ F, quarterFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ *
          (∫ s in S, ‖f s k‖ ∂μ)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [hcoord k]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (norm_nonneg _)) (Real.sqrt_nonneg _)
    _ = ∫ s in S, ∑ k ∈ F, quarterFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖) ∂μ := by
      rw [integral_finsetSum F (fun k _ => htermInt k)]
      simp_rw [integral_const_mul]
    _ ≤ ∫ s in S, heatFiveEighthGeneratorMoment (f s) ∂μ := by
      apply integral_mono_ae
      · exact integrable_finsetSum F fun k _ => htermInt k
      · exact hfM
      · filter_upwards [hfsum] with s hs
        unfold heatFiveEighthGeneratorMoment
        exact hs.sum_le_tsum F fun k _ => mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The constant multiplying the integrable `δ^(-7/8)` endpoint density. -/
def fiveEighthDiniConstant (ν R C : ℝ) : ℝ :=
  (8 / ν) * R * C *
    (Real.sqrt (Real.sqrt (Real.sqrt (ν / 2))))⁻¹

theorem inv_mul_eighthRoot_eq_rpow_neg_seven_eighths
    {δ : ℝ} (hδ : 0 < δ) :
    δ⁻¹ * Real.sqrt (Real.sqrt (Real.sqrt δ)) =
      δ ^ (-(7 / 8 : ℝ)) := by
  rw [← Real.rpow_neg_one]
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hδ.le, ← Real.rpow_mul hδ.le,
    ← Real.rpow_add hδ]
  norm_num

/-- Exact reduction of the five-eighth cancellation density to the
integrable power `δ^(-7/8)`. -/
theorem fiveEighth_cancellation_density_eq
    {ν R C δ : ℝ} (hν : 0 < ν) (hδ : 0 < δ) :
    (Real.sqrt (Real.sqrt (Real.sqrt (ν * (δ / 2)))))⁻¹ *
        ((2 / (ν * (δ / 2))) * (2 * R) *
          (C * Real.sqrt (Real.sqrt δ))) =
      fiveEighthDiniConstant ν R C * δ ^ (-(7 / 8 : ℝ)) := by
  have hν2 : 0 < ν / 2 := by positivity
  have hrootSplit :
      Real.sqrt (Real.sqrt (Real.sqrt ((ν / 2) * δ))) =
        Real.sqrt (Real.sqrt (Real.sqrt (ν / 2))) *
          Real.sqrt (Real.sqrt (Real.sqrt δ)) := by
    rw [Real.sqrt_mul hν2.le,
      Real.sqrt_mul (Real.sqrt_nonneg (ν / 2)),
      Real.sqrt_mul (Real.sqrt_nonneg (Real.sqrt (ν / 2)))]
  have hrootδ : 0 < Real.sqrt (Real.sqrt (Real.sqrt δ)) := by positivity
  have hsqrtδ : Real.sqrt (Real.sqrt δ) =
      Real.sqrt (Real.sqrt (Real.sqrt δ)) *
        Real.sqrt (Real.sqrt (Real.sqrt δ)) := by
    rw [Real.mul_self_sqrt (Real.sqrt_nonneg (Real.sqrt δ))]
  have hinvrootδ :
      (Real.sqrt (Real.sqrt (Real.sqrt δ)))⁻¹ *
          Real.sqrt (Real.sqrt δ) =
        Real.sqrt (Real.sqrt (Real.sqrt δ)) := by
    calc
      (Real.sqrt (Real.sqrt (Real.sqrt δ)))⁻¹ *
          Real.sqrt (Real.sqrt δ) =
        (Real.sqrt (Real.sqrt (Real.sqrt δ)))⁻¹ *
          (Real.sqrt (Real.sqrt (Real.sqrt δ)) *
            Real.sqrt (Real.sqrt (Real.sqrt δ))) :=
          congrArg (fun x =>
            (Real.sqrt (Real.sqrt (Real.sqrt δ)))⁻¹ * x) hsqrtδ
      _ = Real.sqrt (Real.sqrt (Real.sqrt δ)) := by field_simp
  have hpow := inv_mul_eighthRoot_eq_rpow_neg_seven_eighths hδ
  rw [show ν * (δ / 2) = (ν / 2) * δ by ring, hrootSplit,
    mul_inv_rev, show 2 / ((ν / 2) * δ) = (4 / ν) * δ⁻¹ by
      field_simp [hν.ne', hδ.ne']; ring]
  calc
    (Real.sqrt (Real.sqrt (Real.sqrt δ)))⁻¹ *
          (Real.sqrt (Real.sqrt (Real.sqrt (ν / 2))))⁻¹ *
            ((4 / ν) * δ⁻¹ * (2 * R) *
              (C * Real.sqrt (Real.sqrt δ))) =
        ((8 / ν) * R * C *
          (Real.sqrt (Real.sqrt (Real.sqrt (ν / 2))))⁻¹) *
            (δ⁻¹ *
              ((Real.sqrt (Real.sqrt (Real.sqrt δ)))⁻¹ *
                Real.sqrt (Real.sqrt δ))) := by ring
    _ = ((8 / ν) * R * C *
          (Real.sqrt (Real.sqrt (Real.sqrt (ν / 2))))⁻¹) *
            (δ⁻¹ * Real.sqrt (Real.sqrt (Real.sqrt δ))) := by
      rw [hinvrootδ]
    _ = fiveEighthDiniConstant ν R C * δ ^ (-(7 / 8 : ℝ)) := by
      rw [hpow]
      rfl

/-- Exact integral of the five-eighth bootstrap endpoint kernel. -/
theorem integral_rpow_neg_seven_eighths_time_gap
    {b t : ℝ} (hbt : b ≤ t) :
    (∫ s in Ioc b t, (t - s) ^ (-(7 / 8 : ℝ))) =
      8 * (t - b) ^ (1 / 8 : ℝ) := by
  rw [← intervalIntegral.integral_of_le hbt,
    intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => x ^ (-(7 / 8 : ℝ))) t]
  simp only [sub_self]
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [show -(7 / 8 : ℝ) + 1 = 1 / 8 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 8 : ℝ) ≠ 0)]
  ring

set_option maxHeartbeats 1000000 in
/-- The actual quarter-Hölder terminal window makes the five-eighth-generator
moment of the cancelling nonlinear history integrable. -/
theorem intervalIntegrable_fiveEighthMoment_path_sub_constant_of_actualMild
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R b t : ℝ} (hR : 0 ≤ R) (hb : 0 < b) (hbt : b ≤ t)
    (hunit : t - b ≤ 1) (hinterior : Real.sqrt (t - b) < b)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    IntervalIntegrable
      (fun s => heatFiveEighthGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s -
          criticalMildPathIntegrand ν hν (fun _ => u t) (fun _ => hu t) t s))
      volume b t := by
  let f : ℝ → WeightedLatticeBanach := fun s =>
    criticalMildPathIntegrand ν hν u hu t s -
      criticalMildPathIntegrand ν hν (fun _ => u t) (fun _ => hu t) t s
  let C : ℝ := interiorQuarterWindowConstant ν u₀ R b t
  let K : ℝ := fiveEighthDiniConstant ν R C
  have hC : 0 ≤ C := by
    dsimp [C, interiorQuarterWindowConstant]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K, fiveEighthDiniConstant]
    positivity
  have hpow : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-(7 / 8 : ℝ))) volume b t := by
    have hzero := intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := t - b) (by norm_num : (-1 : ℝ) < -(7 / 8 : ℝ))
    simpa using (hzero.comp_sub_left t).symm
  have hmajor : IntervalIntegrable
      (fun s : ℝ => K * (t - s) ^ (-(7 / 8 : ℝ))) volume b t :=
    hpow.const_mul K
  have hconst : Continuous (fun _ : ℝ => u t) := continuous_const
  have hmeas : Measurable
      (fun s => heatFiveEighthGeneratorMoment (f s)) := by
    unfold heatFiveEighthGeneratorMoment
    exact Measurable.tsum fun k => measurable_const.mul
      (measurable_const.mul
        (((stronglyMeasurable_criticalMildPathIntegrand_apply
            ν hν u huc hu t k).sub
          (stronglyMeasurable_criticalMildPathIntegrand_apply
            ν hν (fun _ => u t) hconst (fun _ => hu t) t k)).norm.measurable))
  have hmod := norm_mildTrajectory_sub_le_quarter_on_terminalWindow
    ν hν u₀ hu₀ u huc hu hR hb hbt hunit hinterior huR hmild
  apply hmajor.mono_fun' hmeas.aestronglyMeasurable
  rw [Set.uIoc_of_le hbt]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs,
    abs_of_nonneg (heatFiveEighthGeneratorMoment_nonneg _)]
  by_cases hsteq : s = t
  · subst s
    dsimp [f]
    simp [criticalMildPathIntegrand,
      positiveTimeHeatRegularizedSpectralOutput,
      heatFiveEighthGeneratorMoment]
  have hst : s < t := lt_of_le_of_ne hs.2 hsteq
  have hgap : 0 < t - s := sub_pos.mpr hst
  have hs0 : 0 < s := hb.trans hs.1
  have hus : ‖u s‖ ≤ R := huR s ⟨hs0, hs.2⟩
  have hut : ‖u t‖ ≤ R := huR t ⟨hs0.trans hst, le_rfl⟩
  have hpoint := hmod s ⟨hs.1.le, hs.2⟩
  have hcanc : heatFiveEighthGeneratorMoment (f s) ≤
      (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
        ((2 / (ν * ((t - s) / 2))) *
          (‖u s‖ + ‖u t‖) * ‖u s - u t‖) := by
    dsimp [f]
    unfold criticalMildPathIntegrand
    rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
        ν hν (u s) (u s) (hu s) hgap,
      positiveTimeHeatRegularizedSpectralOutput_of_pos
        ν hν (u t) (u t) (hu t) hgap]
    exact heatFiveEighthGeneratorMoment_heatRegularizedSpectralOutput_sub_le
      ν (t - s) hν hgap (u s) (u t) (hu s) (hu t)
  refine hcanc.trans ?_
  calc
    (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
        ((2 / (ν * ((t - s) / 2))) *
          (‖u s‖ + ‖u t‖) * ‖u s - u t‖) ≤
      (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
        ((2 / (ν * ((t - s) / 2))) * (2 * R) *
          (C * Real.sqrt (Real.sqrt (t - s)))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hpoint
        (norm_nonneg _) (mul_nonneg (by positivity) (by positivity))
    _ = K * (t - s) ^ (-(7 / 8 : ℝ)) := by
      dsimp [K, C]
      exact fiveEighth_cancellation_density_eq hν hgap

/-! ## The frozen endpoint source at the next moment -/

/-- A product-space majorant that allocates the output quarter-frequency to
the two half-generator inputs. -/
def quarterFrozenOutputPairMajorant
    (u v : WeightedLatticeBanach) (ij : LatticeMode × LatticeMode) : ℝ :=
  (1 + ‖complexFrequency (latticeFrequency ij.1)‖ +
      ‖complexFrequency (latticeFrequency ij.2)‖) *
    ‖u ij.1‖ * ‖v ij.2‖

set_option maxHeartbeats 800000 in
theorem summable_quarterFrozenOutputPairMajorant
    (u v : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖)
    (hv : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖v k‖) :
    Summable (quarterFrozenOutputPairMajorant u v) := by
  have hu0 : Summable fun k : LatticeMode => ‖u k‖ := by simpa using u.2.summable
  have hv0 : Summable fun k : LatticeMode => ‖v k‖ := by simpa using v.2.summable
  have hbase : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u ij.1‖ * ‖v ij.2‖ :=
    hu0.mul_of_nonneg hv0 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hleft : Summable fun ij : LatticeMode × LatticeMode =>
      (‖complexFrequency (latticeFrequency ij.1)‖ * ‖u ij.1‖) * ‖v ij.2‖ :=
    hu.mul_of_nonneg hv0
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun _ => norm_nonneg _)
  have hright : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u ij.1‖ *
        (‖complexFrequency (latticeFrequency ij.2)‖ * ‖v ij.2‖) :=
    hu0.mul_of_nonneg hv (fun _ => norm_nonneg _)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (hbase.add hleft |>.add hright).congr (fun ij => by
    unfold quarterFrozenOutputPairMajorant
    ring)

theorem quarterFrequencyWeight_output_le_pairMajorant
    (ij : LatticeMode × LatticeMode) :
    quarterFrequencyWeight (ij.1 + ij.2) ≤
      1 + ‖complexFrequency (latticeFrequency ij.1)‖ +
        ‖complexFrequency (latticeFrequency ij.2)‖ := by
  let q : ℝ := ‖complexFrequency (latticeFrequency (ij.1 + ij.2))‖
  have hq : 0 ≤ q := norm_nonneg _
  have hquarter : Real.sqrt (Real.sqrt q) ≤ 1 + q := by
    by_cases hq1 : q ≤ 1
    · exact (Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr hq1)).trans
        (le_add_of_nonneg_right hq)
    · have hq1' : 1 ≤ q := le_of_not_ge hq1
      have hsqrt : Real.sqrt q ≤ q := (Real.sqrt_le_iff).2 ⟨hq, by nlinarith⟩
      have hfourth : Real.sqrt (Real.sqrt q) ≤ Real.sqrt q :=
        (Real.sqrt_le_iff).2 ⟨Real.sqrt_nonneg q, by
          rw [Real.sq_sqrt hq]
          exact hsqrt⟩
      exact (hfourth.trans hsqrt).trans (le_add_of_nonneg_left zero_le_one)
  have htri : q ≤ ‖complexFrequency (latticeFrequency ij.1)‖ +
      ‖complexFrequency (latticeFrequency ij.2)‖ := by
    dsimp [q]
    rw [complexFrequency_latticeFrequency_add]
    exact norm_add_le _ _
  dsimp [quarterFrequencyWeight]
  exact hquarter.trans (by linarith)

/-- The quarter-weighted frozen fiber masses are summable when both endpoint
inputs have the already-proved half-generator moment. -/
theorem summable_quarterWeight_mul_frozenOutputFiberMass
    (u v : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖)
    (hv : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖v k‖) :
    Summable fun k : LatticeMode =>
      quarterFrequencyWeight k * frozenOutputFiberMass u v k := by
  have hpair : Summable fun ij : LatticeMode × LatticeMode =>
      quarterFrequencyWeight (latticeOutputMode ij) * frozenOutputPairMass u v ij := by
    apply (summable_quarterFrozenOutputPairMajorant u v hu hv).of_nonneg_of_le
    · intro ij
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · intro ij
      unfold latticeOutputMode frozenOutputPairMass quarterFrozenOutputPairMajorant
      exact (mul_le_mul_of_nonneg_right
        (quarterFrequencyWeight_output_le_pairMajorant ij)
        (mul_nonneg (norm_nonneg (u ij.1)) (norm_nonneg (v ij.2)))).trans_eq
          (by ring)
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      quarterFrequencyWeight x.1 * frozenOutputPairMass u v x.2.1) := by
    have hsigma0 := latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
    exact hsigma0.congr (fun x => by
      change quarterFrequencyWeight (latticeOutputMode x.2.1) *
          frozenOutputPairMass u v x.2.1 =
        quarterFrequencyWeight x.1 * frozenOutputPairMass u v x.2.1
      have hx : latticeOutputMode x.2.1 = x.1 := by
        have hx' := x.2.2
        change latticeOutputMode x.2.1 = x.1 at hx'
        exact hx'
      rw [hx])
  have hfiber := hsigma.sigma
  rw [show (fun k : LatticeMode =>
      quarterFrequencyWeight k * frozenOutputFiberMass u v k) =
      fun k => ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        quarterFrequencyWeight k * frozenOutputPairMass u v ij.1 by
    funext k
    unfold frozenOutputFiberMass
    rw [tsum_mul_left]]
  exact hfiber

/-- The exact frozen nonlinear endpoint integral gains the strict next
five-eighth-generator moment from the endpoint half-generator moment. -/
theorem summable_fiveEighthMoment_frozenOutputIntegral
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (huHalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖)
    (hvHalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖v k‖) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ *
        ‖positiveTimeHeatRegularizedSpectralOutputIntegral
          ν T hν hT u v hu k‖) := by
  have hright : Summable fun k : LatticeMode =>
      ν⁻¹ * (quarterFrequencyWeight k * frozenOutputFiberMass u v k) :=
    (summable_quarterWeight_mul_frozenOutputFiberMass u v huHalf hvHalf).mul_left _
  exact hright.of_nonneg_of_le
    (fun k => mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun k => by
      calc
        quarterFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ *
              ‖positiveTimeHeatRegularizedSpectralOutputIntegral
                ν T hν hT u v hu k‖) ≤
          quarterFrequencyWeight k *
            (ν⁻¹ * frozenOutputFiberMass u v k) :=
          mul_le_mul_of_nonneg_left
            (frequency_mul_norm_frozenOutputIntegral_apply_le
              ν T hν hT u v hu k) (Real.sqrt_nonneg _)
        _ = ν⁻¹ *
            (quarterFrequencyWeight k * frozenOutputFiberMass u v k) := by ring)

set_option maxHeartbeats 1200000 in
/-- **First genuine higher-moment bootstrap for the actual raw mild
trajectory.** At every positive observation time the full nonlinear Duhamel
term gains the strict moment `sum |k|^(5/4) ||D_k||`. The result uses the
derived quarter-Hölder endpoint cancellation and the already-proved
half-generator moment of the frozen endpoint; it assumes no higher-moment
bundle. -/
theorem criticalMildDuhamel_fullPositiveTime_fiveEighthGenerator
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ *
        ‖criticalMildDuhamel ν hν u hu t k‖) := by
  obtain ⟨b, hb, hbt, hunit, hinterior⟩ := exists_admissible_terminalWindow ht
  let cpath : ℝ → WeightedLatticeBanach := fun _ => u t
  let hucpath : ∀ s, LatticeDivergenceFree (cpath s) := fun _ => hu t
  let f : ℝ → WeightedLatticeBanach := fun s =>
    criticalMildPathIntegrand ν hν u hu t s -
      criticalMildPathIntegrand ν hν cpath hucpath t s
  let d : WeightedLatticeBanach := ∫ s in Ioc 0 t, f s
  let c : WeightedLatticeBanach :=
    positiveTimeHeatRegularizedSpectralOutputIntegral
      ν t hν ht.le (u t) (u t) (hu t)
  have huInt := integrableOn_criticalMildPathIntegrand
    ν hν u huc hu hR ht.le huR
  have hcInt : IntegrableOn
      (criticalMildPathIntegrand ν hν cpath hucpath t) (Ioc 0 t) volume := by
    apply integrableOn_criticalMildPathIntegrand
      ν hν cpath continuous_const hucpath (norm_nonneg (u t)) ht.le
    intro s hs
    exact le_rfl
  have hfInt : IntegrableOn f (Ioc 0 t) volume := huInt.sub hcInt
  have hfMomentInterval : IntervalIntegrable
      (fun s => heatFiveEighthGeneratorMoment (f s)) volume b t := by
    dsimp [f, cpath, hucpath]
    exact intervalIntegrable_fiveEighthMoment_path_sub_constant_of_actualMild
      ν hν u₀ hu₀ u huc hu hR hb hbt.le hunit hinterior huR hmild
  have hfMomentPrefix : IntervalIntegrable
      (fun s => heatFiveEighthGeneratorMoment (f s)) volume 0 b := by
    have hgap : b < t := hbt
    let C : ℝ := (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - b) / 2)))))⁻¹ *
      ((2 / (ν * ((t - b) / 2))) * (2 * R) * (2 * R))
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc 0 b) volume :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hconstPath : Continuous cpath := continuous_const
    have hmeas : Measurable
        (fun s => heatFiveEighthGeneratorMoment (f s)) := by
      unfold heatFiveEighthGeneratorMoment
      exact Measurable.tsum fun k => measurable_const.mul
        (measurable_const.mul
          (((stronglyMeasurable_criticalMildPathIntegrand_apply
              ν hν u huc hu t k).sub
            (stronglyMeasurable_criticalMildPathIntegrand_apply
              ν hν cpath hconstPath hucpath t k)).norm.measurable))
    have hp : IntegrableOn
        (fun s => heatFiveEighthGeneratorMoment (f s)) (Ioc 0 b) volume := by
      apply hconst.mono' hmeas.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs,
        abs_of_nonneg (heatFiveEighthGeneratorMoment_nonneg _)]
      have hst : s < t := hs.2.trans_lt hgap
      have hs0 : 0 < s := hs.1
      have hus : ‖u s‖ ≤ R := huR s ⟨hs0, hst.le⟩
      have hut : ‖u t‖ ≤ R := huR t ⟨ht, le_rfl⟩
      have hcanc : heatFiveEighthGeneratorMoment (f s) ≤
          (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
            ((2 / (ν * ((t - s) / 2))) *
              (‖u s‖ + ‖u t‖) * ‖u s - u t‖) := by
        dsimp [f, cpath, hucpath]
        unfold criticalMildPathIntegrand
        rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
            ν hν (u s) (u s) (hu s) (sub_pos.mpr hst),
          positiveTimeHeatRegularizedSpectralOutput_of_pos
            ν hν (u t) (u t) (hu t) (sub_pos.mpr hst)]
        exact heatFiveEighthGeneratorMoment_heatRegularizedSpectralOutput_sub_le
          ν (t - s) hν (sub_pos.mpr hst) (u s) (u t) (hu s) (hu t)
      refine hcanc.trans ?_
      have hcoef :
          (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
              (2 / (ν * ((t - s) / 2))) ≤
            (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - b) / 2)))))⁻¹ *
              (2 / (ν * ((t - b) / 2))) := by
        have harg : ν * ((t - b) / 2) ≤ ν * ((t - s) / 2) := by
          exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) hν.le
        have hroot : Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - b) / 2)))) ≤
            Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))) := by
          exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt harg))
        have hinvroot :
            (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ ≤
              (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - b) / 2)))))⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hroot
        have hinv : (ν * ((t - s) / 2))⁻¹ ≤
            (ν * ((t - b) / 2))⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le (by positivity) harg
        have htwo : 2 / (ν * ((t - s) / 2)) ≤
            2 / (ν * ((t - b) / 2)) := by
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
        exact mul_le_mul hinvroot htwo (by positivity) (by positivity)
      dsimp [C]
      calc
        (Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
            ((2 / (ν * ((t - s) / 2))) *
              (‖u s‖ + ‖u t‖) * ‖u s - u t‖) =
          ((Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
            (2 / (ν * ((t - s) / 2)))) *
              (‖u s‖ + ‖u t‖) * ‖u s - u t‖ := by ring
        _ ≤ ((Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - b) / 2)))))⁻¹ *
            (2 / (ν * ((t - b) / 2)))) * (2 * R) * (2 * R) := by
          calc
            ((Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - s) / 2)))))⁻¹ *
                (2 / (ν * ((t - s) / 2)))) *
                  (‖u s‖ + ‖u t‖) * ‖u s - u t‖ ≤
              ((Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - b) / 2)))))⁻¹ *
                (2 / (ν * ((t - b) / 2)))) *
                  (‖u s‖ + ‖u t‖) * ‖u s - u t‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoef
                  (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)
            _ ≤ ((Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - b) / 2)))))⁻¹ *
                (2 / (ν * ((t - b) / 2)))) * (2 * R) * ‖u s - u t‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (norm_nonneg _)
            _ ≤ ((Real.sqrt (Real.sqrt (Real.sqrt (ν * ((t - b) / 2)))))⁻¹ *
                (2 / (ν * ((t - b) / 2)))) * (2 * R) * (2 * R) :=
              mul_le_mul_of_nonneg_left
                (norm_sub_le (u s) (u t) |>.trans (by linarith))
                (mul_nonneg (by positivity) (by positivity))
        _ = C := by dsimp [C]; ring
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr hp
  have hfMoment : IntegrableOn
      (fun s => heatFiveEighthGeneratorMoment (f s)) (Ioc 0 t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp
      (hfMomentPrefix.trans hfMomentInterval)
  have hfSum : ∀ᵐ s ∂volume.restrict (Ioc 0 t), Summable fun k : LatticeMode =>
      quarterFrequencyWeight k *
        (‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    by_cases hst : s < t
    · have hevol := summable_fiveEighthGeneratorMoment_heatRegularizedSpectralOutput
        ν (t - s) hν (sub_pos.mpr hst) (u s) (u s) (hu s)
      have hconst := summable_fiveEighthGeneratorMoment_heatRegularizedSpectralOutput
        ν (t - s) hν (sub_pos.mpr hst) (u t) (u t) (hu t)
      dsimp [f, cpath, hucpath]
      unfold criticalMildPathIntegrand
      rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
          ν hν (u s) (u s) (hu s) (sub_pos.mpr hst),
        positiveTimeHeatRegularizedSpectralOutput_of_pos
          ν hν (u t) (u t) (hu t) (sub_pos.mpr hst)]
      exact summable_fiveEighthGeneratorMoment_sub _ _ hevol hconst
    · have hst' : s = t := le_antisymm hs.2 (not_lt.mp hst)
      subst s
      simp [f, criticalMildPathIntegrand,
        positiveTimeHeatRegularizedSpectralOutput, quarterFrequencyWeight]
  have hdSum : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖d k‖) := by
    apply summable_of_sum_le
    · intro k
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · intro F
      exact sum_heatFiveEighthGeneratorMoment_integral_le_integral
        F f hfInt hfSum hfMoment
  have hutHalf := (mildTrajectory_fullPositiveTime_halfGenerator
    ν hν u₀ hu₀ u huc hu hR ht huR hmild).1
  have hcSum : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖c k‖) := by
    dsimp [c]
    exact summable_fiveEighthMoment_frozenOutputIntegral
      ν t hν ht.le (u t) (u t) (hu t) hutHalf hutHalf
  have hdecomp : criticalMildDuhamel ν hν u hu t = d + c := by
    have hsub : d = criticalMildDuhamel ν hν u hu t -
        criticalMildDuhamel ν hν cpath hucpath t := by
      dsimp [d, f]
      rw [integral_sub huInt hcInt]
      rfl
    have hconst : criticalMildDuhamel ν hν cpath hucpath t = c := by
      dsimp [cpath, hucpath, c]
      exact criticalMildDuhamel_constant_eq_frozenOutputIntegral
        ν t hν ht.le (u t) (hu t)
    rw [hsub, hconst]
    abel
  rw [hdecomp]
  have hright := hdSum.add hcSum
  exact hright.of_nonneg_of_le
    (fun k => mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun k => by
      change quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * ‖d k + c k‖) ≤ _
      calc
        quarterFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * ‖d k + c k‖) ≤
          quarterFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * (‖d k‖ + ‖c k‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
            (Real.sqrt_nonneg _)
        _ = quarterFrequencyWeight k *
              (‖complexFrequency (latticeFrequency k)‖ * ‖d k‖) +
            quarterFrequencyWeight k *
              (‖complexFrequency (latticeFrequency k)‖ * ‖c k‖) := by ring)

/-- A positive linear heat interval creates the strict five-eighth-generator
moment from arbitrary raw carrier data. -/
theorem summable_fiveEighthGeneratorMoment_weightedHeatFlow_of_base
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ *
        ‖weightedHeatFlow ν t hν.le ht.le u k‖) := by
  let a : ℝ := t / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let z := weightedHeatFlow ν a hν.le ha.le u
  have hz : LatticeDivergenceFree z :=
    weightedHeatFlow_divergenceFree ν a hν.le ha.le u
  have hzHalf := summable_halfGeneratorMoment_weightedHeatFlow
    ν a hν ha u hu
  have hs := summable_fiveEighthGeneratorMoment_weightedHeatFlow
    ν a hν ha z hz hzHalf
  have hsemigroup := weightedHeatFlow_semigroup
    ν a a hν.le ha.le ha.le u
  have haa : a + a = t := by dsimp [a]; ring
  have hsemigroup' : weightedHeatFlow ν a hν.le ha.le z =
      weightedHeatFlow ν t hν.le ht.le u := by
    dsimp [z]
    symm
    simpa only [haa] using hsemigroup
  rw [hsemigroup'] at hs
  exact hs

/-- **Actual first higher moment.** Every positive-time value of the raw mild
trajectory lies in the strict five-eighth-generator domain. -/
theorem mildTrajectory_fullPositiveTime_fiveEighthGenerator
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖u t k‖) := by
  have hheat := summable_fiveEighthGeneratorMoment_weightedHeatFlow_of_base
    ν t hν ht u₀ hu₀
  have hduhamel := criticalMildDuhamel_fullPositiveTime_fiveEighthGenerator
    ν hν u₀ hu₀ u huc hu hR ht huR hmild
  have hut := hmild t ⟨ht.le, le_rfl⟩
  rw [hut, criticalMildImage]
  have hright := hheat.add hduhamel
  exact hright.of_nonneg_of_le
    (fun k => mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun k => by
      change quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            ‖weightedHeatFlow ν t hν.le ht.le u₀ k +
              criticalMildDuhamel ν hν u hu t k‖) ≤ _
      calc
        quarterFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ *
              ‖weightedHeatFlow ν t hν.le ht.le u₀ k +
                criticalMildDuhamel ν hν u hu t k‖) ≤
          quarterFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ *
              (‖weightedHeatFlow ν t hν.le ht.le u₀ k‖ +
                ‖criticalMildDuhamel ν hν u hu t k‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _))
            (Real.sqrt_nonneg _)
        _ = _ := by ring)

/-- Removing the native carrier weight converts the strict new raw moment to
decoded spatial order `2 + 1/4`. Physical Fourier meaning still requires the
separate phase/viscosity decoder. -/
theorem summable_decoded_twoAndQuarterSpatialMoments_of_fiveEighth
    (v : WeightedLatticeBanach)
    (hv : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖)) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient v k)) := by
  apply hv.of_nonneg_of_le
  · intro k
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  · intro k
    rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
    have hweight : ‖complexFrequency (latticeFrequency k)‖ ≤
        latticeModeWeight k := by
      unfold latticeModeWeight
      linarith [norm_nonneg (complexFrequency (latticeFrequency k))]
    calc
      quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ ^ 2 *
            complexEuclideanNorm (weightedLatticeCoefficient v k)) =
        quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            (‖complexFrequency (latticeFrequency k)‖ *
              complexEuclideanNorm (weightedLatticeCoefficient v k))) := by ring
      _ ≤ quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            (latticeModeWeight k *
              complexEuclideanNorm (weightedLatticeCoefficient v k))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)) (norm_nonneg _))
          (Real.sqrt_nonneg _)
      _ = quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ *
            latticeWeightedAmplitude (weightedLatticeCoefficient v) k) := rfl
      _ = quarterFrequencyWeight k *
          (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖) :=
        congrArg
          (fun z => quarterFrequencyWeight k *
            (‖complexFrequency (latticeFrequency k)‖ * z))
          (latticeWeightedAmplitude_coefficient v k)

/-- The actual positive-time raw mild value therefore has decoded carrier
spatial summability of order `2 + 1/4`. -/
theorem mildTrajectory_decoded_twoAndQuarterSpatialMoments
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient (u t) k)) :=
  summable_decoded_twoAndQuarterSpatialMoments_of_fiveEighth (u t)
    (mildTrajectory_fullPositiveTime_fiveEighthGenerator
      ν hν u₀ hu₀ u huc hu hR ht huR hmild)

end Navier.Analysis.CriticalMildHigherMomentBootstrap

#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.sqrt_mul_exp_neg_mul_sq_le_inv_fourthRoot
#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.summable_threeQuarterGeneratorMoment_weightedHeatFlow
#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.fourthRoot_mul_exp_neg_mul_sq_le_inv_eighthRoot
#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.intervalIntegrable_fiveEighthMoment_path_sub_constant_of_actualMild
#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.summable_fiveEighthMoment_frozenOutputIntegral
#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.criticalMildDuhamel_fullPositiveTime_fiveEighthGenerator
#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.mildTrajectory_fullPositiveTime_fiveEighthGenerator
#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.summable_decoded_twoAndQuarterSpatialMoments_of_fiveEighth
#print axioms Navier.Analysis.CriticalMildHigherMomentBootstrap.mildTrajectory_decoded_twoAndQuarterSpatialMoments
