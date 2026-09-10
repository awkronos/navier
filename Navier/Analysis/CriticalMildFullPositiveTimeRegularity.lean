import Navier.Analysis.CriticalMildPositiveTimeSmoothing
import Navier.Analysis.CriticalMildInteriorTimeModulus
import Navier.Analysis.PeriodicDynamicCriticalTail

/-!
# Full positive-time graph regularity of the actual critical mild path

The interior quarter-Hölder modulus makes the endpoint Dini cancellation
integrable. The frozen-source resolvent spends each output heat mode exactly
once. Combining the two removes the last terminal-tail premise and puts the
full nonlinear Duhamel term, and hence the actual mild trajectory, in the
half-generator domain at every positive time.

The bounds here are local in the observation time and in the native chart
radius. They do not assert a horizon-uniform critical bound or global
continuation for arbitrary data.

All statements remain on the repository's raw critical mild carrier. The
coefficient bridge below removes the native lattice weight; identifying those
coefficients with a physically normalized velocity is a separate decoder
theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set

namespace Navier.Analysis.CriticalMildFullPositiveTimeRegularity

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.LerayProjection
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildObservationContinuity
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildQuantitativeRestart
open Navier.Analysis.CriticalMildInteriorTimeModulus
open Navier.Analysis.PeriodicDynamicCriticalTail

/-- The exact endpoint Dini density in the frozen-source decomposition. -/
def mildDiniDensity
    (ν t : ℝ) (u : ℝ → WeightedLatticeBanach) (s : ℝ) : ℝ :=
  (2 / (ν * (t - s))) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖

theorem measurable_mildDiniDensity
    (ν t : ℝ) (u : ℝ → WeightedLatticeBanach) (huc : Continuous u) :
    Measurable (mildDiniDensity ν t u) := by
  have hcoef : Measurable (fun s : ℝ => 2 / (ν * (t - s))) :=
    measurable_const.div
      (measurable_const.mul (measurable_const.sub measurable_id))
  have hnormu : Measurable (fun s : ℝ => ‖u s‖) := huc.norm.measurable
  have hdiff : Measurable (fun s : ℝ => ‖u s - u t‖) :=
    (huc.sub continuous_const).norm.measurable
  exact (hcoef.mul (hnormu.add measurable_const)).mul hdiff

/-- Before a strict cutoff the Dini density is integrable by the positive
denominator gap and the native radius bound. -/
theorem intervalIntegrable_mildDiniDensity_prefix
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    {R b t : ℝ} (hR : 0 ≤ R) (hb0 : 0 ≤ b) (hbt : b < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    IntervalIntegrable (mildDiniDensity ν t u) volume 0 b := by
  let C : ℝ := (2 / (ν * (t - b))) * (2 * R) * (2 * R)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc 0 b) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hmeas := measurable_mildDiniDensity ν t u huc
  have hprefix : IntegrableOn (mildDiniDensity ν t u) (Ioc 0 b) volume := by
    apply hconst.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hst : s < t := lt_of_le_of_lt hs.2 hbt
    have hus : ‖u s‖ ≤ R := huR s ⟨hs.1, hst.le⟩
    have hut : ‖u t‖ ≤ R := huR t ⟨lt_of_le_of_lt hb0 hbt, le_rfl⟩
    have hcoef : 0 ≤ 2 / (ν * (t - s)) := by positivity
    have hcoefle : 2 / (ν * (t - s)) ≤ 2 / (ν * (t - b)) := by
      have hden : ν * (t - b) ≤ ν * (t - s) :=
        mul_le_mul_of_nonneg_left (by linarith [hs.2]) hν.le
      have hinv : (ν * (t - s))⁻¹ ≤ (ν * (t - b))⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le
          (mul_pos hν (sub_pos.mpr hbt)) hden
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [mildDiniDensity]
      positivity)]
    dsimp [mildDiniDensity, C]
    calc
      2 / (ν * (t - s)) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖ ≤
          2 / (ν * (t - b)) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoefle
            (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)
      _ ≤ 2 / (ν * (t - b)) * (2 * R) * ‖u s - u t‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (norm_nonneg _)
      _ ≤ 2 / (ν * (t - b)) * (2 * R) * (2 * R) :=
        mul_le_mul_of_nonneg_left
          (norm_sub_le (u s) (u t) |>.trans (by linarith))
          (mul_nonneg (by positivity) (by positivity))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0).mpr hprefix

/-- The actual mild equation supplies the full `[0,t]` Dini input: ordinary
positive-gap control on the prefix and the derived quarter-Hölder estimate on
a nontrivial terminal window. -/
theorem intervalIntegrable_mildDiniDensity_full_of_actualMild
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    IntervalIntegrable (mildDiniDensity ν t u) volume 0 t := by
  obtain ⟨b, hb0, hbt, hterminal, -⟩ :=
    exists_terminalWindow_dini_and_cancellingGraphMoment
      ν hν u₀ hu₀ u huc hu hR ht huR hmild
  have hprefix := intervalIntegrable_mildDiniDensity_prefix
    ν hν u huc hR hb0.le hbt huR
  have hterminal' : IntervalIntegrable (mildDiniDensity ν t u) volume b t := by
    change IntervalIntegrable
      (fun s => (2 / (ν * (t - s))) *
        (‖u s‖ + ‖u t‖) * ‖u s - u t‖) volume b t
    exact hterminal
  exact hprefix.trans hterminal'

/-- Exact integral of the quarter-Hölder Dini majorant on a terminal
window. -/
theorem integral_rpow_neg_three_fourths_time_gap
    {b t : ℝ} (hbt : b ≤ t) :
    (∫ s in Ioc b t, (t - s) ^ (-(3 / 4 : ℝ))) =
      4 * (t - b) ^ (1 / 4 : ℝ) := by
  rw [← intervalIntegral.integral_of_le hbt,
    intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) t]
  simp only [sub_self]
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [show -(3 / 4 : ℝ) + 1 = 1 / 4 by norm_num,
    Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  ring

/-- Explicit full Dini budget obtained by joining the positive-gap prefix to
the quarter-Hölder terminal window. -/
def mildDiniExplicitBudget
    (ν : ℝ) (u₀ : WeightedLatticeBanach) (R b t : ℝ) : ℝ :=
  b * ((2 / (ν * (t - b))) * (2 * R) * (2 * R)) +
    4 * ((4 / ν) * R *
      interiorQuarterWindowConstant ν u₀ R b t) *
        (t - b) ^ (1 / 4 : ℝ)

set_option maxHeartbeats 800000 in
/-- Quantitative form of the derived full Dini estimate. Every term on the
right is an explicit function of viscosity, datum norm, chart radius, the
observation time, and the constructed interior cutoff. -/
theorem integral_mildDiniDensity_le_explicitBudget
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R b t : ℝ} (hR : 0 ≤ R) (hb : 0 < b) (hbt : b < t)
    (hunit : t - b ≤ 1) (hinterior : Real.sqrt (t - b) < b)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    (∫ s in Ioc 0 t, mildDiniDensity ν t u s) ≤
      mildDiniExplicitBudget ν u₀ R b t := by
  let Cp : ℝ := (2 / (ν * (t - b))) * (2 * R) * (2 * R)
  let C : ℝ := interiorQuarterWindowConstant ν u₀ R b t
  let K : ℝ := (4 / ν) * R * C
  have ht : 0 < t := hb.trans hbt
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hC : 0 ≤ C := by
    dsimp [C, interiorQuarterWindowConstant]
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hprefix := intervalIntegrable_mildDiniDensity_prefix
    ν hν u huc hR hb.le hbt huR
  have hprefixOn : IntegrableOn (mildDiniDensity ν t u) (Ioc 0 b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hprefix
  have hprefixConst : IntegrableOn (fun _ : ℝ => Cp) (Ioc 0 b) volume :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hprefixLe : (∫ s in Ioc 0 b, mildDiniDensity ν t u s) ≤ b * Cp := by
    calc
      (∫ s in Ioc 0 b, mildDiniDensity ν t u s) ≤
          ∫ _s in Ioc 0 b, Cp := by
        apply integral_mono_ae hprefixOn hprefixConst
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hst : s < t := lt_of_le_of_lt hs.2 hbt
        have hus : ‖u s‖ ≤ R := huR s ⟨hs.1, hst.le⟩
        have hut : ‖u t‖ ≤ R := huR t ⟨ht, le_rfl⟩
        have hcoef : 0 ≤ 2 / (ν * (t - s)) := by positivity
        have hcoefle : 2 / (ν * (t - s)) ≤ 2 / (ν * (t - b)) := by
          have hden : ν * (t - b) ≤ ν * (t - s) :=
            mul_le_mul_of_nonneg_left (by linarith [hs.2]) hν.le
          have hinv : (ν * (t - s))⁻¹ ≤ (ν * (t - b))⁻¹ := by
            simpa only [one_div] using one_div_le_one_div_of_le
              (mul_pos hν (sub_pos.mpr hbt)) hden
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
        dsimp [mildDiniDensity, Cp]
        calc
          2 / (ν * (t - s)) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖ ≤
              2 / (ν * (t - b)) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoefle
                (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)
          _ ≤ 2 / (ν * (t - b)) * (2 * R) * (2 * R) := by
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
              (norm_sub_le (u s) (u t) |>.trans (by linarith))
              (norm_nonneg _)
              (mul_nonneg (by positivity) (by positivity))
      _ = b * Cp := by simp [hb.le]
  have hterminalPair :=
    intervalIntegrable_dini_and_cancellingGraphMoment_of_actualMild
      ν hν u₀ hu₀ u huc hu hR hb hbt.le hunit hinterior huR hmild
  have hterminal : IntervalIntegrable (mildDiniDensity ν t u) volume b t := by
    change IntervalIntegrable
      (fun s => (2 / (ν * (t - s))) *
        (‖u s‖ + ‖u t‖) * ‖u s - u t‖) volume b t
    exact hterminalPair.1
  have hterminalOn : IntegrableOn (mildDiniDensity ν t u) (Ioc b t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hbt.le).mp hterminal
  have hpow : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) volume b t := by
    have hzero := intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := t - b) (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))
    simpa using (hzero.comp_sub_left t).symm
  have hmajor : IntervalIntegrable
      (fun s : ℝ => K * (t - s) ^ (-(3 / 4 : ℝ))) volume b t :=
    hpow.const_mul K
  have hmajorOn : IntegrableOn
      (fun s : ℝ => K * (t - s) ^ (-(3 / 4 : ℝ))) (Ioc b t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hbt.le).mp hmajor
  have hmod := norm_mildTrajectory_sub_le_quarter_on_terminalWindow
    ν hν u₀ hu₀ u huc hu hR hb hbt.le hunit hinterior huR hmild
  have hterminalLe : (∫ s in Ioc b t, mildDiniDensity ν t u s) ≤
      4 * K * (t - b) ^ (1 / 4 : ℝ) := by
    calc
      (∫ s in Ioc b t, mildDiniDensity ν t u s) ≤
          ∫ s in Ioc b t, K * (t - s) ^ (-(3 / 4 : ℝ)) := by
        apply integral_mono_ae hterminalOn hmajorOn
        have hne : ∀ᵐ s : ℝ ∂volume.restrict (Ioc b t), s ≠ t := by
          rw [ae_iff]
          simp
        filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with s hs hstne
        have hst : s < t := lt_of_le_of_ne hs.2 hstne
        have hgap : 0 < t - s := sub_pos.mpr hst
        have hs0 : 0 < s := hb.trans hs.1
        have hus : ‖u s‖ ≤ R := huR s ⟨hs0, hs.2⟩
        have hut : ‖u t‖ ≤ R := huR t ⟨ht, le_rfl⟩
        have hcoef : 0 ≤ 2 / (ν * (t - s)) := by positivity
        have hpoint := hmod s ⟨hs.1.le, hs.2⟩
        dsimp [mildDiniDensity, K, C]
        calc
          2 / (ν * (t - s)) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖ ≤
              2 / (ν * (t - s)) * (2 * R) *
                (interiorQuarterWindowConstant ν u₀ R b t *
                  Real.sqrt (Real.sqrt (t - s))) :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left (by linarith) hcoef) hpoint
              (norm_nonneg _)
              (mul_nonneg hcoef (by positivity))
          _ = (4 / ν * R * interiorQuarterWindowConstant ν u₀ R b t) *
              (t - s) ^ (-(3 / 4 : ℝ)) := by
            rw [show 2 / (ν * (t - s)) = (2 / ν) * (t - s)⁻¹ by
              field_simp [hν.ne', ne_of_gt hgap]]
            calc
              2 / ν * (t - s)⁻¹ * (2 * R) *
                  (interiorQuarterWindowConstant ν u₀ R b t *
                    Real.sqrt (Real.sqrt (t - s))) =
                (4 / ν * R * interiorQuarterWindowConstant ν u₀ R b t) *
                  ((t - s)⁻¹ * Real.sqrt (Real.sqrt (t - s))) := by ring
              _ = _ := by
                rw [inv_mul_sqrt_sqrt_eq_rpow_neg_three_fourths hgap]
      _ = 4 * K * (t - b) ^ (1 / 4 : ℝ) := by
        rw [integral_const_mul,
          integral_rpow_neg_three_fourths_time_gap hbt.le]
        ring
  rw [← intervalIntegral.integral_of_le ht.le,
    ← intervalIntegral.integral_add_adjacent_intervals hprefix hterminal,
    intervalIntegral.integral_of_le hb.le,
    intervalIntegral.integral_of_le hbt.le]
  exact (add_le_add hprefixLe hterminalLe).trans_eq (by
    dsimp [mildDiniExplicitBudget, Cp, K])

/-- **Full positive-time nonlinear smoothing.** The actual Duhamel term lies
in the half-generator domain at every positive time, without a terminal-tail,
modulus, or graph-domain premise. -/
theorem criticalMildDuhamel_fullPositiveTime_graph
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    (Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ *
        ‖criticalMildDuhamel ν hν u hu t k‖) ∧
      heatHalfGeneratorMoment (criticalMildDuhamel ν hν u hu t) ≤
        (∫ s in Ioc 0 t, mildDiniDensity ν t u s) + ν⁻¹ * ‖u t‖ ^ 2 := by
  have hDini := intervalIntegrable_mildDiniDensity_full_of_actualMild
    ν hν u₀ hu₀ u huc hu hR ht huR hmild
  simpa [mildDiniDensity] using
    criticalMildDuhamel_graph_and_moment_le_of_dini
      ν hν u huc hu hR ht.le huR hDini

/-- Quantitative full positive-time nonlinear smoothing. The cutoff is
constructed from the observation time, and the graph bound contains only the
viscosity, datum, chart radius, observation time, and that explicit cutoff. -/
theorem exists_criticalMildDuhamel_fullPositiveTime_graph_with_explicitBound
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    ∃ b : ℝ, 0 < b ∧ b < t ∧ t - b ≤ 1 ∧ Real.sqrt (t - b) < b ∧
      (Summable fun k : LatticeMode =>
        ‖complexFrequency (latticeFrequency k)‖ *
          ‖criticalMildDuhamel ν hν u hu t k‖) ∧
      heatHalfGeneratorMoment (criticalMildDuhamel ν hν u hu t) ≤
        mildDiniExplicitBudget ν u₀ R b t + ν⁻¹ * R ^ 2 := by
  obtain ⟨b, hb, hbt, hunit, hinterior⟩ := exists_admissible_terminalWindow ht
  have hgraph := criticalMildDuhamel_fullPositiveTime_graph
    ν hν u₀ hu₀ u huc hu hR ht huR hmild
  have hbudget := integral_mildDiniDensity_le_explicitBudget
    ν hν u₀ hu₀ u huc hu hR hb hbt hunit hinterior huR hmild
  have hut : ‖u t‖ ≤ R := huR t ⟨ht, le_rfl⟩
  have hsquare : ‖u t‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).2 hut
  refine ⟨b, hb, hbt, hunit, hinterior, hgraph.1, hgraph.2.trans ?_⟩
  exact add_le_add hbudget
    (mul_le_mul_of_nonneg_left hsquare (inv_nonneg.mpr hν.le))

/-- Full positive-time graph membership of the actual mild trajectory. -/
theorem mildTrajectory_fullPositiveTime_halfGenerator
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    (Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u t k‖) ∧
      heatHalfGeneratorMoment (u t) ≤
        (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
          (∫ s in Ioc 0 t, mildDiniDensity ν t u s) + ν⁻¹ * ‖u t‖ ^ 2 := by
  have hnonlinear := criticalMildDuhamel_fullPositiveTime_graph
    ν hν u₀ hu₀ u huc hu hR ht huR hmild
  have hheat := summable_halfGeneratorMoment_weightedHeatFlow
    ν t hν ht u₀ hu₀
  have htI : t ∈ Icc (0 : ℝ) t := ⟨ht.le, le_rfl⟩
  have hut := hmild t htI
  constructor
  · rw [hut, criticalMildImage]
    exact (hheat.add hnonlinear.1).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun k => by
        change ‖complexFrequency (latticeFrequency k)‖ *
            ‖weightedHeatFlow ν t hν.le ht.le u₀ k +
              criticalMildDuhamel ν hν u hu t k‖ ≤ _
        exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans_eq
          (mul_add _ _ _))
  · calc
      heatHalfGeneratorMoment (u t) =
          heatHalfGeneratorMoment
            (weightedHeatFlow ν t hν.le ht.le u₀ +
              criticalMildDuhamel ν hν u hu t) := by
        rw [hut]
        rfl
      _ ≤ heatHalfGeneratorMoment (weightedHeatFlow ν t hν.le ht.le u₀) +
          heatHalfGeneratorMoment (criticalMildDuhamel ν hν u hu t) :=
        heatHalfGeneratorMoment_add_le _ _ hheat hnonlinear.1
      _ ≤ (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
          ((∫ s in Ioc 0 t, mildDiniDensity ν t u s) + ν⁻¹ * ‖u t‖ ^ 2) :=
        add_le_add
          (heatHalfGeneratorMoment_weightedHeatFlow_le ν t hν ht u₀ hu₀)
          hnonlinear.2
      _ = (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
          (∫ s in Ioc 0 t, mildDiniDensity ν t u s) + ν⁻¹ * ‖u t‖ ^ 2 := by
        ring

/-- Quantitative full positive-time graph membership of the actual mild
trajectory. The linear heat term displays the initial-data cost explicitly,
while the nonlinear contribution uses the constructed Dini budget. -/
theorem exists_mildTrajectory_fullPositiveTime_halfGenerator_with_explicitBound
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    ∃ b : ℝ, 0 < b ∧ b < t ∧ t - b ≤ 1 ∧ Real.sqrt (t - b) < b ∧
      (Summable fun k : LatticeMode =>
        ‖complexFrequency (latticeFrequency k)‖ * ‖u t k‖) ∧
      heatHalfGeneratorMoment (u t) ≤
        (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
          mildDiniExplicitBudget ν u₀ R b t + ν⁻¹ * R ^ 2 := by
  obtain ⟨b, hb, hbt, hunit, hinterior, hnonlinearSummable, hnonlinearBound⟩ :=
    exists_criticalMildDuhamel_fullPositiveTime_graph_with_explicitBound
      ν hν u₀ hu₀ u huc hu hR ht huR hmild
  have hheat := summable_halfGeneratorMoment_weightedHeatFlow
    ν t hν ht u₀ hu₀
  have htI : t ∈ Icc (0 : ℝ) t := ⟨ht.le, le_rfl⟩
  have hut := hmild t htI
  refine ⟨b, hb, hbt, hunit, hinterior, ?_, ?_⟩
  · rw [hut, criticalMildImage]
    exact (hheat.add hnonlinearSummable).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun k => by
        change ‖complexFrequency (latticeFrequency k)‖ *
            ‖weightedHeatFlow ν t hν.le ht.le u₀ k +
              criticalMildDuhamel ν hν u hu t k‖ ≤ _
        exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)).trans_eq
          (mul_add _ _ _))
  · calc
      heatHalfGeneratorMoment (u t) =
          heatHalfGeneratorMoment
            (weightedHeatFlow ν t hν.le ht.le u₀ +
              criticalMildDuhamel ν hν u hu t) := by
        rw [hut]
        rfl
      _ ≤ heatHalfGeneratorMoment (weightedHeatFlow ν t hν.le ht.le u₀) +
          heatHalfGeneratorMoment (criticalMildDuhamel ν hν u hu t) :=
        heatHalfGeneratorMoment_add_le _ _ hheat hnonlinearSummable
      _ ≤ (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
          (mildDiniExplicitBudget ν u₀ R b t + ν⁻¹ * R ^ 2) :=
        add_le_add
          (heatHalfGeneratorMoment_weightedHeatFlow_le ν t hν ht u₀ hu₀)
          hnonlinearBound
      _ = (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
          mildDiniExplicitBudget ν u₀ R b t + ν⁻¹ * R ^ 2 := by
        ring

/-- Once the trajectory has reached a positive time, its newly proved graph
membership upgrades the forward time modulus from the construction's
quarter-Hölder estimate to the semigroup-sharp square-root scale. The
coefficient is explicit in the same local chart data. -/
theorem exists_norm_mildTrajectory_increment_le_sqrt_with_explicitBound
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t r : ℝ} (hR : 0 ≤ R) (ht : 0 < t) (hr : 0 ≤ r)
    (huR : ∀ s ∈ Ioc (0 : ℝ) (t + r), ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) (t + r)),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    ∃ b : ℝ, 0 < b ∧ b < t ∧ t - b ≤ 1 ∧ Real.sqrt (t - b) < b ∧
      ‖u (t + r) - u t‖ ≤
        (Real.sqrt ν *
            ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
              mildDiniExplicitBudget ν u₀ R b t + ν⁻¹ * R ^ 2) +
          2 * R ^ 2 / Real.sqrt ν) * Real.sqrt r := by
  have htr : 0 ≤ t + r := by linarith
  have huRt : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R := by
    intro s hs
    exact huR s ⟨hs.1, hs.2.trans (by linarith)⟩
  have hmildt : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1 := by
    intro s hs
    exact hmild s ⟨hs.1, hs.2.trans (by linarith)⟩
  obtain ⟨b, hb, hbt, hunit, hinterior, hhalf, hmoment⟩ :=
    exists_mildTrajectory_fullPositiveTime_halfGenerator_with_explicitBound
      ν hν u₀ hu₀ u huc hu hR ht huRt hmildt
  let M : ℝ := (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
    mildDiniExplicitBudget ν u₀ R b t + ν⁻¹ * R ^ 2
  have hM : heatHalfGeneratorMoment (u t) ≤ M := by
    simpa only [M] using hmoment
  have hheat :
      ‖weightedHeatFlow ν r hν.le hr (u t) - u t‖ ≤
        (Real.sqrt ν * M) * Real.sqrt r := by
    refine (norm_weightedHeatFlow_sub_le_sqrt_mul_halfGeneratorMoment
      ν r hν.le hr (u t) (hu t) hhalf).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg ν)) (Real.sqrt_nonneg r)
  have hmild_t : u t = criticalMildImage ν hν u₀ u hu t ht.le := by
    exact hmild t ⟨ht.le, by linarith⟩
  have hmild_tr : u (t + r) =
      criticalMildImage ν hν u₀ u hu (t + r) htr := by
    exact hmild (t + r) ⟨htr, le_rfl⟩
  have hincrement := norm_shifted_trajectory_sub_le_sqrt
    ν hν u₀ u huc hu hR ht.le hr huR hmild_t hmild_tr hheat
  refine ⟨b, hb, hbt, hunit, hinterior, ?_⟩
  simpa only [M] using hincrement

/-- One extra carrier moment implies two-spatial-derivative summability after
removing the native lattice weight. This is a raw-carrier statement; a physical
Fourier interpretation additionally requires the normalization decoder. -/
theorem summable_decoded_twoSpatialDerivatives_of_halfGenerator
    (v : WeightedLatticeBanach)
    (hv : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖v k‖) :
    Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient v k) := by
  apply hv.of_nonneg_of_le
  · intro k
    exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
  · intro k
    rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
    have hweight : ‖complexFrequency (latticeFrequency k)‖ ≤
        latticeModeWeight k := by
      unfold latticeModeWeight
      linarith [norm_nonneg (complexFrequency (latticeFrequency k))]
    calc
      ‖complexFrequency (latticeFrequency k)‖ ^ 2 *
          complexEuclideanNorm (weightedLatticeCoefficient v k) =
        ‖complexFrequency (latticeFrequency k)‖ *
          (‖complexFrequency (latticeFrequency k)‖ *
            complexEuclideanNorm (weightedLatticeCoefficient v k)) := by ring
      _ ≤ ‖complexFrequency (latticeFrequency k)‖ *
          (latticeModeWeight k *
            complexEuclideanNorm (weightedLatticeCoefficient v k)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)) (norm_nonneg _)
      _ = ‖complexFrequency (latticeFrequency k)‖ *
          latticeWeightedAmplitude (weightedLatticeCoefficient v) k := rfl
      _ = ‖complexFrequency (latticeFrequency k)‖ * ‖v k‖ :=
        congrArg (fun z => ‖complexFrequency (latticeFrequency k)‖ * z)
          (latticeWeightedAmplitude_coefficient v k)

/-- The actual positive-time raw mild value reaches the fixed-time carrier
two-spatial-derivative reconstruction threshold. -/
theorem mildTrajectory_decoded_twoSpatialDerivatives
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient (u t) k) :=
  summable_decoded_twoSpatialDerivatives_of_halfGenerator (u t)
    (mildTrajectory_fullPositiveTime_halfGenerator
      ν hν u₀ hu₀ u huc hu hR ht huR hmild).1

end Navier.Analysis.CriticalMildFullPositiveTimeRegularity

#print axioms Navier.Analysis.CriticalMildFullPositiveTimeRegularity.criticalMildDuhamel_fullPositiveTime_graph
#print axioms Navier.Analysis.CriticalMildFullPositiveTimeRegularity.integral_mildDiniDensity_le_explicitBudget
#print axioms Navier.Analysis.CriticalMildFullPositiveTimeRegularity.exists_criticalMildDuhamel_fullPositiveTime_graph_with_explicitBound
#print axioms Navier.Analysis.CriticalMildFullPositiveTimeRegularity.mildTrajectory_fullPositiveTime_halfGenerator
#print axioms Navier.Analysis.CriticalMildFullPositiveTimeRegularity.exists_mildTrajectory_fullPositiveTime_halfGenerator_with_explicitBound
#print axioms Navier.Analysis.CriticalMildFullPositiveTimeRegularity.exists_norm_mildTrajectory_increment_le_sqrt_with_explicitBound
#print axioms Navier.Analysis.CriticalMildFullPositiveTimeRegularity.summable_decoded_twoSpatialDerivatives_of_halfGenerator
#print axioms Navier.Analysis.CriticalMildFullPositiveTimeRegularity.mildTrajectory_decoded_twoSpatialDerivatives
