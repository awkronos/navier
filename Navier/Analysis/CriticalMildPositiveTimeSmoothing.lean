import Navier.Analysis.LeiLinPositiveRestartMild

/-!
# Positive-time smoothing of the resolved mild history

At a positive observation time, every part of the nonlinear Duhamel history
that stays a fixed positive heat lag away from the observation endpoint gains
one full homogeneous Fourier moment.  This file proves that statement for the
literal completed mild integrand and its actual Bochner integral.

The estimate isolates the remaining endpoint issue sharply: the heat term and
every lag-separated portion of the Duhamel integral are in the
half-generator domain.  Only the arbitrarily short terminal tail still needs
the endpoint cancellation/Volterra argument.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set

namespace Navier.Analysis.CriticalMildPositiveTimeSmoothing

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildObservationContinuity
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinPositiveRestartMild

/-- The literal portion of the nonlinear mild history integrated only up to
`a`, at the later observation time `t`. -/
def lagSeparatedDuhamel
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t a : ℝ) : WeightedLatticeBanach :=
  ∫ s in Ioc 0 a, criticalMildPathIntegrand ν hν u hu t s

/-- On `0 ≤ s ≤ a < t`, the full graph moment of the actual nonlinear
integrand is bounded by the endpoint-independent positive-lag constant. -/
theorem heatHalfGeneratorMoment_criticalMildPathIntegrand_le_of_le_cutoff
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a s : ℝ} (hR : 0 ≤ R) (ha : a < t)
    (hs : s ∈ Ioc (0 : ℝ) a) (huR : ‖u s‖ ≤ R) :
    heatHalfGeneratorMoment (criticalMildPathIntegrand ν hν u hu t s) ≤
      (2 / (ν * (t - a))) * R ^ 2 := by
  have hst : s < t := lt_of_le_of_lt hs.2 ha
  have hbase := heatHalfGeneratorMoment_criticalMildPathIntegrand_le_radius
    ν hν u hu hR hst huR
  have hden : ν * (t - a) ≤ ν * (t - s) := by
    exact mul_le_mul_of_nonneg_left (by linarith [hs.2]) hν.le
  have hinv : (ν * (t - s))⁻¹ ≤ (ν * (t - a))⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (mul_pos hν (sub_pos.mpr ha)) hden
  have hcoef : 2 / (ν * (t - s)) ≤ 2 / (ν * (t - a)) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg R))

/-- The graph moment of the lag-separated literal integrand is integrable,
with its explicit positive-lag budget. -/
theorem integrableOn_heatHalfGeneratorMoment_criticalMildPathIntegrand_cutoff
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a : ℝ} (hR : 0 ≤ R) (_ha0 : 0 ≤ a) (ha : a < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    IntegrableOn
      (fun s => heatHalfGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s))
      (Ioc 0 a) volume := by
  let C : ℝ := (2 / (ν * (t - a))) * R ^ 2
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmeas : Measurable
      (fun s => heatHalfGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s)) := by
    unfold heatHalfGeneratorMoment
    exact Measurable.tsum fun k => measurable_const.mul
      ((stronglyMeasurable_criticalMildPathIntegrand_apply
        ν hν u huc hu t k).norm.measurable)
  have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc 0 a) volume :=
    integrableOn_const (measure_Ioc_lt_top.ne)
  apply hconst.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (heatHalfGeneratorMoment_nonneg _)]
  exact heatHalfGeneratorMoment_criticalMildPathIntegrand_le_of_le_cutoff
    ν hν u hu hR ha hs (huR s ⟨hs.1, (hs.2.trans_lt ha).le⟩)

/-- **Actual lag-separated nonlinear smoothing.**  Every positive heat gap
places the literal Duhamel history in the half-generator domain.  The graph
moment has the quantitative bound

`M(∫₀ᵃ B_{t-s}(u(s),u(s)) ds) ≤ 2a R² / (ν(t-a))`.

No graph regularity of the evolving path is assumed. -/
theorem lagSeparatedDuhamel_halfGenerator
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a : ℝ} (hR : 0 ≤ R) (ha0 : 0 ≤ a) (ha : a < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖lagSeparatedDuhamel ν hν u hu t a m‖) ∧
    heatHalfGeneratorMoment (lagSeparatedDuhamel ν hν u hu t a) ≤
      a * ((2 / (ν * (t - a))) * R ^ 2) := by
  let f : ℝ → WeightedLatticeBanach :=
    criticalMildPathIntegrand ν hν u hu t
  let C : ℝ := (2 / (ν * (t - a))) * R ^ 2
  have hf : IntegrableOn f (Ioc 0 a) volume := by
    have hfull := integrableOn_criticalMildPathIntegrand
      ν hν u huc hu hR (le_of_lt (ha0.trans_lt ha))
      huR
    exact hfull.mono_set (Ioc_subset_Ioc_right ha.le)
  have hfsum : ∀ᵐ s ∂volume.restrict (Ioc 0 a),
      Summable fun m : LatticeMode =>
        ‖complexFrequency (latticeFrequency m)‖ * ‖f s m‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact summable_halfGeneratorMoment_criticalMildPathIntegrand_of_strictTime
      ν hν u hu (lt_of_le_of_lt hs.2 ha)
  have hfM : IntegrableOn (fun s => heatHalfGeneratorMoment (f s))
      (Ioc 0 a) volume := by
    exact integrableOn_heatHalfGeneratorMoment_criticalMildPathIntegrand_cutoff
      ν hν u huc hu hR ha0 ha huR
  have hfinite : ∀ F : Finset LatticeMode,
      (∑ m ∈ F, ‖complexFrequency (latticeFrequency m)‖ *
        ‖(∫ s in Ioc 0 a, f s) m‖) ≤ a * C := by
    intro F
    refine (sum_heatHalfGeneratorMoment_integral_le_integral
      F f hf hfsum hfM).trans ?_
    have hbound : ∀ s ∈ Ioc (0 : ℝ) a,
        heatHalfGeneratorMoment (f s) ≤ C := by
      intro s hs
      exact heatHalfGeneratorMoment_criticalMildPathIntegrand_le_of_le_cutoff
        ν hν u hu hR ha hs (huR s ⟨hs.1, (hs.2.trans_lt ha).le⟩)
    calc
      (∫ s in Ioc 0 a, heatHalfGeneratorMoment (f s)) ≤
          ∫ _s in Ioc 0 a, C := by
        apply integral_mono_ae hfM (integrableOn_const measure_Ioc_lt_top.ne)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hbound s hs
      _ = a * C := by simp [ha0]
  have hsummable : Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖(∫ s in Ioc 0 a, f s) m‖) := by
    apply summable_of_sum_le
      (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact hfinite
  have hmoment := heatHalfGeneratorMoment_integral_le_integral f hf hfsum hfM
  refine ⟨?_, ?_⟩
  · simpa [lagSeparatedDuhamel, f] using hsummable
  · change heatHalfGeneratorMoment (∫ s in Ioc 0 a, f s) ≤ _
    refine hmoment.trans ?_
    have hbound : ∀ s ∈ Ioc (0 : ℝ) a,
        heatHalfGeneratorMoment (f s) ≤ C := by
      intro s hs
      exact heatHalfGeneratorMoment_criticalMildPathIntegrand_le_of_le_cutoff
        ν hν u hu hR ha hs (huR s ⟨hs.1, (hs.2.trans_lt ha).le⟩)
    calc
      (∫ s in Ioc 0 a, heatHalfGeneratorMoment (f s)) ≤
          ∫ _s in Ioc 0 a, C := by
        apply integral_mono_ae hfM (integrableOn_const measure_Ioc_lt_top.ne)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact hbound s hs
      _ = a * C := by simp [ha0]
      _ = a * ((2 / (ν * (t - a))) * R ^ 2) := rfl

/-- The heat evolution of the initial datum and every lag-separated nonlinear
history are jointly in the half-generator domain at positive time.  This is
the resolved, already-smooth portion of the actual mild formula. -/
theorem summable_halfGenerator_resolvedMildHistory
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a : ℝ} (hR : 0 ≤ R) (ht : 0 < t) (ha0 : 0 ≤ a) (ha : a < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖(weightedHeatFlow ν t hν.le ht.le u₀ +
          lagSeparatedDuhamel ν hν u hu t a) m‖ := by
  have hheat := summable_halfGeneratorMoment_weightedHeatFlow
    ν t hν ht u₀ hu₀
  have hpast :=
    (lagSeparatedDuhamel_halfGenerator ν hν u huc hu hR ha0 ha huR).1
  exact (hheat.add hpast).of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun m => by
      change ‖complexFrequency (latticeFrequency m)‖ *
          ‖weightedHeatFlow ν t hν.le ht.le u₀ m +
            lagSeparatedDuhamel ν hν u hu t a m‖ ≤ _
      exact (mul_le_mul_of_nonneg_left (norm_add_le
        (weightedHeatFlow ν t hν.le ht.le u₀ m)
        (lagSeparatedDuhamel ν hν u hu t a m))
        (norm_nonneg (complexFrequency (latticeFrequency m)))).trans_eq
          (mul_add _ _ _))

/-- **Direct interface to the actual mild image.**  Removing only the
terminal interval `(a,t]` from the completed nonlinear mild image leaves a
half-generator-domain vector.  Thus every possible failure of positive-time
graph regularity is confined to arbitrarily short terminal Duhamel tails.

The displayed estimate also records the complete graph budget of the resolved
part: the positive-time heat budget plus the explicit lag-separated nonlinear
budget. -/
theorem criticalMildImage_sub_terminalTail_halfGenerator
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a : ℝ} (hR : 0 ≤ R) (ht : 0 < t) (ha0 : 0 ≤ a) (ha : a < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖(criticalMildImage ν hν u₀ u hu t ht.le -
          criticalMildDuhamelTail ν hν u hu a t) m‖) ∧
    heatHalfGeneratorMoment
        (criticalMildImage ν hν u₀ u hu t ht.le -
          criticalMildDuhamelTail ν hν u hu a t) ≤
      (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
        a * ((2 / (ν * (t - a))) * R ^ 2) := by
  have hsplit := criticalMildDuhamel_eq_truncated_add_tail
    ν hν u huc hu hR ha0 ha.le huR
  have heq :
      criticalMildImage ν hν u₀ u hu t ht.le -
          criticalMildDuhamelTail ν hν u hu a t =
        weightedHeatFlow ν t hν.le ht.le u₀ +
          lagSeparatedDuhamel ν hν u hu t a := by
    rw [criticalMildImage, hsplit]
    abel
  rw [heq]
  have hheat := summable_halfGeneratorMoment_weightedHeatFlow
    ν t hν ht u₀ hu₀
  have hpast := lagSeparatedDuhamel_halfGenerator
    ν hν u huc hu hR ha0 ha huR
  refine ⟨summable_halfGenerator_resolvedMildHistory
    ν hν u₀ hu₀ u huc hu hR ht ha0 ha huR, ?_⟩
  exact (heatHalfGeneratorMoment_add_le _ _ hheat hpast.1).trans
    (add_le_add
      (heatHalfGeneratorMoment_weightedHeatFlow_le ν t hν ht u₀ hu₀)
      hpast.2)

end Navier.Analysis.CriticalMildPositiveTimeSmoothing

#print axioms Navier.Analysis.CriticalMildPositiveTimeSmoothing.lagSeparatedDuhamel_halfGenerator
#print axioms Navier.Analysis.CriticalMildPositiveTimeSmoothing.summable_halfGenerator_resolvedMildHistory
#print axioms Navier.Analysis.CriticalMildPositiveTimeSmoothing.criticalMildImage_sub_terminalTail_halfGenerator
