import Navier.Analysis.CriticalMildQuantitativeRestart
import Navier.Analysis.LeiLinPositiveRestartCancellation

/-!
# Interior time modulus for the actual critical mild trajectory

The critical carrier is only assumed continuous in the fixed-point
construction. At a strictly positive time, however, the mild equation gives
a quantitative modulus. The proof resolves the history a positive heat lag
before the observation endpoint, retains the integrable logarithmic graph
budget of that history, and estimates the remaining terminal strip directly.

This is a local positive-time result. Its constants depend on the interior
time and the chart radius; it does not provide a horizon-uniform bound for
arbitrary data.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set

namespace Navier.Analysis.CriticalMildInteriorTimeModulus

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildObservationContinuity
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildRestart
open Navier.Analysis.CriticalMildQuantitativeRestart
open Navier.Analysis.LeiLinPositiveRestartMild
open Navier.Analysis.LeiLinPositiveRestartCancellation

/-- Exact logarithmic integral of the inverse heat lag before a strict
cutoff. -/
theorem integral_inv_time_gap
    {t a : ℝ} (ha0 : 0 ≤ a) (ha : a < t) :
    (∫ s in Ioc (0 : ℝ) a, (t - s)⁻¹) =
      Real.log (t / (t - a)) := by
  rw [← intervalIntegral.integral_of_le ha0,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) t]
  simpa using integral_inv_of_pos (sub_pos.mpr ha)
    (lt_of_le_of_lt ha0 ha)

/-- The actual Duhamel history before a strict cutoff has a logarithmic,
rather than inverse-gap, graph budget. -/
theorem truncatedDuhamel_halfGenerator_log
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a : ℝ} (hR : 0 ≤ R) (ha0 : 0 ≤ a) (ha : a < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖(∫ s in Ioc 0 a,
          criticalMildPathIntegrand ν hν u hu t s) m‖) ∧
    heatHalfGeneratorMoment
        (∫ s in Ioc 0 a, criticalMildPathIntegrand ν hν u hu t s) ≤
      ((2 / ν) * R ^ 2) * Real.log (t / (t - a)) := by
  let f : ℝ → WeightedLatticeBanach :=
    criticalMildPathIntegrand ν hν u hu t
  let g : ℝ → ℝ := fun s => ((2 / ν) * R ^ 2) * (t - s)⁻¹
  have ht0 : 0 ≤ t := (lt_of_le_of_lt ha0 ha).le
  have hf : IntegrableOn f (Ioc 0 a) volume := by
    exact (integrableOn_criticalMildPathIntegrand
      ν hν u huc hu hR ht0 huR).mono_set (Ioc_subset_Ioc_right ha.le)
  have hfsum : ∀ᵐ s ∂volume.restrict (Ioc 0 a),
      Summable fun m : LatticeMode =>
        ‖complexFrequency (latticeFrequency m)‖ * ‖f s m‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact summable_halfGeneratorMoment_criticalMildPathIntegrand_of_strictTime
      ν hν u hu (lt_of_le_of_lt hs.2 ha)
  have hinvInterval : IntervalIntegrable (fun s : ℝ => (t - s)⁻¹)
      volume 0 a := by
    have hcontinuous : ContinuousOn (fun s : ℝ => (t - s)⁻¹) (uIcc 0 a) :=
      (continuousOn_const.sub continuousOn_id).inv₀ (fun s hs hzero => by
        have hs' : s ∈ Icc (0 : ℝ) a := by
          simpa [uIcc_of_le ha0] using hs
        simp only [id_eq] at hzero
        linarith [hs'.2])
    exact hcontinuous.intervalIntegrable
  have hg : IntegrableOn g (Ioc 0 a) volume := by
    have hinv : IntegrableOn (fun s : ℝ => (t - s)⁻¹) (Ioc 0 a) volume := by
      simpa [uIoc_of_le ha0] using intervalIntegrable_iff.mp hinvInterval
    exact hinv.const_mul ((2 / ν) * R ^ 2)
  have hmeas : Measurable (fun s => heatHalfGeneratorMoment (f s)) := by
    unfold heatHalfGeneratorMoment
    exact Measurable.tsum fun k => measurable_const.mul
      ((stronglyMeasurable_criticalMildPathIntegrand_apply
        ν hν u huc hu t k).norm.measurable)
  have hfM : IntegrableOn (fun s => heatHalfGeneratorMoment (f s))
      (Ioc 0 a) volume := by
    apply hg.mono' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (heatHalfGeneratorMoment_nonneg _)]
    have hbase :=
      heatHalfGeneratorMoment_criticalMildPathIntegrand_le_radius
        ν hν u hu hR (lt_of_le_of_lt hs.2 ha)
        (huR s ⟨hs.1, (hs.2.trans_lt ha).le⟩)
    simpa [f, g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase
  have hmoment := heatHalfGeneratorMoment_integral_le_integral f hf hfsum hfM
  have hintegral :
      (∫ s in Ioc (0 : ℝ) a, heatHalfGeneratorMoment (f s)) ≤
        ((2 / ν) * R ^ 2) * Real.log (t / (t - a)) := by
    calc
      (∫ s in Ioc (0 : ℝ) a, heatHalfGeneratorMoment (f s)) ≤
          ∫ s in Ioc (0 : ℝ) a, g s := by
        apply integral_mono_ae hfM hg
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hbase :=
          heatHalfGeneratorMoment_criticalMildPathIntegrand_le_radius
            ν hν u hu hR (lt_of_le_of_lt hs.2 ha)
            (huR s ⟨hs.1, (hs.2.trans_lt ha).le⟩)
        simpa [f, g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase
      _ = ((2 / ν) * R ^ 2) * Real.log (t / (t - a)) := by
        rw [show g = fun s => ((2 / ν) * R ^ 2) * (t - s)⁻¹ by rfl,
          integral_const_mul, integral_inv_time_gap ha0 ha]
  have hfinite : ∀ F : Finset LatticeMode,
      (∑ m ∈ F, ‖complexFrequency (latticeFrequency m)‖ *
        ‖(∫ s in Ioc 0 a, f s) m‖) ≤
        ((2 / ν) * R ^ 2) * Real.log (t / (t - a)) := by
    intro F
    exact (sum_heatHalfGeneratorMoment_integral_le_integral
      F f hf hfsum hfM).trans hintegral
  have hsummable : Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖(∫ s in Ioc 0 a, f s) m‖) := by
    apply summable_of_sum_le
      (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact hfinite
  refine ⟨by simpa [f] using hsummable, ?_⟩
  exact hmoment.trans hintegral

/-- The heat term plus the history before `a` is the resolved part of the
mild image at `t`. -/
def resolvedMildHistory
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t a : ℝ) (ht : 0 ≤ t) : WeightedLatticeBanach :=
  weightedHeatFlow ν t hν.le ht u₀ +
    ∫ s in Ioc 0 a, criticalMildPathIntegrand ν hν u hu t s

/-- The resolved mild history has the sum of the linear positive-time graph
budget and the logarithmic nonlinear budget. -/
theorem resolvedMildHistory_halfGenerator_log
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a : ℝ} (hR : 0 ≤ R) (ht : 0 < t) (ha0 : 0 ≤ a) (ha : a < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖resolvedMildHistory ν hν u₀ u hu t a ht.le m‖) ∧
    heatHalfGeneratorMoment
        (resolvedMildHistory ν hν u₀ u hu t a ht.le) ≤
      (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
        ((2 / ν) * R ^ 2) * Real.log (t / (t - a)) := by
  have hheat := summable_halfGeneratorMoment_weightedHeatFlow
    ν t hν ht u₀ hu₀
  have hpast := truncatedDuhamel_halfGenerator_log
    ν hν u huc hu hR ha0 ha huR
  have hsum : Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖(weightedHeatFlow ν t hν.le ht.le u₀ +
          ∫ s in Ioc 0 a, criticalMildPathIntegrand ν hν u hu t s) m‖) :=
    (hheat.add hpast.1).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun m => by
        change ‖complexFrequency (latticeFrequency m)‖ *
            ‖weightedHeatFlow ν t hν.le ht.le u₀ m +
              (∫ s in Ioc 0 a,
                criticalMildPathIntegrand ν hν u hu t s) m‖ ≤ _
        exact (mul_le_mul_of_nonneg_left (norm_add_le _ _)
          (norm_nonneg _)).trans_eq (mul_add _ _ _))
  refine ⟨by simpa [resolvedMildHistory] using hsum, ?_⟩
  exact (heatHalfGeneratorMoment_add_le _ _ hheat hpast.1).trans
    (add_le_add
      (heatHalfGeneratorMoment_weightedHeatFlow_le ν t hν ht u₀ hu₀)
      hpast.2)

/-- The resolved mild history remains divergence-free. -/
theorem resolvedMildHistory_divergenceFree
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (_ha0 : 0 ≤ a) (ha : a ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    LatticeDivergenceFree
      (resolvedMildHistory ν hν u₀ u hu t a ht) := by
  have hf : IntegrableOn
      (criticalMildPathIntegrand ν hν u hu t) (Ioc 0 a) volume :=
    (integrableOn_criticalMildPathIntegrand
      ν hν u huc hu hR ht huR).mono_set (Ioc_subset_Ioc_right ha)
  apply Navier.Analysis.CriticalMildSelfMap.LatticeDivergenceFree.add
  · exact weightedHeatFlow_divergenceFree ν t hν.le ht u₀
  · intro m
    change latticeDivergenceCLM m
        (∫ s in Ioc 0 a, criticalMildPathIntegrand ν hν u hu t s) = 0
    rw [← (latticeDivergenceCLM m).integral_comp_comm hf]
    have hz : (fun s => latticeDivergenceCLM m
        (criticalMildPathIntegrand ν hν u hu t s)) = fun _ => 0 := by
      funext s
      exact criticalMildPathIntegrand_divergenceFree ν hν u hu t s m
    rw [hz, integral_zero]

set_option maxHeartbeats 600000 in
/-- The same-weight heat increment of an actual positive-time mild image is
quantitative after resolving its history at any strict cutoff. The first
term is the two-sided cost of the unresolved terminal strip; the second is
the analytic-semigroup increment of the resolved graph-domain history. -/
theorem norm_weightedHeatFlow_mildImage_sub_le_cutoff_log
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t a r : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (ha0 : 0 ≤ a) (ha : a < t) (hr : 0 ≤ r)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    ‖weightedHeatFlow ν r hν.le hr
          (criticalMildImage ν hν u₀ u hu t ht.le) -
        criticalMildImage ν hν u₀ u hu t ht.le‖ ≤
      4 * Real.sqrt (t - a) / Real.sqrt ν * R ^ 2 +
        Real.sqrt ν *
          ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
            ((2 / ν) * R ^ 2) * Real.log (t / (t - a))) *
          Real.sqrt r := by
  let w := resolvedMildHistory ν hν u₀ u hu t a ht.le
  let q := criticalMildDuhamelTail ν hν u hu a t
  have hsplit := criticalMildDuhamel_eq_truncated_add_tail
    ν hν u huc hu hR ha0 ha.le huR
  have himage : criticalMildImage ν hν u₀ u hu t ht.le = w + q := by
    dsimp [w, q, resolvedMildHistory]
    rw [criticalMildImage, hsplit]
    abel
  have hwgraph := resolvedMildHistory_halfGenerator_log
    ν hν u₀ hu₀ u huc hu hR ht ha0 ha huR
  have hwdf := resolvedMildHistory_divergenceFree
    ν hν u₀ u huc hu hR ht.le ha0 ha.le huR
  have hwinc := norm_weightedHeatFlow_sub_le_sqrt_mul_halfGeneratorMoment
    ν r hν.le hr w hwdf hwgraph.1
  have hq := norm_criticalMildDuhamelTail_le_sqrt_sub
    ν hν u huc hu hR ha0 ha.le huR
  rw [himage, ← weightedHeatFlowCLM_apply, map_add,
    weightedHeatFlowCLM_apply, weightedHeatFlowCLM_apply]
  calc
    ‖weightedHeatFlow ν r hν.le hr w +
          weightedHeatFlow ν r hν.le hr q - (w + q)‖ =
        ‖(weightedHeatFlow ν r hν.le hr w - w) +
          (weightedHeatFlow ν r hν.le hr q - q)‖ := by
      congr 1
      abel
    _ ≤ ‖weightedHeatFlow ν r hν.le hr w - w‖ +
          ‖weightedHeatFlow ν r hν.le hr q - q‖ := norm_add_le _ _
    _ ≤ Real.sqrt ν * heatHalfGeneratorMoment w * Real.sqrt r +
          2 * ‖q‖ := by
      apply add_le_add hwinc
      calc
        ‖weightedHeatFlow ν r hν.le hr q - q‖ ≤
            ‖weightedHeatFlow ν r hν.le hr q‖ + ‖q‖ := norm_sub_le _ _
        _ ≤ ‖q‖ + ‖q‖ := add_le_add
          (norm_weightedHeatFlow_le ν r hν.le hr q) le_rfl
        _ = 2 * ‖q‖ := by ring
    _ ≤ Real.sqrt ν *
          ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
            ((2 / ν) * R ^ 2) * Real.log (t / (t - a))) *
          Real.sqrt r +
        2 * ((2 * Real.sqrt (t - a) / Real.sqrt ν) * R ^ 2) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hwgraph.2 (Real.sqrt_nonneg ν))
          (Real.sqrt_nonneg r))
        (mul_le_mul_of_nonneg_left hq (by norm_num))
    _ = 4 * Real.sqrt (t - a) / Real.sqrt ν * R ^ 2 +
        Real.sqrt ν *
          ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
            ((2 / ν) * R ^ 2) * Real.log (t / (t - a))) *
          Real.sqrt r := by ring

/-- The logarithmic loss produced by the resolved history is dominated by a
quarter-power modulus. -/
theorem sqrt_mul_log_div_sqrt_le_quarter
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    Real.sqrt r * Real.log (t / Real.sqrt r) ≤
      2 * Real.sqrt t * Real.sqrt (Real.sqrt r) := by
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hx : 0 < t / Real.sqrt r := div_pos ht hsr
  have hsx : 0 < Real.sqrt (t / Real.sqrt r) := Real.sqrt_pos.2 hx
  have hlogeq : Real.log (t / Real.sqrt r) =
      2 * Real.log (Real.sqrt (t / Real.sqrt r)) := by
    rw [Real.log_sqrt hx.le]
    ring
  have hlog : Real.log (t / Real.sqrt r) ≤
      2 * Real.sqrt (t / Real.sqrt r) := by
    rw [hlogeq]
    exact (mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos hsx) (by norm_num)).trans (by linarith)
  have hid : Real.sqrt r * Real.sqrt (t / Real.sqrt r) =
      Real.sqrt t * Real.sqrt (Real.sqrt r) := by
    rw [Real.sqrt_div ht.le]
    have hssr : 0 < Real.sqrt (Real.sqrt r) := Real.sqrt_pos.2 hsr
    field_simp [ne_of_gt hssr]
    rw [Real.sq_sqrt (Real.sqrt_nonneg r)]
  calc
    Real.sqrt r * Real.log (t / Real.sqrt r) ≤
        Real.sqrt r * (2 * Real.sqrt (t / Real.sqrt r)) :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg r)
    _ = 2 * (Real.sqrt r * Real.sqrt (t / Real.sqrt r)) := by ring
    _ = 2 * Real.sqrt t * Real.sqrt (Real.sqrt r) := by rw [hid]; ring

/-- On a unit-size increment, a square root is bounded by its quarter root. -/
theorem sqrt_le_sqrt_sqrt {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    Real.sqrt r ≤ Real.sqrt (Real.sqrt r) := by
  have hsr0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsr1 : Real.sqrt r ≤ 1 := by
    nlinarith [Real.sq_sqrt hr]
  calc
    Real.sqrt r = Real.sqrt ((Real.sqrt r) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsr0]
    _ ≤ Real.sqrt (Real.sqrt r) :=
      Real.sqrt_le_sqrt (by nlinarith)

/-- The explicit local quarter-Hölder constant obtained from an interior mild
chart at time `t`. -/
def interiorQuarterModulusConstant
    (ν : ℝ) (u₀ : WeightedLatticeBanach) (R t : ℝ) : ℝ :=
  4 / Real.sqrt ν * R ^ 2 +
    Real.sqrt ν * (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
    Real.sqrt ν * ((2 / ν) * R ^ 2) * (2 * Real.sqrt t) +
    2 / Real.sqrt ν * R ^ 2

set_option maxHeartbeats 600000 in
/-- **Derived interior quarter-Hölder modulus for the actual mild
trajectory.** No time modulus or graph-domain assumption is made. The result
uses only the literal mild identities, continuity, divergence freedom, and
the native critical-radius bound. -/
theorem norm_mildTrajectory_increment_le_quarter
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t r : ℝ} (hR : 0 ≤ R) (ht : 0 < t) (hr : 0 < r)
    (hr1 : r ≤ 1) (hinterior : Real.sqrt r < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) (t + r), ‖u s‖ ≤ R)
    (hmild_t : u t = criticalMildImage ν hν u₀ u hu t ht.le)
    (hmild_tr : u (t + r) =
      criticalMildImage ν hν u₀ u hu (t + r) (by positivity)) :
    ‖u (t + r) - u t‖ ≤
      interiorQuarterModulusConstant ν u₀ R t *
        Real.sqrt (Real.sqrt r) := by
  let a : ℝ := t - Real.sqrt r
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha : a < t := by dsimp [a]; linarith [Real.sqrt_pos.2 hr]
  have hur : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R := by
    intro s hs
    exact huR s ⟨hs.1, hs.2.trans (le_add_of_nonneg_right hr.le)⟩
  have hheat := norm_weightedHeatFlow_mildImage_sub_le_cutoff_log
    ν hν u₀ hu₀ u huc hu hR ht ha0 ha hr.le hur
  have hrestart := norm_shifted_trajectory_sub_le_heatIncrement_add_sqrt
    ν hν u₀ u huc hu hR ht.le hr.le huR hmild_t hmild_tr
  have hheat' : ‖weightedHeatFlow ν r hν.le hr.le (u t) - u t‖ ≤
      4 * Real.sqrt (t - a) / Real.sqrt ν * R ^ 2 +
        Real.sqrt ν *
          ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
            ((2 / ν) * R ^ 2) * Real.log (t / (t - a))) *
          Real.sqrt r := by
    rw [hmild_t]
    exact hheat
  have hlog := sqrt_mul_log_div_sqrt_le_quarter ht hr
  have hsqrt := sqrt_le_sqrt_sqrt hr.le hr1
  have hsqrtν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hgap : t - a = Real.sqrt r := by simp [a]
  refine hrestart.trans (add_le_add hheat' le_rfl) |>.trans ?_
  rw [hgap]
  dsimp [interiorQuarterModulusConstant]
  have hA : 0 ≤ (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (norm_nonneg _)
  have hlogterm :
      Real.sqrt ν * (((2 / ν) * R ^ 2) *
          Real.log (t / Real.sqrt r)) * Real.sqrt r ≤
        Real.sqrt ν * (((2 / ν) * R ^ 2) *
          (2 * Real.sqrt t * Real.sqrt (Real.sqrt r))) := by
    calc
      Real.sqrt ν * (((2 / ν) * R ^ 2) *
          Real.log (t / Real.sqrt r)) * Real.sqrt r =
        (Real.sqrt ν * ((2 / ν) * R ^ 2)) *
          (Real.sqrt r * Real.log (t / Real.sqrt r)) := by ring
      _ ≤ (Real.sqrt ν * ((2 / ν) * R ^ 2)) *
          (2 * Real.sqrt t * Real.sqrt (Real.sqrt r)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = Real.sqrt ν * (((2 / ν) * R ^ 2) *
          (2 * Real.sqrt t * Real.sqrt (Real.sqrt r))) := by ring
  have hmiddle :
      Real.sqrt ν *
            ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
              (2 / ν * R ^ 2) * Real.log (t / Real.sqrt r)) *
            Real.sqrt r ≤
        Real.sqrt ν * ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖) *
            Real.sqrt (Real.sqrt r) +
          Real.sqrt ν * ((2 / ν * R ^ 2) *
            (2 * Real.sqrt t * Real.sqrt (Real.sqrt r))) := by
    calc
      Real.sqrt ν *
              ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
                (2 / ν * R ^ 2) * Real.log (t / Real.sqrt r)) *
            Real.sqrt r =
          Real.sqrt ν * ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖) *
              Real.sqrt r +
            Real.sqrt ν * ((2 / ν * R ^ 2) *
              Real.log (t / Real.sqrt r)) * Real.sqrt r := by ring
      _ ≤ Real.sqrt ν * ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖) *
              Real.sqrt (Real.sqrt r) +
            Real.sqrt ν * ((2 / ν * R ^ 2) *
              (2 * Real.sqrt t * Real.sqrt (Real.sqrt r))) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hsqrt
            (mul_nonneg (Real.sqrt_nonneg ν) hA))
          hlogterm
  have htail : 2 * Real.sqrt r / Real.sqrt ν * R ^ 2 ≤
      2 * Real.sqrt (Real.sqrt r) / Real.sqrt ν * R ^ 2 := by
    calc
      2 * Real.sqrt r / Real.sqrt ν * R ^ 2 =
          (2 / Real.sqrt ν) * Real.sqrt r * R ^ 2 := by ring
      _ ≤ (2 / Real.sqrt ν) * Real.sqrt (Real.sqrt r) * R ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (sq_nonneg R)
      _ = 2 * Real.sqrt (Real.sqrt r) / Real.sqrt ν * R ^ 2 := by ring
  calc
    4 * Real.sqrt (Real.sqrt r) / Real.sqrt ν * R ^ 2 +
          Real.sqrt ν *
            ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
              (2 / ν * R ^ 2) * Real.log (t / Real.sqrt r)) *
            Real.sqrt r +
        2 * Real.sqrt r / Real.sqrt ν * R ^ 2 ≤
      4 * Real.sqrt (Real.sqrt r) / Real.sqrt ν * R ^ 2 +
          (Real.sqrt ν * ((Real.sqrt (ν * t))⁻¹ * ‖u₀‖) *
              Real.sqrt (Real.sqrt r) +
            Real.sqrt ν * ((2 / ν * R ^ 2) *
              (2 * Real.sqrt t * Real.sqrt (Real.sqrt r)))) +
        2 * Real.sqrt (Real.sqrt r) / Real.sqrt ν * R ^ 2 :=
      add_le_add (add_le_add le_rfl hmiddle) htail
    _ = (4 / Real.sqrt ν * R ^ 2 +
          Real.sqrt ν * (Real.sqrt (ν * t))⁻¹ * ‖u₀‖ +
          Real.sqrt ν * (2 / ν * R ^ 2) * (2 * Real.sqrt t) +
          2 / Real.sqrt ν * R ^ 2) * Real.sqrt (Real.sqrt r) := by ring

/-- A uniform version of the quarter-Hölder constant on an interior window
`[b,t]`. -/
def interiorQuarterWindowConstant
    (ν : ℝ) (u₀ : WeightedLatticeBanach) (R b t : ℝ) : ℝ :=
  4 / Real.sqrt ν * R ^ 2 +
    Real.sqrt ν * (Real.sqrt (ν * b))⁻¹ * ‖u₀‖ +
    Real.sqrt ν * ((2 / ν) * R ^ 2) * (2 * Real.sqrt t) +
    2 / Real.sqrt ν * R ^ 2

theorem interiorQuarterModulusConstant_le_window
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach) (R : ℝ)
    {b s t : ℝ} (hb : 0 < b) (hbs : b ≤ s) (hst : s ≤ t) :
    interiorQuarterModulusConstant ν u₀ R s ≤
      interiorQuarterWindowConstant ν u₀ R b t := by
  have hνb : 0 < ν * b := mul_pos hν hb
  have hνs : 0 < ν * s := mul_pos hν (hb.trans_le hbs)
  have hprod : ν * b ≤ ν * s := mul_le_mul_of_nonneg_left hbs hν.le
  have hsqrtprod : Real.sqrt (ν * b) ≤ Real.sqrt (ν * s) :=
    Real.sqrt_le_sqrt hprod
  have hinv : (Real.sqrt (ν * s))⁻¹ ≤ (Real.sqrt (ν * b))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le
      (Real.sqrt_pos.2 hνb) hsqrtprod
  have hsqrtst : Real.sqrt s ≤ Real.sqrt t := Real.sqrt_le_sqrt hst
  dsimp [interiorQuarterModulusConstant, interiorQuarterWindowConstant]
  gcongr

set_option maxHeartbeats 600000 in
/-- The quarter-Hölder estimate is uniform on every sufficiently short
positive-time terminal window. -/
theorem norm_mildTrajectory_sub_le_quarter_on_terminalWindow
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R b t : ℝ} (hR : 0 ≤ R) (hb : 0 < b) (hbt : b ≤ t)
    (hunit : t - b ≤ 1) (hinterior : Real.sqrt (t - b) < b)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    ∀ s ∈ Icc b t,
      ‖u s - u t‖ ≤
        interiorQuarterWindowConstant ν u₀ R b t *
          Real.sqrt (Real.sqrt (t - s)) := by
  intro s hs
  rcases hs.2.eq_or_lt with rfl | hst
  · simp
  · let r : ℝ := t - s
    have hr : 0 < r := by dsimp [r]; linarith
    have hr1 : r ≤ 1 := by dsimp [r]; linarith [hs.1, hunit]
    have hs0 : 0 < s := hb.trans_le hs.1
    have hsqrtle : Real.sqrt r ≤ Real.sqrt (t - b) := by
      apply Real.sqrt_le_sqrt
      dsimp [r]
      linarith [hs.1]
    have hrinterior : Real.sqrt r < s :=
      hsqrtle.trans_lt (hinterior.trans_le hs.1)
    have husR : ∀ x ∈ Ioc (0 : ℝ) (s + r), ‖u x‖ ≤ R := by
      intro x hx
      apply huR x
      simpa [r] using hx
    have hsI : s ∈ Icc (0 : ℝ) t := ⟨hs0.le, hst.le⟩
    have htI : t ∈ Icc (0 : ℝ) t := ⟨hs0.le.trans hst.le, le_rfl⟩
    have hpoint := norm_mildTrajectory_increment_le_quarter
      ν hν u₀ hu₀ u huc hu hR hs0 hr hr1 hrinterior husR
      (hmild s hsI) (by simpa [r] using hmild t htI)
    have hconstant := interiorQuarterModulusConstant_le_window
      ν hν u₀ R hb hs.1 hst.le
    calc
      ‖u s - u t‖ = ‖u (s + r) - u s‖ := by
        rw [show s + r = t by dsimp [r]; ring, norm_sub_rev]
      _ ≤ interiorQuarterModulusConstant ν u₀ R s *
          Real.sqrt (Real.sqrt r) := hpoint
      _ ≤ interiorQuarterWindowConstant ν u₀ R b t *
          Real.sqrt (Real.sqrt r) :=
        mul_le_mul_of_nonneg_right hconstant
          (Real.sqrt_nonneg (Real.sqrt r))
      _ = interiorQuarterWindowConstant ν u₀ R b t *
          Real.sqrt (Real.sqrt (t - s)) := by rfl

/-- Dividing a quarter-power modulus by the time gap gives the integrable
`-3/4` power. -/
theorem inv_mul_sqrt_sqrt_eq_rpow_neg_three_fourths
    {x : ℝ} (hx : 0 < x) :
    x⁻¹ * Real.sqrt (Real.sqrt x) = x ^ (-(3 / 4 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hx.le, ← Real.rpow_neg_one,
    ← Real.rpow_add hx]
  congr 1
  norm_num

set_option maxHeartbeats 600000 in
/-- **The derived quarter-Hölder modulus supplies the exact Dini input used
by frozen-source cancellation.** Both conclusions concern the actual mild
trajectory; no modulus hypothesis is present. -/
theorem intervalIntegrable_dini_and_cancellingGraphMoment_of_actualMild
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
        (fun s => (2 / (ν * (t - s))) *
          (‖u s‖ + ‖u t‖) * ‖u s - u t‖) volume b t ∧
      IntervalIntegrable
        (fun s => heatHalfGeneratorMoment
          (criticalMildPathIntegrand ν hν u hu t s -
            criticalMildPathIntegrand ν hν (fun _ => u t)
              (fun _ => hu t) t s)) volume b t := by
  let C : ℝ := interiorQuarterWindowConstant ν u₀ R b t
  let K : ℝ := (4 / ν) * R * C
  have ht : 0 < t := hb.trans_le hbt
  have hC : 0 ≤ C := by
    dsimp [C, interiorQuarterWindowConstant]
    positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmod := norm_mildTrajectory_sub_le_quarter_on_terminalWindow
    ν hν u₀ hu₀ u huc hu hR hb hbt hunit hinterior huR hmild
  have hpow : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) volume b t := by
    have hzero := intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := t - b) (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))
    have hcomp := hzero.comp_sub_left t
    simpa using hcomp.symm
  have hmajor : IntervalIntegrable
      (fun s : ℝ => K * (t - s) ^ (-(3 / 4 : ℝ))) volume b t :=
    hpow.const_mul K
  have hmeas : Measurable (fun s => (2 / (ν * (t - s))) *
      (‖u s‖ + ‖u t‖) * ‖u s - u t‖) := by
    have hcoef : Measurable (fun s : ℝ => 2 / (ν * (t - s))) :=
      measurable_const.div
        (measurable_const.mul (measurable_const.sub measurable_id))
    have hnormu : Measurable (fun s : ℝ => ‖u s‖) := huc.norm.measurable
    have hdiff : Measurable (fun s : ℝ => ‖u s - u t‖) :=
      (huc.sub continuous_const).norm.measurable
    exact (hcoef.mul (hnormu.add measurable_const)).mul hdiff
  have hDini : IntervalIntegrable
      (fun s => (2 / (ν * (t - s))) *
        (‖u s‖ + ‖u t‖) * ‖u s - u t‖) volume b t := by
    apply hmajor.mono_fun' hmeas.aestronglyMeasurable
    rw [uIoc_of_le hbt]
    have hne : ∀ᵐ s : ℝ ∂volume.restrict (Ioc b t), s ≠ t := by
      rw [ae_iff]
      simp
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with s hs hstne
    have hst : s < t := lt_of_le_of_ne hs.2 hstne
    have hgap : 0 < t - s := sub_pos.mpr hst
    have hs0 : 0 < s := hb.trans hs.1
    have hsI : s ∈ Icc b t := ⟨hs.1.le, hs.2⟩
    have hut : ‖u t‖ ≤ R := huR t ⟨ht, le_rfl⟩
    have hus : ‖u s‖ ≤ R := huR s ⟨hs0, hs.2⟩
    have hnormsum : ‖u s‖ + ‖u t‖ ≤ 2 * R := by linarith
    have hpoint := hmod s hsI
    have hcoef : 0 ≤ 2 / (ν * (t - s)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg hcoef (add_nonneg (norm_nonneg _) (norm_nonneg _)))
        (norm_nonneg _))]
    calc
      (2 / (ν * (t - s))) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖ ≤
          (2 / (ν * (t - s))) * (2 * R) *
            (C * Real.sqrt (Real.sqrt (t - s))) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hnormsum hcoef) hpoint
          (norm_nonneg _)
          (mul_nonneg hcoef (mul_nonneg (by positivity) hR))
      _ = K * (t - s) ^ (-(3 / 4 : ℝ)) := by
        dsimp [K]
        rw [show 2 / (ν * (t - s)) = (2 / ν) * (t - s)⁻¹ by
          field_simp [hν.ne', ne_of_gt hgap]]
        calc
          2 / ν * (t - s)⁻¹ * (2 * R) *
              (C * Real.sqrt (Real.sqrt (t - s))) =
            (4 / ν * R * C) *
              ((t - s)⁻¹ * Real.sqrt (Real.sqrt (t - s))) := by ring
          _ = 4 / ν * R * C * (t - s) ^ (-(3 / 4 : ℝ)) := by
            rw [inv_mul_sqrt_sqrt_eq_rpow_neg_three_fourths hgap]
  exact ⟨hDini,
    intervalIntegrable_heatHalfGeneratorMoment_path_sub_constant_of_dini
      ν hν u huc hu hbt hDini⟩

/-- Every positive observation time admits a nontrivial terminal window on
which the quarter-Hölder construction applies. -/
theorem exists_admissible_terminalWindow {t : ℝ} (ht : 0 < t) :
    ∃ b : ℝ, 0 < b ∧ b < t ∧ t - b ≤ 1 ∧ Real.sqrt (t - b) < b := by
  let q : ℝ := min t 1
  let δ : ℝ := (q / 4) ^ 2
  let b : ℝ := t - δ
  have hq : 0 < q := by dsimp [q]; exact lt_min ht zero_lt_one
  have hqt : q ≤ t := by dsimp [q]; exact min_le_left _ _
  have hq1 : q ≤ 1 := by dsimp [q]; exact min_le_right _ _
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδt : δ < t := by
    dsimp [δ]
    nlinarith [sq_nonneg (q - 1)]
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    nlinarith [sq_nonneg q, sq_nonneg (q - 1)]
  have hsqrtδ : Real.sqrt δ = q / 4 := by
    dsimp [δ]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (div_pos hq (by norm_num))]
  refine ⟨b, by dsimp [b]; linarith, by dsimp [b]; linarith,
    by dsimp [b]; linarith, ?_⟩
  rw [show t - b = δ by dsimp [b]; ring, hsqrtδ]
  dsimp [b, δ]
  nlinarith [sq_nonneg (q - 1)]

/-- At every positive time, the actual mild equation therefore supplies a
nontrivial terminal window with both the Dini modulus and the integrable
frozen-source cancellation graph moment. -/
theorem exists_terminalWindow_dini_and_cancellingGraphMoment
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 < t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      u s = criticalMildImage ν hν u₀ u hu s hs.1) :
    ∃ b : ℝ, 0 < b ∧ b < t ∧
      IntervalIntegrable
        (fun s => (2 / (ν * (t - s))) *
          (‖u s‖ + ‖u t‖) * ‖u s - u t‖) volume b t ∧
      IntervalIntegrable
        (fun s => heatHalfGeneratorMoment
          (criticalMildPathIntegrand ν hν u hu t s -
            criticalMildPathIntegrand ν hν (fun _ => u t)
              (fun _ => hu t) t s)) volume b t := by
  obtain ⟨b, hb, hbt, hunit, hinterior⟩ :=
    exists_admissible_terminalWindow ht
  have hresult :=
    intervalIntegrable_dini_and_cancellingGraphMoment_of_actualMild
      ν hν u₀ hu₀ u huc hu hR hb hbt.le hunit hinterior huR hmild
  exact ⟨b, hb, hbt, hresult⟩

end Navier.Analysis.CriticalMildInteriorTimeModulus

#print axioms Navier.Analysis.CriticalMildInteriorTimeModulus.truncatedDuhamel_halfGenerator_log
#print axioms Navier.Analysis.CriticalMildInteriorTimeModulus.norm_weightedHeatFlow_mildImage_sub_le_cutoff_log
#print axioms Navier.Analysis.CriticalMildInteriorTimeModulus.norm_mildTrajectory_increment_le_quarter
#print axioms Navier.Analysis.CriticalMildInteriorTimeModulus.norm_mildTrajectory_sub_le_quarter_on_terminalWindow
#print axioms Navier.Analysis.CriticalMildInteriorTimeModulus.intervalIntegrable_dini_and_cancellingGraphMoment_of_actualMild
#print axioms Navier.Analysis.CriticalMildInteriorTimeModulus.exists_terminalWindow_dini_and_cancellingGraphMoment
