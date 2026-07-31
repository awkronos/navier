import Navier.Analysis.CriticalMildPathIntegrand

/-!
# Moving-tail control for the critical mild Duhamel integral

The changing observation-time integral separates into a common interval and
the literal tail below.  This file records the tail as an actual Bochner
integral with its explicit shifted heat majorant.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildObservationContinuity

open MeasureTheory Set Topology
open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatTimeKernel

/-- The literal moving observation-time tail, over the part of the later
interval not present at the earlier observation time. -/
def criticalMildDuhamelTail
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t t' : ℝ) : WeightedLatticeBanach :=
  ∫ s in Ioc t t', criticalMildPathIntegrand ν hν u hu t' s

/-- The moving tail is a genuine Bochner integral whenever the path has the
same radius control on the later horizon. -/
theorem integrableOn_criticalMildDuhamelTailIntegrand
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t t' : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (htt' : t ≤ t')
    (huR : ∀ s ∈ Ioc (0 : ℝ) t', ‖u s‖ ≤ R) :
    IntegrableOn (criticalMildPathIntegrand ν hν u hu t') (Ioc t t') volume := by
  have hfull := integrableOn_criticalMildPathIntegrand
    ν hν u huc hu hR (le_trans ht htt') huR
  apply hfull.mono_set
  intro s hs
  exact ⟨lt_of_le_of_lt ht hs.1, hs.2⟩

/-- Norm control for the actual moving tail by the shifted singular scalar
majorant.  It exposes precisely the tail term needed in an observation-time
continuity proof. -/
theorem norm_criticalMildDuhamelTail_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t t' : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (htt' : t ≤ t')
    (huR : ∀ s ∈ Ioc (0 : ℝ) t', ‖u s‖ ≤ R) :
    ‖criticalMildDuhamelTail ν hν u hu t t'‖ ≤
      ∫ s in Ioc t t', criticalMildPathMajorant ν R t' s := by
  have hactual := integrableOn_criticalMildDuhamelTailIntegrand
    ν hν u huc hu hR ht htt' huR
  have hscalarFull : IntegrableOn (criticalMildPathMajorant ν R t')
      (Ioc 0 t') volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_trans ht htt')).mp
      (intervalIntegrable_criticalMildPathMajorant ν R t')
  have hscalar : IntegrableOn (criticalMildPathMajorant ν R t')
      (Ioc t t') volume := by
    apply hscalarFull.mono_set
    intro s hs
    exact ⟨lt_of_le_of_lt ht hs.1, hs.2⟩
  have hmono : (fun s => ‖criticalMildPathIntegrand ν hν u hu t' s‖) ≤ᵐ[
      volume.restrict (Ioc t t')] criticalMildPathMajorant ν R t' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rcases hs.2.eq_or_lt with hst | hst
    · subst s
      simp [criticalMildPathIntegrand,
        positiveTimeHeatRegularizedSpectralOutput, criticalMildPathMajorant]
      exact mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (by norm_num) _))
        (sq_nonneg _)
    · exact norm_criticalMildPathIntegrand_le_of_norm_le
        ν hν u hu hR hst (huR s ⟨lt_of_le_of_lt ht hs.1, hst.le⟩)
  unfold criticalMildDuhamelTail
  calc
    ‖∫ s in Ioc t t', criticalMildPathIntegrand ν hν u hu t' s‖ ≤
        ∫ s in Ioc t t', ‖criticalMildPathIntegrand ν hν u hu t' s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc t t', criticalMildPathMajorant ν R t' s :=
      integral_mono_ae hactual.norm hscalar hmono

/-- Exact shifted inverse-square-root budget on the moving tail interval. -/
theorem integral_inverseSqrtTime_tail
    {t t' : ℝ} (htt' : t ≤ t') :
    (∫ s in Ioc t t', inverseSqrtTime (t' - s)) =
      2 * Real.sqrt (t' - t) := by
  rw [← intervalIntegral.integral_of_le htt',
    intervalIntegral.integral_comp_sub_left,
    sub_self]
  exact integral_inverseSqrtTime_zero (t' - t) (sub_nonneg.mpr htt')

/-- Exact scalar evaluation of the shifted heat majorant over the moving
tail. -/
theorem integral_criticalMildPathMajorant_tail
    (ν R t t' : ℝ) (hν : 0 < ν) (htt' : t ≤ t') :
    (∫ s in Ioc t t', criticalMildPathMajorant ν R t' s) =
      (2 * Real.sqrt (t' - t) / Real.sqrt ν) * R ^ 2 := by
  unfold criticalMildPathMajorant
  rw [show (fun s : ℝ =>
      (Real.sqrt ν)⁻¹ * inverseSqrtTime (t' - s) * R ^ 2) =
      fun s => (Real.sqrt ν)⁻¹ * (inverseSqrtTime (t' - s) * R ^ 2) by
      funext s
      ring,
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_mul_const,
    integral_inverseSqrtTime_tail htt']
  field_simp [ne_of_gt hν]

/-- The actual moving Duhamel tail has the explicit vanishing
`O(sqrt (t' - t))` modulus. -/
theorem norm_criticalMildDuhamelTail_le_sqrt_sub
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t t' : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (htt' : t ≤ t')
    (huR : ∀ s ∈ Ioc (0 : ℝ) t', ‖u s‖ ≤ R) :
    ‖criticalMildDuhamelTail ν hν u hu t t'‖ ≤
      (2 * Real.sqrt (t' - t) / Real.sqrt ν) * R ^ 2 := by
  calc
    ‖criticalMildDuhamelTail ν hν u hu t t'‖ ≤
        ∫ s in Ioc t t', criticalMildPathMajorant ν R t' s :=
      norm_criticalMildDuhamelTail_le ν hν u huc hu hR ht htt' huR
    _ = (2 * Real.sqrt (t' - t) / Real.sqrt ν) * R ^ 2 :=
      integral_criticalMildPathMajorant_tail ν R t t' hν htt'

/-- For a fixed integration time, every literal output coordinate of the
positive-lag nonlinear heat integrand is continuous in observation time. -/
theorem continuous_heatRegularizedSpectralOutputFiber_observation
    (ν s : ℝ) (u : ℝ → WeightedLatticeBanach) (k : LatticeMode) :
    Continuous fun t : ℝ =>
      heatRegularizedSpectralOutputFiber ν (t - s) k (u s) (u s) := by
  exact (continuous_heatRegularizedSpectralOutputFiber_apply ν k (u s) (u s)).comp
    (continuous_id.sub continuous_const)

/-- On the common interval strictly before the observation time, the actual
zero-extended evolving Duhamel integrand has continuous lattice coordinates
as the observation time moves. -/
theorem continuousOn_criticalMildPathIntegrand_observation_apply
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (s : ℝ) (k : LatticeMode) :
    ContinuousOn (fun t : ℝ => criticalMildPathIntegrand ν hν u hu t s k)
      (Ioi s) := by
  apply ContinuousOn.congr
    (continuous_heatRegularizedSpectralOutputFiber_observation ν s u k).continuousOn
  intro t ht
  have hlag : 0 < t - s := sub_pos.mpr ht
  unfold criticalMildPathIntegrand
  change positiveTimeHeatRegularizedSpectralOutput ν hν (u s) (u s) (hu s)
      (t - s) k = heatRegularizedSpectralOutputFiber ν (t - s) k (u s) (u s)
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν _ _ (hu s) hlag]
  exact heatRegularizedSpectralOutput_apply
    ν (t - s) hν hlag (u s) (u s) (hu s) k

/-- Hence every common-interval coordinate has genuine pointwise observation
time convergence at every strictly positive heat lag. -/
theorem continuousAt_criticalMildPathIntegrand_observation_apply
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {s t : ℝ} (hst : s < t) (k : LatticeMode) :
    ContinuousAt (fun t' : ℝ => criticalMildPathIntegrand ν hν u hu t' s k) t :=
  (continuousOn_criticalMildPathIntegrand_observation_apply ν hν u hu s k).continuousAt
    (isOpen_Ioi.mem_nhds hst)

/-- Filter form of the common-interval pointwise convergence used by
dominated convergence: every coordinate converges as the observation time
approaches a strictly later target time. -/
theorem tendsto_criticalMildPathIntegrand_observation_apply
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {s t : ℝ} (hst : s < t) (k : LatticeMode) :
    Filter.Tendsto (fun t' : ℝ => criticalMildPathIntegrand ν hν u hu t' s k)
      (𝓝 t) (𝓝 (criticalMildPathIntegrand ν hν u hu t s k)) :=
  (continuousAt_criticalMildPathIntegrand_observation_apply ν hν u hu hst k).tendsto

/-- Uniform positive-lag domination for the singular scalar: on a
neighborhood with lag at least `δ / 2`, the inverse square root is bounded by
the fixed value at `δ / 2`. -/
theorem inverseSqrtTime_le_of_half_delta_le
    {δ τ : ℝ} (hδ : 0 < δ) (hτ : δ / 2 ≤ τ) :
    inverseSqrtTime τ ≤ inverseSqrtTime (δ / 2) := by
  unfold inverseSqrtTime
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hτ (by norm_num)

/-- The full-pair output majorant is uniformly dominated on every positive
lag neighborhood by its value at the lower lag `δ / 2`. -/
theorem outputHeatPairMajorant_le_of_half_delta_le
    (ν δ τ : ℝ) (hν : 0 < ν) (hδ : 0 < δ) (hτ : δ / 2 ≤ τ)
    (u v : WeightedLatticeBanach) (ij : LatticeMode × LatticeMode) :
    outputHeatPairMajorant ν τ u v ij ≤ outputHeatPairMajorant ν (δ / 2) u v ij := by
  have hτ0 : 0 < τ := lt_of_lt_of_le (by linarith) hτ
  have hδ2 : 0 < δ / 2 := by linarith
  have hscalar : (Real.sqrt (ν * τ))⁻¹ ≤ (Real.sqrt (ν * (δ / 2)))⁻¹ := by
    rw [outputHeatGain_eq_inverseSqrtTime ν τ hν hτ0,
      outputHeatGain_eq_inverseSqrtTime ν (δ / 2) hν hδ2]
    exact mul_le_mul_of_nonneg_left
      (inverseSqrtTime_le_of_half_delta_le hδ hτ)
      (inv_nonneg.mpr (Real.sqrt_nonneg _))
  unfold outputHeatPairMajorant latticeWeightedAmplitude
  have ha : 0 ≤ latticeModeWeight ij.1 *
      complexEuclideanNorm (weightedLatticeCoefficient u ij.1) :=
    mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight ij.1)) (norm_nonneg _)
  have hb : 0 ≤ latticeModeWeight ij.2 *
      complexEuclideanNorm (weightedLatticeCoefficient v ij.2) :=
    mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight ij.2)) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscalar ha) hb

/-- Reindexing the uniform pair estimate gives a summable uniform bound on
every actual output coordinate. -/
theorem outputHeatFiberMajorant_le_of_half_delta_le
    (ν δ τ : ℝ) (hν : 0 < ν) (hδ : 0 < δ) (hτ : δ / 2 ≤ τ)
    (u v : WeightedLatticeBanach) (k : LatticeMode) :
    outputHeatFiberMajorant ν τ u v k ≤
      outputHeatFiberMajorant ν (δ / 2) u v k := by
  unfold outputHeatFiberMajorant
  exact Summable.tsum_le_tsum
    (fun ij => outputHeatPairMajorant_le_of_half_delta_le
      ν δ τ hν hδ hτ u v ij.1)
    ((summable_outputHeatPairMajorant ν τ u v).subtype _)
    ((summable_outputHeatPairMajorant ν (δ / 2) u v).subtype _)

/-- The completed output-frequency heat carrier is exactly the `tsum` of its
actual `lp.single` output coordinates. -/
theorem tsum_single_heatRegularizedSpectralOutput
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    (∑' k : LatticeMode, lp.single (E := fun _ : LatticeMode => ComplexE3)
      1 k (heatRegularizedSpectralOutput ν τ hν hτ u v hu k)) =
      heatRegularizedSpectralOutput ν τ hν hτ u v hu := by
  exact (lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
    (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤)
    (heatRegularizedSpectralOutput ν τ hν hτ u v hu)).tsum_eq

/-- The `lp.single` coordinate terms used by Tannery inherit the exact
summable output-fiber majorant. -/
theorem norm_single_heatRegularizedSpectralOutput_le_outputHeatFiberMajorant
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    ‖lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
        (heatRegularizedSpectralOutput ν τ hν hτ u v hu k)‖ ≤
      outputHeatFiberMajorant ν τ u v k := by
  rw [lp.norm_single (by norm_num : 0 < (1 : ENNReal))]
  rw [heatRegularizedSpectralOutput_apply]
  rw [← constrainedHeatRegularizedFiber_eq_heatRegularizedSpectralOutputFiber
    ν τ hν hτ u v hu k]
  exact norm_constrainedHeatRegularizedFiber_le_outputHeatFiberMajorant
    ν τ hν hτ u v hu k

/-- Total zero-extended `lp.single` heat coordinate family for use with
filter-based dominated convergence. -/
def positiveTimeHeatOutputSingle
    (ν : ℝ) (hν : 0 < ν) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (k : LatticeMode) :
    ℝ → WeightedLatticeBanach := fun τ =>
  lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
    (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ k)

theorem positiveTimeHeatOutputSingle_of_pos
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    positiveTimeHeatOutputSingle ν hν u v hu k τ =
      lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
        (heatRegularizedSpectralOutput ν τ hν hτ u v hu k) := by
  unfold positiveTimeHeatOutputSingle
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν u v hu hτ]

/-- Near every strictly positive lag, the total `lp.single` family selects
the actual positive-time completed heat output coordinate. -/
theorem eventually_positiveTimeHeatOutputSingle_eq
    (ν τ₀ : ℝ) (hν : 0 < ν) (hτ₀ : 0 < τ₀)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    ∀ᶠ τ in 𝓝 τ₀, 0 < τ :=
  eventually_gt_nhds hτ₀

/-- Each total zero-extended `lp.single` coordinate converges at every
strictly positive lag to its actual heat-output coordinate. -/
theorem tendsto_positiveTimeHeatOutputSingle
    (ν τ₀ : ℝ) (hν : 0 < ν) (hτ₀ : 0 < τ₀)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    Filter.Tendsto (positiveTimeHeatOutputSingle ν hν u v hu k)
      (𝓝 τ₀) (𝓝 (positiveTimeHeatOutputSingle ν hν u v hu k τ₀)) := by
  let g : ℝ → WeightedLatticeBanach := fun τ =>
    lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
      (heatRegularizedSpectralOutputFiber ν τ k u v)
  have hg : Continuous g := by
    exact (continuous_duhamelOutputSingleLinear k).comp
      (continuous_heatRegularizedSpectralOutputFiber_apply ν k u v)
  have heq : positiveTimeHeatOutputSingle ν hν u v hu k =ᶠ[𝓝 τ₀] g := by
    filter_upwards [eventually_positiveTimeHeatOutputSingle_eq ν τ₀ hν hτ₀ u v hu k] with τ hτ
    rw [positiveTimeHeatOutputSingle_of_pos ν τ hν hτ u v hu k,
      heatRegularizedSpectralOutput_apply]
  have hbase : Filter.Tendsto g (𝓝 τ₀) (𝓝 (g τ₀)) :=
    hg.continuousAt
  have hlim := hbase.congr' heq.symm
  simpa [g, positiveTimeHeatOutputSingle_of_pos ν τ₀ hν hτ₀ u v hu k,
    heatRegularizedSpectralOutput_apply] using hlim

/-- Tannery summation of the total heat-coordinate family at a strictly
positive lag. -/
theorem tendsto_tsum_positiveTimeHeatOutputSingle
    (ν τ₀ : ℝ) (hν : 0 < ν) (hτ₀ : 0 < τ₀)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Filter.Tendsto (fun τ : ℝ => ∑' k : LatticeMode,
      positiveTimeHeatOutputSingle ν hν u v hu k τ)
      (𝓝 τ₀) (𝓝 (∑' k : LatticeMode,
        positiveTimeHeatOutputSingle ν hν u v hu k τ₀)) := by
  apply tendsto_tsum_of_dominated_convergence
    (summable_outputHeatFiberMajorant ν (τ₀ / 2) u v)
  · intro k
    exact tendsto_positiveTimeHeatOutputSingle ν τ₀ hν hτ₀ u v hu k
  · filter_upwards [eventually_ge_nhds (show τ₀ / 2 < τ₀ by linarith)] with τ hlag k
    have hτ : 0 < τ := lt_of_lt_of_le (by linarith) hlag
    rw [positiveTimeHeatOutputSingle_of_pos ν τ hν hτ u v hu k]
    exact (norm_single_heatRegularizedSpectralOutput_le_outputHeatFiberMajorant
      ν τ hν hτ u v hu k).trans
      (outputHeatFiberMajorant_le_of_half_delta_le ν τ₀ τ hν hτ₀ hlag u v k)

/-- Reconstruction of the total zero-extended completed heat output from its
`lp.single` coordinates. -/
theorem tsum_positiveTimeHeatOutputSingle
    (ν τ : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    (∑' k : LatticeMode, positiveTimeHeatOutputSingle ν hν u v hu k τ) =
      positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ := by
  exact (lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
    (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤)
    (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ)).tsum_eq

/-- Completed-carrier positive-lag continuity of the actual nonlinear heat
output, obtained by Tannery over its `lp.single` coordinates. -/
theorem tendsto_positiveTimeHeatRegularizedSpectralOutput
    (ν τ₀ : ℝ) (hν : 0 < ν) (hτ₀ : 0 < τ₀)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Filter.Tendsto (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu)
      (𝓝 τ₀) (𝓝 (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ₀)) := by
  have h := tendsto_tsum_positiveTimeHeatOutputSingle ν τ₀ hν hτ₀ u v hu
  simpa only [tsum_positiveTimeHeatOutputSingle] using h

/-- Completed-carrier pointwise observation-time convergence of the literal
evolving integrand at every common-interval integration time. -/
theorem tendsto_criticalMildPathIntegrand_observation
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {s t : ℝ} (hst : s < t) :
    Filter.Tendsto (fun t' : ℝ => criticalMildPathIntegrand ν hν u hu t' s)
      (𝓝 t) (𝓝 (criticalMildPathIntegrand ν hν u hu t s)) := by
  unfold criticalMildPathIntegrand
  have hlag : Filter.Tendsto (fun t' : ℝ => t' - s) (𝓝 t) (𝓝 (t - s)) :=
    (continuous_id.sub continuous_const).continuousAt
  exact (tendsto_positiveTimeHeatRegularizedSpectralOutput
    ν (t - s) hν (sub_pos.mpr hst) (u s) (u s) (hu s)).comp hlag

/-- On a common interval kept a positive distance `δ` from the observation
time, the literal Bochner integrals converge by a constant positive-lag
majorant. -/
theorem tendsto_integral_criticalMildPathIntegrand_truncated
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (huR : ∀ s ∈ Ioc (0 : ℝ) (t + δ / 2), ‖u s‖ ≤ R) :
    Filter.Tendsto
      (fun t' : ℝ => ∫ s in Ioc 0 (t - δ),
        criticalMildPathIntegrand ν hν u hu t' s)
      (𝓝 t)
      (𝓝 (∫ s in Ioc 0 (t - δ),
        criticalMildPathIntegrand ν hν u hu t s)) := by
  let C : ℝ := (Real.sqrt ν)⁻¹ * inverseSqrtTime (δ / 2) * R ^ 2
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C)
  · exact Filter.Eventually.of_forall fun t' =>
      (stronglyMeasurable_criticalMildPathIntegrand ν hν u huc hu t').aestronglyMeasurable
  · filter_upwards [eventually_gt_nhds (show t - δ / 2 < t by linarith)] with t' ht'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hlag : δ / 2 ≤ t' - s := by linarith [hs.2]
    have hst' : s < t' := by linarith
    have hus : ‖u s‖ ≤ R := huR s ⟨hs.1, by linarith [hs.2]⟩
    calc
      ‖criticalMildPathIntegrand ν hν u hu t' s‖ ≤
          (Real.sqrt ν)⁻¹ * inverseSqrtTime (t' - s) * R ^ 2 :=
        norm_criticalMildPathIntegrand_le_of_norm_le ν hν u hu hR hst' hus
      _ ≤ C := by
        dsimp [C]
        simpa [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (inverseSqrtTime_le_of_half_delta_le hδ hlag)
            (inv_nonneg.mpr (Real.sqrt_nonneg ν)))
          (sq_nonneg R)
  · exact integrableOn_const (s := Ioc 0 (t - δ)) measure_Ioc_lt_top.ne
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact tendsto_criticalMildPathIntegrand_observation ν hν u hu
      (by linarith [hs.2])

/-- The fixed boundary strip left after a `δ`-truncation has the same
explicit square-root budget as a moving tail. -/
theorem norm_criticalMildDuhamel_boundaryStrip_le_sqrt
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδt : δ ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    ‖criticalMildDuhamelTail ν hν u hu (t - δ) t‖ ≤
      (2 * Real.sqrt δ / Real.sqrt ν) * R ^ 2 := by
  simpa using norm_criticalMildDuhamelTail_le_sqrt_sub
    ν hν u huc hu hR (sub_nonneg.mpr hδt) (sub_le_self t hδ.le) huR

/-- Splitting the actual Duhamel integral at a common truncation time. -/
theorem criticalMildDuhamel_eq_truncated_add_tail
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R a t : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (hat : a ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    criticalMildDuhamel ν hν u hu t =
      (∫ s in Ioc 0 a, criticalMildPathIntegrand ν hν u hu t s) +
        criticalMildDuhamelTail ν hν u hu a t := by
  have hfull := integrableOn_criticalMildPathIntegrand
    ν hν u huc hu hR (le_trans ha hat) huR
  have hleft : IntegrableOn (criticalMildPathIntegrand ν hν u hu t) (Ioc 0 a) volume :=
    hfull.mono_set (Ioc_subset_Ioc_right hat)
  have hright : IntegrableOn (criticalMildPathIntegrand ν hν u hu t) (Ioc a t) volume :=
    hfull.mono_set (fun s hs => ⟨lt_of_le_of_lt ha hs.1, hs.2⟩)
  have hleft' : IntervalIntegrable (criticalMildPathIntegrand ν hν u hu t) volume 0 a :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mpr hleft
  have hright' : IntervalIntegrable (criticalMildPathIntegrand ν hν u hu t) volume a t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hat).mpr hright
  unfold criticalMildDuhamel criticalMildDuhamelTail
  rw [← intervalIntegral.integral_of_le (le_trans ha hat),
    ← intervalIntegral.integral_of_le ha,
    ← intervalIntegral.integral_of_le hat]
  exact (intervalIntegral.integral_add_adjacent_intervals hleft' hright').symm

/-- Metric epsilon--delta gluing for a family of common-interval
approximants.  The two error terms may be controlled by any scalar budget
which can be made arbitrarily small by taking a positive cutoff small. -/
theorem tendsto_of_truncated_gluing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (G : ℝ → ℝ → E) (t : ℝ) (B : ℝ → ℝ)
    (hG : ∀ δ, 0 < δ → Filter.Tendsto (G δ) (𝓝 t) (𝓝 (G δ t)))
    (hnear : ∀ δ, 0 < δ → ∀ᶠ t' in 𝓝 t, ‖F t' - G δ t'‖ ≤ B δ)
    (hbase : ∀ δ, 0 < δ → ‖F t - G δ t‖ ≤ B δ)
    (hsmall : ∀ ε > 0, ∃ δ > 0, B δ < ε) :
    Filter.Tendsto F (𝓝 t) (𝓝 (F t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hB⟩ := hsmall (ε / 3) (by linarith)
  have hcommon : ∀ᶠ t' in 𝓝 t, dist (G δ t') (G δ t) < ε / 3 :=
    (Metric.tendsto_nhds.mp (hG δ hδ)) (ε / 3) (by linarith)
  filter_upwards [hnear δ hδ, hcommon] with t' ht' hcommon'
  have hcommon'' : ‖G δ t' - G δ t‖ < ε / 3 := by
    simpa [dist_eq_norm_sub] using hcommon'
  have hbase' : ‖G δ t - F t‖ ≤ B δ := by
    simpa [norm_sub_rev] using hbase δ hδ
  calc
    dist (F t') (F t) = ‖F t' - F t‖ := dist_eq_norm_sub _ _
    _ = ‖(F t' - G δ t') + (G δ t' - G δ t) + (G δ t - F t)‖ := by
      congr 1
      abel
    _ ≤ ‖(F t' - G δ t') + (G δ t' - G δ t)‖ + ‖G δ t - F t‖ :=
      norm_add_le _ _
    _ ≤ (‖F t' - G δ t'‖ + ‖G δ t' - G δ t‖) + ‖G δ t - F t‖ := by
      gcongr
      exact norm_add_le _ _
    _ < ε := by linarith

/-- A nonnegative square-root tail budget can always be made smaller than a
prescribed positive epsilon. -/
theorem exists_pos_mul_sqrt_lt
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ > 0, C * Real.sqrt δ < ε := by
  let q : ℝ := ε / (C + 1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  refine ⟨q ^ 2, sq_pos_of_pos hq, ?_⟩
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
  dsimp [q]
  have hden : 0 < C + 1 := by linarith
  have hlt : C / (C + 1) < 1 := (div_lt_one hden).mpr (by linarith)
  calc
    C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
    _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
    _ = ε := mul_one _

end Navier.Analysis.CriticalMildObservationContinuity

#print axioms Navier.Analysis.CriticalMildObservationContinuity.integrableOn_criticalMildDuhamelTailIntegrand
#print axioms Navier.Analysis.CriticalMildObservationContinuity.norm_criticalMildDuhamelTail_le
