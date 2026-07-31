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

end Navier.Analysis.CriticalMildObservationContinuity

#print axioms Navier.Analysis.CriticalMildObservationContinuity.integrableOn_criticalMildDuhamelTailIntegrand
#print axioms Navier.Analysis.CriticalMildObservationContinuity.norm_criticalMildDuhamelTail_le
