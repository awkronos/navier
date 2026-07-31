import Navier.Analysis.CriticalMildHeatFlow

/-!
# Time-dependent critical mild Duhamel integrand

The earlier completed Bochner integral accepts two fixed carrier elements.
The mild equation instead evaluates the nonlinear transport on the evolving
path at the integration time.  This file introduces that literal object and
connects it to the already checked inverse-square-root estimate.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildPathIntegrand

open MeasureTheory Set Topology
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildHeatTimeKernel
open Navier.Analysis.CriticalMildDuhamelBochner

/-- The literal path-dependent nonlinear integrand at observation time `t`
and integration time `s`, with heat lag `t-s`. -/
def criticalMildPathIntegrand
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t s : ℝ) : WeightedLatticeBanach :=
  positiveTimeHeatRegularizedSpectralOutput ν hν
    (u s) (u s) (hu s) (t - s)

/-- Decoding a positive-time completed nonlinear output recovers its literal
heat--Leray coefficient. -/
theorem weightedLatticeCoefficient_heatRegularizedSpectralOutput
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (m : LatticeMode) :
    weightedLatticeCoefficient
        (heatRegularizedSpectralOutput ν τ hν hτ u v hu) m =
      complexFrequencyHeatLeray ν τ (latticeFrequency m)
        (spectralOutputCoefficient m u v) := by
  unfold weightedLatticeCoefficient
  rw [heatRegularizedSpectralOutput_apply]
  unfold heatRegularizedSpectralOutputFiber
  rw [smul_smul]
  have hm : latticeModeWeight m ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m))
  rw [inv_mul_cancel₀ hm, one_smul]
  exact WithLp.ofLp_toLp _ _

/-- Every positive-time completed nonlinear output is divergence-free because
the actual output frequency passes through the Leray multiplier. -/
theorem heatRegularizedSpectralOutput_divergenceFree
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    LatticeDivergenceFree
      (heatRegularizedSpectralOutput ν τ hν hτ u v hu) := by
  intro m
  rw [weightedLatticeCoefficient_heatRegularizedSpectralOutput]
  exact complexFrequencyHeatLeray_hermitian_transverse ν τ (latticeFrequency m)
    (spectralOutputCoefficient m u v)

/-- The zero-extended nonlinear output remains divergence-free at every real
heat lag. -/
theorem positiveTimeHeatRegularizedSpectralOutput_divergenceFree
    (ν : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (τ : ℝ) :
    LatticeDivergenceFree
      (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ) := by
  by_cases hτ : 0 < τ
  · rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν u v hu hτ]
    exact heatRegularizedSpectralOutput_divergenceFree ν τ hν hτ u v hu
  · intro m
    have hz :
        positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ = 0 := by
      simp [positiveTimeHeatRegularizedSpectralOutput, hτ]
    rw [hz]
    have hpoint : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
      ext j
      rfl
    rw [show weightedLatticeCoefficient (0 : WeightedLatticeBanach) m =
        (0 : ComplexSpace) by
          simp [weightedLatticeCoefficient],
      hpoint, inner_zero_right]

/-- The literal evolving-path integrand is divergence-free pointwise. -/
theorem criticalMildPathIntegrand_divergenceFree
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t s : ℝ) :
    LatticeDivergenceFree (criticalMildPathIntegrand ν hν u hu t s) := by
  exact positiveTimeHeatRegularizedSpectralOutput_divergenceFree
    ν hν (u s) (u s) (hu s) (t - s)

/-- Every output coordinate of the untruncated heat-regularized nonlinear
fiber varies continuously when the carrier path does. -/
theorem continuous_heatRegularizedSpectralOutputFiber_path
    (ν t : ℝ) (u : ℝ → WeightedLatticeBanach)
    (hu : Continuous u) (k : LatticeMode) :
    Continuous fun s =>
      heatRegularizedSpectralOutputFiber ν (t - s) k (u s) (u s) := by
  unfold heatRegularizedSpectralOutputFiber spectralOutputCoefficient
  change Continuous fun s =>
    latticeModeWeight k • complexEuclideanPoint
      (complexFrequencyHeatLeray ν (t - s) (latticeFrequency k)
        (WithLp.ofLp (weightedLatticeSpectralBilinear k (u s) (u s))))
  have hheat : Continuous fun s =>
      complexFrequencyHeatLeray ν (t - s) (latticeFrequency k)
        (WithLp.ofLp (weightedLatticeSpectralBilinear k (u s) (u s))) := by
    rw [show (fun s =>
        complexFrequencyHeatLeray ν (t - s) (latticeFrequency k)
          (WithLp.ofLp (weightedLatticeSpectralBilinear k (u s) (u s)))) =
      fun s => (complexHeatDecay ν (t - s) (latticeFrequency k) : ℂ) •
        complexLeray (latticeFrequency k)
          (WithLp.ofLp (weightedLatticeSpectralBilinear k (u s) (u s))) by
        funext s
        exact complexFrequencyHeatLeray_apply ν (t - s) (latticeFrequency k) _]
    have hspectral : Continuous fun s =>
        WithLp.ofLp (weightedLatticeSpectralBilinear k (u s) (u s)) := by
      fun_prop
    have hleray : Continuous fun s =>
        complexLeray (latticeFrequency k)
          (WithLp.ofLp (weightedLatticeSpectralBilinear k (u s) (u s))) :=
      (LinearMap.continuous_of_finiteDimensional
        (complexLeray (latticeFrequency k))).comp hspectral
    have hdecay : Continuous fun s =>
        (complexHeatDecay ν (t - s) (latticeFrequency k) : ℂ) := by
      unfold complexHeatDecay heatDecay
      fun_prop
    exact hdecay.smul hleray
  exact (CriticalMildHeatBochner.continuous_complexEuclideanPoint.comp hheat).const_smul _

/-- Each lattice coordinate of the zero-extended evolving-path integrand is
strongly measurable for a continuous path. -/
theorem stronglyMeasurable_criticalMildPathIntegrand_apply
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) (k : LatticeMode) :
    StronglyMeasurable fun s => criticalMildPathIntegrand ν hν u hu t s k := by
  have hpiece : (fun s =>
      criticalMildPathIntegrand ν hν u hu t s k) =
      Set.piecewise (Iio t)
        (fun s => heatRegularizedSpectralOutputFiber ν (t - s) k (u s) (u s))
        (fun _ => 0) := by
    funext s
    by_cases hst : s < t
    · have hlag : 0 < t - s := sub_pos.mpr hst
      simp only [Set.piecewise, Set.mem_Iio, hst, ↓reduceIte]
      unfold criticalMildPathIntegrand
      rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν _ _ (hu s) hlag,
        heatRegularizedSpectralOutput_apply]
    · simp [criticalMildPathIntegrand,
        positiveTimeHeatRegularizedSpectralOutput, hst]
  rw [hpiece]
  exact
    (continuous_heatRegularizedSpectralOutputFiber_path ν t u huc k).stronglyMeasurable.piecewise
      measurableSet_Iio stronglyMeasurable_const

/-- Finite-coordinate approximants to the evolving-path integrand. -/
def criticalMildPathIntegrandNatTruncation
    (n : ℕ) (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) : ℝ → WeightedLatticeBanach := fun s =>
  ∑ j ∈ Finset.range n,
    duhamelOutputSingleLinear (CriticalMildHeatBochner.latticeModeEquivNat.symm j)
      (criticalMildPathIntegrand ν hν u hu t s
        (CriticalMildHeatBochner.latticeModeEquivNat.symm j))

/-- Every finite-coordinate evolving-path approximant is strongly measurable. -/
theorem stronglyMeasurable_criticalMildPathIntegrandNatTruncation
    (n : ℕ) (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) :
    StronglyMeasurable
      (criticalMildPathIntegrandNatTruncation n ν hν u hu t) := by
  unfold criticalMildPathIntegrandNatTruncation
  let f : ℕ → ℝ → WeightedLatticeBanach := fun j s =>
    duhamelOutputSingleLinear (CriticalMildHeatBochner.latticeModeEquivNat.symm j)
      (criticalMildPathIntegrand ν hν u hu t s
        (CriticalMildHeatBochner.latticeModeEquivNat.symm j))
  change StronglyMeasurable fun s => ∑ j ∈ Finset.range n, f j s
  have hsum : StronglyMeasurable (∑ j ∈ Finset.range n, f j) :=
    Finset.stronglyMeasurable_sum _ (fun j _ => by
      apply (continuous_duhamelOutputSingleLinear _).comp_stronglyMeasurable
      exact stronglyMeasurable_criticalMildPathIntegrand_apply
        ν hν u huc hu t _)
  have heq : (fun s => ∑ j ∈ Finset.range n, f j s) =
      ∑ j ∈ Finset.range n, f j := by
    funext s
    simp
  rw [heq]
  exact hsum

/-- The finite-coordinate approximants converge pointwise in the completed
critical norm to the literal evolving-path integrand. -/
theorem tendsto_criticalMildPathIntegrandNatTruncation
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t s : ℝ) :
    Filter.Tendsto
      (fun n => criticalMildPathIntegrandNatTruncation n ν hν u hu t s)
      Filter.atTop (𝓝 (criticalMildPathIntegrand ν hν u hu t s)) := by
  unfold criticalMildPathIntegrandNatTruncation criticalMildPathIntegrand
  exact tendsto_positiveTimeHeatRegularizedSpectralOutputNatTruncation
    ν hν (u s) (u s) (hu s) (t - s)

/-- The full completed evolving-path integrand is strongly measurable for
every continuous divergence-free path. -/
theorem stronglyMeasurable_criticalMildPathIntegrand
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) :
    StronglyMeasurable (criticalMildPathIntegrand ν hν u hu t) := by
  apply stronglyMeasurable_of_tendsto
    (f := fun n => criticalMildPathIntegrandNatTruncation n ν hν u hu t)
    Filter.atTop
  · intro n
    exact stronglyMeasurable_criticalMildPathIntegrandNatTruncation
      n ν hν u huc hu t
  · rw [tendsto_pi_nhds]
    intro s
    exact tendsto_criticalMildPathIntegrandNatTruncation ν hν u hu t s

private theorem norm_criticalMildPathIntegrand_le_of_norm_le_pre
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t s : ℝ} (hR : 0 ≤ R) (hst : s ≤ t)
    (huR : ‖u s‖ ≤ R) :
    ‖criticalMildPathIntegrand ν hν u hu t s‖ ≤
      (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * R ^ 2 := by
  rcases hst.eq_or_lt with hst | hst
  · subst t
    simp [criticalMildPathIntegrand,
      positiveTimeHeatRegularizedSpectralOutput, inverseSqrtTime]
  · unfold criticalMildPathIntegrand
    have hlag : 0 < t - s := sub_pos.mpr hst
    have h := norm_positiveTimeHeatRegularizedSpectralOutput_le
      ν hν (u s) (u s) (hu s) hlag
    have hcoef :
        0 ≤ (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) := by
      exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)
    calc
      ‖positiveTimeHeatRegularizedSpectralOutput ν hν
          (u s) (u s) (hu s) (t - s)‖ ≤
        (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * ‖u s‖ * ‖u s‖ := by
          simpa [duhamelHeatTimeMajorant] using h
      _ = (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * ‖u s‖ ^ 2 := by
        ring
      _ ≤ (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * R ^ 2 :=
        mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ (norm_nonneg _) hR).2 huR) hcoef

/-- The uniform-radius scalar majorant for the evolving-path integrand. -/
def criticalMildPathMajorant (ν R t : ℝ) : ℝ → ℝ := fun s =>
  (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * R ^ 2

/-- The evolving-path scalar majorant is integrable on every finite
nonnegative horizon. -/
theorem intervalIntegrable_criticalMildPathMajorant
    (ν R t : ℝ) :
    IntervalIntegrable (criticalMildPathMajorant ν R t) volume 0 t := by
  unfold criticalMildPathMajorant
  have hlag : IntervalIntegrable
      (fun s => inverseSqrtTime (t - s)) volume t 0 := by
    simpa using (inverseSqrtTime_intervalIntegrable t).comp_sub_left t
  exact ((hlag.symm.const_mul _).mul_const _)

/-- A continuous divergence-free path uniformly bounded by `R` has an actual
Bochner-integrable nonlinear Duhamel integrand on `[0,t]`. -/
theorem integrableOn_criticalMildPathIntegrand
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    IntegrableOn (criticalMildPathIntegrand ν hν u hu t) (Ioc 0 t) volume := by
  have hmajorant := intervalIntegrable_criticalMildPathMajorant ν R t
  have hinterval : IntervalIntegrable
      (criticalMildPathIntegrand ν hν u hu t) volume 0 t :=
    IntervalIntegrable.mono_fun' hmajorant
      (stronglyMeasurable_criticalMildPathIntegrand ν hν u huc hu t).aestronglyMeasurable
      (by
        rw [uIoc_of_le ht]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact norm_criticalMildPathIntegrand_le_of_norm_le_pre
          ν hν u hu hR hs.2 (huR s hs))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hinterval

/-- Continuous coordinate decoding into the Hermitian Euclidean carrier. -/
def weightedLatticePointCLM (m : LatticeMode) :
    WeightedLatticeBanach →L[ℂ] ComplexE3 :=
  LinearMap.mkContinuous
    { toFun := fun u => complexEuclideanPoint (weightedLatticeCoefficient u m)
      map_add' := fun u v => by
        rw [show weightedLatticeCoefficient (u + v) m =
            weightedLatticeCoefficient u m + weightedLatticeCoefficient v m by
          exact congrFun (weightedLatticeCoefficient_add u v) m]
        ext j
        rfl
      map_smul' := fun c u => by
        rw [show weightedLatticeCoefficient (c • u) m =
            c • weightedLatticeCoefficient u m by
          exact congrFun (weightedLatticeCoefficient_smul c u) m]
        ext j
        rfl }
    1
    (fun u => by
      have hw : 1 ≤ latticeModeWeight m := one_le_latticeModeWeight m
      have hn : 0 ≤ ‖complexEuclideanPoint (weightedLatticeCoefficient u m)‖ :=
        norm_nonneg _
      calc
        ‖complexEuclideanPoint (weightedLatticeCoefficient u m)‖ ≤
            latticeModeWeight m *
              ‖complexEuclideanPoint (weightedLatticeCoefficient u m)‖ := by
          nlinarith
        _ = ‖u m‖ := by
          simpa [latticeWeightedAmplitude, complexEuclideanNorm] using
            latticeWeightedAmplitude_coefficient u m
        _ ≤ ‖u‖ := norm_weightedLattice_eval_le u m
        _ = 1 * ‖u‖ := by ring)

/-- The continuous linear divergence functional at one lattice mode. -/
def latticeDivergenceCLM (m : LatticeMode) :
    WeightedLatticeBanach →L[ℂ] ℂ :=
  (innerSL ℂ (complexFrequency (latticeFrequency m))).comp
    (weightedLatticePointCLM m)

/-- The genuine time-dependent nonlinear Duhamel integral. -/
def criticalMildDuhamel
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) : WeightedLatticeBanach :=
  ∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hu t s

/-- The actual time-dependent nonlinear Duhamel integral remains in the
divergence-free subspace. -/
theorem criticalMildDuhamel_divergenceFree
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    LatticeDivergenceFree (criticalMildDuhamel ν hν u hu t) := by
  intro m
  have hint :=
    integrableOn_criticalMildPathIntegrand ν hν u huc hu hR ht huR
  change latticeDivergenceCLM m
      (∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hu t s) = 0
  rw [← (latticeDivergenceCLM m).integral_comp_comm hint]
  have hz : (fun s =>
      latticeDivergenceCLM m (criticalMildPathIntegrand ν hν u hu t s)) =
      fun _ => 0 := by
    funext s
    exact criticalMildPathIntegrand_divergenceFree ν hν u hu t s m
  rw [hz, integral_zero]

/-- The actual time-dependent Duhamel integral satisfies the expected
quadratic `O(sqrt t)` estimate on a radius-`R` path ball. -/
theorem norm_criticalMildDuhamel_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    ‖criticalMildDuhamel ν hν u hu t‖ ≤
      (2 * Real.sqrt t / Real.sqrt ν) * R ^ 2 := by
  have hactual :=
    integrableOn_criticalMildPathIntegrand ν hν u huc hu hR ht huR
  have hscalar :
      IntegrableOn (criticalMildPathMajorant ν R t) (Ioc 0 t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp
      (intervalIntegrable_criticalMildPathMajorant ν R t)
  have hmono :
      (fun s => ‖criticalMildPathIntegrand ν hν u hu t s‖) ≤ᵐ[
        volume.restrict (Ioc 0 t)] criticalMildPathMajorant ν R t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact norm_criticalMildPathIntegrand_le_of_norm_le_pre
      ν hν u hu hR hs.2 (huR s hs)
  unfold criticalMildDuhamel
  calc
    ‖∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hu t s‖ ≤
        ∫ s in Ioc 0 t, ‖criticalMildPathIntegrand ν hν u hu t s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc 0 t, criticalMildPathMajorant ν R t s :=
      integral_mono_ae hactual.norm hscalar hmono
    _ = ∫ s in (0 : ℝ)..t, criticalMildPathMajorant ν R t s := by
      rw [← intervalIntegral.integral_of_le ht]
    _ = (2 * Real.sqrt t / Real.sqrt ν) * R ^ 2 := by
      unfold criticalMildPathMajorant
      rw [show (fun s : ℝ =>
          (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * R ^ 2) =
        fun s => (Real.sqrt ν)⁻¹ *
          (inverseSqrtTime (t - s) * R ^ 2) by
            funext s
            ring,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_comp_sub_left,
        sub_self, sub_zero,
        integral_inverseSqrtTime_zero t ht]
      field_simp [ne_of_gt hν]

/-- The actual evolving nonlinear Duhamel integral is continuous at the
initial observation time from the nonnegative time side.  This uses the
literal Bochner integral and its checked `O(sqrt t)` bound, not a continuity
assumption on a payload. -/
theorem tendsto_criticalMildDuhamel_nnreal_zero
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R : ℝ} (hR : 0 ≤ R) (huR : ∀ s, ‖u s‖ ≤ R) :
    Filter.Tendsto (fun t : NNReal => criticalMildDuhamel ν hν u hu t)
      (𝓝 0) (𝓝 0) := by
  apply squeeze_zero_norm (a := fun t : NNReal =>
    (2 * Real.sqrt (t : ℝ) / Real.sqrt ν) * R ^ 2)
  · intro t
    exact norm_criticalMildDuhamel_le ν hν u huc hu hR t.2
      (fun s _ => huR s)
  · have hcont : Continuous fun t : NNReal =>
        (2 * Real.sqrt (t : ℝ) / Real.sqrt ν) * R ^ 2 := by
      fun_prop
    simpa using hcont.tendsto 0

/-- Before the observation time, the actual path-dependent integrand obeys
the checked inverse-square-root heat-lag majorant. -/
theorem norm_criticalMildPathIntegrand_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s < t) :
    ‖criticalMildPathIntegrand ν hν u hu t s‖ ≤
      (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * ‖u s‖ ^ 2 := by
  unfold criticalMildPathIntegrand
  have hlag : 0 < t - s := sub_pos.mpr hst
  have h := norm_positiveTimeHeatRegularizedSpectralOutput_le
    ν hν (u s) (u s) (hu s) hlag
  calc
    ‖positiveTimeHeatRegularizedSpectralOutput ν hν
        (u s) (u s) (hu s) (t - s)‖ ≤
      (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * ‖u s‖ * ‖u s‖ := by
        simpa [duhamelHeatTimeMajorant] using h
    _ = (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * ‖u s‖ ^ 2 := by
      ring

/-- A uniform radius bound on the evolving path gives the corresponding
quadratic heat-lag majorant. -/
theorem norm_criticalMildPathIntegrand_le_of_norm_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t s : ℝ} (hR : 0 ≤ R) (hst : s < t)
    (huR : ‖u s‖ ≤ R) :
    ‖criticalMildPathIntegrand ν hν u hu t s‖ ≤
      (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) * R ^ 2 := by
  have hbase := norm_criticalMildPathIntegrand_le ν hν u hu hst
  have hcoef :
      0 ≤ (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) := by
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)
  exact hbase.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) hR).2 huR) hcoef)

end Navier.Analysis.CriticalMildPathIntegrand

#print axioms Navier.Analysis.CriticalMildPathIntegrand.norm_criticalMildPathIntegrand_le
#print axioms Navier.Analysis.CriticalMildPathIntegrand.norm_criticalMildPathIntegrand_le_of_norm_le
#print axioms Navier.Analysis.CriticalMildPathIntegrand.continuous_heatRegularizedSpectralOutputFiber_path
#print axioms Navier.Analysis.CriticalMildPathIntegrand.stronglyMeasurable_criticalMildPathIntegrand
#print axioms Navier.Analysis.CriticalMildPathIntegrand.integrableOn_criticalMildPathIntegrand
#print axioms Navier.Analysis.CriticalMildPathIntegrand.criticalMildDuhamel_divergenceFree
#print axioms Navier.Analysis.CriticalMildPathIntegrand.norm_criticalMildDuhamel_le
#print axioms Navier.Analysis.CriticalMildPathIntegrand.tendsto_criticalMildDuhamel_nnreal_zero
