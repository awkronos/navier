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
