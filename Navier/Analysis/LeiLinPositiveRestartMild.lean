import Navier.Analysis.LeiLinPositiveRestartFourier

/-!
# Direct positive-lag smoothing for the literal mild integrand

The nonlinear heat output has a half-generator graph value at every strictly
positive lag, without assuming graph regularity of either input: split the lag
in half and use the heat semigroup once more.  For an evolving mild path this
gives pointwise graph membership of every strict-time Duhamel integrand.

The corresponding carrier-radius estimate has the sharp inverse-time order
`2 / (ν τ)`.  Its scalar majorant is not locally integrable at `τ = 0`, so this
pointwise smoothing cannot be passed through the terminal Bochner integral by
dominated convergence from the fixed-point radius bound alone.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Topology

namespace Navier.Analysis.LeiLinPositiveRestartMild

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.LeiLinTimeMixed

/-- **Actual positive-lag nonlinear smoothing.**  The literal completed
nonlinear output is in the half-generator domain at every positive heat lag,
with no graph hypothesis on its inputs. -/
theorem summable_halfGeneratorMoment_heatRegularizedSpectralOutput_of_positiveLag
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu m‖ := by
  let a : ℝ := τ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let z := heatRegularizedSpectralOutput ν a hν ha u v hu
  have hz : LatticeDivergenceFree z :=
    heatRegularizedSpectralOutput_divergenceFree ν a hν ha u v hu
  have hsemigroup := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha u v hu
  have haa : a + a = τ := by dsimp [a]; ring
  have hsemigroup' : weightedHeatFlow ν a hν.le ha.le z =
      heatRegularizedSpectralOutput ν τ hν hτ u v hu := by
    dsimp [z]
    simpa only [haa] using hsemigroup
  rw [← hsemigroup']
  exact summable_halfGeneratorMoment_weightedHeatFlow ν a hν ha z hz

/-- Every strict-time value of the literal evolving Duhamel integrand has a
finite graph moment, even when the source path value is known only in the base
critical carrier. -/
theorem summable_halfGeneratorMoment_criticalMildPathIntegrand_of_strictTime
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s < t) :
    Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖criticalMildPathIntegrand ν hν u hu t s m‖ := by
  have hlag : 0 < t - s := sub_pos.mpr hst
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
    ν hν (u s) (u s) (hu s) hlag]
  exact
    summable_halfGeneratorMoment_heatRegularizedSpectralOutput_of_positiveLag
      ν (t - s) hν hlag (u s) (u s) (hu s)

/-- The strongest carrier-radius graph estimate for the actual path integrand
has inverse-time order. -/
theorem heatHalfGeneratorMoment_criticalMildPathIntegrand_le_radius
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t s : ℝ} (hR : 0 ≤ R) (hst : s < t)
    (huR : ‖u s‖ ≤ R) :
    heatHalfGeneratorMoment (criticalMildPathIntegrand ν hν u hu t s) ≤
      (2 / (ν * (t - s))) * R ^ 2 := by
  have hlag : 0 < t - s := sub_pos.mpr hst
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
    ν hν (u s) (u s) (hu s) hlag]
  have hbase := heatHalfGeneratorMoment_heatRegularizedSpectralOutput_le
    ν (t - s) hν hlag (u s) (u s) (hu s)
  have hcoef : 0 ≤ 2 / (ν * (t - s)) := by positivity
  have hsq : ‖u s‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (u s)]
  calc
    heatHalfGeneratorMoment
        (heatRegularizedSpectralOutput ν (t - s) hν hlag
          (u s) (u s) (hu s)) ≤
      (2 / (ν * (t - s))) * ‖u s‖ * ‖u s‖ := hbase
    _ = (2 / (ν * (t - s))) * ‖u s‖ ^ 2 := by ring
    _ ≤ (2 / (ν * (t - s))) * R ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoef

/-- The inverse-time radius majorant exposed by the literal nonlinear heat
estimate is not locally integrable at zero.  This holds for every positive
viscosity, nonzero radius, and positive lag window. -/
theorem not_intervalIntegrable_nonlinearRadiusHalfMomentMajorant
    {ν R δ : ℝ} (hν : 0 < ν) (hR : 0 < R) (hδ : 0 < δ) :
    ¬ IntervalIntegrable
      (fun τ : ℝ => (2 / (ν * τ)) * R ^ 2) volume 0 δ := by
  let c : ℝ := 2 * R ^ 2 / ν
  have hc : 0 < c := by dsimp [c]; positivity
  intro hmajor
  have heq : Set.EqOn
      (fun τ : ℝ => (2 / (ν * τ)) * R ^ 2)
      (fun τ : ℝ => c * τ⁻¹) (Set.uIoo (0 : ℝ) δ) := by
    intro τ hτ
    have hτmem : τ ∈ Set.Ioo (0 : ℝ) δ := by
      simpa [Set.uIoo_of_le hδ.le] using hτ
    have hτpos : 0 < τ := by
      exact hτmem.1
    dsimp [c]
    field_simp [hν.ne', hτpos.ne']
  have hcmajor : IntervalIntegrable (fun τ : ℝ => c * τ⁻¹) volume 0 δ :=
    hmajor.congr_uIoo heq
  have hscaled := hcmajor.const_mul c⁻¹
  have hinv : IntervalIntegrable (fun τ : ℝ => τ⁻¹) volume 0 δ := by
    apply hscaled.congr
    intro τ _hτ
    change c⁻¹ * (c * τ⁻¹) = τ⁻¹
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  exact not_intervalIntegrable_inverseTime_zero hδ hinv

end Navier.Analysis.LeiLinPositiveRestartMild

#print axioms Navier.Analysis.LeiLinPositiveRestartMild.summable_halfGeneratorMoment_heatRegularizedSpectralOutput_of_positiveLag
#print axioms Navier.Analysis.LeiLinPositiveRestartMild.summable_halfGeneratorMoment_criticalMildPathIntegrand_of_strictTime
#print axioms Navier.Analysis.LeiLinPositiveRestartMild.heatHalfGeneratorMoment_criticalMildPathIntegrand_le_radius
#print axioms Navier.Analysis.LeiLinPositiveRestartMild.not_intervalIntegrable_nonlinearRadiusHalfMomentMajorant
