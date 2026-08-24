import Navier.Analysis.LeiLinPositiveRestartMild

/-!
# Endpoint cancellation exposed by freezing the nonlinear source

The radius-only estimate for a positive-lag nonlinear output has the
nonintegrable order `1 / τ`.  Subtracting a frozen endpoint value exposes the
smallest genuine cancellation available from time regularity: the same kernel
is multiplied by the carrier increment `‖u - v‖`.

Endpoint convergence alone still does not make the resulting Dini sum finite.
A checked harmonic sequence witness below isolates the exact missing input:
summability of endpoint-modulus samples over logarithmic time scales, not just
convergence of those samples to zero.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Topology

namespace Navier.Analysis.LeiLinPositiveRestartCancellation

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildHeatTimeKernel
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.LeiLinTimeMixed

/-- **Frozen-source cancellation at one positive lag.**  The graph moment of
the difference of two literal nonlinear heat outputs gains the carrier
increment of the inputs.  This is the time-frequency estimate that the raw
radius bound discards. -/
theorem heatHalfGeneratorMoment_heatRegularizedSpectralOutput_sub_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v) :
    heatHalfGeneratorMoment
        (heatRegularizedSpectralOutput ν τ hν hτ u u hu -
          heatRegularizedSpectralOutput ν τ hν hτ v v hv) ≤
      (2 / (ν * τ)) * (‖u‖ + ‖v‖) * ‖u - v‖ := by
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
  have haa : a + a = τ := by dsimp [a]; ring
  have hsemu := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha u u hu
  have hsemv := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha v v hv
  have hsemigroup : weightedHeatFlow ν a hν.le ha.le z =
      heatRegularizedSpectralOutput ν τ hν hτ u u hu -
        heatRegularizedSpectralOutput ν τ hν hτ v v hv := by
    dsimp [z, zu, zv]
    rw [← weightedHeatFlowCLM_apply,
      map_sub, weightedHeatFlowCLM_apply, weightedHeatFlowCLM_apply,
      hsemu, hsemv]
    simp only [haa]
  have hgraph := heatHalfGeneratorMoment_weightedHeatFlow_le ν a hν ha z hz
  have hdiff := norm_positiveTimeHeatRegularizedSpectralOutput_sub_le
    ν hν u v u v hu hv ha
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν u u hu ha,
    positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν v v hv ha]
      at hdiff
  have hnorm : ‖z‖ ≤ (Real.sqrt ν)⁻¹ * inverseSqrtTime a *
      (‖u‖ + ‖v‖) * ‖u - v‖ := by
    dsimp [z, zu, zv]
    calc
      ‖heatRegularizedSpectralOutput ν a hν ha u u hu -
          heatRegularizedSpectralOutput ν a hν ha v v hv‖ ≤
          (Real.sqrt ν)⁻¹ * inverseSqrtTime a *
            (‖u‖ * ‖u - v‖ + ‖u - v‖ * ‖v‖) := hdiff
      _ = (Real.sqrt ν)⁻¹ * inverseSqrtTime a *
          (‖u‖ + ‖v‖) * ‖u - v‖ := by ring
  rw [hsemigroup] at hgraph
  refine hgraph.trans (mul_le_mul_of_nonneg_left hnorm
    (inv_nonneg.mpr (Real.sqrt_nonneg _))) |>.trans ?_
  have hνa : 0 < ν * a := mul_pos hν ha
  have hkernel : (Real.sqrt ν)⁻¹ * inverseSqrtTime a =
      (Real.sqrt (ν * a))⁻¹ := by
    have h := heatTimeMajorant_eq ν a hν ha
    unfold heatTimeMajorant at h
    linarith
  have hcoef : (Real.sqrt (ν * a))⁻¹ *
      ((Real.sqrt ν)⁻¹ * inverseSqrtTime a) = 2 / (ν * τ) := by
    rw [hkernel, ← mul_inv, ← pow_two, Real.sq_sqrt hνa.le]
    dsimp [a]
    field_simp [hν.ne', hτ.ne']
  rw [← mul_assoc, ← mul_assoc, hcoef]

/-- On the actual evolving path, subtracting the nonlinear source frozen at
the observation time inserts precisely the endpoint carrier modulus. -/
theorem heatHalfGeneratorMoment_criticalMildPathIntegrand_sub_frozen_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s < t) :
    heatHalfGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s -
          heatRegularizedSpectralOutput ν (t - s) hν (sub_pos.mpr hst)
            (u t) (u t) (hu t)) ≤
      (2 / (ν * (t - s))) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖ := by
  have hlag : 0 < t - s := sub_pos.mpr hst
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
    ν hν (u s) (u s) (hu s) hlag]
  exact heatHalfGeneratorMoment_heatRegularizedSpectralOutput_sub_le
    ν (t - s) hν hlag (u s) (u t) (hu s) (hu t)

/-- The frozen source can be represented by the literal path integrand of the
constant endpoint path.  The cancellation estimate then also covers the
terminal point, where both integrands vanish by definition. -/
theorem heatHalfGeneratorMoment_criticalMildPathIntegrand_sub_constant_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s ≤ t) :
    heatHalfGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s -
          criticalMildPathIntegrand ν hν (fun _ => u t) (fun _ => hu t) t s) ≤
      (2 / (ν * (t - s))) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖ := by
  rcases hst.eq_or_lt with rfl | hst
  · simp [criticalMildPathIntegrand,
      positiveTimeHeatRegularizedSpectralOutput, heatHalfGeneratorMoment]
  · unfold criticalMildPathIntegrand
    rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
        ν hν (u s) (u s) (hu s) (sub_pos.mpr hst),
      positiveTimeHeatRegularizedSpectralOutput_of_pos
        ν hν (u t) (u t) (hu t) (sub_pos.mpr hst)]
    exact heatHalfGeneratorMoment_heatRegularizedSpectralOutput_sub_le
      ν (t - s) hν (sub_pos.mpr hst) (u s) (u t) (hu s) (hu t)

/-- A Dini-integrable endpoint modulus is sufficient for the graph moment of
the genuinely cancelling part of the Duhamel integrand.  This leaves only the
time-independent frozen-source integral, where modewise heat integration (not
absolute graph domination) must be used. -/
theorem intervalIntegrable_heatHalfGeneratorMoment_path_sub_constant_of_dini
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {a t : ℝ} (hat : a ≤ t)
    (hDini : IntervalIntegrable
      (fun s => (2 / (ν * (t - s))) * (‖u s‖ + ‖u t‖) * ‖u s - u t‖)
      volume a t) :
    IntervalIntegrable
      (fun s => heatHalfGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s -
          criticalMildPathIntegrand ν hν (fun _ => u t) (fun _ => hu t) t s))
      volume a t := by
  have hconst : Continuous (fun _ : ℝ => u t) := continuous_const
  have hmeas : Measurable
      (fun s => heatHalfGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s -
          criticalMildPathIntegrand ν hν (fun _ => u t) (fun _ => hu t) t s)) := by
    unfold heatHalfGeneratorMoment
    exact Measurable.tsum fun k => measurable_const.mul
      (((stronglyMeasurable_criticalMildPathIntegrand_apply
          ν hν u huc hu t k).sub
        (stronglyMeasurable_criticalMildPathIntegrand_apply
          ν hν (fun _ => u t) hconst (fun _ => hu t) t k)).norm.measurable)
  apply hDini.mono_fun' hmeas.aestronglyMeasurable
  rw [Set.uIoc_of_le hat]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs,
    abs_of_nonneg (heatHalfGeneratorMoment_nonneg _)]
  exact heatHalfGeneratorMoment_criticalMildPathIntegrand_sub_constant_le
    ν hν u hu hs.2

/-- **Vanishing is strictly weaker than Dini summability.**  Nonnegative
endpoint-modulus samples can converge to zero while their logarithmic-scale
sum diverges. -/
theorem exists_vanishingEndpointModulus_not_diniSummable :
    ∃ ω : ℕ → ℝ,
      (∀ n, 0 ≤ ω n) ∧
      Tendsto ω atTop (nhds 0) ∧
      ¬ Summable ω := by
  refine ⟨fun n : ℕ => ((n : ℝ) + 1)⁻¹, ?_, ?_, ?_⟩
  · intro n
    positivity
  · simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · have hp : ¬ Summable fun n : ℕ => ((n : ℝ) ^ 1)⁻¹ := by
      simpa using
        (not_congr (Real.summable_nat_pow_inv (p := 1))).2 (by norm_num)
    intro hω
    apply hp
    apply (summable_nat_add_iff 1).1
    simpa [Nat.cast_add, Nat.cast_one] using hω

end Navier.Analysis.LeiLinPositiveRestartCancellation

#print axioms Navier.Analysis.LeiLinPositiveRestartCancellation.heatHalfGeneratorMoment_heatRegularizedSpectralOutput_sub_le
#print axioms Navier.Analysis.LeiLinPositiveRestartCancellation.heatHalfGeneratorMoment_criticalMildPathIntegrand_sub_frozen_le
#print axioms Navier.Analysis.LeiLinPositiveRestartCancellation.heatHalfGeneratorMoment_criticalMildPathIntegrand_sub_constant_le
#print axioms Navier.Analysis.LeiLinPositiveRestartCancellation.intervalIntegrable_heatHalfGeneratorMoment_path_sub_constant_of_dini
#print axioms Navier.Analysis.LeiLinPositiveRestartCancellation.exists_vanishingEndpointModulus_not_diniSummable
