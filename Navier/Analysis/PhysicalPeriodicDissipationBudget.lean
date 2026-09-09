import Navier.Analysis.PhysicalPeriodicTotalEnergyControl

/-!
# Datum-only integrated dissipation for physical periodic mild trajectories

The total raw spectral energy identity is integrated on every positive-time
window.  This yields a viscosity-weighted dissipation budget depending only on
the initial datum, independently of the chart radius and time horizon.

The estimate is an `L²_t H¹_x`-type control in the repository's raw Fourier
normalization.  It does not by itself control the critical weighted `ℓ¹`
carrier norm required by the global continuation endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicDissipationBudget

open Set MeasureTheory intervalIntegral Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicEnergyEvolution
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicEnergyBalance
open Navier.Analysis.PhysicalPeriodicHighEnergyContinuity
open Navier.Analysis.PhysicalPeriodicTotalEnergyControl

/-- The weighted amplitude difference retains one frequency factor before it
is bounded by the completed carrier evaluation. -/
theorem latticeModeSize_mul_abs_weightedAmplitude_sub_le
    (u v : WeightedLatticeBanach) (k : LatticeMode) :
    latticeModeSize k * |weightedAmplitude u k - weightedAmplitude v k| ≤
      ‖(u - v) k‖ := by
  have h := abs_norm_sub_norm_le
    (complexEuclideanPoint (weightedLatticeCoefficient u k))
    (complexEuclideanPoint (weightedLatticeCoefficient v k))
  have hcoeff : weightedLatticeCoefficient u k - weightedLatticeCoefficient v k =
      weightedLatticeCoefficient (u - v) k := by
    ext i
    simp [weightedLatticeCoefficient]
    ring
  have hpoint : complexEuclideanPoint (weightedLatticeCoefficient u k) -
      complexEuclideanPoint (weightedLatticeCoefficient v k) =
      complexEuclideanPoint (weightedLatticeCoefficient (u - v) k) := by
    ext i
    exact congrFun hcoeff i
  rw [hpoint] at h
  change |weightedAmplitude u k - weightedAmplitude v k| ≤ _ at h
  have hmul := mul_le_mul_of_nonneg_left h (latticeModeSize_nonneg k)
  exact hmul.trans (by
    simpa only [latticeModeSize, weightedAmplitude, complexEuclideanNorm] using
      frequency_mul_coefficient_le_eval (u - v) k)

/-- Difference estimate for the raw viscous density. -/
theorem abs_rawSpectralDissipationDensity_sub_le
    (u v : WeightedLatticeBanach) (k : LatticeMode) :
    |rawSpectralDissipationDensity u k -
        rawSpectralDissipationDensity v k| ≤
      (‖u‖ + ‖v‖) * ‖(u - v) k‖ := by
  have hufreq : latticeModeSize k * weightedAmplitude u k ≤ ‖u k‖ := by
    simpa only [latticeModeSize, weightedAmplitude] using
      frequency_mul_coefficient_le_eval u k
  have hvfreq : latticeModeSize k * weightedAmplitude v k ≤ ‖v k‖ := by
    simpa only [latticeModeSize, weightedAmplitude] using
      frequency_mul_coefficient_le_eval v k
  have hu : latticeModeSize k * weightedAmplitude u k ≤ ‖u‖ :=
    hufreq.trans (norm_weightedLattice_eval_le u k)
  have hv : latticeModeSize k * weightedAmplitude v k ≤ ‖v‖ :=
    hvfreq.trans (norm_weightedLattice_eval_le v k)
  have hdiff := latticeModeSize_mul_abs_weightedAmplitude_sub_le u v k
  have hs0 := latticeModeSize_nonneg k
  have ha0 := weightedAmplitude_nonneg u k
  have hb0 := weightedAmplitude_nonneg v k
  unfold rawSpectralDissipationDensity
  have hfactor :
      latticeModeSize k ^ 2 * weightedAmplitude u k ^ 2 -
          latticeModeSize k ^ 2 * weightedAmplitude v k ^ 2 =
        (latticeModeSize k * weightedAmplitude u k +
            latticeModeSize k * weightedAmplitude v k) *
          (latticeModeSize k *
            (weightedAmplitude u k - weightedAmplitude v k)) := by
    ring
  rw [hfactor, abs_mul, abs_mul]
  rw [abs_of_nonneg hs0,
    abs_of_nonneg (add_nonneg (mul_nonneg hs0 ha0) (mul_nonneg hs0 hb0))]
  exact mul_le_mul (add_le_add hu hv) hdiff
    (mul_nonneg hs0 (abs_nonneg _))
    (add_nonneg (norm_nonneg u) (norm_nonneg v))

/-- The completed raw dissipation is locally Lipschitz in the weighted
carrier norm, uniformly in the sharp cutoff. -/
theorem abs_rawHighSpectralDissipation_sub_le
    (N : ℝ) (u v : WeightedLatticeBanach) :
    |rawHighSpectralDissipation N u - rawHighSpectralDissipation N v| ≤
      (‖u‖ + ‖v‖) * ‖u - v‖ := by
  let fu : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then rawSpectralDissipationDensity u k else 0
  let fv : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then rawSpectralDissipationDensity v k else 0
  have hfu : Summable fu := summable_rawHighSpectralDissipation N u
  have hfv : Summable fv := summable_rawHighSpectralDissipation N v
  have hsub : Summable fun k => fu k - fv k := hfu.sub hfv
  have hmajor : Summable fun k : LatticeMode =>
      (‖u‖ + ‖v‖) * ‖(u - v) k‖ :=
    (show Summable fun k : LatticeMode => ‖(u - v) k‖ by
      simpa using (u - v).2.summable).mul_left _
  have hpoint : ∀ k, |fu k - fv k| ≤
      (‖u‖ + ‖v‖) * ‖(u - v) k‖ := by
    intro k
    dsimp [fu, fv]
    split_ifs
    · exact abs_rawSpectralDissipationDensity_sub_le u v k
    · simp only [sub_zero, abs_zero]
      exact mul_nonneg
        (add_nonneg (norm_nonneg u) (norm_nonneg v)) (norm_nonneg _)
  unfold rawHighSpectralDissipation
  rw [← hfu.tsum_sub hfv]
  calc
    |(∑' k, (fu k - fv k))| = ‖(∑' k, (fu k - fv k))‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑' k, |fu k - fv k| := by
      have htriangle := norm_tsum_le_tsum_norm hsub.norm
      simpa only [Real.norm_eq_abs] using htriangle
    _ ≤ ∑' k, (‖u‖ + ‖v‖) * ‖(u - v) k‖ :=
      hsub.abs.tsum_le_tsum hpoint hmajor
    _ = (‖u‖ + ‖v‖) * ‖u - v‖ := by
      rw [tsum_mul_left, ← norm_eq_tsum_norm (u - v)]

/-- Continuity of the sharp raw dissipation functional on the completed
carrier. -/
theorem continuous_rawHighSpectralDissipation (N : ℝ) :
    Continuous (rawHighSpectralDissipation N) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [Metric.continuousAt_iff]
  intro eps heps
  let C : ℝ := 2 * ‖u‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let delta : ℝ := min 1 (eps / C)
  have hdelta : 0 < delta := lt_min zero_lt_one (div_pos heps hC)
  refine ⟨delta, hdelta, ?_⟩
  intro v hv
  by_cases hvu : v = u
  · subst v
    simpa using heps
  rw [Real.dist_eq]
  have hvdist : ‖v - u‖ < delta := by simpa [dist_eq_norm] using hv
  have hvone : ‖v - u‖ < 1 := hvdist.trans_le (min_le_left _ _)
  have hvnorm : ‖v‖ < ‖u‖ + 1 := by
    calc
      ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
        simpa [sub_add_cancel] using norm_add_le (v - u) u
      _ < ‖u‖ + 1 := by linarith
  have hcoef : ‖v‖ + ‖u‖ < C := by dsimp [C]; linarith
  have hvsmall : ‖v - u‖ < eps / C := hvdist.trans_le (min_le_right _ _)
  have hprod : (‖v‖ + ‖u‖) * ‖v - u‖ < eps := by
    have hfirst : (‖v‖ + ‖u‖) * ‖v - u‖ < C * ‖v - u‖ := by
      exact mul_lt_mul_of_pos_right hcoef
        (norm_pos_iff.mpr (sub_ne_zero.mpr hvu))
    have hsecond : C * ‖v - u‖ < eps := by
      calc
        C * ‖v - u‖ < C * (eps / C) := mul_lt_mul_of_pos_left hvsmall hC
        _ = eps := by field_simp
    exact hfirst.trans hsecond
  exact (abs_rawHighSpectralDissipation_sub_le N v u).trans_lt hprod

/-- Every sharp-cutoff dissipation tail is bounded by the total
dissipation.  Negative cutoffs select the same modes as cutoff zero. -/
theorem rawHighSpectralDissipation_le_total
    (N : ℝ) (u : WeightedLatticeBanach) :
    rawHighSpectralDissipation N u ≤ rawHighSpectralDissipation 0 u := by
  have hsumN := summable_rawHighSpectralDissipation N u
  have hsum0 := summable_rawHighSpectralDissipation 0 u
  unfold rawHighSpectralDissipation
  apply hsumN.tsum_le_tsum
  · intro k
    rw [if_pos (latticeModeSize_nonneg k)]
    split_ifs
    · exact le_rfl
    · unfold rawSpectralDissipationDensity
      positivity
  · exact hsum0

/-- Exact integrated total-energy identity on every positive-time subinterval
of an actual physical mild chart. -/
theorem mild_totalEnergy_add_integratedDissipation_eq
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T δ t : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδt : δ ≤ t) (htT : t ≤ T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    rawHighSpectralEnergy 0 (A t) +
        2 * μ * ∫ s in δ..t, rawHighSpectralDissipation 0 (A s) =
      rawHighSpectralEnergy 0 (A δ) := by
  let E : ℝ → ℝ := fun s => rawHighSpectralEnergy 0 (A s)
  let D : ℝ → ℝ := fun s => rawHighSpectralDissipation 0 (A s)
  have hcontE : ContinuousOn E (Icc δ t) :=
    continuousOn_rawHighSpectralEnergy_comp 0 A hAc _
  have hcontD : Continuous D :=
    (continuous_rawHighSpectralDissipation 0).comp hAc
  have hint : IntervalIntegrable (fun s => -2 * μ * D s) volume δ t :=
    (hcontD.const_mul (-2 * μ)).intervalIntegrable δ t
  have hderiv : ∀ s ∈ Ioo δ t, HasDerivAt E (-2 * μ * D s) s := by
    intro s hs
    have hsT : s ∈ Ioo (0 : ℝ) T :=
      ⟨hδ.trans_lt hs.1, hs.2.trans_le htT⟩
    have hd := hasDerivAt_mild_highEnergy_flux_dissipation
      μ hμ a ha A hAc hdiv hR (N := 0) le_rfl hsT hbound hmild
    rw [rawHighFrequencyEnergyFlux_zero_cutoff (A s) (hreal s) (hdiv s)] at hd
    simpa [E, D] using hd
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hδt hcontE hderiv hint
  have hscale :
      (∫ s in δ..t, -2 * μ * D s) =
        (-2 * μ) * ∫ s in δ..t, D s := by
    simpa only using
      (intervalIntegral.integral_const_mul (a := δ) (b := t)
        (-2 * μ : ℝ) D)
  dsimp [E] at hFTC
  rw [hscale] at hFTC
  dsimp [D] at hFTC
  linarith

/-- The integrated identity starts at the datum itself, including the
possibly nonsmooth initial endpoint. -/
theorem mild_totalEnergy_add_integratedDissipation_eq_initial
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    rawHighSpectralEnergy 0 (A t) +
        2 * μ * ∫ s in (0 : ℝ)..t, rawHighSpectralDissipation 0 (A s) =
      rawHighSpectralEnergy 0 a := by
  have hA0 : A 0 = a := by
    rw [hmild 0 ⟨le_rfl, ht0.trans htT⟩]
    simp only [criticalMildImage, criticalMildDuhamel, Ioc_self,
      MeasureTheory.setIntegral_empty, add_zero]
    exact weightedHeatFlow_zero_of_divergenceFree μ hμ.le a ha
  have hidentity := mild_totalEnergy_add_integratedDissipation_eq
    μ hμ a ha A hAc hdiv hreal hR (δ := 0) le_rfl ht0 htT hbound hmild
  simpa only [hA0] using hidentity

/-- The total viscosity-weighted dissipation over every positive-time window
is controlled solely by the initial raw spectral energy. -/
theorem mild_integratedDissipation_le_initial
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T δ t : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδt : δ ≤ t) (htT : t ≤ T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    2 * μ * ∫ s in δ..t, rawHighSpectralDissipation 0 (A s) ≤
      rawHighSpectralEnergy 0 a := by
  have hidentity := mild_totalEnergy_add_integratedDissipation_eq
    μ hμ a ha A hAc hdiv hreal hR hδ hδt htT hbound hmild
  have hEt : 0 ≤ rawHighSpectralEnergy 0 (A t) := by
    apply tsum_nonneg
    intro k
    simp only [if_pos (latticeModeSize_nonneg k), rawSpectralEnergyDensity]
    positivity
  have hδT : δ ≤ T := hδt.trans htT
  have hEδ := mild_totalEnergy_le_initial μ hμ a ha A hAc hdiv hreal
    hR ⟨hδ, hδT⟩ hbound hmild
  linarith

/-- Datum-only spacetime high-frequency estimate.  Viscosity and the square
of the cutoff control the time integral of the raw high spectral energy. -/
theorem mild_integratedHighEnergy_le_initial
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T δ t N : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδt : δ ≤ t) (htT : t ≤ T) (hN : 0 ≤ N)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    2 * μ * N ^ 2 *
        (∫ s in δ..t, rawHighSpectralEnergy N (A s)) ≤
      rawHighSpectralEnergy 0 a := by
  let EN : ℝ → ℝ := fun s => rawHighSpectralEnergy N (A s)
  let D0 : ℝ → ℝ := fun s => rawHighSpectralDissipation 0 (A s)
  have hcontEN : Continuous EN :=
    (continuous_rawHighSpectralEnergy N).comp hAc
  have hcontD0 : Continuous D0 :=
    (continuous_rawHighSpectralDissipation 0).comp hAc
  have hintEN : IntervalIntegrable (fun s => N ^ 2 * EN s) volume δ t :=
    (hcontEN.const_mul (N ^ 2)).intervalIntegrable δ t
  have hintD0 : IntervalIntegrable D0 volume δ t :=
    hcontD0.intervalIntegrable δ t
  have hpoint : ∀ s ∈ Icc δ t, N ^ 2 * EN s ≤ D0 s := by
    intro s _
    exact (cutoff_sq_mul_highEnergy_le_highDissipation N hN (A s)).trans
      (rawHighSpectralDissipation_le_total N (A s))
  have hintegral :
      (∫ s in δ..t, N ^ 2 * EN s) ≤ ∫ s in δ..t, D0 s :=
    intervalIntegral.integral_mono_on hδt hintEN hintD0 hpoint
  have hscale :
      (∫ s in δ..t, N ^ 2 * EN s) =
        N ^ 2 * ∫ s in δ..t, EN s := by
    simpa only using
      (intervalIntegral.integral_const_mul (a := δ) (b := t)
        (N ^ 2 : ℝ) EN)
  have hscaled := mul_le_mul_of_nonneg_left hintegral
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hμ.le)
  have hbudget := mild_integratedDissipation_le_initial
    μ hμ a ha A hAc hdiv hreal hR hδ hδt htT hbound hmild
  dsimp [D0] at hscaled hbudget
  rw [hscale] at hscaled
  dsimp [EN] at hscaled
  nlinarith

end Navier.Analysis.PhysicalPeriodicDissipationBudget
