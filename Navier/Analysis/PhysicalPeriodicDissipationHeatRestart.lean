import Navier.Analysis.PhysicalPeriodicGoodTimeSelection
import Navier.Analysis.CriticalMildHeatCoefficientLift
import Navier.Analysis.CriticalMildTimeJetInterchange

/-!
# Dissipation-controlled heat restart on the physical periodic carrier

This module begins the analytic conversion from the datum-controlled good
time to a critical restart.  Three equal heat substeps turn the existing
one-weight parabolic gain into a summable cubic lattice-weight tail.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicDissipationHeatRestart

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildHeatCoefficientLift
open Navier.Analysis.CriticalMildTimeJetInterchange
open Navier.Analysis.CriticalMildZeroMode
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.PeriodicGlobalCriticalControl
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicGoodTimeSelection
open Navier.Analysis.PhysicalPeriodicGlobalControl

/-- Explicit constant for spending three equal heat substeps. -/
def cubicHeatWeightConstant (ν τ : ℝ) : ℝ :=
  (1 + (Real.sqrt (ν * (τ / 3)))⁻¹) ^ 3

/-- Three applications of the one-weight heat gain give a cubic-weight
decay estimate. -/
theorem latticeModeWeight_cubic_mul_heatDecay_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (k : LatticeMode) :
    latticeModeWeight k ^ 3 *
        complexHeatDecay ν τ (latticeFrequency k) ≤
      cubicHeatWeightConstant ν τ := by
  have hthird : 0 < τ / 3 := by positivity
  have hstep := latticeModeWeight_heatDecay_le
    ν (τ / 3) hν hthird k
  have hdecay : complexHeatDecay ν τ (latticeFrequency k) =
      complexHeatDecay ν (τ / 3) (latticeFrequency k) ^ 3 := by
    unfold complexHeatDecay FrequencyHeatLeray.heatDecay
    let x : ℝ := -ν * (τ / 3) *
      ‖Navier.Analysis.OfficialABEncoding.officialEuclideanPoint
        (latticeFrequency k)‖ ^ 2
    rw [show -ν * τ *
          ‖Navier.Analysis.OfficialABEncoding.officialEuclideanPoint
            (latticeFrequency k)‖ ^ 2 = x + x + x by
      dsimp [x]
      ring, Real.exp_add, Real.exp_add]
    ring
  rw [hdecay]
  have hnonneg : 0 ≤ latticeModeWeight k *
      complexHeatDecay ν (τ / 3) (latticeFrequency k) :=
    mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight k))
      (complexHeatDecay_nonneg _ _ _)
  have hpow := pow_le_pow_left₀ hnonneg hstep 3
  simpa [cubicHeatWeightConstant, mul_pow] using hpow

/-- The cubic heat decay is pointwise dominated by the summable inverse-sixth
lattice kernel after squaring. -/
theorem sq_heatDecay_le_cubicKernel
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (k : LatticeMode) :
    complexHeatDecay ν τ (latticeFrequency k) ^ 2 ≤
      cubicHeatWeightConstant ν τ ^ 2 *
        (latticeModeWeight k ^ 6)⁻¹ := by
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hbase := latticeModeWeight_cubic_mul_heatDecay_le ν τ hν hτ k
  have hd0 := complexHeatDecay_nonneg ν τ (latticeFrequency k)
  have hC0 : 0 ≤ cubicHeatWeightConstant ν τ := by
    unfold cubicHeatWeightConstant
    positivity
  have hsq := sq_le_sq₀
    (mul_nonneg (pow_nonneg hw.le 3) hd0) hC0 |>.2 hbase
  apply (le_div_iff₀ (pow_pos hw 6)).2
  calc
    complexHeatDecay ν τ (latticeFrequency k) ^ 2 *
        latticeModeWeight k ^ 6 =
      (latticeModeWeight k ^ 3 *
        complexHeatDecay ν τ (latticeFrequency k)) ^ 2 := by ring
    _ ≤ cubicHeatWeightConstant ν τ ^ 2 := hsq

/-- The heat-decay square is summable on the three-dimensional lattice with
an explicit bound inherited from the inverse-sixth weight kernel. -/
theorem summable_sq_heatDecay
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    Summable fun k : LatticeMode =>
      complexHeatDecay ν τ (latticeFrequency k) ^ 2 := by
  have hmajor := summable_latticeModeWeight_inv_pow_six.mul_left
    (cubicHeatWeightConstant ν τ ^ 2)
  exact hmajor.of_nonneg_of_le
    (fun k => sq_nonneg _) (sq_heatDecay_le_cubicKernel ν τ hν hτ)

/-- Heat contraction of one decoded modal amplitude, retaining the exact
scalar decay. -/
theorem weightedAmplitude_weightedHeatFlow_le_decay
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) (k : LatticeMode) :
    weightedAmplitude (weightedHeatFlow ν τ hν hτ u) k ≤
      complexHeatDecay ν τ (latticeFrequency k) * weightedAmplitude u k := by
  unfold weightedAmplitude
  rw [weightedLatticeCoefficient_weightedHeatFlow]
  exact complexEuclideanNorm_heatLeray_le_decay ν τ k
    (weightedLatticeCoefficient u k)

/-- The scalar kernel left when one input dissipation factor is extracted
from the heat-smoothed mixed critical density. -/
def dissipationToMixedHeatKernel
    (ν τ : ℝ) (k : LatticeMode) : ℝ :=
  if k = 0 then 0 else
    ((latticeModeSize k)⁻¹ ^ 2 + ν) *
      complexHeatDecay ν τ (latticeFrequency k)

theorem dissipationToMixedHeatKernel_nonneg
    (ν τ : ℝ) (hν : 0 ≤ ν) (k : LatticeMode) :
    0 ≤ dissipationToMixedHeatKernel ν τ k := by
  unfold dissipationToMixedHeatKernel
  split_ifs
  · exact le_rfl
  · exact mul_nonneg
      (add_nonneg (sq_nonneg _) hν)
      (complexHeatDecay_nonneg _ _ _)

/-- The squared restart kernel is dominated by the fixed summable
inverse-sixth lattice weight. -/
theorem sq_dissipationToMixedHeatKernel_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (k : LatticeMode) :
    dissipationToMixedHeatKernel ν τ k ^ 2 ≤
      (1 + ν) ^ 2 * cubicHeatWeightConstant ν τ ^ 2 *
        (latticeModeWeight k ^ 6)⁻¹ := by
  by_cases hk : k = 0
  · simp [dissipationToMixedHeatKernel, hk]
    positivity
  have hs := one_le_latticeModeSize_of_ne_zero hk
  have hinv : (latticeModeSize k)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 hs
  have hinv0 : 0 ≤ (latticeModeSize k)⁻¹ :=
    inv_nonneg.mpr (latticeModeSize_nonneg k)
  have hcoef : (latticeModeSize k)⁻¹ ^ 2 + ν ≤ 1 + ν := by
    nlinarith
  have hcoef0 : 0 ≤ (latticeModeSize k)⁻¹ ^ 2 + ν := by positivity
  have hright0 : 0 ≤ 1 + ν := by positivity
  have hdecay0 := complexHeatDecay_nonneg ν τ (latticeFrequency k)
  have hfirst : dissipationToMixedHeatKernel ν τ k ≤
      (1 + ν) * complexHeatDecay ν τ (latticeFrequency k) := by
    rw [dissipationToMixedHeatKernel, if_neg hk]
    exact mul_le_mul_of_nonneg_right hcoef hdecay0
  have hsquare := sq_le_sq₀
    (dissipationToMixedHeatKernel_nonneg ν τ hν.le k)
    (mul_nonneg hright0 hdecay0) |>.2 hfirst
  have hdecay := sq_heatDecay_le_cubicKernel ν τ hν hτ k
  calc
    dissipationToMixedHeatKernel ν τ k ^ 2 ≤
        ((1 + ν) * complexHeatDecay ν τ (latticeFrequency k)) ^ 2 := hsquare
    _ = (1 + ν) ^ 2 *
        complexHeatDecay ν τ (latticeFrequency k) ^ 2 := by ring
    _ ≤ (1 + ν) ^ 2 *
        (cubicHeatWeightConstant ν τ ^ 2 *
          (latticeModeWeight k ^ 6)⁻¹) :=
      mul_le_mul_of_nonneg_left hdecay (sq_nonneg _)
    _ = _ := by ring

/-- The squared dissipation-to-critical heat kernel is summable. -/
theorem summable_sq_dissipationToMixedHeatKernel
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    Summable fun k : LatticeMode =>
      dissipationToMixedHeatKernel ν τ k ^ 2 := by
  have hmajor := summable_latticeModeWeight_inv_pow_six.mul_left
    ((1 + ν) ^ 2 * cubicHeatWeightConstant ν τ ^ 2)
  exact hmajor.of_nonneg_of_le (fun k => sq_nonneg _)
    (sq_dissipationToMixedHeatKernel_le ν τ hν hτ)

/-- One-mode contribution to the off-zero mixed critical quantity. -/
def offZeroMixedHeatModeDensity
    (ν : ℝ) (u : WeightedLatticeBanach) (k : LatticeMode) : ℝ :=
  ((latticeModeSize k)⁻¹ + ν * latticeModeSize k) *
    amplitudeOffZero u k

theorem offZeroMixedHeatModeDensity_nonneg
    (ν : ℝ) (hν : 0 ≤ ν) (u : WeightedLatticeBanach) (k : LatticeMode) :
    0 ≤ offZeroMixedHeatModeDensity ν u k := by
  unfold offZeroMixedHeatModeDensity
  exact mul_nonneg
    (add_nonneg (inv_nonneg.mpr (latticeModeSize_nonneg k))
      (mul_nonneg hν (latticeModeSize_nonneg k)))
    (amplitudeOffZero_nonneg u k)

/-- Modal Young inequality after extracting one dissipation factor from the
heat-smoothed critical density. -/
theorem offZeroMixedHeatModeDensity_le_dissipation_add_kernel
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) (k : LatticeMode) :
    offZeroMixedHeatModeDensity ν
        (weightedHeatFlow ν τ hν.le hτ.le u) k ≤
      (rawSpectralDissipationDensity u k +
        dissipationToMixedHeatKernel ν τ k ^ 2) / 2 := by
  by_cases hk : k = 0
  · subst k
    simp [offZeroMixedHeatModeDensity, amplitudeOffZero,
      dissipationToMixedHeatKernel, latticeModeSize_zero,
      rawSpectralDissipationDensity]
  have hs := one_le_latticeModeSize_of_ne_zero hk
  have hspos : 0 < latticeModeSize k := zero_lt_one.trans_le hs
  have hamp := weightedAmplitude_weightedHeatFlow_le_decay
    ν τ hν.le hτ.le u k
  have hcoef0 : 0 ≤ (latticeModeSize k)⁻¹ + ν * latticeModeSize k :=
    add_nonneg (inv_nonneg.mpr hspos.le)
      (mul_nonneg hν.le hspos.le)
  have hfirst : offZeroMixedHeatModeDensity ν
      (weightedHeatFlow ν τ hν.le hτ.le u) k ≤
      ((latticeModeSize k)⁻¹ + ν * latticeModeSize k) *
        (complexHeatDecay ν τ (latticeFrequency k) * weightedAmplitude u k) := by
    unfold offZeroMixedHeatModeDensity amplitudeOffZero
    rw [if_neg hk]
    exact mul_le_mul_of_nonneg_left hamp hcoef0
  have hfactor :
      ((latticeModeSize k)⁻¹ + ν * latticeModeSize k) *
          (complexHeatDecay ν τ (latticeFrequency k) * weightedAmplitude u k) =
        (latticeModeSize k * weightedAmplitude u k) *
          dissipationToMixedHeatKernel ν τ k := by
    rw [dissipationToMixedHeatKernel, if_neg hk]
    field_simp [hspos.ne']
  rw [hfactor] at hfirst
  have hyoung :
      (latticeModeSize k * weightedAmplitude u k) *
          dissipationToMixedHeatKernel ν τ k ≤
        ((latticeModeSize k * weightedAmplitude u k) ^ 2 +
          dissipationToMixedHeatKernel ν τ k ^ 2) / 2 := by
    nlinarith [sq_nonneg
      (latticeModeSize k * weightedAmplitude u k -
        dissipationToMixedHeatKernel ν τ k)]
  refine hfirst.trans (hyoung.trans_eq ?_)
  unfold rawSpectralDissipationDensity
  ring

/-- **Dissipation-controlled critical heat restart.**  At every positive heat
lag, the full off-zero mixed critical quantity of the free restarted heat leg
is bounded by one half of the current total dissipation plus one half of an
explicit, datum-independent summable lattice kernel. -/
theorem offZeroMixedCriticalQty_weightedHeatFlow_le_dissipation
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) :
    offZeroMixedCriticalQty ν (weightedHeatFlow ν τ hν.le hτ.le u) ≤
      (rawHighSpectralDissipation 0 u +
        ∑' k : LatticeMode,
          dissipationToMixedHeatKernel ν τ k ^ 2) / 2 := by
  let v := weightedHeatFlow ν τ hν.le hτ.le u
  let f : LatticeMode → ℝ := offZeroMixedHeatModeDensity ν v
  let d : LatticeMode → ℝ := rawSpectralDissipationDensity u
  let q : LatticeMode → ℝ := fun k =>
    dissipationToMixedHeatKernel ν τ k ^ 2
  have hd : Summable d := summable_rawSpectralDissipationDensity u
  have hq : Summable q := summable_sq_dissipationToMixedHeatKernel ν τ hν hτ
  have hmajor : Summable fun k => (d k + q k) / 2 :=
    (hd.add hq).div_const 2
  have hf : Summable f := hmajor.of_nonneg_of_le
    (fun k => offZeroMixedHeatModeDensity_nonneg ν hν.le v k)
    (fun k => offZeroMixedHeatModeDensity_le_dissipation_add_kernel
      ν τ hν hτ u k)
  have hm := InW_Xm1_offZero v (InW_inv_latticeModeSize v)
  have hp := InW_X1_offZero v (InW_latticeModeSize v)
  have hsumf : offZeroMixedCriticalQty ν v = ∑' k, f k := by
    unfold offZeroMixedCriticalQty normXm1 normX1 wNorm f
    rw [← tsum_mul_left]
    rw [← hm.tsum_add (hp.mul_left ν)]
    apply tsum_congr
    intro k
    rw [abs_of_nonneg (amplitudeOffZero_nonneg v k)]
    unfold offZeroMixedHeatModeDensity
    ring
  rw [hsumf]
  have hle := hf.tsum_le_tsum
    (fun k => offZeroMixedHeatModeDensity_le_dissipation_add_kernel
      ν τ hν hτ u k) hmajor
  calc
    (∑' k, f k) ≤ ∑' k, (d k + q k) / 2 := hle
    _ = ((∑' k, d k) + ∑' k, q k) / 2 := by
      rw [tsum_div_const, hd.tsum_add hq]
    _ = _ := by
      dsimp [d, q]
      unfold rawHighSpectralDissipation
      rw [show (∑' k : LatticeMode,
          if 0 ≤ latticeModeSize k then rawSpectralDissipationDensity u k else 0) =
          ∑' k, rawSpectralDissipationDensity u k by
        apply tsum_congr
        intro k
        rw [if_pos (latticeModeSize_nonneg k)]]

/-- **Datum-controlled free restart at a good time.**  Every nondegenerate
window of an actual physical mild chart contains one time whose subsequent
positive-lag free heat evolution has an explicit off-zero mixed critical
bound depending only on the datum, viscosity, window length, and fixed heat
kernel. -/
theorem exists_goodTime_offZeroMixed_heatRestart
    (μ τ : ℝ) (hμ : 0 < μ) (hτ : 0 < τ)
    (a : WeightedLatticeBanach) (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T δ t : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδt : δ < t) (htT : t ≤ T)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    ∃ c ∈ Set.Icc δ t,
      4 * μ * (t - δ) *
          offZeroMixedCriticalQty μ
            (weightedHeatFlow μ τ hμ.le hτ.le (A c)) ≤
        rawHighSpectralEnergy 0 a +
          2 * μ * (t - δ) *
            ∑' k : LatticeMode,
              dissipationToMixedHeatKernel μ τ k ^ 2 := by
  obtain ⟨c, hc, hcD⟩ := exists_goodDissipationTime
    μ hμ a ha A hAc hdiv hreal hR hδ hδt htT hbound hmild
  refine ⟨c, hc, ?_⟩
  have hheat := offZeroMixedCriticalQty_weightedHeatFlow_le_dissipation
    μ τ hμ hτ (A c)
  have hfactor : 0 ≤ 4 * μ * (t - δ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hheat hfactor
  have hkernel : 0 ≤ ∑' k : LatticeMode,
      dissipationToMixedHeatKernel μ τ k ^ 2 :=
    tsum_nonneg fun k => sq_nonneg _
  nlinarith

end Navier.Analysis.PhysicalPeriodicDissipationHeatRestart
