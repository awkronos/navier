import Navier.Analysis.PhysicalPeriodicHighEnergyWindow

/-!
# Continuity of the raw high-frequency energy functional

The squared decoded Fourier tail is continuous in the completed weighted
carrier norm.  A direct difference estimate removes the last topological
premise from the positive-time high-energy window theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicHighEnergyContinuity

open Set Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicEnergyEvolution
open Navier.Analysis.PhysicalPeriodicHighEnergyWindow

theorem abs_weightedAmplitude_sub_le
    (u v : WeightedLatticeBanach) (k : LatticeMode) :
    |weightedAmplitude u k - weightedAmplitude v k| ≤ ‖(u - v) k‖ := by
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
  exact h.trans
    (complexEuclideanNorm_weightedLatticeCoefficient_le_eval (u - v) k)

theorem abs_rawSpectralEnergyDensity_sub_le
    (u v : WeightedLatticeBanach) (k : LatticeMode) :
    |rawSpectralEnergyDensity u k - rawSpectralEnergyDensity v k| ≤
      (‖u‖ + ‖v‖) * ‖(u - v) k‖ := by
  have hu : weightedAmplitude u k ≤ ‖u‖ :=
    (complexEuclideanNorm_weightedLatticeCoefficient_le_eval u k).trans
      (norm_weightedLattice_eval_le u k)
  have hv : weightedAmplitude v k ≤ ‖v‖ :=
    (complexEuclideanNorm_weightedLatticeCoefficient_le_eval v k).trans
      (norm_weightedLattice_eval_le v k)
  have hdiff := abs_weightedAmplitude_sub_le u v k
  have ha0 := weightedAmplitude_nonneg u k
  have hb0 := weightedAmplitude_nonneg v k
  unfold rawSpectralEnergyDensity
  rw [sq_sub_sq, abs_mul]
  have habsadd : |weightedAmplitude u k + weightedAmplitude v k| =
      weightedAmplitude u k + weightedAmplitude v k :=
    abs_of_nonneg (add_nonneg ha0 hb0)
  rw [habsadd]
  exact mul_le_mul (add_le_add hu hv) hdiff
    (abs_nonneg _) (add_nonneg (norm_nonneg u) (norm_nonneg v))

/-- Global difference estimate for every sharp high-frequency cutoff. -/
theorem abs_rawHighSpectralEnergy_sub_le
    (N : ℝ) (u v : WeightedLatticeBanach) :
    |rawHighSpectralEnergy N u - rawHighSpectralEnergy N v| ≤
      (‖u‖ + ‖v‖) * ‖u - v‖ := by
  let fu : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then rawSpectralEnergyDensity u k else 0
  let fv : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then rawSpectralEnergyDensity v k else 0
  have hfu : Summable fu := summable_rawHighSpectralEnergy N u
  have hfv : Summable fv := summable_rawHighSpectralEnergy N v
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
    · exact abs_rawSpectralEnergyDensity_sub_le u v k
    · simp only [sub_zero, abs_zero]
      exact mul_nonneg
        (add_nonneg (norm_nonneg u) (norm_nonneg v)) (norm_nonneg _)
  unfold rawHighSpectralEnergy
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

/-- Continuity of the sharp high-frequency energy on the completed carrier. -/
theorem continuous_rawHighSpectralEnergy (N : ℝ) :
    Continuous (rawHighSpectralEnergy N) := by
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
    have hdist0 := norm_nonneg (v - u)
    have hfirst : (‖v‖ + ‖u‖) * ‖v - u‖ < C * ‖v - u‖ := by
      exact mul_lt_mul_of_pos_right hcoef
        (norm_pos_iff.mpr (sub_ne_zero.mpr hvu))
    have hsecond : C * ‖v - u‖ < eps := by
      calc
        C * ‖v - u‖ < C * (eps / C) := mul_lt_mul_of_pos_left hvsmall hC
        _ = eps := by field_simp
    exact hfirst.trans hsecond
  exact (abs_rawHighSpectralEnergy_sub_le N v u).trans_lt hprod

/-- A continuous carrier path has continuous sharp high-frequency energy on
every time set. -/
theorem continuousOn_rawHighSpectralEnergy_comp
    (N : ℝ) (A : ℝ → WeightedLatticeBanach) (hA : Continuous A)
    (s : Set ℝ) :
    ContinuousOn (fun t => rawHighSpectralEnergy N (A t)) s :=
  ((continuous_rawHighSpectralEnergy N).comp hA).continuousOn

/-- Positive-time high-energy decay with continuity discharged by the actual
continuous mild carrier. -/
theorem mild_highEnergy_le_decay_add_equilibrium_of_continuousPath
    (mu : ℝ) (hmu : 0 < mu) (a0 : WeightedLatticeBanach)
    (ha0 : LatticeDivergenceFree a0)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R H delta T N : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hdelta : 0 < delta)
    (hdeltaT : delta ≤ T) (hN : 0 < N)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage mu hmu a0 A hdiv s hs.1)
    (hhalf : ∀ s ∈ Icc delta T, Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖A s k‖)
    (hmoment : ∀ s ∈ Icc delta T,
      heatHalfGeneratorMoment (A s) ≤ H) :
    ∀ t ∈ Icc delta T,
      rawHighSpectralEnergy N (A t) ≤
        Real.exp (-(2 * mu * N ^ 2) * (t - delta)) *
            rawHighSpectralEnergy N (A delta) +
          4 * R ^ 2 * H / (mu * N ^ 3) := by
  exact mild_highEnergy_le_decay_add_equilibrium
    mu hmu a0 ha0 A hAc hdiv hR hH hdelta hdeltaT hN hbound hmild
      hhalf hmoment (continuousOn_rawHighSpectralEnergy_comp N A hAc (Icc delta T))

end Navier.Analysis.PhysicalPeriodicHighEnergyContinuity
