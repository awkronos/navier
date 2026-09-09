import Navier.Analysis.RawHighEnergyDifferentiation
import Navier.Analysis.RawHighEnergyConvolutionIdentity

/-!
# Exact high-frequency energy-rate identity for the raw mild generator

This file pairs the actual mild mode derivative with the decoded raw
coefficient, sums over the high-output region, and identifies the two resulting
series with the literal triad flux and the raw spectral dissipation.  Every
series used below is absolutely summable.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Navier.Analysis.RawHighEnergyRateIdentity

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.RawHighEnergyConvolutionIdentity
open Navier.Analysis.RawHighEnergyDifferentiation

/-- At one mode the actual mild generator splits into nonlinear energy input
and the exact raw viscous dissipation density. -/
theorem rawModeEnergyRate_mildRawTimeDerivative
    (mu : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ) (k : LatticeMode) :
    rawModeEnergyRate (A t) (mildRawTimeDerivative mu A t) k =
      2 * (inner ℂ
        (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
        (complexEuclideanPoint (projectedModeForcing A k t))).re -
      2 * mu * rawSpectralDissipationDensity (A t) k := by
  unfold rawModeEnergyRate mildRawTimeDerivative rawModeDecayRate
  unfold rawSpectralDissipationDensity weightedAmplitude latticeModeSize
  change 2 * inner ℝ
      (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
      (complexEuclideanPoint (projectedModeForcing A k t) -
        ((mu * ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 : ℝ) : ℂ) •
          complexEuclideanPoint (weightedLatticeCoefficient (A t) k)) = _
  rw [inner_sub_right, Complex.coe_smul, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hinner : inner ℝ
      (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
      (complexEuclideanPoint (projectedModeForcing A k t)) =
        (inner ℂ
          (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
          (complexEuclideanPoint (projectedModeForcing A k t))).re :=
    real_inner_eq_re_inner ℂ _ _
  rw [hinner]
  simp only [complexEuclideanNorm]
  rw [complexFrequency_norm_eq_official]
  ring

/-- The cutoff indicator distributes over the exact modal splitting. -/
theorem rawHighModeEnergyRate_mildRawTimeDerivative
    (mu N : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (k : LatticeMode) :
    rawHighModeEnergyRate N (A t) (mildRawTimeDerivative mu A t) k =
      2 * (if N ≤ latticeModeSize k then
        (inner ℂ
          (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
          (complexEuclideanPoint (projectedModeForcing A k t))).re
        else 0) -
      2 * mu * (if N ≤ latticeModeSize k then
        rawSpectralDissipationDensity (A t) k else 0) := by
  by_cases hk : N ≤ latticeModeSize k
  · rw [rawHighModeEnergyRate, if_pos hk, if_pos hk, if_pos hk,
      rawModeEnergyRate_mildRawTimeDerivative]
  · simp [rawHighModeEnergyRate, hk]

theorem summable_high_re_inner_projectedModeForcing
    (N : ℝ) (A : ℝ → WeightedLatticeBanach)
    (hdiv : ∀ s, LatticeDivergenceFree (A s)) (t : ℝ) :
    Summable fun k : LatticeMode =>
      if N ≤ latticeModeSize k then
        (inner ℂ
          (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
          (complexEuclideanPoint (projectedModeForcing A k t))).re
      else 0 := by
  have hs := (summable_re_inner_projectedModeForcing A hdiv t).indicator
    {k : LatticeMode | N ≤ latticeModeSize k}
  exact hs.congr (fun k => by
    by_cases hk : N ≤ latticeModeSize k <;>
      simp [Set.indicator, hk])

/-- The actual mild generator has a genuinely summable high-mode energy-rate
series; no independent summability hypothesis on the derivative is needed. -/
theorem summable_rawHighModeEnergyRate_mildRawTimeDerivative
    (mu N : ℝ) (A : ℝ → WeightedLatticeBanach)
    (hdiv : ∀ s, LatticeDivergenceFree (A s)) (t : ℝ) :
    Summable (rawHighModeEnergyRate N (A t)
      (mildRawTimeDerivative mu A t)) := by
  have hf := (summable_high_re_inner_projectedModeForcing N A hdiv t).mul_left 2
  have hd := (summable_rawHighSpectralDissipation N (A t)).mul_left (2 * mu)
  exact (hf.sub hd).congr (fun k =>
    (rawHighModeEnergyRate_mildRawTimeDerivative mu N A t k).symm)

/-- **Exact high-frequency energy-rate identity.**  Summing the modal energy
rates of the actual mild generator gives twice the literal nonlinear flux
minus twice viscosity times the exact high-frequency spectral dissipation. -/
theorem tsum_rawHighModeEnergyRate_mildRawTimeDerivative
    (mu N : ℝ) (A : ℝ → WeightedLatticeBanach)
    (hdiv : ∀ s, LatticeDivergenceFree (A s)) (t : ℝ) :
    (∑' k : LatticeMode,
      rawHighModeEnergyRate N (A t) (mildRawTimeDerivative mu A t) k) =
      2 * rawHighFrequencyEnergyFlux N (A t) -
        2 * mu * rawHighSpectralDissipation N (A t) := by
  let f : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then
      (inner ℂ
        (complexEuclideanPoint (weightedLatticeCoefficient (A t) k))
        (complexEuclideanPoint (projectedModeForcing A k t))).re
    else 0
  let d : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then
      rawSpectralDissipationDensity (A t) k else 0
  have hf : Summable f :=
    summable_high_re_inner_projectedModeForcing N A hdiv t
  have hd : Summable d := summable_rawHighSpectralDissipation N (A t)
  calc
    (∑' k : LatticeMode,
        rawHighModeEnergyRate N (A t) (mildRawTimeDerivative mu A t) k) =
        ∑' k : LatticeMode, (2 * f k - 2 * mu * d k) := by
      apply tsum_congr
      intro k
      exact rawHighModeEnergyRate_mildRawTimeDerivative mu N A t k
    _ = 2 * (∑' k : LatticeMode, f k) -
        2 * mu * (∑' k : LatticeMode, d k) := by
      rw [Summable.tsum_sub (hf.mul_left 2) (hd.mul_left (2 * mu)),
        tsum_mul_left, tsum_mul_left]
    _ = 2 * rawHighFrequencyEnergyFlux N (A t) -
        2 * mu * rawHighSpectralDissipation N (A t) := by
      rw [show (∑' k : LatticeMode, f k) =
          rawHighFrequencyEnergyFlux N (A t) by
            exact tsum_re_inner_projectedModeForcing_high_eq_rawFlux N A hdiv t]
      rfl

end Navier.Analysis.RawHighEnergyRateIdentity
