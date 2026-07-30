import Navier.Analysis.CriticalMildHeatSmoothing

/-!
# Inhomogeneous heat lift for weighted lattice coefficients

The zero Fourier mode is handled by the contractive part of the heat
multiplier; the nonzero-frequency gain contributes `1 / √(ν τ)`.  Thus the
faithful inhomogeneous estimate has factor `1 + 1 / √(ν τ)`.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatCoefficientLift

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildHeatSmoothing

/-- The exact heat--Leray coefficient estimate retaining its scalar decay. -/
theorem complexEuclideanNorm_heatLeray_le_decay (ν τ : ℝ)
    (k : LatticeMode) (z : ComplexSpace) :
    complexEuclideanNorm
      (complexFrequencyHeatLeray ν τ (latticeFrequency k) z) ≤
      complexHeatDecay ν τ (latticeFrequency k) * complexEuclideanNorm z := by
  rw [complexEuclideanNorm,
    complexEuclideanPoint_complexFrequencyHeatLeray,
    norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (complexHeatDecay_nonneg ν τ (latticeFrequency k))]
  exact mul_le_mul_of_nonneg_left (complexEuclideanLeray_norm_le _ _)
    (complexHeatDecay_nonneg _ _ _)

/-- The inhomogeneous output weight is controlled by heat contraction for
the zero mode and by the scalar frequency gain for the remaining weight. -/
theorem latticeModeWeight_heatDecay_le (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (k : LatticeMode) :
    latticeModeWeight k * complexHeatDecay ν τ (latticeFrequency k) ≤
      1 + (Real.sqrt (ν * τ))⁻¹ := by
  unfold latticeModeWeight
  have hcontract : complexHeatDecay ν τ (latticeFrequency k) ≤ 1 := by
    exact complexHeatDecay_le_one hν.le hτ.le _
  have hgain := latticeHeat_frequency_gain ν τ (mul_pos hν hτ) k
  calc
    (1 + ‖complexFrequency (latticeFrequency k)‖) *
        complexHeatDecay ν τ (latticeFrequency k) =
      complexHeatDecay ν τ (latticeFrequency k) +
        ‖complexFrequency (latticeFrequency k)‖ *
          complexHeatDecay ν τ (latticeFrequency k) := by ring
    _ ≤ 1 + (Real.sqrt (ν * τ))⁻¹ := add_le_add hcontract hgain

/-- The actual heat--Leray multiplier maps a two-weight coefficient estimate
to a one-weight coefficient estimate with the faithful inhomogeneous factor.
The right side is deliberately expressed on the same coefficient; applying
the two-weight decoder supplies its extra input weight in a later global sum. -/
theorem latticeModeWeight_heatLeray_coefficient_le (ν τ : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (k : LatticeMode) (z : ComplexSpace) :
    latticeModeWeight k * complexEuclideanNorm
      (complexFrequencyHeatLeray ν τ (latticeFrequency k) z) ≤
      (1 + (Real.sqrt (ν * τ))⁻¹) * complexEuclideanNorm z := by
  calc
    latticeModeWeight k * complexEuclideanNorm
        (complexFrequencyHeatLeray ν τ (latticeFrequency k) z) ≤
      latticeModeWeight k *
        (complexHeatDecay ν τ (latticeFrequency k) * complexEuclideanNorm z) :=
      mul_le_mul_of_nonneg_left (complexEuclideanNorm_heatLeray_le_decay ν τ k z)
        (zero_le_one.trans (one_le_latticeModeWeight k))
    _ = (latticeModeWeight k * complexHeatDecay ν τ (latticeFrequency k)) *
        complexEuclideanNorm z := by ring
    _ ≤ (1 + (Real.sqrt (ν * τ))⁻¹) * complexEuclideanNorm z :=
      mul_le_mul_of_nonneg_right (latticeModeWeight_heatDecay_le ν τ hν hτ k)
        (norm_nonneg _)

end Navier.Analysis.CriticalMildHeatCoefficientLift
