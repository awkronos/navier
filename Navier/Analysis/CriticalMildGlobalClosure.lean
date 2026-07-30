import Navier.Analysis.CriticalMildWeightedBilinear

/-!
# Exact derivative accounting for global lattice closure

The actual transport kernel contains one frequency factor.  After placing the
inhomogeneous weight on the output mode, a weighted `ℓ¹` closure therefore
requires a second weight on the transported input.  This file proves that
kernel estimate; it does not claim the false same-weight closure.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildGlobalClosure

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace

/-- Output-weighted scalar majorant for the actual lattice transport term. -/
def latticeOutputWeightedMajorant (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) : ℝ :=
  latticeModeWeight k * latticeSpectralMajorant k v w ij

/-- The literal input majorant with one weight on the advected amplitude and
two weights on the transported amplitude. -/
def latticeOneDerivativeInputMajorant (v w : LatticeMode → ComplexSpace)
    (ij : LatticeMode × LatticeMode) : ℝ :=
  latticeModeWeight ij.1 * complexEuclideanNorm (v ij.1) *
    latticeModeWeight ij.2 ^ 2 * complexEuclideanNorm (w ij.2)

/-- The actual output-weighted transport kernel is controlled by one input
weight on the first mode and two on the transported second mode. -/
theorem latticeOutputWeightedMajorant_le_oneDerivativeInput (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) :
    latticeOutputWeightedMajorant k v w ij ≤
      latticeOneDerivativeInputMajorant v w ij := by
  by_cases hij : ij.1 + ij.2 = k
  · rw [latticeOutputWeightedMajorant, latticeSpectralMajorant, if_pos hij,
      latticeOneDerivativeInputMajorant, ← hij]
    have hi : 0 ≤ complexEuclideanNorm (v ij.1) := norm_nonneg _
    have hj : 0 ≤ complexEuclideanNorm (w ij.2) := norm_nonneg _
    have hq : ‖complexFrequency (latticeFrequency ij.2)‖ ≤ latticeModeWeight ij.2 := by
      unfold latticeModeWeight
      linarith [norm_nonneg (complexFrequency (latticeFrequency ij.2))]
    have hk : latticeModeWeight (ij.1 + ij.2) ≤
        latticeModeWeight ij.1 * latticeModeWeight ij.2 :=
      latticeModeWeight_add_le_mul ij.1 ij.2
    have hwi : 0 ≤ latticeModeWeight ij.1 :=
      zero_le_one.trans (one_le_latticeModeWeight ij.1)
    have hwj : 0 ≤ latticeModeWeight ij.2 :=
      zero_le_one.trans (one_le_latticeModeWeight ij.2)
    calc
      latticeModeWeight (ij.1 + ij.2) *
          (‖complexFrequency (latticeFrequency ij.2)‖ *
            complexEuclideanNorm (v ij.1) * complexEuclideanNorm (w ij.2)) =
        latticeModeWeight (ij.1 + ij.2) *
          ‖complexFrequency (latticeFrequency ij.2)‖ *
          complexEuclideanNorm (v ij.1) * complexEuclideanNorm (w ij.2) := by ring
      _ ≤ (latticeModeWeight ij.1 * latticeModeWeight ij.2) *
          ‖complexFrequency (latticeFrequency ij.2)‖ *
          complexEuclideanNorm (v ij.1) * complexEuclideanNorm (w ij.2) := by
          calc
            _ = latticeModeWeight (ij.1 + ij.2) *
                (‖complexFrequency (latticeFrequency ij.2)‖ *
                  complexEuclideanNorm (v ij.1) * complexEuclideanNorm (w ij.2)) := by ring
            _ ≤ (latticeModeWeight ij.1 * latticeModeWeight ij.2) *
                (‖complexFrequency (latticeFrequency ij.2)‖ *
                  complexEuclideanNorm (v ij.1) * complexEuclideanNorm (w ij.2)) :=
              mul_le_mul_of_nonneg_right hk
                (mul_nonneg (mul_nonneg (norm_nonneg _) hi) hj)
            _ = _ := by ring
      _ ≤ (latticeModeWeight ij.1 * latticeModeWeight ij.2) *
          latticeModeWeight ij.2 * complexEuclideanNorm (v ij.1) *
          complexEuclideanNorm (w ij.2) := by
          calc
            _ = (latticeModeWeight ij.1 * latticeModeWeight ij.2) *
                (‖complexFrequency (latticeFrequency ij.2)‖ *
                  complexEuclideanNorm (v ij.1) * complexEuclideanNorm (w ij.2)) := by ring
            _ ≤ (latticeModeWeight ij.1 * latticeModeWeight ij.2) *
                (latticeModeWeight ij.2 * complexEuclideanNorm (v ij.1) *
                  complexEuclideanNorm (w ij.2)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq hi) hj)
                (mul_nonneg hwi hwj)
            _ = _ := by ring
      _ = latticeModeWeight ij.1 * complexEuclideanNorm (v ij.1) *
          latticeModeWeight ij.2 ^ 2 * complexEuclideanNorm (w ij.2) := by ring
  · rw [latticeOutputWeightedMajorant, latticeSpectralMajorant, if_neg hij]
    simp only [mul_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight ij.1))
        (norm_nonneg _)) (sq_nonneg _))
      (norm_nonneg _)

end Navier.Analysis.CriticalMildGlobalClosure
