import Navier.Analysis.CriticalMildWeightedBanach

/-!
# Continuous linear slices of weighted lattice transport

This module proves the series interchanges needed to make each input slice of
the actual weighted lattice transport convolution a continuous linear map.
It does not assert any fixed point or PDE statement.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildWeightedBilinear

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach

/-- Decoding the weighted carrier commutes with addition. -/
theorem weightedLatticeCoefficient_add (u v : WeightedLatticeBanach) :
    weightedLatticeCoefficient (u + v) =
      weightedLatticeCoefficient u + weightedLatticeCoefficient v := by
  funext m
  simp [weightedLatticeCoefficient, smul_add]

/-- Decoding the weighted carrier commutes with complex scalar multiplication. -/
theorem weightedLatticeCoefficient_smul (c : ℂ) (u : WeightedLatticeBanach) :
    weightedLatticeCoefficient (c • u) = c • weightedLatticeCoefficient u := by
  funext m
  simp [weightedLatticeCoefficient, lp.coeFn_smul]
  exact smul_comm _ _ _

/-- The actual transport summand is additive in its first amplitude. -/
theorem latticeSpectralTerm_add_left (k : LatticeMode)
    (v₁ v₂ w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) :
    latticeSpectralTerm k (v₁ + v₂) w ij =
      latticeSpectralTerm k v₁ w ij + latticeSpectralTerm k v₂ w ij := by
  unfold latticeSpectralTerm spectralTransport
  split_ifs
  · change inner ℂ _
      (complexEuclideanPoint (v₁ ij.1) + complexEuclideanPoint (v₂ ij.1)) •
        complexEuclideanPoint (w ij.2) = _
    rw [inner_add_right, add_smul, complexEuclideanPoint_smul,
      complexEuclideanPoint_smul]
  · simp

/-- The actual transport summand is complex-linear in its first amplitude. -/
theorem latticeSpectralTerm_smul_left (c : ℂ) (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) :
    latticeSpectralTerm k (c • v) w ij = c • latticeSpectralTerm k v w ij := by
  unfold latticeSpectralTerm spectralTransport
  split_ifs <;> simp [smul_smul]

/-- Absolute summability justifies addition under the actual transport `tsum`. -/
theorem latticeSpectralConvolution_add_left (k : LatticeMode)
    (v₁ v₂ w : LatticeMode → ComplexSpace)
    (h₁ : LatticeConvolutionWeightedL1 k v₁ w)
    (h₂ : LatticeConvolutionWeightedL1 k v₂ w) :
    latticeSpectralConvolution k (v₁ + v₂) w =
      latticeSpectralConvolution k v₁ w + latticeSpectralConvolution k v₂ w := by
  unfold latticeSpectralConvolution
  rw [← Summable.tsum_add
    (summable_latticeSpectralTerm_of_weightedL1 k v₁ w h₁)
    (summable_latticeSpectralTerm_of_weightedL1 k v₂ w h₂)]
  apply tsum_congr
  intro ij
  exact latticeSpectralTerm_add_left k v₁ v₂ w ij

/-- Absolute summability justifies scalar multiplication under the actual
transport `tsum`. -/
theorem latticeSpectralConvolution_smul_left (c : ℂ) (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace)
    (h : LatticeConvolutionWeightedL1 k v w) :
    latticeSpectralConvolution k (c • v) w = c • latticeSpectralConvolution k v w := by
  unfold latticeSpectralConvolution
  rw [← Summable.tsum_const_smul c
    (summable_latticeSpectralTerm_of_weightedL1 k v w h)]
  apply tsum_congr
  intro ij
  exact latticeSpectralTerm_smul_left c k v w ij

/-- The actual weighted transport convolution is additive in the first
complete-space input. -/
theorem weightedLatticeSpectralConvolution_add_left (k : LatticeMode)
    (u v z : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k (u + v) z =
      weightedLatticeSpectralConvolution k u z +
        weightedLatticeSpectralConvolution k v z := by
  unfold weightedLatticeSpectralConvolution
  rw [weightedLatticeCoefficient_add]
  exact latticeSpectralConvolution_add_left k _ _ _
    (latticeConvolutionWeightedL1_of_weightedL1 k _ _
      (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient z))
    (latticeConvolutionWeightedL1_of_weightedL1 k _ _
      (latticeWeightedL1_coefficient v) (latticeWeightedL1_coefficient z))

/-- The actual weighted transport convolution is complex-linear in its first
complete-space input. -/
theorem weightedLatticeSpectralConvolution_smul_left (c : ℂ) (k : LatticeMode)
    (u z : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k (c • u) z =
      c • weightedLatticeSpectralConvolution k u z := by
  unfold weightedLatticeSpectralConvolution
  rw [weightedLatticeCoefficient_smul]
  exact latticeSpectralConvolution_smul_left c k _ _
    (latticeConvolutionWeightedL1_of_weightedL1 k _ _
      (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient z))

/-- The actual weighted transport convolution is additive in its second
complete-space input; the same absolute-summability witness justifies the
interchange. -/
theorem weightedLatticeSpectralConvolution_add_right (k : LatticeMode)
    (u v z : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k u (v + z) =
      weightedLatticeSpectralConvolution k u v +
        weightedLatticeSpectralConvolution k u z := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [weightedLatticeCoefficient_add]
  rw [← Summable.tsum_add
    (summable_latticeSpectralTerm_of_weightedL1 k _ _
      (latticeConvolutionWeightedL1_of_weightedL1 k _ _
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient v)))
    (summable_latticeSpectralTerm_of_weightedL1 k _ _
      (latticeConvolutionWeightedL1_of_weightedL1 k _ _
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient z)))]
  apply tsum_congr
  intro ij
  unfold latticeSpectralTerm spectralTransport
  split_ifs
  · change (inner ℂ (complexFrequency (latticeFrequency ij.2))
      (complexEuclideanPoint (weightedLatticeCoefficient u ij.1))) •
      (complexEuclideanPoint (weightedLatticeCoefficient v ij.2) +
      complexEuclideanPoint (weightedLatticeCoefficient z ij.2)) = _
    rw [smul_add, complexEuclideanPoint_smul, complexEuclideanPoint_smul]
  · simp

/-- The actual weighted transport convolution is complex-linear in its second
complete-space input. -/
theorem weightedLatticeSpectralConvolution_smul_right (c : ℂ) (k : LatticeMode)
    (u z : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k u (c • z) =
      c • weightedLatticeSpectralConvolution k u z := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [weightedLatticeCoefficient_smul, ← Summable.tsum_const_smul c
    (summable_latticeSpectralTerm_of_weightedL1 k _ _
      (latticeConvolutionWeightedL1_of_weightedL1 k _ _
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient z)))]
  apply tsum_congr
  intro ij
  unfold latticeSpectralTerm spectralTransport
  split_ifs
  · simp only [Pi.smul_apply, complexEuclideanPoint_smul, smul_smul]
    rw [mul_comm]
  · simp

/-- For each output mode and second input, the actual transport convolution
is a continuous complex-linear map on the complete weighted carrier. -/
noncomputable def weightedLatticeSpectralCLM (k : LatticeMode)
    (z : WeightedLatticeBanach) : WeightedLatticeBanach →L[ℂ] ComplexE3 :=
  LinearMap.mkContinuous
    { toFun := fun u => weightedLatticeSpectralConvolution k u z
      map_add' := fun u v => weightedLatticeSpectralConvolution_add_left k u v z
      map_smul' := fun c u => weightedLatticeSpectralConvolution_smul_left c k u z }
    ‖z‖
    (fun u => by
      rw [mul_comm]
      exact norm_weightedLatticeSpectralConvolution_le k u z)

/-- Operator-norm control for the continuous first-input slice. -/
theorem norm_weightedLatticeSpectralCLM_le (k : LatticeMode)
    (z : WeightedLatticeBanach) : ‖weightedLatticeSpectralCLM k z‖ ≤ ‖z‖ := by
  unfold weightedLatticeSpectralCLM
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (fun u => by
    rw [mul_comm]
    exact norm_weightedLatticeSpectralConvolution_le k u z)

end Navier.Analysis.CriticalMildWeightedBilinear
