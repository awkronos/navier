import Navier.Analysis.CriticalMildSeries

/-!
# Weighted lattice sequence estimates for the mild layer

This module gives a concrete frequency weight and the scalar weighted `ℓ¹`
estimates that control the countable lattice transport series.  It does not
reconstruct a function space or assert a fixed point or PDE solution.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildWeightedSpace

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildSeries

/-- The concrete inhomogeneous frequency weight on the lattice carrier. -/
def latticeModeWeight (m : LatticeMode) : ℝ :=
  1 + ‖complexFrequency (latticeFrequency m)‖

/-- The lattice frequency embedding respects mode addition. -/
theorem latticeFrequency_add (m n : LatticeMode) :
    latticeFrequency (m + n) = latticeFrequency m + latticeFrequency n := by
  ext i
  fin_cases i <;> simp [latticeFrequency]

/-- The inhomogeneous lattice weight is at least one. -/
theorem one_le_latticeModeWeight (m : LatticeMode) : 1 ≤ latticeModeWeight m := by
  unfold latticeModeWeight
  linarith [norm_nonneg (complexFrequency (latticeFrequency m))]

/-- The frequency weight is submultiplicative under lattice-mode addition. -/
theorem latticeModeWeight_add_le_mul (m n : LatticeMode) :
    latticeModeWeight (m + n) ≤ latticeModeWeight m * latticeModeWeight n := by
  unfold latticeModeWeight
  rw [latticeFrequency_add]
  have hm : 0 ≤ ‖complexFrequency (latticeFrequency m)‖ := norm_nonneg _
  have hn : 0 ≤ ‖complexFrequency (latticeFrequency n)‖ := norm_nonneg _
  have htri : ‖complexFrequency (latticeFrequency m) +
      complexFrequency (latticeFrequency n)‖ ≤
      ‖complexFrequency (latticeFrequency m)‖ +
        ‖complexFrequency (latticeFrequency n)‖ := norm_add_le _ _
  have hcomplex : complexFrequency (latticeFrequency m + latticeFrequency n) =
      complexFrequency (latticeFrequency m) + complexFrequency (latticeFrequency n) := by
    ext i
    simp [complexFrequency, complexEuclideanPoint, complexOfReal, complexOfParts]
  rw [hcomplex]
  nlinarith [mul_nonneg hm hn]

/-- The weighted scalar amplitude of one complex lattice coefficient. -/
def latticeWeightedAmplitude (u : LatticeMode → ComplexSpace) (m : LatticeMode) : ℝ :=
  latticeModeWeight m * complexEuclideanNorm (u m)

/-- The explicit weighted `ℓ¹` contract for a lattice coefficient sequence. -/
def LatticeWeightedL1 (u : LatticeMode → ComplexSpace) : Prop :=
  Summable (latticeWeightedAmplitude u)

/-- The product majorant obtained by assigning one inhomogeneous weight to
each input lattice coefficient. -/
def latticeWeightedPairMajorant (v w : LatticeMode → ComplexSpace)
    (ij : LatticeMode × LatticeMode) : ℝ :=
  latticeWeightedAmplitude v ij.1 * latticeWeightedAmplitude w ij.2

/-- The actual transport majorant is bounded by the product of the two
weighted coefficient amplitudes. -/
theorem latticeSpectralMajorant_le_weightedPair (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) :
    latticeSpectralMajorant k v w ij ≤ latticeWeightedPairMajorant v w ij := by
  by_cases hij : ij.1 + ij.2 = k
  · rw [latticeSpectralMajorant, if_pos hij]
    unfold latticeWeightedPairMajorant latticeWeightedAmplitude
    have hi : 0 ≤ complexEuclideanNorm (v ij.1) := norm_nonneg _
    have hj : 0 ≤ complexEuclideanNorm (w ij.2) := norm_nonneg _
    have hq : ‖complexFrequency (latticeFrequency ij.2)‖ ≤ latticeModeWeight ij.2 := by
      unfold latticeModeWeight
      linarith [norm_nonneg (complexFrequency (latticeFrequency ij.2))]
    calc
      ‖complexFrequency (latticeFrequency ij.2)‖ *
          complexEuclideanNorm (v ij.1) * complexEuclideanNorm (w ij.2) ≤
        latticeModeWeight ij.2 * complexEuclideanNorm (v ij.1) *
          complexEuclideanNorm (w ij.2) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hq hi) hj
      _ ≤ latticeModeWeight ij.1 *
          (latticeModeWeight ij.2 * complexEuclideanNorm (v ij.1) *
            complexEuclideanNorm (w ij.2)) := by
          exact le_mul_of_one_le_left
            (mul_nonneg (mul_nonneg (le_trans (norm_nonneg _) hq) hi) hj)
            (one_le_latticeModeWeight ij.1)
      _ = (latticeModeWeight ij.1 * complexEuclideanNorm (v ij.1)) *
          (latticeModeWeight ij.2 * complexEuclideanNorm (w ij.2)) := by ring
  · rw [latticeSpectralMajorant, if_neg hij]
    exact mul_nonneg
      (mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight ij.1)) (norm_nonneg _))
      (mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight ij.2)) (norm_nonneg _))

/-- Two weighted `ℓ¹` coefficient contracts make the actual scalar lattice
transport majorant summable. -/
theorem summable_latticeSpectralMajorant_of_weightedL1 (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeWeightedL1 w) :
    Summable (latticeSpectralMajorant k v w) := by
  have hv0 : ∀ m, 0 ≤ latticeWeightedAmplitude v m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hw0 : ∀ m, 0 ≤ latticeWeightedAmplitude w m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hp : Summable (latticeWeightedPairMajorant v w) := by
    unfold latticeWeightedPairMajorant
    exact hv.mul_of_nonneg hw hv0 hw0
  refine hp.of_nonneg_of_le ?_ (latticeSpectralMajorant_le_weightedPair k v w)
  intro ij
  unfold latticeSpectralMajorant
  split_ifs
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  · exact le_rfl

/-- The weighted `ℓ¹` contracts feed directly into the countable-series
contract from `CriticalMildSeries`. -/
theorem latticeConvolutionWeightedL1_of_weightedL1 (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeWeightedL1 w) :
    LatticeConvolutionWeightedL1 k v w :=
  summable_latticeSpectralMajorant_of_weightedL1 k v w hv hw

/-- Product-form norm control for the actual countable lattice transport
series under the two explicit weighted `ℓ¹` contracts. -/
theorem norm_latticeSpectralConvolution_le_weightedProduct (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeWeightedL1 w) :
    ‖latticeSpectralConvolution k v w‖ ≤
      (∑' m, latticeWeightedAmplitude v m) * ∑' n, latticeWeightedAmplitude w n := by
  have hmajorant := summable_latticeSpectralMajorant_of_weightedL1 k v w hv hw
  have hp : Summable (latticeWeightedPairMajorant v w) := by
    unfold latticeWeightedPairMajorant
    apply hv.mul_of_nonneg hw
    · intro m
      exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
    · intro m
      exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hv0 : ∀ m, 0 ≤ latticeWeightedAmplitude v m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hw0 : ∀ m, 0 ≤ latticeWeightedAmplitude w m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hvnorm : Summable fun m => ‖latticeWeightedAmplitude v m‖ := by
    change Summable (latticeWeightedAmplitude v) at hv
    rw [show (fun m => ‖latticeWeightedAmplitude v m‖) = latticeWeightedAmplitude v by
      funext m
      exact abs_of_nonneg (hv0 m)]
    exact hv
  have hwnorm : Summable fun m => ‖latticeWeightedAmplitude w m‖ := by
    change Summable (latticeWeightedAmplitude w) at hw
    rw [show (fun m => ‖latticeWeightedAmplitude w m‖) = latticeWeightedAmplitude w by
      funext m
      exact abs_of_nonneg (hw0 m)]
    exact hw
  calc
    ‖latticeSpectralConvolution k v w‖ ≤ ∑' ij, latticeSpectralMajorant k v w ij :=
      norm_latticeSpectralConvolution_le_weighted_tsum k v w hmajorant
    _ ≤ ∑' ij, latticeWeightedPairMajorant v w ij :=
      hmajorant.tsum_le_tsum (latticeSpectralMajorant_le_weightedPair k v w) hp
    _ = (∑' m, latticeWeightedAmplitude v m) * ∑' n, latticeWeightedAmplitude w n := by
      unfold latticeWeightedPairMajorant
      symm
      exact tsum_mul_tsum_of_summable_norm
        hvnorm hwnorm

end Navier.Analysis.CriticalMildWeightedSpace
