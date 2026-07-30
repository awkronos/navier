import Navier.Analysis.CriticalMildGlobalENNRealMajorant

/-!
# Summability of the asymmetric lattice transport majorant

The one-derivative kernel estimate factors into one weighted `ℓ¹` input and a
two-weight `ℓ¹` transported input.  This module proves the resulting pair
majorant summability without asserting an output reconstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildAsymmetricPairSummable

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildGlobalClosure

/-- The explicit two-weight `ℓ¹` input condition needed for the transported
factor of the actual lattice kernel. -/
def LatticeTwoWeightL1 (w : LatticeMode → ComplexSpace) : Prop :=
  Summable fun m => latticeModeWeight m ^ 2 * complexEuclideanNorm (w m)

/-- The asymmetric one-derivative pair majorant is summable from one weighted
and one two-weight input contract. -/
theorem summable_latticeOneDerivativeInputMajorant
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    Summable (latticeOneDerivativeInputMajorant v w) := by
  have hv0 : ∀ m, 0 ≤ latticeModeWeight m * complexEuclideanNorm (v m) := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hw0 : ∀ m, 0 ≤ latticeModeWeight m ^ 2 * complexEuclideanNorm (w m) := by
    intro m
    exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
  have hp : Summable (fun ij : LatticeMode × LatticeMode =>
      (latticeModeWeight ij.1 * complexEuclideanNorm (v ij.1)) *
        (latticeModeWeight ij.2 ^ 2 * complexEuclideanNorm (w ij.2))) :=
    hv.mul_of_nonneg hw hv0 hw0
  convert hp using 1
  ext ij
  simp only [latticeOneDerivativeInputMajorant]
  ring

end Navier.Analysis.CriticalMildAsymmetricPairSummable
