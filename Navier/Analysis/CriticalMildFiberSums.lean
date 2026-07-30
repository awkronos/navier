import Navier.Analysis.CriticalMildAsymmetricPairSummable

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildFiberSums

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildGlobalClosure
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildAsymmetricPairSummable

/-- Weighted actual transport terms restricted to the exact output fiber. -/
def latticeWeightedFiberTerm (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) : ComplexE3 :=
  latticeModeWeight k • complexEuclideanPoint
    (spectralTransport (latticeFrequency ij.1.2) (v ij.1.1) (w ij.1.2))

/-- Pointwise weighted fiber control by the asymmetric pair majorant. -/
theorem norm_latticeWeightedFiberTerm_le (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖latticeWeightedFiberTerm k v w ij‖ ≤
      latticeOneDerivativeInputMajorant v w ij.1 := by
  have hik : ij.1.1 + ij.1.2 = k := ij.2
  unfold latticeWeightedFiberTerm
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (zero_le_one.trans (one_le_latticeModeWeight k))]
  calc
    latticeModeWeight k * ‖complexEuclideanPoint
        (spectralTransport (latticeFrequency ij.1.2) (v ij.1.1) (w ij.1.2))‖ ≤
      latticeModeWeight k * (‖complexFrequency (latticeFrequency ij.1.2)‖ *
        complexEuclideanNorm (v ij.1.1) * complexEuclideanNorm (w ij.1.2)) := by
      have htransport := complexEuclideanNorm_spectralTransport_le
        (latticeFrequency ij.1.2) (v ij.1.1) (w ij.1.2)
      exact mul_le_mul_of_nonneg_left
        (by simpa [complexEuclideanNorm] using htransport)
        (zero_le_one.trans (one_le_latticeModeWeight k))
    _ = latticeOutputWeightedMajorant k v w ij.1 := by
      unfold latticeOutputWeightedMajorant latticeSpectralMajorant
      rw [if_pos hik]
    _ ≤ latticeOneDerivativeInputMajorant v w ij.1 :=
      latticeOutputWeightedMajorant_le_oneDerivativeInput k v w ij.1

/-- The weighted actual vector series converges on every exact output fiber. -/
theorem summable_latticeWeightedFiberTerm (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    Summable (latticeWeightedFiberTerm k v w) := by
  have hpair := (summable_latticeOneDerivativeInputMajorant v w hv hw).subtype
    (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))
  exact hpair.of_norm_bounded (norm_latticeWeightedFiberTerm_le k v w)

/-- Norm estimate for the actual weighted vector fiber sum. -/
theorem norm_tsum_latticeWeightedFiberTerm_le (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    ‖∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        latticeWeightedFiberTerm k v w ij‖ ≤
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        latticeOneDerivativeInputMajorant v w ij.1 :=
  tsum_of_norm_bounded
    ((summable_latticeOneDerivativeInputMajorant v w hv hw).subtype _).hasSum
    (norm_latticeWeightedFiberTerm_le k v w)

end Navier.Analysis.CriticalMildFiberSums
