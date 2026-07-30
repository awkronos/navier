import Navier.Analysis.CriticalMildFiberSums
import Navier.Analysis.CriticalMildGlobalENNRealMajorant

/-!
# Exact global weighted spectral fibers

This file exposes the completed output fiber before any global same-weight
closure claim.  Its bound remains asymmetric in the one- and two-weight inputs.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildGlobalWeightedOutput

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildGlobalClosure
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildFiberSums
open Navier.Analysis.CriticalMildAsymmetricPairSummable

/-- The actual completed weighted spectral output at one lattice mode. -/
def globalWeightedSpectralOutputFiber (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) : ComplexE3 :=
  ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
    latticeWeightedFiberTerm k v w ij

/-- The exact output fiber is controlled by its asymmetric one-derivative
fiber majorant. -/
theorem norm_globalWeightedSpectralOutputFiber_le (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    ‖globalWeightedSpectralOutputFiber k v w hv hw‖ ≤
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        latticeOneDerivativeInputMajorant v w ij.1 := by
  exact norm_tsum_latticeWeightedFiberTerm_le k v w hv hw

/-- The concrete output-fiber sigma type is equivalent to unconstrained
ordered lattice pairs. -/
def latticeOutputFiberSigmaEquiv :
    (Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) ≃
      LatticeMode × LatticeMode where
  toFun x := x.2.1
  invFun ij := ⟨latticeOutputMode ij, ⟨ij, by simp⟩⟩
  left_inv x := by
    rcases x with ⟨k, ⟨ij, hij⟩⟩
    change latticeOutputMode ij = k at hij
    subst k
    rfl
  right_inv ij := rfl

/-- The real asymmetric fiber majorants are summable after summing over all
output modes.  This is the real form of the exact constrained reindex. -/
theorem summable_latticeOneDerivativeInputMajorant_fibers
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    Summable fun k : LatticeMode =>
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        latticeOneDerivativeInputMajorant v w ij.1 := by
  have hpair := summable_latticeOneDerivativeInputMajorant v w hv hw
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      latticeOneDerivativeInputMajorant v w x.2.1) := by
    exact latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
  exact hsigma.sigma

/-- The norms of all completed weighted output fibers are summable under the
asymmetric one- and two-weight input contracts. -/
theorem summable_norm_globalWeightedSpectralOutputFiber
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    Summable fun k : LatticeMode =>
      ‖globalWeightedSpectralOutputFiber k v w hv hw‖ := by
  exact (summable_latticeOneDerivativeInputMajorant_fibers v w hv hw).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun k => norm_globalWeightedSpectralOutputFiber_le k v w hv hw)

/-- The global weighted spectral output as an actual completed Mathlib `ℓ¹`
carrier element. -/
def globalWeightedSpectralOutput
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) : WeightedLatticeBanach :=
  ⟨fun k => globalWeightedSpectralOutputFiber k v w hv hw,
    memℓp_gen (by
      simpa using summable_norm_globalWeightedSpectralOutputFiber v w hv hw)⟩

/-- The one-weight real input factor used by the asymmetric global estimate. -/
def globalWeightedInputFactor (v : LatticeMode → ComplexSpace) : LatticeMode → ℝ :=
  fun m => latticeModeWeight m * complexEuclideanNorm (v m)

/-- The two-weight real input factor used by the asymmetric global estimate. -/
def globalTwoWeightInputFactor (w : LatticeMode → ComplexSpace) : LatticeMode → ℝ :=
  fun m => latticeModeWeight m ^ 2 * complexEuclideanNorm (w m)

/-- The pair majorant factors exactly as the product of the two named input
factors. -/
theorem tsum_latticeOneDerivativeInputMajorant_eq_product
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    (∑' ij : LatticeMode × LatticeMode, latticeOneDerivativeInputMajorant v w ij) =
      (∑' m, globalWeightedInputFactor v m) *
        ∑' m, globalTwoWeightInputFactor w m := by
  let a : LatticeMode → ℝ := globalWeightedInputFactor v
  let b : LatticeMode → ℝ := globalTwoWeightInputFactor w
  have ha0 : ∀ m, 0 ≤ a m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hb0 : ∀ m, 0 ≤ b m := by
    intro m
    exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
  have ha : Summable a := by
    change Summable (fun m => latticeModeWeight m * complexEuclideanNorm (v m)) at hv
    exact hv
  have hb : Summable b := by
    change Summable (fun m => latticeModeWeight m ^ 2 * complexEuclideanNorm (w m)) at hw
    exact hw
  have hab : Summable (fun ij : LatticeMode × LatticeMode => a ij.1 * b ij.2) :=
    ha.mul_of_nonneg hb ha0 hb0
  convert (ha.tsum_mul_tsum hb hab).symm using 1
  · apply tsum_congr
    intro ij
    change latticeModeWeight ij.1 * complexEuclideanNorm (v ij.1) *
        latticeModeWeight ij.2 ^ 2 * complexEuclideanNorm (w ij.2) =
      (latticeModeWeight ij.1 * complexEuclideanNorm (v ij.1)) *
        (latticeModeWeight ij.2 ^ 2 * complexEuclideanNorm (w ij.2))
    ring

/-- The total constrained-fiber majorant sum is exactly the unconstrained
pair-majorant sum. -/
theorem tsum_latticeOneDerivativeInputMajorant_fibers_eq_pair
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    (∑' k : LatticeMode,
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        latticeOneDerivativeInputMajorant v w ij.1) =
      ∑' ij : LatticeMode × LatticeMode,
        latticeOneDerivativeInputMajorant v w ij := by
  have hpair := summable_latticeOneDerivativeInputMajorant v w hv hw
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      latticeOneDerivativeInputMajorant v w x.2.1) := by
    exact latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
  rw [← hsigma.tsum_sigma]
  exact latticeOutputFiberSigmaEquiv.tsum_eq _

/-- The `ℓ¹` norm of the completed output is the sum of its exact fiber
norms. -/
theorem norm_globalWeightedSpectralOutput_eq_tsum
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    ‖globalWeightedSpectralOutput v w hv hw‖ =
      ∑' k, ‖globalWeightedSpectralOutputFiber k v w hv hw‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  change (∑' k : LatticeMode,
    ‖globalWeightedSpectralOutputFiber k v w hv hw‖ ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) = _
  rw [show (1 : ℝ) / 1 = 1 by norm_num, Real.rpow_one]
  apply congrArg tsum
  funext k
  exact Real.rpow_one _

/-- Quantitative global asymmetric output estimate for the completed spectral
carrier. -/
theorem norm_globalWeightedSpectralOutput_le
    (v w : LatticeMode → ComplexSpace) (hv : LatticeWeightedL1 v)
    (hw : LatticeTwoWeightL1 w) :
    ‖globalWeightedSpectralOutput v w hv hw‖ ≤
      (∑' m, globalWeightedInputFactor v m) *
        ∑' m, globalTwoWeightInputFactor w m := by
  rw [norm_globalWeightedSpectralOutput_eq_tsum]
  calc
    (∑' k, ‖globalWeightedSpectralOutputFiber k v w hv hw‖) ≤
      ∑' k, ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        latticeOneDerivativeInputMajorant v w ij.1 := by
      exact Summable.tsum_le_tsum (fun k => norm_globalWeightedSpectralOutputFiber_le k v w hv hw)
        (summable_norm_globalWeightedSpectralOutputFiber v w hv hw)
        (summable_latticeOneDerivativeInputMajorant_fibers v w hv hw)
    _ = ∑' ij : LatticeMode × LatticeMode,
        latticeOneDerivativeInputMajorant v w ij :=
      tsum_latticeOneDerivativeInputMajorant_fibers_eq_pair v w hv hw
    _ = (∑' m, globalWeightedInputFactor v m) *
        ∑' m, globalTwoWeightInputFactor w m :=
      tsum_latticeOneDerivativeInputMajorant_eq_product v w hv hw


#print axioms globalWeightedSpectralOutputFiber
#print axioms norm_globalWeightedSpectralOutputFiber_le
#print axioms norm_globalWeightedSpectralOutput_le

end Navier.Analysis.CriticalMildGlobalWeightedOutput
