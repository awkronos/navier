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

#print axioms globalWeightedSpectralOutputFiber
#print axioms norm_globalWeightedSpectralOutputFiber_le

end Navier.Analysis.CriticalMildGlobalWeightedOutput
