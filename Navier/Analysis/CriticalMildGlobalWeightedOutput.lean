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

#print axioms globalWeightedSpectralOutputFiber
#print axioms norm_globalWeightedSpectralOutputFiber_le

end Navier.Analysis.CriticalMildGlobalWeightedOutput
