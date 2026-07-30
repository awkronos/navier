import Navier.Analysis.CriticalMildGlobalReindex

/-!
# Nonnegative fiber majorants for lattice transport

This module transports the exact one-derivative lattice kernel estimate to
`ℝ≥0∞`, the codomain in which the output-fiber reindex is unconditional.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildGlobalENNRealMajorant

open scoped ENNReal
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildGlobalClosure
open Navier.Analysis.CriticalMildGlobalReindex

/-- The output-weighted actual transport majorant, viewed as a nonnegative
extended-real series term. -/
def latticeOutputWeightedENNMajorant (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) : ℝ≥0∞ :=
  ENNReal.ofReal (latticeOutputWeightedMajorant k v w ij)

/-- The asymmetric one-derivative input majorant in nonnegative extended
reals. -/
def latticeOneDerivativeInputENNMajorant
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) : ℝ≥0∞ :=
  ENNReal.ofReal (latticeOneDerivativeInputMajorant v w ij)

/-- The checked real kernel comparison remains valid after the canonical
nonnegative extended-real embedding. -/
theorem latticeOutputWeightedENNMajorant_le_oneDerivativeInput
    (k : LatticeMode) (v w : LatticeMode → ComplexSpace)
    (ij : LatticeMode × LatticeMode) :
    latticeOutputWeightedENNMajorant k v w ij ≤
      latticeOneDerivativeInputENNMajorant v w ij := by
  unfold latticeOutputWeightedENNMajorant latticeOneDerivativeInputENNMajorant
  exact ENNReal.ofReal_le_ofReal
    (latticeOutputWeightedMajorant_le_oneDerivativeInput k v w ij)

/-- Reindex the nonnegative asymmetric input majorant along the concrete
output-mode fibers. -/
theorem tsum_latticeOneDerivativeInput_fiberwise
    (v w : LatticeMode → ComplexSpace) :
    ∑' k : LatticeMode,
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        latticeOneDerivativeInputENNMajorant v w ij =
      ∑' ij : LatticeMode × LatticeMode,
        latticeOneDerivativeInputENNMajorant v w ij :=
  tsum_latticeOutput_fiberwise _

end Navier.Analysis.CriticalMildGlobalENNRealMajorant
