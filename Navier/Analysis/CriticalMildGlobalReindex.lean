import Navier.Analysis.CriticalMildHeatCoefficientLift

/-!
# Fiberwise reindexing for lattice convolution outputs

The output mode of an ordered lattice pair is its sum.  This module records
the exact nonnegative `tsum` reindexing from constrained output fibers back to
unconstrained input pairs.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildGlobalReindex

open scoped ENNReal
open Navier.Analysis.CriticalMildSeries

/-- The output lattice mode of an ordered pair of input modes. -/
def latticeOutputMode (ij : LatticeMode × LatticeMode) : LatticeMode :=
  ij.1 + ij.2

/-- Reindex a nonnegative double series from its constrained output-mode
fibers to unconstrained ordered input pairs. -/
theorem tsum_latticeOutput_fiberwise (f : (LatticeMode × LatticeMode) → ℝ≥0∞) :
    ∑' k : LatticeMode,
      ∑' ij : (latticeOutputMode ⁻¹' ({k} : Set LatticeMode)), f ij =
      ∑' ij : LatticeMode × LatticeMode, f ij :=
  ENNReal.tsum_fiberwise f latticeOutputMode

end Navier.Analysis.CriticalMildGlobalReindex
