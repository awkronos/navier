import Navier.Analysis.CriticalMildWeightedBilinear

/-!
# Continuous weighted lattice paths and the contraction prerequisite

This file places the checked weighted lattice carrier in Mathlib's complete
continuous-path space.  The actual Duhamel self-map cannot yet be defined:
the preceding development controls a convolution at one output mode, but has
not proved that the collection of all output modes lies in the same weighted
`ℓ¹` carrier.  Consequently no Banach-fixed-point assertion is made here.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildPathContraction

open Navier
open Navier.Analysis.CriticalMildWeightedBanach

/-- Continuous paths in the complete weighted lattice carrier on the closed
local-time interval. -/
abbrev WeightedMildPath (T : ℝ) :=
  C(Set.Icc (0 : ℝ) T, WeightedLatticeBanach)

/-- Evaluation of a continuous weighted path is bounded by its native
supremum norm. -/
theorem norm_weightedMildPath_eval_le (T : ℝ) (u : WeightedMildPath T)
    (t : Set.Icc (0 : ℝ) T) : ‖u t‖ ≤ ‖u‖ :=
  u.norm_coe_le_norm t

/-- The zero path is an admissible member of every closed path-norm ball. -/
theorem zero_mem_weightedMildPath_closedBall (T R : ℝ) (hR : 0 ≤ R) :
    (0 : WeightedMildPath T) ∈ Metric.closedBall 0 R := by
  simpa using hR

/-- A genuine Duhamel self-map on `WeightedMildPath T` requires this output
closure statement.  It is recorded as an explicit predicate, not assumed by
any theorem in this module. -/
def LatticeConvolutionOutputClosed : Prop :=
  ∀ (u z : WeightedLatticeBanach),
    ∃ y : WeightedLatticeBanach,
      ∀ k : Navier.Analysis.CriticalMildSeries.LatticeMode,
        y k = Navier.Analysis.CriticalMildWeightedBanach.weightedLatticeSpectralConvolution k u z

end Navier.Analysis.CriticalMildPathContraction
