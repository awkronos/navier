import Navier.Analysis.CriticalMildHeatFlow

/-!
# Coordinate algebra for the completed critical heat carrier
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildHeatCarrierAlgebra

open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildSeries

/-- The completed heat-flow carrier has exactly its declared encoded coordinate
at every lattice mode. -/
theorem weightedHeatFlow_apply
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    weightedHeatFlow ν τ hν hτ u m = weightedHeatFlowCoordinate ν τ u m := by
  rfl

/-- Completed heat flow composes additively in time. -/
theorem weightedHeatFlow_semigroup
    (ν t s : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (u : WeightedLatticeBanach) :
    weightedHeatFlow ν (t + s) hν (add_nonneg ht hs) u =
      weightedHeatFlow ν t hν ht (weightedHeatFlow ν s hν hs u) := by
  ext m i
  change weightedHeatFlowCoordinate ν (t + s) u m i =
    weightedHeatFlowCoordinate ν t (weightedHeatFlow ν s hν hs u) m i
  unfold weightedHeatFlowCoordinate
  rw [weightedLatticeCoefficient_weightedHeatFlow]
  rw [ComplexFrequencyHeatLeray.complexFrequencyHeatLeray_semigroup]

end Navier.Analysis.CriticalMildHeatCarrierAlgebra

#print axioms Navier.Analysis.CriticalMildHeatCarrierAlgebra.weightedHeatFlow_apply
#print axioms Navier.Analysis.CriticalMildHeatCarrierAlgebra.weightedHeatFlow_semigroup
