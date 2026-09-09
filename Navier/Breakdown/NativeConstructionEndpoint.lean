import Navier.Analysis.EuclideanPDETransport
import Navier.Analysis.ViscosityEndpoints
import Navier.Construction.R3FiniteEnergyComparison

/-!
# Native statement-C endpoint from the Euclidean construction

The explicit candidate remains on its natural Euclidean carrier.  Its force is
transported to `Navier.Space`, while every hypothetical native global solution
is transported back to the exact finite-energy `GlobalSolutionRn` consumed by
the whole-space uniqueness theorem.  This closes the repository's original
all-positive-viscosity breakdown proposition through the existing viscosity
equivalence.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Breakdown.NativeConstructionEndpoint

open Navier
open Navier.Analysis.EuclideanPDETransport

/-- Any actual compact Euclidean candidate inhabits the exact original
whole-space breakdown endpoint. -/
theorem wholeSpaceBreakdown_of_compactCandidate
    {u : EVelocityField} {p : EPressureField} {f : EVelocityField}
    (h : Navier.Construction.R3CompactCandidate.Properties u p f) :
    ProblemStatements.WholeSpaceBreakdown := by
  apply Navier.Analysis.ViscosityEndpoints.wholeSpaceBreakdown_iff_atViscosityOne.mpr
  refine ⟨0, ProblemStatements.divergenceFreeInitial_zero, nativeForce f,
    R3CompactCandidate.nativeForce_forcedDataRapidDecay h, ?_⟩
  rintro ⟨v, q, hglobal⟩
  exact Navier.Construction.ComparatorBridge.compact_candidate_excludes_global_solution
    h (IsClassicalSolution.toGlobalSolutionRn hglobal)

/-- A selected compact candidate closes statement C.  This theorem exposes the
single construction input so the final selected witness can be wired without
changing any PDE or endpoint type. -/
theorem wholeSpaceBreakdown_of_selectedCandidate
    (hselected : ∃ u : EVelocityField, ∃ p : EPressureField,
      ∃ f : EVelocityField,
        Navier.Construction.R3CompactCandidate.Properties u p f) :
    ProblemStatements.WholeSpaceBreakdown := by
  obtain ⟨u, p, f, h⟩ := hselected
  exact wholeSpaceBreakdown_of_compactCandidate h

#print axioms wholeSpaceBreakdown_of_compactCandidate
#print axioms wholeSpaceBreakdown_of_selectedCandidate

end Navier.Breakdown.NativeConstructionEndpoint
