import Navier.Breakdown.NativeConstructionEndpoint
import Navier.Construction.R3ActualCandidate
import Navier.Analysis.ForceCoordinateEquivalence
import Navier.Analysis.ConstructedForceExtension
import Navier.Analysis.ConstructedFiniteTimeObstruction

/-!
# Constructed whole-space breakdown

The selected compact candidate is constructed by the locally adapted OpenAI
source. Its finite-energy comparison theorem and the proved Euclidean/native
transport inhabit the original all-positive-viscosity statement C. No
candidate, continuation agreement, or coordinate equivalence is assumed by
the endpoint below.

This is forced breakdown. It does not assert unforced global regularity or a
globally smooth continuation of the singular candidate.
-/

set_option autoImplicit false
open scoped ContDiff

namespace Navier.Breakdown.ConstructedBreakdown

open Navier.Analysis.ForceCoordinateEquivalence

theorem wholeSpaceBreakdown : Navier.ProblemStatements.WholeSpaceBreakdown := by
  exact Navier.Analysis.ConstructedForceExtension.constructedWholeSpaceBreakdown

/-- The same unit-viscosity construction supplies a globally smooth force and
uniform finite energy for its selected Euclidean velocity before breakdown. -/
theorem selectedFiniteEnergyCandidate :
    ∃ u : Navier.Construction.ProblemStatement.VelocityField,
      ∃ p : Navier.Construction.ProblemStatement.PressureField,
      ∃ f : Navier.Construction.ProblemStatement.VelocityField,
      Navier.Construction.R3CompactCandidate.Properties u p f ∧ ContDiff ℝ ∞ f ∧
        Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Set.Ico (0 : ℝ) 1) u := by
  obtain ⟨u, p, f, _, h, hf, henergy, _⟩ :=
    Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile
  exact ⟨u, p, f, h, hf, henergy⟩

/-- The same constructed counterexample also satisfies weighted bounds for
successive coordinate differentiation as an actual recursive operation. Every
ordering is covered, so no permutation convention is needed for the estimates. -/
theorem wholeSpaceBreakdown_with_successivePartials (ν : ℝ) (hν : 0 < ν) :
    ∃ u₀ : Navier.SchwartzVelocity, Navier.DivergenceFreeInitial u₀ ∧
      ∃ f : Navier.ForceField, Navier.ForcedDataRapidDecay f ∧
        (∀ (n K : ℕ) (axes : Fin n → Option (Fin 3)) (component : Fin 3),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Navier.Space,
            (1 + Navier.Breakdown.OfficialCDEncoding.euclideanNorm x + t) ^ K *
              |Navier.Analysis.ForceRecursivePartials.successivePartialWithin
                (fun z => f z.1 z.2) n
                (fun j => Navier.Breakdown.OfficialCDEncoding.spacetimeCoordinateDirection
                  (axes j)) (t, x) component| ≤ C) ∧
        ¬ ∃ u p, Navier.IsClassicalSolution ν f u₀ u p := by
  obtain ⟨u₀, hu₀, f, hf, hbad⟩ := wholeSpaceBreakdown ν hν
  exact ⟨u₀, hu₀, f, hf,
    ((forcedDataRapidDecay_iff_successivePartials f).mp hf).2,
    hbad⟩

end Navier.Breakdown.ConstructedBreakdown
