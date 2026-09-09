/-
Adapted from OpenAI/NavierStokesAndEuler, revision
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538, under Apache-2.0.
Upstream source: NavierStokes/R3ActualCandidate.lean
Changes: native module namespace; further compatibility edits are in Git history.
License: references/licenses/OpenAI-Apache-2.0.txt.
-/
import Navier.Construction.R3CompactCandidate
import Navier.Construction.ActualCandidateAssembly

/-!
# The project's actual sums give a compact whole-space candidate

This is an extraction from `selected_witness`, which retains the original
potential, direct field, and pressure sums. It does not invoke whole-space
uniqueness or claim the comparator's nonexistence conclusion.
-/

noncomputable section

namespace Navier.Construction.R3CompactCandidate

open ProblemStatement

theorem selected_compact_candidate :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, Properties u p f := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ := ActualCandidateAssembly.selected_witness
  exact ⟨_, _, _, of_localized_fields hc⟩

end Navier.Construction.R3CompactCandidate
