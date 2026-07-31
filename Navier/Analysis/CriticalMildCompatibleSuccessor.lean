import Navier.Analysis.CriticalMildRestrictionCompatibility

/-!
# Compatible successors for critical mild paths

This is scientific-frontier construction infrastructure.  It realizes one
compatible successor from a finite mild witness, but neither chooses an
infinite family nor constructs a direct limit.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildCompatibleSuccessor

open Navier
open Set
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildLocalSelection
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildRestrictionCompatibility
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach

/-- Every actual finite-horizon mild witness has a strictly longer witness
whose underlying path restricts exactly to the old path.  The radius may grow
to `max R Q`, so the equality is stated on paths rather than on radius-indexed
subtypes. -/
theorem exists_criticalMild_compatible_successor
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R)
    (hu : ∀ τ : Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) :
    ∃ T' R' : ℝ, ∃ w : CriticalMildPathBall T' R', ∃ hTT' : T < T',
      criticalMildPathRestrict (le_of_lt hTT') w.1 = u.1 ∧
      ∀ τ : Icc (0 : ℝ) T',
        w.1 τ = criticalMildImage ν hν a
          (criticalMildPathExtension T' (le_trans hT hTT'.le) w.1)
          (criticalMildPathBallExtension_divergenceFree
            (le_trans hT hTT'.le) w) τ.1 τ.2.1 := by
  obtain ⟨S, Q, hS, v, hv, hjoin⟩ :=
    exists_criticalMild_adjacent_local_trajectory ν hν u ⟨T, ⟨hT, le_rfl⟩⟩
  let w : CriticalMildPathBall (T + S) (max R Q) :=
    ⟨criticalMildTwoIntervalPath hT hS.le u v hjoin, by
      intro τ
      change LatticeDivergenceFree
          (criticalMildTwoIntervalExtension hT hS.le u v τ.1) ∧
        ‖criticalMildTwoIntervalExtension hT hS.le u v τ.1‖ ≤ max R Q
      exact ⟨criticalMildTwoIntervalExtension_divergenceFree hT hS.le u v τ.1,
        norm_criticalMildTwoIntervalExtension_le_max hT hS.le u v τ.1⟩⟩
  have hTS : 0 ≤ T + S := add_nonneg hT hS.le
  have hcanonical : ∀ x, LatticeDivergenceFree
      (criticalMildPathExtension (T + S) hTS
        (criticalMildTwoIntervalPath hT hS.le u v hjoin) x) := by
    intro x
    simpa only [w] using
      (criticalMildPathBallExtension_divergenceFree hTS w x)
  have hstrict : T < T + S := by linarith
  refine ⟨T + S, max R Q, w, hstrict, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro τ
    change criticalMildTwoIntervalPath hT hS.le u v hjoin
        (criticalMildTimeInclusion (le_of_lt hstrict) τ) = u.1 τ
    simpa [criticalMildTimeInclusion] using
      (criticalMildTwoIntervalPath_apply_of_le hT hS.le u v hjoin
        (criticalMildTimeInclusion (le_of_lt hstrict) τ) τ.2.2)
  · intro τ
    simpa only [w] using
      (criticalMildTwoIntervalPath_satisfies_original_mild ν hν a hT hS.le
        u v hjoin hu hv hcanonical τ)

end Navier.Analysis.CriticalMildCompatibleSuccessor

#print axioms Navier.Analysis.CriticalMildCompatibleSuccessor.exists_criticalMild_compatible_successor
