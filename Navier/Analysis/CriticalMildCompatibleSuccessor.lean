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

/-- A finite-horizon witness with the exact original-data mild equation. -/
structure CriticalMildSuccessorState
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) where
  horizon : ℝ
  radius : ℝ
  horizon_nonneg : 0 ≤ horizon
  path : CriticalMildPathBall horizon radius
  mild : ∀ τ : Icc (0 : ℝ) horizon,
    path.1 τ = criticalMildImage ν hν a
      (criticalMildPathExtension horizon horizon_nonneg path.1)
      (criticalMildPathBallExtension_divergenceFree horizon_nonneg path) τ.1 τ.2.1

theorem exists_criticalMild_initialState
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    Nonempty (CriticalMildSuccessorState ν hν a) := by
  obtain ⟨T, R, hT, u, hu⟩ := exists_criticalMild_local_trajectory ν hν a
  exact ⟨⟨T, R, hT.le, u, fun τ => by simpa using hu τ⟩⟩

theorem exists_criticalMild_successorState
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (x : CriticalMildSuccessorState ν hν a) :
    ∃ y : CriticalMildSuccessorState ν hν a, ∃ hxy : x.horizon < y.horizon,
      criticalMildPathRestrict (le_of_lt hxy)
        y.path.1 = x.path.1 := by
  obtain ⟨T', R', w, hTT', hrestrict, hmild⟩ :=
    exists_criticalMild_compatible_successor ν hν a x.horizon_nonneg x.path x.mild
  let y : CriticalMildSuccessorState ν hν a :=
    ⟨T', R', le_trans x.horizon_nonneg hTT'.le, w, by
      intro τ
      simpa using hmild τ⟩
  refine ⟨y, hTT', ?_⟩
  simpa [y] using hrestrict

noncomputable def criticalMildInitialState
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    CriticalMildSuccessorState ν hν a :=
  Classical.choice (exists_criticalMild_initialState ν hν a)

noncomputable def criticalMildSuccessorState.next
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (x : CriticalMildSuccessorState ν hν a) : CriticalMildSuccessorState ν hν a :=
  Classical.choose (exists_criticalMild_successorState ν hν a x)

theorem criticalMildSuccessorState.next_spec
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (x : CriticalMildSuccessorState ν hν a) :
    ∃ hxy : x.horizon < (criticalMildSuccessorState.next ν hν a x).horizon,
      criticalMildPathRestrict (le_of_lt hxy)
        (criticalMildSuccessorState.next ν hν a x).path.1 = x.path.1 :=
  Classical.choose_spec (exists_criticalMild_successorState ν hν a x)

/-- A recursively selected sequence of actual finite mild witnesses. -/
noncomputable def criticalMildCompatibleChain
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) : ℕ →
    CriticalMildSuccessorState ν hν a
  | 0 => criticalMildInitialState ν hν a
  | n + 1 => criticalMildSuccessorState.next ν hν a
      (criticalMildCompatibleChain ν hν a n)

/-- Consecutive members of the recursively selected chain have strictly
increasing horizons and compatible restricted underlying paths. -/
theorem criticalMildCompatibleChain_adjacent
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (n : ℕ) :
    ∃ hxy : (criticalMildCompatibleChain ν hν a n).horizon <
      (criticalMildCompatibleChain ν hν a (n + 1)).horizon,
    criticalMildPathRestrict (le_of_lt hxy)
      (criticalMildCompatibleChain ν hν a (n + 1)).path.1 =
      (criticalMildCompatibleChain ν hν a n).path.1 := by
  exact criticalMildSuccessorState.next_spec ν hν a
    (criticalMildCompatibleChain ν hν a n)

/-- The selected finite-horizon chain is strictly increasing in its horizons. -/
theorem criticalMildCompatibleChain_strictMono
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    StrictMono (fun n => (criticalMildCompatibleChain ν hν a n).horizon) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (criticalMildCompatibleChain_adjacent ν hν a n).choose

/-- Compatibility propagates across every pair of stages by restriction
transitivity.  This is coherence of the finite chain only; it does not form a
direct-limit path. -/
theorem criticalMildCompatibleChain_pairwise
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    {m n : ℕ} (hmn : m ≤ n) :
    criticalMildPathRestrict
      ((criticalMildCompatibleChain_strictMono ν hν a).monotone hmn)
      (criticalMildCompatibleChain ν hν a n).path.1 =
      (criticalMildCompatibleChain ν hν a m).path.1 := by
  induction n, hmn using Nat.le_induction with
  | base =>
      apply ContinuousMap.ext
      intro τ
      rfl
  | @succ n hmn ih =>
      obtain ⟨hnext, hcompat⟩ := criticalMildCompatibleChain_adjacent ν hν a n
      have htrans := criticalMildPathRestrict_trans
        ((criticalMildCompatibleChain_strictMono ν hν a).monotone hmn)
        hnext.le (criticalMildCompatibleChain ν hν a (n + 1)).path.1
      calc
        criticalMildPathRestrict
            ((criticalMildCompatibleChain_strictMono ν hν a).monotone
              (Nat.le_succ_of_le hmn))
            (criticalMildCompatibleChain ν hν a (n + 1)).path.1 =
            criticalMildPathRestrict
              ((criticalMildCompatibleChain_strictMono ν hν a).monotone hmn)
              (criticalMildPathRestrict hnext.le
                (criticalMildCompatibleChain ν hν a (n + 1)).path.1) := by
                  simpa using htrans.symm
        _ = criticalMildPathRestrict
              ((criticalMildCompatibleChain_strictMono ν hν a).monotone hmn)
              (criticalMildCompatibleChain ν hν a n).path.1 := by
                rw [hcompat]
        _ = (criticalMildCompatibleChain ν hν a m).path.1 := ih

end Navier.Analysis.CriticalMildCompatibleSuccessor

#print axioms Navier.Analysis.CriticalMildCompatibleSuccessor.exists_criticalMild_compatible_successor
#print axioms Navier.Analysis.CriticalMildCompatibleSuccessor.criticalMildCompatibleChain_adjacent
#print axioms Navier.Analysis.CriticalMildCompatibleSuccessor.criticalMildCompatibleChain_strictMono
#print axioms Navier.Analysis.CriticalMildCompatibleSuccessor.criticalMildCompatibleChain_pairwise
