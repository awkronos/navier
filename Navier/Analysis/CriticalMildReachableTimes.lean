import Navier.Analysis.CriticalMildLocalSelection

/-!
# Reachable horizons for the critical mild chart

This is an exact set-valued record of horizons carrying the established local
critical-mild fixed-point equation.  It neither asserts maximality nor an
unbounded continuation theorem.
-/

noncomputable section

namespace Navier.Analysis.CriticalMildReachableTimes

open Navier
open Navier.Analysis.CriticalMildLocalSelection
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildPathFixedPoint

/-- Horizons reached by an actual critical-mild path ball with its fixed-point
equation on the full closed interval. -/
def reachableHorizons (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) : Set ℝ :=
  {T | ∃ hT : 0 ≤ T, ∃ R : ℝ, ∃ u : CriticalMildPathBall T R,
    ∀ τ : Set.Icc (0 : ℝ) T,
      u.1 τ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u)
        τ.1 τ.2.1}

/-- The order-theoretic continuation boundary of the actually reachable
horizons.  This is a real supremum only when the reachable set is bounded
above; it is deliberately not identified with a global solution time. -/
def criticalMildMaximalTime
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) : ℝ :=
  sSup (reachableHorizons ν hν a)

/-- Local selection produces a strictly positive reachable horizon. -/
theorem exists_pos_reachableHorizon
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    ∃ T ∈ reachableHorizons ν hν a, 0 < T := by
  obtain ⟨T, R, hT, u, hu⟩ :=
    exists_criticalMild_local_trajectory ν hν a
  refine ⟨T, ?_, hT⟩
  refine ⟨hT.le, R, u, ?_⟩
  intro τ
  simpa using hu τ

/-- A reachable chart can be continued across one freshly selected adjacent
chart.  The result is an actual path on the longer combined horizon satisfying
the original-data mild equation, rather than merely a pair of local charts. -/
theorem exists_larger_reachableHorizon
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    {T : ℝ} (hreachable : T ∈ reachableHorizons ν hν a) :
    ∃ T' ∈ reachableHorizons ν hν a, T < T' := by
  obtain ⟨hT, R, u, hu⟩ := hreachable
  obtain ⟨S, Q, hS, v, hv, hjoin⟩ :=
    exists_criticalMild_adjacent_local_trajectory ν hν u
      ⟨T, ⟨hT, le_rfl⟩⟩
  have hTS : 0 ≤ T + S := add_nonneg hT hS.le
  let hwball : CriticalMildPathBall (T + S) (max R Q) :=
    ⟨criticalMildTwoIntervalPath hT hS.le u v hjoin, by
      intro τ
      change LatticeDivergenceFree
          (criticalMildTwoIntervalExtension hT hS.le u v τ.1) ∧
        ‖criticalMildTwoIntervalExtension hT hS.le u v τ.1‖ ≤ max R Q
      exact ⟨criticalMildTwoIntervalExtension_divergenceFree hT hS.le u v τ.1,
        norm_criticalMildTwoIntervalExtension_le_max hT hS.le u v τ.1⟩⟩
  have hcanonical : ∀ x, LatticeDivergenceFree
      (criticalMildPathExtension (T + S) hTS
        (criticalMildTwoIntervalPath hT hS.le u v hjoin) x) := by
    intro x
    simpa only [hwball] using
      (criticalMildPathBallExtension_divergenceFree hTS hwball x)
  refine ⟨T + S, ⟨hTS, max R Q, hwball, ?_⟩, ?_⟩
  · intro τ
    simpa only [hwball] using
      (criticalMildTwoIntervalPath_satisfies_original_mild ν hν a hT hS.le
        u v hjoin hu hv hcanonical τ)
  · linarith

/-- No reachable horizon is maximal: the one-step continuation theorem gives
a strictly larger reached horizon from any representative. -/
theorem no_reachableHorizon_isGreatest
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    ¬ ∃ T, IsGreatest (reachableHorizons ν hν a) T := by
  rintro ⟨T, hT, hgreatest⟩
  obtain ⟨T', hT', hlt⟩ := exists_larger_reachableHorizon ν hν a hT
  exact (not_le_of_gt hlt) (hgreatest hT')

/-- If the reachable set is bounded above, every reached horizon lies
strictly below its continuation boundary. -/
theorem reachableHorizon_lt_criticalMildMaximalTime
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (hbounded : BddAbove (reachableHorizons ν hν a))
    {T : ℝ} (hT : T ∈ reachableHorizons ν hν a) :
    T < criticalMildMaximalTime ν hν a := by
  obtain ⟨T', hT', hlt⟩ := exists_larger_reachableHorizon ν hν a hT
  exact lt_of_lt_of_le hlt (by
    simpa [criticalMildMaximalTime] using le_csSup hbounded hT')

/-- A finite bounded continuation boundary is not itself a reached horizon.
Thus the strict local-extension theorem yields an exact finite-boundary
alternative, but does not supply a path at that boundary. -/
theorem criticalMildMaximalTime_not_reachable
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (hbounded : BddAbove (reachableHorizons ν hν a)) :
    criticalMildMaximalTime ν hν a ∉ reachableHorizons ν hν a := by
  intro hmax
  have hlt := reachableHorizon_lt_criticalMildMaximalTime ν hν a hbounded hmax
  exact (lt_irrefl _) hlt

/-- Precise continuation alternative supplied by the local construction:
either reachable horizons are unbounded, or their bounded supremum is an
unreached boundary strictly above every reached horizon. -/
theorem criticalMild_continuation_alternative
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    (¬ BddAbove (reachableHorizons ν hν a)) ∨
      (BddAbove (reachableHorizons ν hν a) ∧
        (∀ T ∈ reachableHorizons ν hν a, T < criticalMildMaximalTime ν hν a) ∧
        criticalMildMaximalTime ν hν a ∉ reachableHorizons ν hν a) := by
  classical
  by_cases hbounded : BddAbove (reachableHorizons ν hν a)
  · right
    exact ⟨hbounded,
      fun T hT => reachableHorizon_lt_criticalMildMaximalTime ν hν a hbounded hT,
      criticalMildMaximalTime_not_reachable ν hν a hbounded⟩
  · exact Or.inl hbounded

end Navier.Analysis.CriticalMildReachableTimes

#print axioms Navier.Analysis.CriticalMildReachableTimes.exists_pos_reachableHorizon
#print axioms Navier.Analysis.CriticalMildReachableTimes.exists_larger_reachableHorizon
#print axioms Navier.Analysis.CriticalMildReachableTimes.no_reachableHorizon_isGreatest
#print axioms Navier.Analysis.CriticalMildReachableTimes.reachableHorizon_lt_criticalMildMaximalTime
#print axioms Navier.Analysis.CriticalMildReachableTimes.criticalMildMaximalTime_not_reachable
#print axioms Navier.Analysis.CriticalMildReachableTimes.criticalMild_continuation_alternative
