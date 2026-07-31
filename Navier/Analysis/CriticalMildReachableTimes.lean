import Navier.Analysis.CriticalMildLocalSelection

/-!
# Reachable horizons for the critical mild chart

This is an exact set-valued record of horizons carrying the established local
critical-mild fixed-point equation.  It neither asserts maximality nor an
unbounded continuation theorem.
-/

namespace Navier.Analysis.CriticalMildReachableTimes

open Navier.Analysis.CriticalMildLocalSelection
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
  let w : CriticalMildPath (T + S) :=
    criticalMildTwoIntervalPath hT hS.le u v hjoin
  have hTS : 0 ≤ T + S := add_nonneg hT hS.le
  have hwball : CriticalMildPathBall (T + S) (max R Q) := by
    refine ⟨w, ?_⟩
    intro τ
    change LatticeDivergenceFree
        (criticalMildTwoIntervalExtension hT hS.le u v τ.1) ∧
      ‖criticalMildTwoIntervalExtension hT hS.le u v τ.1‖ ≤ max R Q
    exact ⟨criticalMildTwoIntervalExtension_divergenceFree hT hS.le u v τ.1,
      norm_criticalMildTwoIntervalExtension_le_max hT hS.le u v τ.1⟩
  have hcanonical : ∀ x, LatticeDivergenceFree
      (criticalMildPathExtension (T + S) hTS w x) := by
    intro x
    exact criticalMildPathBallExtension_divergenceFree hTS hwball x
  refine ⟨T + S, ⟨hTS, max R Q, w, ?_⟩, ?_⟩
  · intro τ
    simpa [w] using
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

end Navier.Analysis.CriticalMildReachableTimes

#print axioms Navier.Analysis.CriticalMildReachableTimes.exists_pos_reachableHorizon
#print axioms Navier.Analysis.CriticalMildReachableTimes.exists_larger_reachableHorizon
#print axioms Navier.Analysis.CriticalMildReachableTimes.no_reachableHorizon_isGreatest
