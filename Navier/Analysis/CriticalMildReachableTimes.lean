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

end Navier.Analysis.CriticalMildReachableTimes

#print axioms Navier.Analysis.CriticalMildReachableTimes.exists_pos_reachableHorizon
