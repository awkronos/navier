import Navier.Analysis.CriticalMildRestartFixedPoint

/-!
# Explicit local critical mild selection
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildLocalSelection

open Navier
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildPathFixedPoint

/-- Every completed terminal datum admits an explicit positive radius and
horizon satisfying the local-ball budget and contraction inequalities. -/
theorem exists_criticalMild_local_selection
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    ∃ T R : ℝ, 0 < T ∧ 0 < R ∧
      ‖a‖ + (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 ≤ R ∧
      (4 * Real.sqrt T / Real.sqrt ν) * R < 1 := by
  let R : ℝ := ‖a‖ + 1
  let T : ℝ := (Real.sqrt ν / (8 * R ^ 2)) ^ 2
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg a]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hνsqrt : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hden : 0 < 8 * R ^ 2 := by positivity
  have hq : 0 < Real.sqrt ν / (8 * R ^ 2) := div_pos hνsqrt hden
  have hsqrt : Real.sqrt T = Real.sqrt ν / (8 * R ^ 2) := by
    dsimp [T]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
  refine ⟨T, R, sq_pos_of_pos hq, hRpos, ?_, ?_⟩
  · rw [hsqrt]
    dsimp [R]
    have hs : Real.sqrt ν ≠ 0 := ne_of_gt hνsqrt
    field_simp
    nlinarith [sq_nonneg R]
  · rw [hsqrt]
    have hs : Real.sqrt ν ≠ 0 := ne_of_gt hνsqrt
    field_simp
    nlinarith [hR]

/-- The explicit selection feeds the existing Banach local-trajectory theorem. -/
theorem exists_criticalMild_local_trajectory
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) :
    ∃ T R : ℝ, ∃ hT : 0 < T,
      ∃ u : CriticalMildPathBall T R,
        ∀ τ : Set.Icc (0 : ℝ) T,
          u.1 τ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν a
            (criticalMildPathExtension T hT.le u.1)
            (criticalMildPathBallExtension_divergenceFree hT.le u)
            τ.1 τ.2.1 := by
  obtain ⟨T, R, hT, hR, hbudget, hcontr⟩ :=
    exists_criticalMild_local_selection ν hν a
  obtain ⟨u, hu⟩ := exists_criticalMild_trajectory
    ν hν a hT.le hR.le hbudget hcontr
  exact ⟨T, R, hT, u, hu⟩

/-- A divergence-free terminal carrier always starts a fresh positive-time
local mild trajectory.  This is the one-step continuation interface used at
adjacent restart times. -/
theorem exists_criticalMild_terminal_continuation
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a) :
    ∃ T R : ℝ, ∃ hT : 0 < T,
      ∃ u : CriticalMildPathBall T R,
        (∀ τ : Set.Icc (0 : ℝ) T,
          u.1 τ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν a
            (criticalMildPathExtension T hT.le u.1)
            (criticalMildPathBallExtension_divergenceFree hT.le u)
            τ.1 τ.2.1) ∧
        u.1 ⟨0, ⟨le_rfl, hT.le⟩⟩ = a := by
  obtain ⟨T, R, hT, u, hu⟩ :=
    exists_criticalMild_local_trajectory ν hν a
  refine ⟨T, R, hT, u, hu, ?_⟩
  have hzero := hu ⟨0, ⟨le_rfl, hT.le⟩⟩
  rw [Navier.Analysis.CriticalMildSelfMap.criticalMildImage_zero_nonlinear] at hzero
  rw [weightedHeatFlow_zero_of_divergenceFree ν hν.le a ha] at hzero
  exact hzero

/-- Applying the terminal-continuation interface to any point of an existing
local path supplies the next adjacent local trajectory, initialized at that
terminal carrier.  This does not yet assert a glued path across the join. -/
theorem exists_criticalMild_adjacent_local_trajectory
    (ν : ℝ) (hν : 0 < ν) {T R : ℝ}
    (u : CriticalMildPathBall T R) (t : Set.Icc (0 : ℝ) T) :
    ∃ S Q : ℝ, ∃ hS : 0 < S,
      ∃ v : CriticalMildPathBall S Q,
        (∀ σ : Set.Icc (0 : ℝ) S,
          v.1 σ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν (u.1 t)
            (criticalMildPathExtension S hS.le v.1)
            (criticalMildPathBallExtension_divergenceFree hS.le v)
            σ.1 σ.2.1) ∧
        v.1 ⟨0, ⟨le_rfl, hS.le⟩⟩ = u.1 t := by
  exact exists_criticalMild_terminal_continuation ν hν (u.1 t)
    (criticalMildPathBall_divergenceFree u t)

end Navier.Analysis.CriticalMildLocalSelection

#print axioms Navier.Analysis.CriticalMildLocalSelection.exists_criticalMild_local_selection
#print axioms Navier.Analysis.CriticalMildLocalSelection.exists_criticalMild_terminal_continuation
#print axioms Navier.Analysis.CriticalMildLocalSelection.exists_criticalMild_adjacent_local_trajectory
