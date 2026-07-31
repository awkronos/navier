import Navier.Analysis.CriticalMildLocalSelection

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildQuantitativeRestart

open Set
open Navier
open Navier.Analysis.CriticalMildLocalSelection
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildRestart
open Navier.Analysis.CriticalMildObservationContinuity
open Navier.Analysis.CriticalMildHeatFlow

/-- The explicit contraction selector controlled by a norm bound `M`. -/
def criticalMildBoundedRadius (M : ℝ) : ℝ := M + 1
def criticalMildBoundedHorizon (ν M : ℝ) : ℝ :=
  (Real.sqrt ν / (8 * (criticalMildBoundedRadius M) ^ 2)) ^ 2

/-- On one restart interval, the actual terminal-data heat evolution and the
literal shifted Duhamel integral propagate a radius bound by the explicit
critical `sqrt` budget.  This is an estimate, rather than a continuation
assumption: its right-hand side is obtained from the heat contraction and the
Bochner tail estimate. -/
theorem norm_criticalMildRestartImage_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t r : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (huR : ∀ s ∈ Set.Ioc (0 : ℝ) (t + r), ‖u s‖ ≤ R) :
    ‖criticalMildRestartImage ν hν u hu t r hr‖ ≤
      ‖u t‖ + (2 * Real.sqrt r / Real.sqrt ν) * R ^ 2 := by
  unfold criticalMildRestartImage criticalMildTerminalData
  calc
    ‖weightedHeatFlow ν r hν.le hr (u t) +
        criticalMildDuhamelRestartTail ν hν u hu t r‖ ≤
      ‖weightedHeatFlow ν r hν.le hr (u t)‖ +
        ‖criticalMildDuhamelRestartTail ν hν u hu t r‖ := norm_add_le _ _
    _ ≤ ‖u t‖ + (2 * Real.sqrt r / Real.sqrt ν) * R ^ 2 := by
      exact add_le_add
        (norm_weightedHeatFlow_le ν r hν.le hr (u t))
        (by
          rw [criticalMildDuhamelRestartTail_eq_tail ν hν u hu t r hr]
          simpa only [add_sub_cancel_left] using
            norm_criticalMildDuhamelTail_le_sqrt_sub
              ν hν u huc hu hR ht (show t ≤ t + r by linarith) huR)

/-- A bounded terminal value therefore stays inside the explicitly enlarged
radius on a single restart interval. -/
theorem norm_criticalMildRestartImage_le_terminal_budget
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {M R t r : ℝ} (hM : ‖u t‖ ≤ M) (hR : 0 ≤ R) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (huR : ∀ s ∈ Set.Ioc (0 : ℝ) (t + r), ‖u s‖ ≤ R) :
    ‖criticalMildRestartImage ν hν u hu t r hr‖ ≤
      M + (2 * Real.sqrt r / Real.sqrt ν) * R ^ 2 :=
  (norm_criticalMildRestartImage_le ν hν u huc hu hR ht hr huR).trans
    (by linarith)

theorem exists_criticalMild_trajectory_at_bounded_selector
    (ν : ℝ) (hν : 0 < ν) (M : ℝ) (hM : 0 ≤ M)
    (a : WeightedLatticeBanach) (ha : ‖a‖ ≤ M) :
    ∃ hT : 0 < criticalMildBoundedHorizon ν M,
      ∃ u : CriticalMildPathBall (criticalMildBoundedHorizon ν M)
      (criticalMildBoundedRadius M),
      ∀ τ : Icc (0 : ℝ) (criticalMildBoundedHorizon ν M),
        u.1 τ = criticalMildImage ν hν a
          (criticalMildPathExtension (criticalMildBoundedHorizon ν M)
            hT.le u.1)
          (criticalMildPathBallExtension_divergenceFree hT.le u) τ.1 τ.2.1 := by
  let R := criticalMildBoundedRadius M
  let T := criticalMildBoundedHorizon ν M
  have hR : 1 ≤ R := by dsimp [R, criticalMildBoundedRadius]; linarith
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hRa : ‖a‖ + 1 ≤ R := by
    dsimp [R, criticalMildBoundedRadius]
    linarith
  have hνsqrt : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hden : 0 < 8 * R ^ 2 := by positivity
  have hq : 0 < Real.sqrt ν / (8 * R ^ 2) := div_pos hνsqrt hden
  have hsqrt : Real.sqrt T = Real.sqrt ν / (8 * R ^ 2) := by
    dsimp [T, criticalMildBoundedHorizon]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have hT : 0 < T := sq_pos_of_pos hq
  have hbudget : ‖a‖ + (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 ≤ R := by
    rw [hsqrt]
    have hs : Real.sqrt ν ≠ 0 := ne_of_gt hνsqrt
    field_simp
    nlinarith [sq_nonneg R, hRa]
  have hcontr : (4 * Real.sqrt T / Real.sqrt ν) * R < 1 := by
    rw [hsqrt]
    have hs : Real.sqrt ν ≠ 0 := ne_of_gt hνsqrt
    field_simp
    nlinarith [hR]
  obtain ⟨u, hu⟩ := exists_criticalMild_trajectory ν hν a hT.le hRpos.le hbudget hcontr
  exact ⟨by simpa [T] using hT, u, by simpa [T, R] using hu⟩

end Navier.Analysis.CriticalMildQuantitativeRestart

#print axioms Navier.Analysis.CriticalMildQuantitativeRestart.exists_criticalMild_trajectory_at_bounded_selector
#print axioms Navier.Analysis.CriticalMildQuantitativeRestart.norm_criticalMildRestartImage_le
#print axioms Navier.Analysis.CriticalMildQuantitativeRestart.norm_criticalMildRestartImage_le_terminal_budget
