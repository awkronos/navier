import Navier.Analysis.CriticalMildRestartFixedPoint

/-!
# Explicit local critical mild selection
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildLocalSelection

open MeasureTheory
open Navier
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildWeightedBanach
open Set
open Navier.Analysis.CriticalMildPathFixedPoint

/-- The real-line representative obtained by joining an old local path to a
subsequent local path.  At the join it takes the old branch; the compatibility
proof below identifies that value with the new branch at elapsed time zero. -/
def criticalMildTwoIntervalExtension
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q) :
    ℝ → WeightedLatticeBanach :=
  (Iic T).piecewise
    (criticalMildPathExtension T hT u.1)
    (fun x => criticalMildPathExtension S hS v.1 (x - T))

/-- The two real-line branches are continuous once the second local path is
initialized by the old terminal carrier. -/
theorem continuous_criticalMildTwoIntervalExtension
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩) :
    Continuous (criticalMildTwoIntervalExtension hT hS u v) := by
  unfold criticalMildTwoIntervalExtension
  apply Continuous.piecewise
  · intro x hx
    rw [frontier_Iic] at hx
    have hxT : x = T := hx
    subst x
    rw [criticalMildPathExtension_apply T hT u.1 ⟨hT, le_rfl⟩]
    have hv0 : criticalMildPathExtension S hS v.1 0 =
        v.1 ⟨0, ⟨le_rfl, hS⟩⟩ :=
      criticalMildPathExtension_apply S hS v.1 ⟨le_rfl, hS⟩
    simpa [hv0] using hjoin.symm
  · exact continuous_criticalMildPathExtension T hT u.1
  · exact (continuous_criticalMildPathExtension S hS v.1).comp
      (continuous_id.sub continuous_const)

/-- In strictly positive elapsed coordinates, the glued extension is exactly
the adjacent chart. -/
theorem criticalMildTwoIntervalExtension_shift_apply
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
    {s : ℝ} (hs : 0 < s) (hsS : s ≤ S) :
    criticalMildTwoIntervalExtension hT hS u v (T + s) = v.1 ⟨s, ⟨hs.le, hsS⟩⟩ := by
  classical
  unfold criticalMildTwoIntervalExtension
  have hnot : T + s ∉ Iic T := by
    show ¬ T + s ≤ T
    linarith
  simp [Set.piecewise, hnot]
  exact criticalMildPathExtension_apply S hS v.1 ⟨hs.le, hsS⟩

/-- The nonlinear integrand in the glued chart translates exactly to the
adjacent chart under `s ↦ T+s`. -/
theorem criticalMildTwoIntervalIntegrand_shift_eq
    (ν : ℝ) (hν : 0 < ν) {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
    (hglue : ∀ x, LatticeDivergenceFree (criticalMildTwoIntervalExtension hT hS u v x))
    {r s : ℝ} (hs : s ∈ Ioc (0 : ℝ) r) (hrS : r ≤ S) :
    criticalMildPathIntegrand ν hν
      (criticalMildTwoIntervalExtension hT hS u v) hglue (T + r) (T + s) =
      criticalMildPathIntegrand ν hν
        (criticalMildPathExtension S hS v.1)
        (criticalMildPathBallExtension_divergenceFree hS v) r s := by
  have hsS : s ≤ S := le_trans hs.2 hrS
  unfold criticalMildPathIntegrand
  have heq : criticalMildTwoIntervalExtension hT hS u v (T + s) =
      v.1 ⟨s, ⟨hs.1.le, hsS⟩⟩ :=
    criticalMildTwoIntervalExtension_shift_apply hT hS u v hjoin hs.1 hsS
  have hev : criticalMildPathExtension S hS v.1 s =
      v.1 ⟨s, ⟨hs.1.le, hsS⟩⟩ :=
    criticalMildPathExtension_apply S hS v.1 ⟨hs.1.le, hsS⟩
  simp only [heq, hev]
  congr 1 <;> ring

/-- The glued restart tail is precisely the adjacent chart's local Duhamel
integral. -/
theorem criticalMildDuhamelRestartTail_glued_eq_adjacent
    (ν : ℝ) (hν : 0 < ν) {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
    (hglue : ∀ x, LatticeDivergenceFree (criticalMildTwoIntervalExtension hT hS u v x))
    {r : ℝ} (hrS : r ≤ S) :
    Navier.Analysis.CriticalMildRestart.criticalMildDuhamelRestartTail ν hν
      (criticalMildTwoIntervalExtension hT hS u v) hglue T r =
      criticalMildDuhamel ν hν (criticalMildPathExtension S hS v.1)
        (criticalMildPathBallExtension_divergenceFree hS v) r := by
  unfold Navier.Analysis.CriticalMildRestart.criticalMildDuhamelRestartTail
    criticalMildDuhamel
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact criticalMildTwoIntervalIntegrand_shift_eq ν hν hT hS u v hjoin hglue hs hrS

/-- The joined real-line representative preserves the divergence-free
constraint on both charts. -/
theorem criticalMildTwoIntervalExtension_divergenceFree
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q) (x : ℝ) :
    LatticeDivergenceFree (criticalMildTwoIntervalExtension hT hS u v x) := by
  classical
  unfold criticalMildTwoIntervalExtension
  by_cases hx : x ≤ T
  · rw [Set.piecewise_eq_of_mem (Iic T) _ _ hx]
    exact criticalMildPathBallExtension_divergenceFree hT u x
  · have hnot : x ∉ Iic T := by exact hx
    simp [Set.piecewise, hnot]
    exact criticalMildPathBallExtension_divergenceFree hS v (x - T)

/-- A single `max R Q` bound controls the joined representative, hence also
its restriction to every finite restart interval. -/
theorem norm_criticalMildTwoIntervalExtension_le_max
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q) (x : ℝ) :
    ‖criticalMildTwoIntervalExtension hT hS u v x‖ ≤ max R Q := by
  classical
  unfold criticalMildTwoIntervalExtension
  by_cases hx : x ≤ T
  · rw [Set.piecewise_eq_of_mem (Iic T) _ _ hx]
    exact le_trans (criticalMildPathBallExtension_norm_le hT u x) (le_max_left _ _)
  · have hnot : x ∉ Iic T := by exact hx
    simp [Set.piecewise, hnot]
    exact Or.inr (criticalMildPathBallExtension_norm_le hS v (x - T))

/-- The joined continuous local path on the combined closed horizon. -/
def criticalMildTwoIntervalPath
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩) :
    CriticalMildPath (T + S) :=
  ⟨fun τ => criticalMildTwoIntervalExtension hT hS u v τ.1,
    (continuous_criticalMildTwoIntervalExtension hT hS u v hjoin).comp
      continuous_subtype_val⟩

/-- Before the join, the combined path is literally the original local path. -/
theorem criticalMildTwoIntervalPath_apply_of_le
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
    (τ : Icc (0 : ℝ) (T + S)) (hτ : τ.1 ≤ T) :
    criticalMildTwoIntervalPath hT hS u v hjoin τ =
      u.1 ⟨τ.1, ⟨τ.2.1, hτ⟩⟩ := by
  classical
  change criticalMildTwoIntervalExtension hT hS u v τ.1 = _
  unfold criticalMildTwoIntervalExtension
  rw [Set.piecewise_eq_of_mem (Iic T) _ _ hτ]
  exact criticalMildPathExtension_apply T hT u.1 ⟨τ.2.1, hτ⟩

/-- Strictly after the join, the combined path is the subsequent local path
in elapsed-time coordinates. -/
theorem criticalMildTwoIntervalPath_apply_of_lt
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
    (τ : Icc (0 : ℝ) (T + S)) (hτ : T < τ.1) :
    criticalMildTwoIntervalPath hT hS u v hjoin τ =
      v.1 ⟨τ.1 - T, ⟨sub_nonneg.mpr hτ.le,
        by linarith [τ.2.2]⟩⟩ := by
  classical
  rw [show criticalMildTwoIntervalPath hT hS u v hjoin τ =
      criticalMildTwoIntervalExtension hT hS u v τ.1 by rfl]
  unfold criticalMildTwoIntervalExtension
  have hnot : τ.1 ∉ Iic T := not_le.mpr hτ
  simp [Set.piecewise, hnot]
  exact criticalMildPathExtension_apply S hS v.1
    ⟨sub_nonneg.mpr hτ.le, by linarith [τ.2.2]⟩

/-- The two continuous charts agree at their common endpoint. -/
theorem criticalMildTwoIntervalPath_join
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩) :
    criticalMildTwoIntervalPath hT hS u v hjoin
      ⟨T, ⟨hT, by linarith⟩⟩ = v.1 ⟨0, ⟨le_rfl, hS⟩⟩ := by
  rw [criticalMildTwoIntervalPath_apply_of_le hT hS u v hjoin
    ⟨T, ⟨hT, by linarith⟩⟩ le_rfl]
  exact hjoin.symm

/-- The mild equation appropriate to a joined pair of local charts: the old
equation holds through the join and the terminal-data equation holds strictly
after it in elapsed coordinates. -/
def SatisfiesCriticalMildTwoInterval
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (w : CriticalMildPath (T + S)) : Prop :=
  (∀ τ : Icc (0 : ℝ) (T + S), τ.1 ≤ T →
    w τ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν u₀
      (criticalMildPathExtension T hT u.1)
      (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) ∧
  (∀ τ : Icc (0 : ℝ) (T + S), (hτ : T < τ.1) →
    w τ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν
      (u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
      (criticalMildPathExtension S hS v.1)
      (criticalMildPathBallExtension_divergenceFree hS v)
      (τ.1 - T) (sub_nonneg.mpr hτ.le))

/-- The explicitly joined path satisfies the two-chart mild equation. -/
theorem criticalMildTwoIntervalPath_satisfies
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    {T R S Q : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (u : CriticalMildPathBall T R) (v : CriticalMildPathBall S Q)
    (hjoin : v.1 ⟨0, ⟨le_rfl, hS⟩⟩ = u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
    (hu : ∀ τ : Icc (0 : ℝ) T,
      u.1 τ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν u₀
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1)
    (hv : ∀ σ : Icc (0 : ℝ) S,
      v.1 σ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν
        (u.1 ⟨T, ⟨hT, le_rfl⟩⟩)
        (criticalMildPathExtension S hS v.1)
        (criticalMildPathBallExtension_divergenceFree hS v) σ.1 σ.2.1) :
    SatisfiesCriticalMildTwoInterval ν hν u₀ hT hS u v
      (criticalMildTwoIntervalPath hT hS u v hjoin) := by
  constructor
  · intro τ hτ
    rw [criticalMildTwoIntervalPath_apply_of_le hT hS u v hjoin τ hτ]
    exact hu ⟨τ.1, ⟨τ.2.1, hτ⟩⟩
  · intro τ hτ
    rw [criticalMildTwoIntervalPath_apply_of_lt hT hS u v hjoin τ hτ]
    exact hv ⟨τ.1 - T, ⟨sub_nonneg.mpr hτ.le, by linarith [τ.2.2]⟩⟩

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

/-- Every fixed-point local path has a selected adjacent chart and hence a
continuous two-interval trajectory satisfying the joined mild equation. -/
theorem exists_criticalMild_glued_twoInterval
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R)
    (hu : ∀ τ : Icc (0 : ℝ) T,
      u.1 τ = Navier.Analysis.CriticalMildSelfMap.criticalMildImage ν hν u₀
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) :
    ∃ S Q : ℝ, ∃ hS : 0 < S, ∃ v : CriticalMildPathBall S Q,
      ∃ w : CriticalMildPath (T + S),
        SatisfiesCriticalMildTwoInterval ν hν u₀ hT hS.le u v w := by
  obtain ⟨S, Q, hS, v, hv, hjoin⟩ :=
    exists_criticalMild_adjacent_local_trajectory ν hν u
      ⟨T, ⟨hT, le_rfl⟩⟩
  refine ⟨S, Q, hS, v, criticalMildTwoIntervalPath hT hS.le u v hjoin, ?_⟩
  exact criticalMildTwoIntervalPath_satisfies ν hν u₀ hT hS.le u v hjoin hu hv

end Navier.Analysis.CriticalMildLocalSelection

#print axioms Navier.Analysis.CriticalMildLocalSelection.exists_criticalMild_local_selection
#print axioms Navier.Analysis.CriticalMildLocalSelection.exists_criticalMild_terminal_continuation
#print axioms Navier.Analysis.CriticalMildLocalSelection.exists_criticalMild_adjacent_local_trajectory
#print axioms Navier.Analysis.CriticalMildLocalSelection.exists_criticalMild_glued_twoInterval
#print axioms Navier.Analysis.CriticalMildLocalSelection.criticalMildDuhamelRestartTail_glued_eq_adjacent
