import Navier.Analysis.CriticalMildDirectLimit
import Navier.Analysis.CriticalMildQuantitativeRestart

/-!
# Quantitative conditional continuation of critical mild paths

The sole scientific hypothesis in this module is `CriticalMildTerminalNormBound`:
every finite original-data mild chart has terminal critical norm at most `M`.
Given it, the concrete Banach selector supplies the same positive duration at
every restart.  This is a conditional continuation theorem, not a proof of the
terminal bound.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildBoundedContinuation

open Set
open Navier
open Navier.Analysis.CriticalMildCompatibleSuccessor
open Navier.Analysis.CriticalMildDirectLimit
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildLocalSelection
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildQuantitativeRestart
open Navier.Analysis.CriticalMildRestrictionCompatibility
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach

/-- The single unproved analytic payload: every finite original-data mild
chart has terminal critical norm at most `M`. -/
def CriticalMildTerminalNormBound (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) : Prop :=
  ∀ {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R),
    (∀ τ : Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) →
      ‖u.1 ⟨T, ⟨hT, le_rfl⟩⟩‖ ≤ M

/-- The explicit restart duration determined only by viscosity and `M`. -/
abbrev boundedRestartDuration (ν M : ℝ) : ℝ :=
  criticalMildBoundedHorizon ν M

theorem boundedRestartDuration_pos (ν : ℝ) (hν : 0 < ν) (M : ℝ) (hM : 0 ≤ M) :
    0 < boundedRestartDuration ν M := by
  unfold boundedRestartDuration criticalMildBoundedHorizon criticalMildBoundedRadius
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hR : 0 < M + 1 := by linarith
  have hden : 0 < 8 * (M + 1) ^ 2 := by positivity
  exact sq_pos_of_pos (div_pos hs hden)

/-- A finite original-data chart, retaining the terminal estimate needed for
the next exact-duration restart. -/
structure CriticalMildBoundedState (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) where
  horizon : ℝ
  radius : ℝ
  horizon_nonneg : 0 ≤ horizon
  path : CriticalMildPathBall horizon radius
  mild : ∀ τ : Icc (0 : ℝ) horizon,
    path.1 τ = criticalMildImage ν hν a
      (criticalMildPathExtension horizon horizon_nonneg path.1)
      (criticalMildPathBallExtension_divergenceFree horizon_nonneg path) τ.1 τ.2.1
  terminal_norm_le : ‖path.1 ⟨horizon, ⟨horizon_nonneg, le_rfl⟩⟩‖ ≤ M

theorem exists_initial_boundedState (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M) :
    ∃ x : CriticalMildBoundedState ν hν a M,
      x.horizon = boundedRestartDuration ν M := by
  obtain ⟨hT, u, hu⟩ :=
    exists_criticalMild_trajectory_at_bounded_selector ν hν M hM a ha
  let x : CriticalMildBoundedState ν hν a M :=
    ⟨boundedRestartDuration ν M, criticalMildBoundedRadius M, hT.le, u, hu,
      hbound hT.le u hu⟩
  exact ⟨x, rfl⟩

/-- A bounded state has a compatible successor whose horizon is increased by
exactly the concrete selector duration. -/
theorem exists_bounded_successor (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M)
    (x : CriticalMildBoundedState ν hν a M) :
    ∃ y : CriticalMildBoundedState ν hν a M,
      ∃ hxy : x.horizon < y.horizon,
        y.horizon = x.horizon + boundedRestartDuration ν M ∧
        criticalMildPathRestrict hxy.le y.path.1 = x.path.1 := by
  let b : WeightedLatticeBanach := x.path.1 ⟨x.horizon, ⟨x.horizon_nonneg, le_rfl⟩⟩
  have hb : ‖b‖ ≤ M := x.terminal_norm_le
  obtain ⟨hS, v, hv⟩ :=
    exists_criticalMild_trajectory_at_bounded_selector ν hν M hM b hb
  have hbdf : LatticeDivergenceFree b :=
    criticalMildPathBall_divergenceFree x.path
      ⟨x.horizon, ⟨x.horizon_nonneg, le_rfl⟩⟩
  have hjoin : v.1 ⟨0, ⟨le_rfl, hS.le⟩⟩ = b := by
    have hz := hv ⟨0, ⟨le_rfl, hS.le⟩⟩
    rw [criticalMildImage_zero_nonlinear] at hz
    rw [Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlow_zero_of_divergenceFree
      ν hν.le b hbdf] at hz
    exact hz
  let w : CriticalMildPathBall (x.horizon + boundedRestartDuration ν M)
      (max x.radius (criticalMildBoundedRadius M)) :=
    ⟨criticalMildTwoIntervalPath x.horizon_nonneg hS.le x.path v hjoin, by
      intro τ
      exact ⟨criticalMildTwoIntervalExtension_divergenceFree
          x.horizon_nonneg hS.le x.path v τ.1,
        norm_criticalMildTwoIntervalExtension_le_max
          x.horizon_nonneg hS.le x.path v τ.1⟩⟩
  have hw_nonneg : 0 ≤ x.horizon + boundedRestartDuration ν M :=
    add_nonneg x.horizon_nonneg (boundedRestartDuration_pos ν hν M hM).le
  have hw_mild : ∀ τ : Icc (0 : ℝ) (x.horizon + boundedRestartDuration ν M),
      w.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension (x.horizon + boundedRestartDuration ν M) hw_nonneg w.1)
        (criticalMildPathBallExtension_divergenceFree hw_nonneg w) τ.1 τ.2.1 := by
    intro τ
    simpa only [w] using criticalMildTwoIntervalPath_satisfies_original_mild
      ν hν a x.horizon_nonneg hS.le x.path v hjoin x.mild hv
      (criticalMildPathBallExtension_divergenceFree hw_nonneg w) τ
  let y : CriticalMildBoundedState ν hν a M :=
    ⟨x.horizon + boundedRestartDuration ν M,
      max x.radius (criticalMildBoundedRadius M), hw_nonneg, w, hw_mild,
      hbound hw_nonneg w hw_mild⟩
  have hxy : x.horizon < y.horizon := by
    dsimp [y]
    linarith [boundedRestartDuration_pos ν hν M hM]
  refine ⟨y, hxy, rfl, ?_⟩
  apply ContinuousMap.ext
  intro τ
  change criticalMildTwoIntervalPath x.horizon_nonneg hS.le x.path v hjoin
      (criticalMildTimeInclusion hxy.le τ) = x.path.1 τ
  simpa [criticalMildTimeInclusion] using
    (criticalMildTwoIntervalPath_apply_of_le x.horizon_nonneg hS.le x.path v hjoin
      (criticalMildTimeInclusion hxy.le τ) τ.2.2)

noncomputable def boundedInitialState (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M) :
    CriticalMildBoundedState ν hν a M :=
  Classical.choose (exists_initial_boundedState ν hν a M hM ha hbound)

theorem boundedInitialState_horizon (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M) :
    (boundedInitialState ν hν a M hM ha hbound).horizon =
      boundedRestartDuration ν M :=
  (Classical.choose_spec (exists_initial_boundedState ν hν a M hM ha hbound))

noncomputable def boundedSuccessorState (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M)
    (x : CriticalMildBoundedState ν hν a M) : CriticalMildBoundedState ν hν a M :=
  Classical.choose (exists_bounded_successor ν hν a M hM hbound x)

theorem boundedSuccessorState_spec (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M)
    (x : CriticalMildBoundedState ν hν a M) :
    ∃ hxy : x.horizon < (boundedSuccessorState ν hν a M hM hbound x).horizon,
      (boundedSuccessorState ν hν a M hM hbound x).horizon =
        x.horizon + boundedRestartDuration ν M ∧
      criticalMildPathRestrict hxy.le
        (boundedSuccessorState ν hν a M hM hbound x).path.1 = x.path.1 :=
  Classical.choose_spec (exists_bounded_successor ν hν a M hM hbound x)

/-- The recursively selected exact-duration continuation chain. -/
noncomputable def boundedContinuationChain (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M) : ℕ →
    CriticalMildBoundedState ν hν a M
  | 0 => boundedInitialState ν hν a M hM ha hbound
  | n + 1 => boundedSuccessorState ν hν a M hM hbound
      (boundedContinuationChain ν hν a M hM ha hbound n)

theorem boundedContinuationChain_succ_horizon (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M) (n : ℕ) :
    (boundedContinuationChain ν hν a M hM ha hbound (n + 1)).horizon =
      (boundedContinuationChain ν hν a M hM ha hbound n).horizon +
        boundedRestartDuration ν M := by
  exact (boundedSuccessorState_spec ν hν a M hM hbound
    (boundedContinuationChain ν hν a M hM ha hbound n)).choose_spec.1

theorem boundedContinuationChain_adjacent_compatible (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M) (n : ℕ) :
    ∃ hxy :
      (boundedContinuationChain ν hν a M hM ha hbound n).horizon <
        (boundedContinuationChain ν hν a M hM ha hbound (n + 1)).horizon,
      criticalMildPathRestrict hxy.le
        (boundedContinuationChain ν hν a M hM ha hbound (n + 1)).path.1 =
          (boundedContinuationChain ν hν a M hM ha hbound n).path.1 := by
  obtain ⟨hxy, _, hcompat⟩ := boundedSuccessorState_spec ν hν a M hM hbound
    (boundedContinuationChain ν hν a M hM ha hbound n)
  refine ⟨?_, ?_⟩
  · simpa only [boundedContinuationChain] using hxy
  · simpa only [boundedContinuationChain] using hcompat

/-- Every stage has the explicit linear lower lifespan bound `Tₙ ≥ (n+1)δ`. -/
theorem boundedContinuationChain_horizon_lower (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * boundedRestartDuration ν M ≤
      (boundedContinuationChain ν hν a M hM ha hbound n).horizon := by
  induction n with
  | zero =>
      change ((0 + 1 : ℕ) : ℝ) * boundedRestartDuration ν M ≤
        (boundedInitialState ν hν a M hM ha hbound).horizon
      rw [boundedInitialState_horizon ν hν a M hM ha hbound]
      norm_num
  | succ n ih =>
      rw [boundedContinuationChain_succ_horizon ν hν a M hM ha hbound n]
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      nlinarith [boundedRestartDuration_pos ν hν M hM]

/-- The horizons of the exact-duration chain are cofinal in the nonnegative
real line.  This is the quantitative continuation conclusion of the sole
terminal-bound hypothesis. -/
theorem boundedContinuationChain_cofinal (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (M : ℝ) (hM : 0 ≤ M) (ha : ‖a‖ ≤ M)
    (hbound : CriticalMildTerminalNormBound ν hν a M) :
    ∀ t : ℝ, 0 ≤ t → ∃ n : ℕ, t ≤
      (boundedContinuationChain ν hν a M hM ha hbound n).horizon := by
  intro t ht
  have hδ := boundedRestartDuration_pos ν hν M hM
  obtain ⟨n, hn⟩ := exists_nat_ge (t / boundedRestartDuration ν M)
  refine ⟨n, le_trans ?_ (boundedContinuationChain_horizon_lower
    ν hν a M hM ha hbound n)⟩
  have hn' : t / boundedRestartDuration ν M ≤ (n : ℝ) := by simpa using hn
  have hnonneg : 0 ≤ boundedRestartDuration ν M := hδ.le
  calc
    t = (t / boundedRestartDuration ν M) * boundedRestartDuration ν M := by
      field_simp
    _ ≤ (n : ℝ) * boundedRestartDuration ν M :=
      mul_le_mul_of_nonneg_right hn' hnonneg
    _ ≤ ((n + 1 : ℕ) : ℝ) * boundedRestartDuration ν M := by
      apply mul_le_mul_of_nonneg_right _ hnonneg
      exact_mod_cast Nat.le_succ n

end Navier.Analysis.CriticalMildBoundedContinuation

#print axioms Navier.Analysis.CriticalMildBoundedContinuation.exists_bounded_successor
#print axioms Navier.Analysis.CriticalMildBoundedContinuation.boundedContinuationChain_horizon_lower
#print axioms Navier.Analysis.CriticalMildBoundedContinuation.boundedContinuationChain_cofinal
