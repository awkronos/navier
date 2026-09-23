import Navier.Analysis.ClassRestartDecomposition

/-!
# Classical quantifier order: locally horizon-uniform continuation

`ClassRestartDecomposition` threads the three leaves by a solution class but
keeps the step order of `DatumContinuationFromCriticalControl`: one step
`δ = δ(ν, u₀, M)` serving EVERY horizon `T`.  That order is not what the
Beale–Kato–Majda continuation delivers.  The BKM Grönwall bound reads
`‖u(t)‖_{H^s} ≤ ‖u₀‖_{H^s} · exp(C ∫₀ᵗ (1 + ‖ω‖_{L²} + ‖ω‖_∞ (1 + log⁺ ‖u‖_{H^s})))`,
whose right-hand side grows with `t` through the `1 + ‖ω‖_{L²}` terms even when
`∫ ‖ω‖_∞ ≤ M`; the restart length obtained from it is therefore bounded below
only on bounded horizon sets: `∀ T̄ ∃ δ ∀ T ≤ T̄`, never `∃ δ ∀ T`.  Ledger F-025
records the horizon-uniform step as a non-classical strengthening.

The gluing composition does not need the uniform step.  A chain with horizon-
dependent steps `T_{n+1} = T_n + δ(⌈T_n⌉)` diverges: if it stayed below `B`, all
its steps would be at least `min_{k ≤ ⌈B⌉} δ k > 0`, and the chain would be
unbounded.  So the composition is re-proved here for the classical order
(`wholeSpaceGlobalRegularity_of_localIn_locallyUniform_aprioriIn`); a single
chain is used, no uniqueness between chains is needed.  The restart engine and
its budget decomposition are restated in the same order
(`LocallyUniformRestartIn`, `BudgetPropagationLocallyUniformIn`): the budget
bound `K = K(ν, u₀, M, T̄)` may now depend on the horizon bound, which is exactly
the classical BKM estimate.  The horizon-uniform leaves imply the locally uniform
ones (`..._of_...`), so this file only weakens hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology

namespace Navier.Analysis.ClassRestartLocallyUniform

open Navier Navier.Breakdown Navier.Analysis.GlobalRegularityEndpoint
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Analysis.RestartPaste
open Navier.Analysis.ClassRestartDecomposition

/-! ## The classical-order leaves -/

/-- Datum-dependent continuation, locally uniform in the horizon: for every
horizon bound `T̄` there is one step `δ = δ(ν, u₀, M, T̄)` serving every horizon
`T ≤ T̄`.  This is the quantifier order of the classical continuation criteria. -/
def LocallyUniformContinuationIn (C : SolutionClass) (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ → ∀ M : ℝ≥0,
    ∀ Tbar : ℝ, 0 < Tbar → ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, 0 < T → T ≤ Tbar → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
          SolvesBefore ν (T + δ) u' p' ∧ PressureNormalizedBefore (T + δ) p' ∧
            VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p' ∧
            C.mem 0 (T + δ) u'

/-- The restart engine in the classical order. -/
def LocallyUniformRestartIn (C : SolutionClass) (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ → ∀ M : ℝ≥0,
    ∀ Tbar : ℝ, 0 < Tbar → ∃ h : ℝ, 0 < h ∧
      ∀ T : ℝ, 0 < T → T ≤ Tbar → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ T₀ : ℝ, 0 ≤ T₀ ∧ T₀ < T ∧ ∃ w : VelocityEvolution, ∃ q : PressureEvolution,
          (∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) ∧
          (∀ t : ℝ, T₀ < t → t < T → p t = q t) ∧
          SolvesFrom ν T₀ (T - T₀ + h) w q ∧
          (∀ t : ℝ, T₀ ≤ t → t < T + h → q t 0 = 0) ∧
          C.mem T₀ (T - T₀ + h) w

/-- Budget propagation, locally uniform in the horizon: `K = K(ν, u₀, M, T̄)`
bounds the budget of every preterminal slice of every class solution with
horizon `T ≤ T̄` and `N T u ≤ M`.  This is the BKM Grönwall estimate with its
horizon-dependent constant. -/
def BudgetPropagationLocallyUniformIn (C : SolutionClass) (B : VelocityField → ℝ≥0∞)
    (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ → ∀ M : ℝ≥0,
    ∀ Tbar : ℝ, 0 < Tbar → ∃ K : ℝ≥0, ∀ T : ℝ, 0 < T → T ≤ Tbar →
      ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
      N T u ≤ (M : ℝ≥0∞) → ∀ t : ℝ, 0 ≤ t → t < T → B (u t) ≤ (K : ℝ≥0∞)

/-! ## The horizon-uniform leaves imply the classical-order ones -/

theorem locallyUniformContinuationIn_of_datumContinuationIn {C : SolutionClass}
    {N : CriticalQuantity} (h : DatumContinuationIn C N) :
    LocallyUniformContinuationIn C N := by
  intro ν hν u₀ hu₀ M Tbar _
  obtain ⟨δ, hδ, hstep⟩ := h ν hν u₀ hu₀ M
  exact ⟨δ, hδ, fun T hT _ u p hinit hsol hmem hnorm hN =>
    hstep T hT u p hinit hsol hmem hnorm hN⟩

theorem locallyUniformRestartIn_of_datumRestartIn {C : SolutionClass}
    {N : CriticalQuantity} (h : DatumRestartIn C N) :
    LocallyUniformRestartIn C N := by
  intro ν hν u₀ hu₀ M Tbar _
  obtain ⟨h₀, hh, heng⟩ := h ν hν u₀ hu₀ M
  exact ⟨h₀, hh, fun T hT _ u p hinit hsol hmem hnorm hN =>
    heng T hT u p hinit hsol hmem hnorm hN⟩

theorem budgetPropagationLocallyUniformIn_of_budgetPropagationIn {C : SolutionClass}
    {B : VelocityField → ℝ≥0∞} {N : CriticalQuantity} (h : BudgetPropagationIn C B N) :
    BudgetPropagationLocallyUniformIn C B N := by
  intro ν hν u₀ hu₀ M Tbar _
  obtain ⟨K, hK⟩ := h ν hν u₀ hu₀ M
  exact ⟨K, fun T hT _ u p hinit hsol hmem hN => hK T hT u p hinit hsol hmem hN⟩

/-! ## Engine ⟹ continuation, and the budget decomposition, in the classical order -/

theorem locallyUniformContinuationIn_of_restartIn {C : SolutionClass} {N : CriticalQuantity}
    (hN : LocallyUniformRestartIn C N) : LocallyUniformContinuationIn C N := by
  intro ν hν u₀ hu₀ M Tbar hTbar
  obtain ⟨h, hh, heng⟩ := hN ν hν u₀ hu₀ M Tbar hTbar
  refine ⟨h, hh, fun T hT hTle u p hinit hsol hmem hnorm hNbound => ?_⟩
  obtain ⟨T₀, hT₀, hT₀T, w, q, hv, hp, hw, hq, hwmem⟩ :=
    heng T hT hTle u p hinit hsol hmem hnorm hNbound
  obtain ⟨hsol', hnorm', hv', hp'⟩ := restart_paste_glueAt hT₀ hT₀T hh hsol hnorm hw hq hv hp
  exact ⟨glueAt T u w, glueAt T p q, hsol', hnorm', hv', hp',
    C.glue hT₀ hT₀T hh hmem hwmem hv⟩

/-- The classical-order restart engine from budget existence, locally uniform
budget propagation, and restart uniqueness. -/
theorem locallyUniformRestartIn_of_budget_propagation_uniqueness {C : SolutionClass}
    {B : VelocityField → ℝ≥0∞} {N : CriticalQuantity}
    (hloc : BudgetLocalExistenceIn C B) (hprop : BudgetPropagationLocallyUniformIn C B N)
    (huniq : RestartUniquenessIn C) : LocallyUniformRestartIn C N := by
  intro ν hν u₀ hu₀ M Tbar hTbar
  obtain ⟨K, hK⟩ := hprop ν hν u₀ hu₀ M Tbar hTbar
  obtain ⟨h, hh, hrestart⟩ := hloc ν hν K
  refine ⟨h / 2, by positivity, fun T hT hTle u p hinit hsol hmem hnorm hN => ?_⟩
  set T₀ : ℝ := max 0 (T - h / 2) with hT₀_def
  have hT₀0 : 0 ≤ T₀ := le_max_left _ _
  have hT₀T : T₀ < T := max_lt hT (by linarith)
  have hTle' : T - T₀ ≤ h / 2 := by
    have := le_max_right 0 (T - h / 2)
    linarith
  have hB : B (u T₀) ≤ (K : ℝ≥0∞) := hK T hT hTle u p hinit hsol hmem hN T₀ hT₀0 hT₀T
  obtain ⟨w, q, hw0, hw, hqn, hwmem⟩ := hrestart T₀ T hT₀0 hT₀T u p hsol hmem hB
  have hagree_v : ∀ t : ℝ, T₀ ≤ t → t < T → u t = w t := fun t ht htT =>
    huniq ν hν T₀ T h hT₀0 hT₀T hh u p w q hsol hmem hw hwmem hw0 t ht htT (by linarith)
  refine ⟨T₀, hT₀0, hT₀T, w, q, hagree_v, ?_, solvesFrom_mono_right hw (by linarith),
    fun t ht htL => hqn t ht (by linarith), C.mono_right hwmem (by linarith)⟩
  intro t ht0 htT
  exact pressure_eq_of_velocity_eq_interior hT₀0 hsol hw hnorm hqn
    (fun s hs hsT _ => hagree_v s hs hsT) ht0 htT (by linarith)

/-! ## The composition with horizon-dependent steps -/

/-- **Chain assembly (sub-keystone of the composition).**  A monotone,
unbounded chain of class stages, each agreeing with its successor before its
own horizon, assembles into a global classical solution; the class membership
is not needed at this point.  Shared by the horizon-uniform and the classical-
order compositions. -/
theorem wholeSpaceGlobalRegularity_of_chain_aux {C : SolutionClass} {ν : ℝ}
    {u₀ : SchwartzVelocity} (stage : ℕ → ClassStage C ν u₀)
    (hmono : Monotone fun n : ℕ => (stage n).horizon)
    (hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < (stage n).horizon)
    (hnext_v : ∀ n : ℕ, VelocityAgreesBefore (stage n).horizon (stage n).vel (stage (n + 1)).vel)
    (hnext_p : ∀ n : ℕ, PressureAgreesBefore (stage n).horizon (stage n).pres (stage (n + 1)).pres) :
    ∃ (u : VelocityEvolution) (p : PressureEvolution), IsClassicalSolution ν zeroForce u₀ u p := by
  choose idx hidx using hunbounded
  have hidx_lt : ∀ t : ℝ, 0 ≤ t → t < (stage (idx t)).horizon := fun t _ => hidx t
  have hagree_v : ∀ n m : ℕ, n ≤ m →
      VelocityAgreesBefore (stage n).horizon (stage n).vel (stage m).vel := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro t _ _; rfl
    | succ k hk ih =>
        intro t ht htn
        have hkn : (stage n).horizon ≤ (stage k).horizon := hmono hk
        rw [ih t ht htn]
        exact hnext_v k t ht (lt_of_lt_of_le htn hkn)
  have hagree_p : ∀ n m : ℕ, n ≤ m →
      PressureAgreesBefore (stage n).horizon (stage n).pres (stage m).pres := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro t _ _; rfl
    | succ k hk ih =>
        intro t ht htn
        have hkn : (stage n).horizon ≤ (stage k).horizon := hmono hk
        rw [ih t ht htn]
        exact hnext_p k t ht (lt_of_lt_of_le htn hkn)
  let U : VelocityEvolution := fun t => (stage (idx t)).vel t
  let P : PressureEvolution := fun t => (stage (idx t)).pres t
  have hinit : ∀ x : Space, U 0 x = u₀ x := by
    intro x
    exact (stage (idx 0)).init x
  have hkey_v : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, t < (stage n).horizon →
      U t = (stage n).vel t := by
    intro t ht n hn
    have h1 := hagree_v (idx t) (max (idx t) n) (le_max_left _ _) t ht
      (hidx_lt t ht)
    have h2 := hagree_v n (max (idx t) n) (le_max_right _ _) t ht hn
    change (stage (idx t)).vel t = (stage n).vel t
    rw [h1, h2]
  have hkey_p : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, t < (stage n).horizon →
      P t = (stage n).pres t := by
    intro t ht n hn
    have h1 := hagree_p (idx t) (max (idx t) n) (le_max_left _ _) t ht
      (hidx_lt t ht)
    have h2 := hagree_p n (max (idx t) n) (le_max_right _ _) t ht hn
    change (stage (idx t)).pres t = (stage n).pres t
    rw [h1, h2]
  have hbefore : ∀ T : ℝ, 0 < T → OriginalSolvesBefore ν T U P := by
    intro T hT
    obtain ⟨n, hTn⟩ : ∃ n : ℕ, T < (stage n).horizon :=
      ⟨idx T, hidx_lt T hT.le⟩
    obtain ⟨hvsm, hpsm, hinc, heq⟩ := (stage n).solves.classical
    have hveq : ∀ t : ℝ, 0 ≤ t → t < T → U t = (stage n).vel t :=
      fun t ht htT => hkey_v t ht n (lt_trans htT hTn)
    have hpeq : ∀ t : ℝ, 0 ≤ t → t < T → P t = (stage n).pres t :=
      fun t ht htT => hkey_p t ht n (lt_trans htT hTn)
    have hsub : Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set Space) ⊆
        spacetimeBefore (stage n).horizon :=
      Set.prod_mono (Set.Ico_subset_Ico_right hTn.le) (subset_refl _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ((hvsm.mono hsub).congr ?_)
      rintro ⟨t, x⟩ ⟨ht, -⟩
      exact congrFun (hveq t ht.1 ht.2) x
    · refine ((hpsm.mono hsub).congr ?_)
      rintro ⟨t, x⟩ ⟨ht, -⟩
      exact congrFun (hpeq t ht.1 ht.2) x
    · intro t ht htT x
      have : divergence U t x = divergence (stage n).vel t x := by
        simp only [divergence, spatialDerivative, hveq t ht htT]
      rw [this]
      exact hinc t ht (lt_trans htT hTn) x
    · intro t ht htT x
      have htn : t < (stage n).horizon := lt_trans htT hTn
      have htime : timeDerivative U t x = timeDerivative (stage n).vel t x :=
        timeDerivative_congr_before (T := T) hveq ht htT x
      have hslice : U t = (stage n).vel t := hveq t ht htT
      have hpslice : P t = (stage n).pres t := hpeq t ht htT
      have hconv : convection U t x = convection (stage n).vel t x := by
        simp only [convection, spatialDerivative, hslice]
      have hlap : laplacian U t x = laplacian (stage n).vel t x := by
        simp only [laplacian, hslice]
      have hgrad : pressureGradient P t x = pressureGradient (stage n).pres t x := by
        unfold pressureGradient
        rw [hpslice]
      rw [htime, hconv, hlap, hgrad]
      exact heq t ht htn x
  have hvelocity : SmoothVelocityOnNonnegativeTime U :=
    contDiffOn_ici_of_forall_before (fun T hT => (hbefore T hT).1)
  have hpressure : SmoothPressureOnNonnegativeTime P :=
    contDiffOn_ici_of_forall_before (fun T hT => (hbefore T hT).2.1)
  have hincompressible : Incompressible U := by
    intro t ht x
    exact (hbefore (t + 1) (by linarith)).2.2.1 t ht (by linarith) x
  have hequation : SatisfiesNavierStokes ν zeroForce U P := by
    intro t ht x
    exact (hbefore (t + 1) (by linarith)).2.2.2 t ht (by linarith) x
  have hfinite : ∀ t : ℝ, 0 ≤ t →
      MeasureTheory.Integrable (fun x : Space => ‖U t x‖ ^ 2) := by
    intro t ht
    exact (stage (idx t)).solves.finite_energy t ht (hidx_lt t ht)
  have henergy : ∀ t : ℝ, 0 ≤ t → kineticEnergy U t ≤ kineticEnergy U 0 := by
    intro t ht
    have hle := (stage (idx t)).solves.energy_le_initial t ht (hidx_lt t ht)
    have hleft : kineticEnergy U t = kineticEnergy (stage (idx t)).vel t := by
      unfold kineticEnergy
      rw [hkey_v t ht (idx t) (hidx_lt t ht)]
    have hright : kineticEnergy (stage (idx t)).vel 0 = kineticEnergy U 0 := by
      unfold kineticEnergy
      congr 1
      funext x
      rw [(stage (idx t)).init x, hinit x]
    rw [hleft]
    exact hle.trans_eq hright
  have hbounded : ∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → kineticEnergy U t < E := by
    refine ⟨|kineticEnergy U 0| + 1, by positivity, ?_⟩
    intro t ht
    have hstrict : kineticEnergy U 0 < |kineticEnergy U 0| + 1 := by
      linarith [le_abs_self (kineticEnergy U 0)]
    exact lt_of_le_of_lt (henergy t ht) hstrict
  exact ⟨U, P, {
    velocity_smooth := hvelocity
    pressure_smooth := hpressure
    initial_condition := hinit
    incompressible := hincompressible
    equation := hequation
    finite_energy := hfinite
    uniformly_bounded_energy := hbounded }⟩


/-- **The composition in the classical order.**  The chain advances from
horizon `T` by the step `δ ⌈T⌉₊`, where `δ k` is the step serving every horizon
`≤ k + 1`; the chain is unbounded because a bounded chain would take steps of
size at least the positive minimum of finitely many `δ k`. -/
theorem wholeSpaceGlobalRegularity_of_localIn_locallyUniform_aprioriIn
    (C : SolutionClass) (N : CriticalQuantity)
    (hlocal : LocalExistenceIn C)
    (hcont : LocallyUniformContinuationIn C N)
    (hapriori : APrioriCriticalControlIn C N) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  intro ν hν u₀ hdiv
  obtain ⟨M, hM⟩ := hapriori ν hν u₀ hdiv
  have hstepAll : ∀ n : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, 0 < T → T ≤ (n : ℝ) + 1 → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
          SolvesBefore ν (T + δ) u' p' ∧ PressureNormalizedBefore (T + δ) p' ∧
            VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p' ∧
            C.mem 0 (T + δ) u' :=
    fun n => hcont ν hν u₀ hdiv M ((n : ℝ) + 1) (by positivity)
  choose δ hδpos hstep using hstepAll
  obtain ⟨T₀, hT₀, v₀, q₀, hinit₀, hsolves₀, hmem₀⟩ := hlocal ν hν u₀ hdiv
  let base : ClassStage C ν u₀ :=
    { horizon := T₀, vel := v₀, pres := normalizePressure q₀, horizon_pos := hT₀,
      init := hinit₀, solves := hsolves₀.normalizePressure,
      pressure_normalized := normalizePressure_normalizedBefore T₀ q₀, mem := hmem₀ }
  have advance : ∀ s : ClassStage C ν u₀, ∃ s' : ClassStage C ν u₀,
      s'.horizon = s.horizon + δ ⌈s.horizon⌉₊ ∧
        VelocityAgreesBefore s.horizon s.vel s'.vel ∧
        PressureAgreesBefore s.horizon s.pres s'.pres := by
    intro s
    have hle : s.horizon ≤ (⌈s.horizon⌉₊ : ℝ) + 1 := (Nat.le_ceil _).trans (by linarith)
    obtain ⟨u', p', hsolve', hpnormalized', hvagree, hpagree, hmem'⟩ :=
      hstep ⌈s.horizon⌉₊ s.horizon s.horizon_pos hle s.vel s.pres s.init s.solves s.mem
        s.pressure_normalized
        (hM s.horizon s.horizon_pos s.vel s.pres s.init s.solves s.mem)
    refine ⟨{ horizon := s.horizon + δ ⌈s.horizon⌉₊, vel := u', pres := p',
              horizon_pos := by linarith [s.horizon_pos, hδpos ⌈s.horizon⌉₊],
              init := ?_, solves := hsolve', pressure_normalized := hpnormalized',
              mem := hmem' },
      rfl, hvagree, hpagree⟩
    intro x
    have h0 := hvagree 0 le_rfl s.horizon_pos
    rw [← congrFun h0 x]
    exact s.init x
  choose next hnext_h hnext_v hnext_p using advance
  set stage : ℕ → ClassStage C ν u₀ := fun n => Nat.rec base (fun _ s => next s) n
    with hstage_def
  have hstage_succ : ∀ n : ℕ, stage (n + 1) = next (stage n) := fun _ => rfl
  have hstage_zero : stage 0 = base := rfl
  have hsucc_lt : ∀ n : ℕ, (stage n).horizon < (stage (n + 1)).horizon := by
    intro n
    rw [hstage_succ n, hnext_h (stage n)]
    linarith [hδpos ⌈(stage n).horizon⌉₊]
  have hmono : Monotone fun n : ℕ => (stage n).horizon :=
    monotone_nat_of_le_succ fun n => (hsucc_lt n).le
  have hunbounded : ∀ t : ℝ, ∃ n : ℕ, t < (stage n).horizon := by
    intro t
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, -, hmin⟩ := (Finset.range (⌈t⌉₊ + 1)).exists_min_image δ
      ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    have hε : 0 < δ k₀ := hδpos k₀
    have hgrow : ∀ n : ℕ, T₀ + n * δ k₀ ≤ (stage n).horizon := by
      intro n
      induction n with
      | zero => simp [hstage_zero, base]
      | succ k ih =>
          rw [hstage_succ k, hnext_h (stage k)]
          have hk : ⌈(stage k).horizon⌉₊ ≤ ⌈t⌉₊ := Nat.ceil_mono (hcon k)
          have hstepk : δ k₀ ≤ δ ⌈(stage k).horizon⌉₊ :=
            hmin _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
          push_cast
          linarith
    obtain ⟨n, hn⟩ := exists_nat_gt ((t - T₀) / δ k₀)
    have hlt : t < T₀ + n * δ k₀ := by
      rw [div_lt_iff₀ hε] at hn
      linarith
    exact absurd (hcon n) (not_le.mpr (lt_of_lt_of_le hlt (hgrow n)))
  exact wholeSpaceGlobalRegularity_of_chain_aux stage hmono hunbounded
    (fun n => by rw [hstage_succ n]; exact hnext_v (stage n))
    (fun n => by rw [hstage_succ n]; exact hnext_p (stage n))

/-- The horizon-uniform composition of `ClassRestartDecomposition` is the
special case of the classical-order one. -/
theorem wholeSpaceGlobalRegularity_of_localIn_datumContinuationIn_aprioriIn_viaLocallyUniform
    (C : SolutionClass) (N : CriticalQuantity)
    (hlocal : LocalExistenceIn C)
    (hcont : DatumContinuationIn C N)
    (hapriori : APrioriCriticalControlIn C N) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_localIn_locallyUniform_aprioriIn C N hlocal
    (locallyUniformContinuationIn_of_datumContinuationIn hcont) hapriori

/-- **The whole-space endpoint from classical-order class leaves.**  Local
existence in the class, the BKM a priori bound on class solutions, budget local
existence, horizon-locally-uniform budget propagation under the BKM integral
(the classical BKM Grönwall bound, constants allowed to depend on the horizon
bound), and restart uniqueness in the class. -/
theorem wholeSpaceGlobalRegularity_of_classBudgetRestart_locallyUniform
    (C : SolutionClass) (B : VelocityField → ℝ≥0∞)
    (hlocal : LocalExistenceIn C)
    (hbkm : APrioriCriticalControlIn C bkmVorticityControl)
    (hloc : BudgetLocalExistenceIn C B)
    (hprop : BudgetPropagationLocallyUniformIn C B bkmVorticityControl)
    (huniq : RestartUniquenessIn C) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_localIn_locallyUniform_aprioriIn C bkmVorticityControl
    hlocal
    (locallyUniformContinuationIn_of_restartIn
      (locallyUniformRestartIn_of_budget_propagation_uniqueness hloc hprop huniq))
    hbkm

end Navier.Analysis.ClassRestartLocallyUniform

set_option pp.fullNames true in
#check @Navier.Analysis.ClassRestartLocallyUniform.wholeSpaceGlobalRegularity_of_localIn_locallyUniform_aprioriIn
set_option pp.fullNames true in
#check @Navier.Analysis.ClassRestartLocallyUniform.wholeSpaceGlobalRegularity_of_classBudgetRestart_locallyUniform
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartLocallyUniform.locallyUniformContinuationIn_of_restartIn
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartLocallyUniform.locallyUniformRestartIn_of_budget_propagation_uniqueness
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartLocallyUniform.wholeSpaceGlobalRegularity_of_localIn_locallyUniform_aprioriIn
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartLocallyUniform.wholeSpaceGlobalRegularity_of_localIn_datumContinuationIn_aprioriIn_viaLocallyUniform
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartLocallyUniform.wholeSpaceGlobalRegularity_of_classBudgetRestart_locallyUniform
