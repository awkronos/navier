import Navier.Analysis.CriticalControlDecomposition

/-!
# The critical-control decomposition over a solution class

`CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori`
asks its continuation and a priori leaves for EVERY member of the classical class
`SolvesBefore`.  That class is supercritical at spatial infinity (smooth,
`L²` slices, energy at most initial, no dissipation integral, no decay of `∇u`
or `p`), and uniqueness inside it is not known; each universal leaf therefore
carries a hidden uniqueness burden that the existential crown does not (ledger
F-024).  This module restates the composition over an arbitrary class predicate
`C` that is carried along the restart ladder: local existence must land in `C`,
continuation is only requested from members of `C` (and must return one), and
the a priori bound is only requested on members of `C`.  The crown is
unchanged.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal

namespace Navier.Analysis.ClassDecomposition

open Navier Navier.Breakdown Navier.Analysis.GlobalRegularityEndpoint
open Navier.Analysis.CriticalControlDecomposition

/-- A class of velocity evolutions indexed by the horizon. -/
abbrev SolutionClassPred := ℝ → VelocityEvolution → PressureEvolution → Prop

/-- Local existence landing in the class `C`. -/
def LocalClassicalExistenceIn (C : SolutionClassPred) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ T : ℝ, 0 < T ∧ ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧ SolvesBefore ν T u p ∧ C T u p

/-- Datum-dependent continuation requested only from members of `C`, returning
a member of `C`. -/
def DatumContinuationIn (C : SolutionClassPred) (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ M : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C T u p →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
          SolvesBefore ν (T + δ) u' p' ∧ C (T + δ) u' p' ∧
            PressureNormalizedBefore (T + δ) p' ∧
            VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p'

/-- The a priori bound requested only on members of `C`. -/
def APrioriIn (C : SolutionClassPred) (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ M : ℝ≥0, ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C T u p → N T u ≤ (M : ℝ≥0∞)

/-- One rung of the restart ladder inside the class `C`. -/
structure StageIn (C : SolutionClassPred) (ν : ℝ) (u₀ : SchwartzVelocity) where
  horizon : ℝ
  vel : VelocityEvolution
  pres : PressureEvolution
  horizon_pos : 0 < horizon
  init : ∀ x : Space, vel 0 x = u₀ x
  solves : SolvesBefore ν horizon vel pres
  pressure_normalized : PressureNormalizedBefore horizon pres
  reg : C horizon vel pres

/-- **The class-restricted composition.** -/
theorem wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_in
    (C : SolutionClassPred) (N : CriticalQuantity)
    (hnormC : ∀ T u p, C T u p → C T u (normalizePressure p))
    (hlocal : LocalClassicalExistenceIn C)
    (hcont : DatumContinuationIn C N)
    (hapriori : APrioriIn C N) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  intro ν hν u₀ hdiv
  obtain ⟨M, hM⟩ := hapriori ν hν u₀ hdiv
  obtain ⟨δ, hδ, hstep⟩ := hcont ν hν u₀ hdiv M
  obtain ⟨T₀, hT₀, v₀, q₀, hinit₀, hsolves₀, hreg₀⟩ := hlocal ν hν u₀ hdiv
  let base : StageIn C ν u₀ :=
    { horizon := T₀, vel := v₀, pres := normalizePressure q₀, horizon_pos := hT₀,
      init := hinit₀, solves := hsolves₀.normalizePressure,
      pressure_normalized := normalizePressure_normalizedBefore T₀ q₀,
      reg := hnormC T₀ v₀ q₀ hreg₀ }
  have advance : ∀ s : StageIn C ν u₀, ∃ s' : StageIn C ν u₀,
      s'.horizon = s.horizon + δ ∧
        VelocityAgreesBefore s.horizon s.vel s'.vel ∧
        PressureAgreesBefore s.horizon s.pres s'.pres := by
    intro s
    obtain ⟨u', p', hsolve', hreg', hpnormalized', hvagree, hpagree⟩ :=
      hstep s.horizon s.horizon_pos s.vel s.pres s.init s.solves s.reg
        s.pressure_normalized
        (hM s.horizon s.horizon_pos s.vel s.pres s.init s.solves s.reg)
    refine ⟨{ horizon := s.horizon + δ, vel := u', pres := p',
              horizon_pos := by linarith [s.horizon_pos],
              init := ?_, solves := hsolve', pressure_normalized := hpnormalized',
              reg := hreg' },
      rfl, hvagree, hpagree⟩
    intro x
    have h0 := hvagree 0 le_rfl s.horizon_pos
    rw [← congrFun h0 x]
    exact s.init x
  choose next hnext_h hnext_v hnext_p using advance
  set stage : ℕ → StageIn C ν u₀ := fun n => Nat.rec base (fun _ s => next s) n
    with hstage_def
  have hstage_succ : ∀ n : ℕ, stage (n + 1) = next (stage n) := fun _ => rfl
  have hstage_zero : stage 0 = base := rfl
  have hhorizon : ∀ n : ℕ, (stage n).horizon = T₀ + n * δ := by
    intro n
    induction n with
    | zero => simp [hstage_zero, base]
    | succ k ih =>
        rw [hstage_succ k, hnext_h (stage k), ih]
        push_cast
        ring
  have hmono : Monotone fun n : ℕ => (stage n).horizon := by
    intro a b hab
    simp only [hhorizon]
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    nlinarith [hδ.le]
  have hagree_v : ∀ n m : ℕ, n ≤ m →
      VelocityAgreesBefore (stage n).horizon (stage n).vel (stage m).vel := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro t _ _; rfl
    | succ k hk ih =>
        intro t ht htn
        have hkn : (stage n).horizon ≤ (stage k).horizon := hmono hk
        rw [ih t ht htn, hstage_succ k]
        exact hnext_v (stage k) t ht (lt_of_lt_of_le htn hkn)
  have hagree_p : ∀ n m : ℕ, n ≤ m →
      PressureAgreesBefore (stage n).horizon (stage n).pres (stage m).pres := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro t _ _; rfl
    | succ k hk ih =>
        intro t ht htn
        have hkn : (stage n).horizon ≤ (stage k).horizon := hmono hk
        rw [ih t ht htn, hstage_succ k]
        exact hnext_p (stage k) t ht (lt_of_lt_of_le htn hkn)
  set idx : ℝ → ℕ := fun t => ⌈t / δ⌉₊ with hidx_def
  have hidx_lt : ∀ t : ℝ, 0 ≤ t → t < (stage (idx t)).horizon := by
    intro t ht
    rw [hhorizon]
    have hceil : t / δ ≤ (⌈t / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hmul : t ≤ (⌈t / δ⌉₊ : ℝ) * δ := by
      have := mul_le_mul_of_nonneg_right hceil hδ.le
      rwa [div_mul_cancel₀ t (ne_of_gt hδ)] at this
    simp only [hidx_def]
    linarith
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


/-! ## The restatement only weakens the a priori and local obligations -/

/-- The universal a priori leaf implies its class restriction. -/
theorem aprioriIn_of_apriori (C : SolutionClassPred) {N : CriticalQuantity}
    (h : APrioriCriticalControl N) : APrioriIn C N := by
  intro ν hν u₀ hdiv
  obtain ⟨M, hM⟩ := h ν hν u₀ hdiv
  exact ⟨M, fun T hT u p hinit hsol _ => hM T hT u p hinit hsol⟩

/-- Local existence in a class implies plain local existence. -/
theorem localClassicalExistence_of_in (C : SolutionClassPred)
    (h : LocalClassicalExistenceIn C) : LocalClassicalExistence := by
  intro ν hν u₀ hdiv
  obtain ⟨T, hT, u, p, hinit, hsol, -⟩ := h ν hν u₀ hdiv
  exact ⟨T, hT, u, p, hinit, hsol⟩

/-- For the trivial class the restated leaves are exactly the old ones: the old
continuation leaf implies the restated one, so the old consumer factors through
the class-restricted consumer. -/
theorem datumContinuationIn_true_of {N : CriticalQuantity}
    (h : DatumContinuationFromCriticalControl N) :
    DatumContinuationIn (fun _ _ _ => True) N := by
  intro ν hν u₀ hdiv M
  obtain ⟨δ, hδ, hstep⟩ := h ν hν u₀ hdiv M
  refine ⟨δ, hδ, fun T hT u p hinit hsol _ hnorm hN => ?_⟩
  obtain ⟨u', p', h1, h2, h3, h4⟩ := hstep T hT u p hinit hsol hnorm hN
  exact ⟨u', p', h1, trivial, h2, h3, h4⟩

theorem wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_via_class
    (N : CriticalQuantity) (hlocal : LocalClassicalExistence)
    (hcont : DatumContinuationFromCriticalControl N) (hapriori : APrioriCriticalControl N) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_in (fun _ _ _ => True) N
    (fun _ _ _ _ => trivial)
    (fun ν hν u₀ hdiv => by
      obtain ⟨T, hT, u, p, hinit, hsol⟩ := hlocal ν hν u₀ hdiv
      exact ⟨T, hT, u, p, hinit, hsol, trivial⟩)
    (datumContinuationIn_true_of hcont) (aprioriIn_of_apriori _ hapriori)

/-! ## The regular class `R` -/

/-- The `Ḣ¹ ∩ Ḣ² ∩ Ḣ³` bound `K` of a single velocity slice. -/
def RegSlice (K : ℝ) (v : VelocityField) : Prop :=
  ∀ i j l : Fin 3,
    MeasureTheory.Integrable (fun x : Space => ‖fderiv ℝ v x (basisVector i)‖ ^ 2) ∧
    (∫ x : Space, ‖fderiv ℝ v x (basisVector i)‖ ^ 2) ≤ K ∧
    MeasureTheory.Integrable (fun x : Space =>
      ‖fderiv ℝ (fun y => fderiv ℝ v y (basisVector i)) x (basisVector j)‖ ^ 2) ∧
    (∫ x : Space, ‖fderiv ℝ (fun y => fderiv ℝ v y (basisVector i)) x (basisVector j)‖ ^ 2)
      ≤ K ∧
    MeasureTheory.Integrable (fun x : Space =>
      ‖fderiv ℝ (fun z => fderiv ℝ (fun y => fderiv ℝ v y (basisVector i)) z
        (basisVector j)) x (basisVector l)‖ ^ 2) ∧
    (∫ x : Space, ‖fderiv ℝ (fun z => fderiv ℝ (fun y => fderiv ℝ v y (basisVector i)) z
        (basisVector j)) x (basisVector l)‖ ^ 2) ≤ K

/-- The `∇p ∈ H¹` bound `K` of a single pressure slice (first and second
derivatives). -/
def PresSlice (K : ℝ) (q : PressureField) : Prop :=
  ∀ i j : Fin 3,
    MeasureTheory.Integrable (fun x : Space => ‖fderiv ℝ q x (basisVector i)‖ ^ 2) ∧
    (∫ x : Space, ‖fderiv ℝ q x (basisVector i)‖ ^ 2) ≤ K ∧
    MeasureTheory.Integrable (fun x : Space =>
      ‖fderiv ℝ (fun y => fderiv ℝ q y (basisVector i)) x (basisVector j)‖ ^ 2) ∧
    (∫ x : Space, ‖fderiv ℝ (fun y => fderiv ℝ q y (basisVector i)) x (basisVector j)‖ ^ 2)
      ≤ K

/-- The `∂ₜu ∈ L²` bound `K` at time `t`. -/
def TimeSlice (K : ℝ) (u : VelocityEvolution) (t : ℝ) : Prop :=
  MeasureTheory.Integrable (fun x : Space => ‖timeDerivative u t x‖ ^ 2) ∧
    (∫ x : Space, ‖timeDerivative u t x‖ ^ 2) ≤ K

theorem RegSlice.mono {K K' : ℝ} {v : VelocityField} (h : RegSlice K v) (hK : K ≤ K') :
    RegSlice K' v := fun i j l => by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h i j l
  exact ⟨a1, a2.trans hK, a3, a4.trans hK, a5, a6.trans hK⟩

theorem PresSlice.mono {K K' : ℝ} {q : PressureField} (h : PresSlice K q) (hK : K ≤ K') :
    PresSlice K' q := fun i j => by
  obtain ⟨a1, a2, a3, a4⟩ := h i j
  exact ⟨a1, a2.trans hK, a3, a4.trans hK⟩

theorem TimeSlice.mono {K K' : ℝ} {u : VelocityEvolution} {t : ℝ} (h : TimeSlice K u t)
    (hK : K ≤ K') : TimeSlice K' u t := ⟨h.1, h.2.trans hK⟩

/-- **`R`: uniform control on compact sub-horizons.**  For every `T' < T`, a single
bound `K` over `t ∈ [0,T']` on: the `Ḣ¹ ∩ Ḣ² ∩ Ḣ³` norm of the velocity slice
(the log-Sobolev inequality behind the T-uniform continuation estimate needs
`Hˢ`, `s > 5/2`), the `H¹` norm of the pressure gradient, and the `L²` norm of
`∂ₜu` (both needed by the weak–strong energy identity, whose pressure pairing
and time derivative must be integrable).

OBLIGATION (recorded 2026-09-23): the R-restart leaf must RETURN an R-strip, so
the local existence theorem from `H³` data (item 6) must produce the pressure
and `∂ₜu` bounds as well as the velocity bounds; otherwise this strengthening
would make `RegularRestart.DatumHorizonIndependentRestartR` unsatisfiable. -/
def RegularOnCompacts : SolutionClassPred := fun T u p =>
  ∀ T' : ℝ, T' < T → ∃ K : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T',
    RegSlice K (u t) ∧ PresSlice K (p t) ∧ TimeSlice K u t

theorem presSlice_normalize {K : ℝ} {p : PressureEvolution} {t : ℝ}
    (h : PresSlice K (p t)) : PresSlice K (normalizePressure p t) := by
  have e : fderiv ℝ (normalizePressure p t) = fderiv ℝ (p t) := by
    funext x
    exact fderiv_sub_const (p t 0)
  intro i j
  simp only [e]
  exact h i j

/-- `R` does not see the pressure gauge. -/
theorem regularOnCompacts_normalize (T : ℝ) (u : VelocityEvolution) (p : PressureEvolution)
    (h : RegularOnCompacts T u p) : RegularOnCompacts T u (normalizePressure p) := by
  intro T' hT'
  obtain ⟨K, hK⟩ := h T' hT'
  exact ⟨K, fun t ht => ⟨(hK t ht).1, presSlice_normalize (hK t ht).2.1, (hK t ht).2.2⟩⟩

/-- **The R-route consumer** (primary): every leaf quantifies over
`SolvesBefore ∧ RegularOnCompacts` only. -/
theorem wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_R
    (N : CriticalQuantity)
    (hlocal : LocalClassicalExistenceIn RegularOnCompacts)
    (hcont : DatumContinuationIn RegularOnCompacts N)
    (hapriori : APrioriIn RegularOnCompacts N) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_in RegularOnCompacts N
    regularOnCompacts_normalize
    hlocal hcont hapriori

/-- The universal a priori leaf implies the R-leaf. -/
theorem aprioriR_of_apriori {N : CriticalQuantity} (h : APrioriCriticalControl N) :
    APrioriIn RegularOnCompacts N :=
  aprioriIn_of_apriori RegularOnCompacts h

end Navier.Analysis.ClassDecomposition

set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassDecomposition.wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_in
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassDecomposition.aprioriIn_of_apriori
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassDecomposition.wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_R
