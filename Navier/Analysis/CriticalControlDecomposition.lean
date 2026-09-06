import Navier.Analysis.GlobalRegularityEndpoint

/-!
# Continuation with a fixed pressure normalization

The theorem below constructs a coherent half-line solution from local
existence, a uniform continuation step, and a uniform bound on a specified
velocity quantity. These are explicit hypotheses, whose proofs must match
the chosen quantity and solution class.

Pressure is normalized by `p(t,x) - p(t,0)`. This preserves smoothness and
the spatial gradient, hence the PDE, and fixes the time-dependent additive
gauge at every restart. The local solution is normalized before the first
step, and normalization is carried through every later stage.

The old unrestricted same-gauge continuation assertion is retained only as
`RejectedSameGaugeContinuationFromCriticalControl`, the exact target
refuted in `PressureGaugeObstruction.lean`. Zero velocity with pressure
`(1-t)⁻¹` shows why exact pressure agreement cannot be requested without
first fixing its gauge.

The construction carries finite energy and the datum-level energy inequality
through every stage, so the glued solution satisfies the full energy clauses.
No proof of the three analytic hypotheses is asserted here.
-/

set_option autoImplicit false

open scoped ContDiff ENNReal NNReal

namespace Navier.Analysis.CriticalControlDecomposition

open Navier Navier.Breakdown Navier.Analysis.GlobalRegularityEndpoint

/-! ## Local vocabulary -/

/-- The four PDE clauses of a classical solution on the half-open horizon
`[0,T)`, with the initial condition deliberately left out so that the
continuation leaf need not restate it. -/
def OriginalSolvesBefore (ν T : ℝ) (u : VelocityEvolution) (p : PressureEvolution) :
    Prop :=
  SmoothVelocityBefore T u ∧ SmoothPressureBefore T p ∧
    IncompressibleBefore T u ∧ SatisfiesNavierStokesBefore ν zeroForce T u p

/-- Agreement of pressure time-slices before a horizon, the pressure twin of
`Navier.Breakdown.VelocityAgreesBefore`. -/
def PressureAgreesBefore (T : ℝ) (p q : PressureEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < T → p t = q t

/-- Fix the time-dependent pressure gauge by requiring the pressure to vanish
at the spatial origin. -/
def PressureNormalizedBefore (T : ℝ) (p : PressureEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < T → p t 0 = 0

/-- Canonical representative of a pressure modulo spatially constant,
time-dependent gauge. -/
def normalizePressure (p : PressureEvolution) : PressureEvolution :=
  fun t x => p t x - p t 0

theorem normalizePressure_normalizedBefore (T : ℝ) (p : PressureEvolution) :
    PressureNormalizedBefore T (normalizePressure p) := by
  intro t _ _
  simp [normalizePressure]

theorem smoothPressureBefore_normalize {T : ℝ} {p : PressureEvolution}
    (hp : SmoothPressureBefore T p) : SmoothPressureBefore T (normalizePressure p) := by
  have hbase : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 0) (spacetimeBefore T) := by
    exact hp.comp
      (contDiff_fst.prodMk contDiff_const).contDiffOn
      (by
        rintro z ⟨ht, -⟩
        exact ⟨ht, Set.mem_univ _⟩)
  exact hp.sub hbase

theorem pressureGradient_normalize_eq {T t : ℝ} {p : PressureEvolution}
    (hp : SmoothPressureBefore T p) (ht : 0 ≤ t) (htT : t < T) (x : Space) :
    pressureGradient (normalizePressure p) t x = pressureGradient p t x := by
  have hslice : ContDiff ℝ ∞ (p t) := by
    rw [← contDiffOn_univ]
    exact hp.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (by
        intro y _
        exact ⟨⟨ht, htT⟩, Set.mem_univ _⟩)
  unfold pressureGradient normalizePressure
  funext i
  have hc : DifferentiableAt ℝ (fun _ : Space => p t 0) x := differentiableAt_const _
  change (fderiv ℝ (p t - fun _ : Space => p t 0) x) (basisVector i) =
    (fderiv ℝ (p t) x) (basisVector i)
  rw [fderiv_sub (hslice.differentiable (by simp) x) hc]
  simp

theorem OriginalSolvesBefore.normalizePressure {ν T : ℝ} {u : VelocityEvolution}
    {p : PressureEvolution} (h : OriginalSolvesBefore ν T u p) :
    OriginalSolvesBefore ν T u (normalizePressure p) := by
  obtain ⟨hu, hp, hinc, heq⟩ := h
  refine ⟨hu, smoothPressureBefore_normalize hp, hinc, ?_⟩
  intro t ht htT x
  rw [pressureGradient_normalize_eq hp ht htT x]
  exact heq t ht htT x

/-- The admissible local solution class used by continuation.  Besides the
four classical PDE clauses it requires each preterminal velocity slice to have
finite energy and to obey the datum-level energy inequality. -/
structure SolvesBefore (ν T : ℝ) (u : VelocityEvolution)
    (p : PressureEvolution) : Prop where
  classical : OriginalSolvesBefore ν T u p
  finite_energy :
    ∀ t : ℝ, 0 ≤ t → t < T → MeasureTheory.Integrable (fun x : Space => ‖u t x‖ ^ 2)
  energy_le_initial :
    ∀ t : ℝ, 0 ≤ t → t < T → kineticEnergy u t ≤ kineticEnergy u 0

theorem SolvesBefore.normalizePressure {ν T : ℝ} {u : VelocityEvolution}
    {p : PressureEvolution} (h : SolvesBefore ν T u p) :
    SolvesBefore ν T u (normalizePressure p) where
  classical := h.classical.normalizePressure
  finite_energy := h.finite_energy
  energy_le_initial := h.energy_le_initial

/-- The real-valued quantity used by the rejected original interface,
retained to state its exact counterexample. -/
abbrev OriginalCriticalQuantity := ℝ → VelocityEvolution → ℝ

/-- A critical quantity may diverge at a finite terminal time.  The extended
codomain prevents the continuation premise from treating every locally smooth
trajectory as automatically bounded. -/
abbrev CriticalQuantity := ℝ → VelocityEvolution → ℝ≥0∞

/-! ## The three leaves -/

/-- Every positive viscosity and divergence-free Schwartz datum admits a
classical solution with finite-energy slices and the initial-energy inequality
on some positive horizon. It requires no continuation to every horizon. -/
def LocalClassicalExistence : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ T : ℝ, 0 < T ∧ ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧ SolvesBefore ν T u p

/-- Rejected universal continuation claim. It asks for exact pressure
agreement even for an arbitrary time-dependent input gauge.
`PressureGaugeObstruction.not_rejectedSameGaugeContinuation` refutes this
statement for every `N`. It is not a hypothesis of the composition below. -/
def RejectedSameGaugeContinuationFromCriticalControl (N : OriginalCriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → OriginalSolvesBefore ν T u p → N T u ≤ M →
        ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
          OriginalSolvesBefore ν (T + δ) u' p' ∧
            VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p'

/-- Corrected continuation interface.  Exact pressure agreement is requested
only after both the input and output have been put in the canonical gauge
`p(t,0)=0`. -/
def NormalizedContinuationFromCriticalControl (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ M : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
          SolvesBefore ν (T + δ) u' p' ∧
            PressureNormalizedBefore (T + δ) p' ∧
            VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p'

/-- A uniform bound on the selected velocity quantity, uniform in the
horizon and in the chosen solution for each viscosity and datum.
This proposition does not assert that `N` controls a physical critical norm;
the continuation hypothesis must be established for the same `N`. -/
def APrioriCriticalControl (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ M : ℝ≥0, ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → N T u ≤ (M : ℝ≥0∞)

/-! ## The chain carrier -/

/-- One rung of the restart ladder: a classical solution from `u₀` on a
positive horizon. -/
structure Stage (ν : ℝ) (u₀ : SchwartzVelocity) where
  horizon : ℝ
  vel : VelocityEvolution
  pres : PressureEvolution
  horizon_pos : 0 < horizon
  init : ∀ x : Space, vel 0 x = u₀ x
  solves : SolvesBefore ν horizon vel pres
  pressure_normalized : PressureNormalizedBefore horizon pres

/-! ## Elementary transfer lemmas -/

/-- Truncating a horizon preserves the PDE clauses. -/
theorem SolvesBefore.mono {ν T T' : ℝ} {u : VelocityEvolution}
    {p : PressureEvolution} (h : SolvesBefore ν T u p) (hle : T' ≤ T) :
    SolvesBefore ν T' u p := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hu, hp, hinc, heq⟩ := h.classical
    refine ⟨hu.mono ?_, hp.mono ?_, ?_, ?_⟩
    · exact Set.prod_mono (Set.Ico_subset_Ico_right hle) (subset_refl _)
    · exact Set.prod_mono (Set.Ico_subset_Ico_right hle) (subset_refl _)
    · exact fun t ht htT => hinc t ht (lt_of_lt_of_le htT hle)
    · exact fun t ht htT => heq t ht (lt_of_lt_of_le htT hle)
  · exact fun t ht htT => h.finite_energy t ht (lt_of_lt_of_le htT hle)
  · exact fun t ht htT => h.energy_le_initial t ht (lt_of_lt_of_le htT hle)

/-- The half-open horizon region is a neighbourhood, within the closed
nonnegative half-line, of each of its own times.  This is what lets a
`fderivWithin ℝ · (Set.Ici 0)` be computed from data on `[0,T)` alone; the time
derivative in `Navier.timeDerivative` is taken within `Set.Ici 0`, not within
the horizon, so pointwise agreement on `[0,T)` is not by itself enough. -/
theorem Ico_mem_nhdsWithin_Ici {T t : ℝ} (htT : t < T) :
    Set.Ico (0 : ℝ) T ∈ nhdsWithin t (Set.Ici (0 : ℝ)) := by
  refine mem_nhdsWithin.mpr ⟨Set.Iio T, isOpen_Iio, Set.mem_Iio.mpr htT, ?_⟩
  rintro s ⟨hs1, hs2⟩
  exact ⟨hs2, hs1⟩

/-- If two velocity evolutions agree on `[0,T)` then their `Set.Ici 0` time
derivatives agree at every time of `[0,T)`. -/
theorem timeDerivative_congr_before {T : ℝ} {u v : VelocityEvolution}
    (h : ∀ s : ℝ, 0 ≤ s → s < T → u s = v s) {t : ℝ} (ht : 0 ≤ t)
    (htT : t < T) (x : Space) :
    timeDerivative u t x = timeDerivative v t x := by
  have hev : (fun s : ℝ => u s x) =ᶠ[nhdsWithin t (Set.Ici (0 : ℝ))]
      fun s : ℝ => v s x := by
    filter_upwards [Ico_mem_nhdsWithin_Ici htT] with s hs
    exact congrFun (h s hs.1 hs.2) x
  simpa [timeDerivative] using
    congrArg (fun L : ℝ →L[ℝ] Space => L 1)
      (hev.fderivWithin_eq (congrFun (h t ht htT) x))

/-! ## The composition -/

/-- Local existence, continuation in the normalized pressure gauge, and a
uniform bound on the chosen quantity give a coherent global solution. The
finite-energy and dissipative-energy fields are carried by every rung; after
gluing they supply the two energy clauses of `WholeSpaceGlobalRegularity` for
the constructed velocity itself. All three analytic inputs remain explicit
hypotheses of this theorem. -/
theorem wholeSpaceGlobalRegularity_of_local_continuation_apriori
    (N : CriticalQuantity)
    (hlocal : LocalClassicalExistence)
    (hcont : NormalizedContinuationFromCriticalControl N)
    (hapriori : APrioriCriticalControl N) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  intro ν hν u₀ hdiv
  obtain ⟨M, hM⟩ := hapriori ν hν u₀ hdiv
  obtain ⟨δ, hδ, hstep⟩ := hcont ν hν M
  obtain ⟨T₀, hT₀, v₀, q₀, hinit₀, hsolves₀⟩ := hlocal ν hν u₀ hdiv
  let base : Stage ν u₀ :=
    { horizon := T₀, vel := v₀, pres := normalizePressure q₀, horizon_pos := hT₀,
      init := hinit₀, solves := hsolves₀.normalizePressure,
      pressure_normalized := normalizePressure_normalizedBefore T₀ q₀ }
  have advance : ∀ s : Stage ν u₀, ∃ s' : Stage ν u₀,
      s'.horizon = s.horizon + δ ∧
        VelocityAgreesBefore s.horizon s.vel s'.vel ∧
        PressureAgreesBefore s.horizon s.pres s'.pres := by
    intro s
    obtain ⟨u', p', hsolve', hpnormalized', hvagree, hpagree⟩ :=
      hstep u₀ hdiv s.horizon s.horizon_pos s.vel s.pres s.init s.solves
        s.pressure_normalized
        (hM s.horizon s.horizon_pos s.vel s.pres s.init s.solves)
    refine ⟨{ horizon := s.horizon + δ, vel := u', pres := p',
              horizon_pos := by linarith [s.horizon_pos],
              init := ?_, solves := hsolve', pressure_normalized := hpnormalized' },
      rfl, hvagree, hpagree⟩
    intro x
    have h0 := hvagree 0 le_rfl s.horizon_pos
    rw [← congrFun h0 x]
    exact s.init x
  choose next hnext_h hnext_v hnext_p using advance
  set stage : ℕ → Stage ν u₀ := fun n => Nat.rec base (fun _ s => next s) n
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

/-! ## Regression witnesses for the repaired interface -/

/-- An infinite critical value cannot pass a finite continuation threshold. -/
theorem top_not_le_finiteCriticalBound (M : ℝ≥0) :
    ¬ (⊤ : ℝ≥0∞) ≤ (M : ℝ≥0∞) := by
  simp

/-- The known spatially uniform accelerating solution is excluded from the
admissible class by its nonintegrable slice at time one. -/
theorem acceleratingVelocity_not_admissible (ν : ℝ) :
    ¬ SolvesBefore ν 2 acceleratingVelocity acceleratingPressure := by
  intro h
  exact acceleratingVelocity_not_integrable
    (h.finite_energy 1 zero_le_one (by norm_num))

/-! ## Satisfiability smoke tests

These checks establish the zero-datum instances only. They do not prove the
universally quantified local-existence, continuation, or a priori premises. -/

/-- The `SolvesBefore` clause bundle is inhabited by the zero pair at every
viscosity and horizon, so it is not unsatisfiable. -/
theorem solvesBefore_zero (ν T : ℝ) :
    SolvesBefore ν T (fun _ _ => 0) (fun _ _ => 0) where
  classical := zero_is_solution_before ν T
  finite_energy := by intro t _ _; simp
  energy_le_initial := by intro t _ _; simp [kineticEnergy]

/-- The normalized conclusion shape is inhabited: the zero solution extends
itself to any later horizon in the canonical gauge. -/
theorem continuation_conclusion_inhabited (ν T δ : ℝ) :
    ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
      SolvesBefore ν (T + δ) u' p' ∧
        PressureNormalizedBefore (T + δ) p' ∧
        VelocityAgreesBefore T (fun _ _ => 0) u' ∧
        PressureAgreesBefore T (fun _ _ => 0) p' :=
  ⟨fun _ _ => 0, fun _ _ => 0, solvesBefore_zero ν (T + δ),
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Both leaf-1 and leaf-3 shapes are non-vacuous in the strong sense that
their bodies quantify over the actual Schwartz data: the divergence-free datum
class is inhabited. -/
theorem divergenceFreeInitial_inhabited :
    ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ :=
  ⟨0, ProblemStatements.divergenceFreeInitial_zero⟩

end Navier.Analysis.CriticalControlDecomposition

#print axioms Navier.Analysis.CriticalControlDecomposition.smoothPressureBefore_normalize
#print axioms Navier.Analysis.CriticalControlDecomposition.pressureGradient_normalize_eq
#print axioms Navier.Analysis.CriticalControlDecomposition.SolvesBefore.normalizePressure
#print axioms Navier.Analysis.CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_continuation_apriori
#print axioms Navier.Analysis.CriticalControlDecomposition.top_not_le_finiteCriticalBound
#print axioms Navier.Analysis.CriticalControlDecomposition.acceleratingVelocity_not_admissible
