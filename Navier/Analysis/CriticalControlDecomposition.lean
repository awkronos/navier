import Navier.Analysis.GlobalRegularityEndpoint

/-!
# Decomposing the half-line existence residual along the critical-control edge

`Frontier.dependencies .globalContinuation =
  { .localClassicalExistence, .continuationCriterion, .aPrioriCriticalControl }`
was, before this module, **planning data only**: a `Finset` of enum
constructors with no Lean proposition behind any of the three nodes and no
theorem asserting that the three compose.  `Frontier.lean` says so itself
("The map is planning data: it does not assert that arbitrary proofs of the
listed nodes compose").

This module supplies the missing content.  It states the three nodes as honest
Lean propositions and proves that they compose to
`GlobalRegularityEndpoint.HalfLineClassicalExistence`, which is the hard
hypothesis of the single proved edge into
`ProblemStatements.WholeSpaceGlobalRegularity`.

## The decomposition

Everything is parametrised by a **critical quantity**
`N : ℝ → VelocityEvolution → ℝ`, read as "the critical norm of `u` accumulated
over `[0,T)`".  Quantifying over every `N` is deliberate: the theorem is not
tuned to one functional, and no instantiation is privileged.  The three leaves
are

* `LocalClassicalExistence` — from every divergence-free Schwartz datum there
  is *some* positive horizon carrying a classical solution.
  Reference: Fujita–Kato, *Arch. Rational Mech. Anal.* 16 (1964), 269–315;
  Kato, *Math. Z.* 187 (1984), 471–480.  Estimated 1500–3000 LOC over Mathlib
  as it stands (needs the Leray projector as a bounded operator and a mild
  formulation, both listed as absent).
* `ContinuationFromCriticalControl N` — a solution on `[0,T)` whose critical
  quantity is bounded by `M` extends, in the same gauge, to `[0,T+δ)` with
  `δ = δ(ν,M) > 0` **independent of `T` and of the datum**.
  Reference: Beale–Kato–Majda, *Comm. Math. Phys.* 94 (1984), 61–66 (with
  `N T u = ∫₀ᵀ ‖curl u(t)‖_∞ dt`); Escauriaza–Seregin–Šverák, *Russ. Math.
  Surveys* 58 (2003), 211–250 (with `N T u = sup_{t<T} ‖u(t)‖_{L³}`);
  Prodi–Serrin for the `L^q_t L^r_x` scale.  Estimated 2000+ LOC; the uniform
  lower bound on the restart lifespan is the part that carries `δ`'s
  independence of `T`.
* `APrioriCriticalControl N` — the critical quantity of *every* classical
  solution issuing from a fixed datum is bounded by a single `M = M(ν,u₀)`.

**`APrioriCriticalControl` is the Millennium content.**  Nothing here reduces
it, and this module claims no reduction of it.  What the module does is make
the other two leaves separately attackable and remove them from the monolithic
`HalfLineClassicalExistence`.

## Quantifier order (checked, not incidental)

`APrioriCriticalControl` puts `∃ M` **above** `∀ T`.  The inner-`∃` form
`∀ T, ∃ M, N T u ≤ M` is dischargeable per horizon for any locally bounded
functional and extracts none of the intended content; it would make the leaf
true and useless.  Likewise `ContinuationFromCriticalControl` puts `∃ δ` above
`∀ T` and above `∀ u₀`: a `δ` allowed to shrink with `T` gives horizons with a
finite supremum and the composition below would be false.  Both hoists are
load-bearing in the proof: `δ` is fixed once and the horizons advance by a
constant step.

## The Tao barrier

Tao, *J. Amer. Math. Soc.* 29 (2016), 601–674, exhibits an averaged
Navier–Stokes equation obeying the same energy identity and the same scaling
which blows up in finite time.  Consequence: no argument using only the energy
inequality and the local theory can settle the problem.

This decomposition survives that barrier, in the precise sense that it does not
attempt to evade it.  The barrier applies to `APrioriCriticalControl`, which is
exactly where supercriticality is quarantined here: the energy identity is a
statement about `‖u(t)‖_{L²}`, a subcritical quantity, and it bounds no critical
`N`.  The two leaves this module makes separately attackable
(`LocalClassicalExistence`, `ContinuationFromCriticalControl`) are both known
theorems in the literature and are *not* obstructed by Tao's construction —
they hold for his averaged equation too.  So the reduction moves no difficulty
across the barrier and does not trivialise anything; it isolates the
supercritical step in one named leaf.  A reader looking for the place where a
proof must do something Tao's example cannot do should look at
`APrioriCriticalControl` and nowhere else in this file.

## Gauge conjunct

`ContinuationFromCriticalControl` asks the extension to agree with the given
solution in **both** velocity and pressure before `T`.  The pressure conjunct is
a gauge normalisation, not a second estimate: two classical solutions sharing a
velocity on `[0,T)` have pressures whose gradients agree there, so they differ
by a function of time alone.  It is recorded here as part of the leaf's
statement rather than claimed to be free, because producing the extension
already normalised is an obligation on the producer.  It is needed: the glued
pressure below must be a single function, and `pressureGradient` is evaluated
pointwise in time.

Scope: this is a CONDITIONAL decomposition.  It closes no leaf, discharges no
hypothesis of the endpoint, and makes no global-regularity claim.  What is
kernel-clean here is the composition itself.
-/

set_option autoImplicit false

open scoped ContDiff

namespace Navier.Analysis.CriticalControlDecomposition

open Navier Navier.Breakdown Navier.Analysis.GlobalRegularityEndpoint

/-! ## Local vocabulary -/

/-- The four PDE clauses of a classical solution on the half-open horizon
`[0,T)`, with the initial condition deliberately left out so that the
continuation leaf need not restate it. -/
def SolvesBefore (ν T : ℝ) (u : VelocityEvolution) (p : PressureEvolution) :
    Prop :=
  SmoothVelocityBefore T u ∧ SmoothPressureBefore T p ∧
    IncompressibleBefore T u ∧ SatisfiesNavierStokesBefore ν zeroForce T u p

/-- Agreement of pressure time-slices before a horizon, the pressure twin of
`Navier.Breakdown.VelocityAgreesBefore`. -/
def PressureAgreesBefore (T : ℝ) (p q : PressureEvolution) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < T → p t = q t

/-- A critical quantity: `N T u` is the critical norm of `u` accumulated over
`[0,T)`.  Left abstract so that the decomposition is not tuned to one
functional. -/
abbrev CriticalQuantity := ℝ → VelocityEvolution → ℝ

/-! ## The three leaves -/

/-- **Leaf 1 (`Frontier.localClassicalExistence`).**  Every viscosity and every
divergence-free Schwartz datum admits a classical solution on *some* positive
horizon.

Reference: Fujita–Kato 1964, Kato 1984.  Strictly weaker than
`HalfLineClassicalExistence`, which demands every horizon. -/
def LocalClassicalExistence : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ T : ℝ, 0 < T ∧ ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧ SolvesBefore ν T u p

/-- **Leaf 2 (`Frontier.continuationCriterion`).**  Given a bound `M` on the
critical quantity there is a restart step `δ = δ(ν,M) > 0`, *uniform in the
horizon and in the datum*, by which every controlled classical solution extends
in the same gauge.

Reference: Beale–Kato–Majda 1984, Escauriaza–Seregin–Šverák 2003,
Prodi–Serrin.  Strictly weaker than `HalfLineClassicalExistence`: it constructs
nothing from nothing, its hypothesis is a solution it does not produce, and its
conclusion advances one step rather than reaching every horizon. -/
def ContinuationFromCriticalControl (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → N T u ≤ M →
        ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
          SolvesBefore ν (T + δ) u' p' ∧
            VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p'

/-- **Leaf 3 (`Frontier.aPrioriCriticalControl`) — the Millennium content.**
For each viscosity and datum a *single* bound `M` controls the critical
quantity of every classical solution issuing from that datum, on every
horizon.

No reference discharges this for any critical `N` in three dimensions; its
absence is the problem.  The `∃ M` is hoisted above `∀ T` on purpose (see the
module docstring). -/
def APrioriCriticalControl (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ M : ℝ, ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → N T u ≤ M

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

/-! ## Elementary transfer lemmas -/

/-- Truncating a horizon preserves the PDE clauses. -/
theorem SolvesBefore.mono {ν T T' : ℝ} {u : VelocityEvolution}
    {p : PressureEvolution} (h : SolvesBefore ν T u p) (hle : T' ≤ T) :
    SolvesBefore ν T' u p := by
  obtain ⟨hu, hp, hinc, heq⟩ := h
  refine ⟨hu.mono ?_, hp.mono ?_, ?_, ?_⟩
  · exact Set.prod_mono (Set.Ico_subset_Ico_right hle) (subset_refl _)
  · exact Set.prod_mono (Set.Ico_subset_Ico_right hle) (subset_refl _)
  · exact fun t ht htT => hinc t ht (lt_of_lt_of_le htT hle)
  · exact fun t ht htT => heq t ht (lt_of_lt_of_le htT hle)

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

/-- **DECOMPOSITION (kernel-clean).**  The three frontier leaves compose to the
half-line existence residual:

`LocalClassicalExistence → ContinuationFromCriticalControl N →
APrioriCriticalControl N → HalfLineClassicalExistence`

for **every** critical quantity `N`.

This is the Lean content of the planning edge
`dependencies .globalContinuation = {localClassicalExistence,
continuationCriterion, aPrioriCriticalControl}`, which until now asserted
nothing.

The mathematics proved here is the restart ladder and its gluing: the a priori
bound is extracted first, so the continuation step size `δ` is fixed once and
for all; the horizons then advance by the constant `δ` and are cofinal in
`[0,∞)`; the rungs agree with each other before every earlier horizon, so the
diagonal `fun t => (stage ⌈t/δ⌉₊)` is a single well-defined pair reproducing
each rung on that rung's own horizon.

Scope: CONDITIONAL.  All three hypotheses are open; none is discharged here,
and `APrioriCriticalControl` is the Millennium content. -/
theorem halfLineClassicalExistence_of_local_continuation_apriori
    (N : CriticalQuantity)
    (hlocal : LocalClassicalExistence)
    (hcont : ContinuationFromCriticalControl N)
    (hapriori : APrioriCriticalControl N) :
    HalfLineClassicalExistence := by
  intro ν hν u₀ hdiv
  obtain ⟨M, hM⟩ := hapriori ν hν u₀ hdiv
  obtain ⟨δ, hδ, hstep⟩ := hcont ν hν M
  obtain ⟨T₀, hT₀, v₀, q₀, hinit₀, hsolves₀⟩ := hlocal ν hν u₀ hdiv
  -- the base rung
  let base : Stage ν u₀ :=
    { horizon := T₀, vel := v₀, pres := q₀, horizon_pos := hT₀,
      init := hinit₀, solves := hsolves₀ }
  -- one restart, packaged as a total function on rungs
  have advance : ∀ s : Stage ν u₀, ∃ s' : Stage ν u₀,
      s'.horizon = s.horizon + δ ∧
        VelocityAgreesBefore s.horizon s.vel s'.vel ∧
        PressureAgreesBefore s.horizon s.pres s'.pres := by
    intro s
    obtain ⟨u', p', hsolve', hvagree, hpagree⟩ :=
      hstep u₀ hdiv s.horizon s.horizon_pos s.vel s.pres s.init s.solves
        (hM s.horizon s.horizon_pos s.vel s.pres s.init s.solves)
    refine ⟨{ horizon := s.horizon + δ, vel := u', pres := p',
              horizon_pos := by linarith [s.horizon_pos],
              init := ?_, solves := hsolve' }, rfl, hvagree, hpagree⟩
    intro x
    have h0 := hvagree 0 le_rfl s.horizon_pos
    rw [← congrFun h0 x]
    exact s.init x
  choose next hnext_h hnext_v hnext_p using advance
  -- the ladder
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
  -- rungs agree with all later rungs before their own horizon
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
  -- the index whose horizon already passed `t`
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
  -- the glued pair
  refine ⟨fun t => (stage (idx t)).vel t, fun t => (stage (idx t)).pres t,
    fun x => (stage (idx 0)).init x, ?_⟩
  -- the diagonal reproduces every rung on that rung's own horizon
  have hkey_v : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, t < (stage n).horizon →
      (stage (idx t)).vel t = (stage n).vel t := by
    intro t ht n hn
    have h1 := hagree_v (idx t) (max (idx t) n) (le_max_left _ _) t ht
      (hidx_lt t ht)
    have h2 := hagree_v n (max (idx t) n) (le_max_right _ _) t ht hn
    rw [h1, h2]
  have hkey_p : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, t < (stage n).horizon →
      (stage (idx t)).pres t = (stage n).pres t := by
    intro t ht n hn
    have h1 := hagree_p (idx t) (max (idx t) n) (le_max_left _ _) t ht
      (hidx_lt t ht)
    have h2 := hagree_p n (max (idx t) n) (le_max_right _ _) t ht hn
    rw [h1, h2]
  intro T hT
  -- one rung already covers the horizon `T`
  obtain ⟨n, hTn⟩ : ∃ n : ℕ, T < (stage n).horizon := ⟨idx T, hidx_lt T hT.le⟩
  obtain ⟨hvsm, hpsm, hinc, heq⟩ := (stage n).solves
  have hveq : ∀ t : ℝ, 0 ≤ t → t < T → (stage (idx t)).vel t = (stage n).vel t :=
    fun t ht htT => hkey_v t ht n (lt_trans htT hTn)
  have hpeq : ∀ t : ℝ, 0 ≤ t → t < T →
      (stage (idx t)).pres t = (stage n).pres t :=
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
    have : divergence (fun s => (stage (idx s)).vel s) t x
        = divergence (stage n).vel t x := by
      simp only [divergence, spatialDerivative, hveq t ht htT]
    rw [this]
    exact hinc t ht (lt_trans htT hTn) x
  · intro t ht htT x
    have htn : t < (stage n).horizon := lt_trans htT hTn
    have htime : timeDerivative (fun s => (stage (idx s)).vel s) t x
        = timeDerivative (stage n).vel t x :=
      timeDerivative_congr_before (T := T) hveq ht htT x
    have hslice : (stage (idx t)).vel t = (stage n).vel t := hveq t ht htT
    have hpslice : (stage (idx t)).pres t = (stage n).pres t := hpeq t ht htT
    have hconv : convection (fun s => (stage (idx s)).vel s) t x
        = convection (stage n).vel t x := by
      simp only [convection, spatialDerivative, hslice]
    have hlap : laplacian (fun s => (stage (idx s)).vel s) t x
        = laplacian (stage n).vel t x := by
      simp only [laplacian, hslice]
    have hgrad : pressureGradient (fun s => (stage (idx s)).pres s) t x
        = pressureGradient (stage n).pres t x := by
      have hp' : (fun s => (stage (idx s)).pres s) t = (stage n).pres t :=
        hpslice
      unfold pressureGradient
      rw [hp']
    rw [htime, hconv, hlap, hgrad]
    exact heq t ht htn x

/-! ## Satisfiability smoke tests

Guards against the two vacuity poles for the shapes introduced above.  They are
evidence that the propositions are inhabitable, never evidence for the leaves
themselves. -/

/-- The `SolvesBefore` clause bundle is inhabited by the zero pair at every
viscosity and horizon, so it is not unsatisfiable. -/
theorem solvesBefore_zero (ν T : ℝ) :
    SolvesBefore ν T (fun _ _ => 0) (fun _ _ => 0) :=
  zero_is_solution_before ν T

/-- The conclusion shape of `ContinuationFromCriticalControl` is inhabited: the
zero solution extends itself to any later horizon in its own gauge.  In
particular the gauge conjunct `PressureAgreesBefore` is not unsatisfiable. -/
theorem continuation_conclusion_inhabited (ν T δ : ℝ) :
    ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
      SolvesBefore ν (T + δ) u' p' ∧
        VelocityAgreesBefore T (fun _ _ => 0) u' ∧
        PressureAgreesBefore T (fun _ _ => 0) p' :=
  ⟨fun _ _ => 0, fun _ _ => 0, solvesBefore_zero ν (T + δ),
    fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Both leaf-1 and leaf-3 shapes are non-vacuous in the strong sense that
their bodies quantify over the actual Schwartz data: the divergence-free datum
class is inhabited. -/
theorem divergenceFreeInitial_inhabited :
    ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ :=
  ⟨0, ProblemStatements.divergenceFreeInitial_zero⟩

/-! ## Tie to the frontier enum -/

/-- The planning edge this module supplies content for.  The correspondence
between the three enum constructors and the three propositions above is by
name and by docstring, not by a certified translation: `FrontierNode` carries
no semantics.  What the theorem below records is that the edge whose Lean
content is `halfLineClassicalExistence_of_local_continuation_apriori` is
exactly the edge the frontier map declares. -/
theorem globalContinuation_dependencies :
    Frontier.dependencies .globalContinuation =
      { Frontier.FrontierNode.localClassicalExistence,
        Frontier.FrontierNode.continuationCriterion,
        Frontier.FrontierNode.aPrioriCriticalControl } := rfl

/-! ## The endpoint restated over the three leaves -/

/-- **CONDITIONAL: Fefferman statement A from four named residuals.**

The composite of the decomposition above with the repository's single proved
edge into the endpoint.  Its hypothesis list is the current frontier of the
whole-space problem in this repository, with the monolithic
`HalfLineClassicalExistence` replaced by three separately attackable leaves:

* `LocalClassicalExistence` — known (Fujita–Kato), unformalised;
* `ContinuationFromCriticalControl N` — known (Beale–Kato–Majda /
  Escauriaza–Seregin–Šverák), unformalised;
* `APrioriCriticalControl N` — **open; the Millennium content**;
* `WholeSpaceEnergyClause` — the `Frontier.wholeSpaceEnergyBridge` residual.

Scope: CONDITIONAL.  This is a reduction, not a solution.  No hypothesis is
discharged here and no global-regularity claim is made.  Nothing in this
repository proves any of the four. -/
theorem wholeSpaceGlobalRegularity_of_criticalControlDecomposition
    (N : CriticalQuantity)
    (hlocal : LocalClassicalExistence)
    (hcont : ContinuationFromCriticalControl N)
    (hapriori : APrioriCriticalControl N)
    (henergy : WholeSpaceEnergyClause) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_halfLineExistence_and_energyClause
    (halfLineClassicalExistence_of_local_continuation_apriori N hlocal hcont
      hapriori)
    henergy

end Navier.Analysis.CriticalControlDecomposition
