import Navier.Analysis.ContinuationScaleSelfImprovement

/-!
# The restart input of the BKM endpoint, at the repository's layer

`ContinuationScaleSelfImprovement.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_datumRestart`
consumes three inputs; its third is
`RestartPaste.DatumHorizonIndependentRestart bkmVorticityControl`, the
Beale–Kato–Majda continuation in datum-dependent order.  Truth-checked at the
repository's abstraction layer, that input is NOT the classical continuation
theorem: it quantifies over the whole `SolvesBefore` class (joint smoothness,
finite-energy slices, the datum-level energy inequality), while the classical
theorem [BKM1984] is stated for a solution class carrying a Sobolev budget and
time continuity in it, and its restart's agreement clause is Kato uniqueness in
that class.  Two facts separate the two:

* `SolvesBefore` carries no Sobolev budget: a smooth velocity with finite-energy
  slices need not have square-integrable derivatives, so the BKM Grönwall
  argument (whose input is `‖u(t)‖_{H^s}`) has no state variable to propagate;
* `SolvesBefore` carries no time continuity: a jointly smooth evolution with
  finite-energy slices can fail to be continuous into `L²` (a bump translated to
  infinity as `t ↓ 0`, extended by zero), so the Serrin/Kato energy argument for
  uniqueness has nothing to differentiate.

Consequently the restart on the full class silently contains a weak–strong
uniqueness statement (`RestartUniquenessIn trivialClass` below) that no
classical theorem supplies.  Ledger entry `F-023` records this as a scope gap of
the inference, not as a falsification of the leaf.

## What this file does

The gluing composition never uses the leaf outside the class of solutions it
itself produces.  So the consumer's real requirement is moved into the leaves:
every leaf is threaded by a `SolutionClass` — a membership predicate on
half-open time intervals, closed under right truncation and under the
interior-time paste — and the composition
`wholeSpaceGlobalRegularity_of_localIn_datumContinuationIn_aprioriIn` is proved
for an arbitrary class.  At `trivialClass` the threaded leaves are exactly the
existing ones (`localExistenceIn_trivial_iff`, `aPrioriCriticalControlIn_trivial_iff`,
`datumContinuationIn_trivial_iff`), so the existing endpoint is a corollary
(`wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_viaClass`).
The class-threaded a priori leaf is strictly weaker than the full-class one:
it bounds the BKM integral only on class solutions, which is the form in which
the Millennium content is actually conjectured.

Then the class restart engine `DatumRestartIn C N` is proved from three
classical, strictly weaker leaves in the class
(`datumRestartIn_of_budget_propagation_uniqueness`):

* `BudgetLocalExistenceIn C B` — restart existence with a horizon depending only
  on the viscosity and a budget bound `B (u T₀) ≤ K` (Kato's local theorem);
* `BudgetPropagationIn C B N` — the budget stays below `K(ν, u₀, M)` on every
  class solution with `N T u ≤ M` (the BKM Grönwall estimate);
* `RestartUniquenessIn C` — a class restart from the slice `u T₀` agrees with
  `u` on the overlap (Kato uniqueness in the class).

The restart length is `h/2` where `h = h(ν, K)` is the budget horizon; the
restart time is `T₀ = max 0 (T - h/2)`, so the strip reaches `T + h/2` and the
overlap `[T₀, T)` is inside the restart strip.  Pressure agreement on the open
overlap is DERIVED (`pressure_eq_of_velocity_eq_interior`): equal velocities
give equal pressure gradients through the equation, hence spatially constant
pressure difference, killed by the normalization `p(t,0) = 0`.

Everything here is kernel-checked with strict axioms; nothing here proves any
of the analytic leaves.  `APrioriCriticalControlIn C bkmVorticityControl` is the
Millennium core in class form and is not attacked here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology

namespace Navier.Analysis.ClassRestartDecomposition

open Navier Navier.Breakdown Navier.Analysis.GlobalRegularityEndpoint
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.AprioriCriticalControlQuantifiers
open Navier.Analysis.RestartPaste
open Navier.Analysis.LocalExistenceViscosityReduction
open Navier.Analysis.ContinuationScaleSelfImprovement

/-! ## Solution classes -/

/-- The piecewise function used by the interior-time paste: `f` before `T`,
`g` from `T` on. -/
def glueAt {α : Type*} (T : ℝ) (f g : ℝ → α) : ℝ → α :=
  fun t => if t < T then f t else g t

/-- **A solution class.**  `mem a L u` reads "`u` belongs to the class on the
half-open interval `[a, a + L)`" (start and LENGTH, the `SolvesFrom` convention).
Two closure laws are required: right truncation of the interval, and stability under the interior-time paste of a class piece
on `[0, T)` with a class restart strip on `[T₀, T + h)` agreeing on `[T₀, T)`.
Both hold for the trivial class, for every slice-wise class
(`sliceClass`), and for the classical class `C([a, b); H^s)` (continuity of the
glue at `T` is inherited from the restart piece, which agrees with the first
piece just before `T`). -/
structure SolutionClass where
  mem : ℝ → ℝ → VelocityEvolution → Prop
  mono_right : ∀ {a L L' : ℝ} {u : VelocityEvolution}, mem a L u → L' ≤ L → mem a L' u
  glue : ∀ {T T₀ h : ℝ} {u w : VelocityEvolution}, 0 ≤ T₀ → T₀ < T → 0 < h →
    mem 0 T u → mem T₀ (T - T₀ + h) w → (∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) →
    mem 0 (T + h) (glueAt T u w)

/-- The trivial class: every evolution belongs on every interval.  Its
threaded leaves are the existing full-class leaves. -/
def trivialClass : SolutionClass where
  mem := fun _ _ _ => True
  mono_right := fun _ _ => trivial
  glue := fun _ _ _ _ _ _ => trivial

/-- A slice-wise class: `u` belongs on `[a, a + L)` when every slice `u t`,
`a ≤ t < a + L`, has the property `S`.  This is a nontrivial witness that the
class laws are satisfiable. -/
def sliceClass (S : VelocityField → Prop) : SolutionClass where
  mem := fun a L u => ∀ t : ℝ, a ≤ t → t < a + L → S (u t)
  mono_right := fun h hL t hat htL => h t hat (by linarith)
  glue := by
    intro T T₀ h u w _ hT₀T _ hu hw _ t ht htT
    show S (if t < T then u t else w t)
    by_cases hlt : t < T
    · simp only [hlt, ↓reduceIte]
      exact hu t ht (by linarith)
    · simp only [hlt, ↓reduceIte]
      exact hw t (le_of_lt (lt_of_lt_of_le hT₀T (not_lt.mp hlt))) (by linarith)

/-! ## The class-threaded leaves -/

/-- Local existence inside the class. -/
def LocalExistenceIn (C : SolutionClass) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ T : ℝ, 0 < T ∧ ∃ u : VelocityEvolution, ∃ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) ∧ SolvesBefore ν T u p ∧ C.mem 0 T u

/-- A priori control of `N`, uniform in horizon and solution, required only on
class solutions.  Strictly weaker than `APrioriCriticalControl N`. -/
def APrioriCriticalControlIn (C : SolutionClass) (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∃ M : ℝ≥0, ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
      N T u ≤ (M : ℝ≥0∞)

/-- Datum-dependent continuation inside the class: class solutions under the
budget extend by a datum-dependent step to class solutions. -/
def DatumContinuationIn (C : SolutionClass) (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ M : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ u' : VelocityEvolution, ∃ p' : PressureEvolution,
          SolvesBefore ν (T + δ) u' p' ∧ PressureNormalizedBefore (T + δ) p' ∧
            VelocityAgreesBefore T u u' ∧ PressureAgreesBefore T p p' ∧
            C.mem 0 (T + δ) u'

/-- The class restart engine: same shape as `DatumHorizonIndependentRestart N`,
restricted to class solutions, with the restart strip in the class; pressure
agreement is asked only on the open overlap `(T₀, T)`, which is all the paste
consumes. -/
def DatumRestartIn (C : SolutionClass) (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ M : ℝ≥0, ∃ h : ℝ, 0 < h ∧
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ T₀ : ℝ, 0 ≤ T₀ ∧ T₀ < T ∧ ∃ w : VelocityEvolution, ∃ q : PressureEvolution,
          (∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) ∧
          (∀ t : ℝ, T₀ < t → t < T → p t = q t) ∧
          SolvesFrom ν T₀ (T - T₀ + h) w q ∧
          (∀ t : ℝ, T₀ ≤ t → t < T + h → q t 0 = 0) ∧
          C.mem T₀ (T - T₀ + h) w

/-! ## Trivial class: the threaded leaves are the existing leaves -/

theorem localExistenceIn_trivial_iff :
    LocalExistenceIn trivialClass ↔ LocalClassicalExistence := by
  constructor
  · intro h ν hν u₀ hu₀
    obtain ⟨T, hT, u, p, hinit, hsol, -⟩ := h ν hν u₀ hu₀
    exact ⟨T, hT, u, p, hinit, hsol⟩
  · intro h ν hν u₀ hu₀
    obtain ⟨T, hT, u, p, hinit, hsol⟩ := h ν hν u₀ hu₀
    exact ⟨T, hT, u, p, hinit, hsol, trivial⟩

theorem aPrioriCriticalControlIn_trivial_iff (N : CriticalQuantity) :
    APrioriCriticalControlIn trivialClass N ↔ APrioriCriticalControl N := by
  constructor
  · intro h ν hν u₀ hu₀
    obtain ⟨M, hM⟩ := h ν hν u₀ hu₀
    exact ⟨M, fun T hT u p hinit hsol => hM T hT u p hinit hsol trivial⟩
  · intro h ν hν u₀ hu₀
    obtain ⟨M, hM⟩ := h ν hν u₀ hu₀
    exact ⟨M, fun T hT u p hinit hsol _ => hM T hT u p hinit hsol⟩

theorem datumContinuationIn_trivial_iff (N : CriticalQuantity) :
    DatumContinuationIn trivialClass N ↔ DatumContinuationFromCriticalControl N := by
  constructor
  · intro h ν hν u₀ hu₀ M
    obtain ⟨δ, hδ, hstep⟩ := h ν hν u₀ hu₀ M
    refine ⟨δ, hδ, fun T hT u p hinit hsol hnorm hN => ?_⟩
    obtain ⟨u', p', hsol', hnorm', hv, hp, -⟩ := hstep T hT u p hinit hsol trivial hnorm hN
    exact ⟨u', p', hsol', hnorm', hv, hp⟩
  · intro h ν hν u₀ hu₀ M
    obtain ⟨δ, hδ, hstep⟩ := h ν hν u₀ hu₀ M
    refine ⟨δ, hδ, fun T hT u p hinit hsol _ hnorm hN => ?_⟩
    obtain ⟨u', p', hsol', hnorm', hv, hp⟩ := hstep T hT u p hinit hsol hnorm hN
    exact ⟨u', p', hsol', hnorm', hv, hp, trivial⟩

/-- The full-class restart engine of `RestartPaste` is the trivial-class
instance of the class engine (it asks pressure agreement on the closed
overlap, so only this direction is stated). -/
theorem datumRestartIn_trivial_of_datumRestart {N : CriticalQuantity}
    (h : DatumHorizonIndependentRestart N) : DatumRestartIn trivialClass N := by
  intro ν hν u₀ hu₀ M
  obtain ⟨h₀, hh, heng⟩ := h ν hν u₀ hu₀ M
  refine ⟨h₀, hh, fun T hT u p hinit hsol _ hnorm hN => ?_⟩
  obtain ⟨T₀, hT₀, hT₀T, w, q, hv, hp, hw, hq⟩ := heng T hT u p hinit hsol hnorm hN
  exact ⟨T₀, hT₀, hT₀T, w, q, hv, fun t ht htT => hp t ht.le htT, hw, hq, trivial⟩

/-! ## Slice-congruence leaves (generalized `u t = v s` form) -/

private theorem divergence_congr {u v : VelocityEvolution} {t s : ℝ} (x : Space)
    (h : u t = v s) : divergence u t x = divergence v s x := by
  show ∑ i : Fin 3, fderiv ℝ (u t) x (basisVector i) i
      = ∑ i : Fin 3, fderiv ℝ (v s) x (basisVector i) i
  rw [h]

private theorem convection_congr {u v : VelocityEvolution} {t s : ℝ} (x : Space)
    (h : u t = v s) : convection u t x = convection v s x := by
  show fderiv ℝ (u t) x (u t x) = fderiv ℝ (v s) x (v s x)
  rw [h]

private theorem laplacian_congr {u v : VelocityEvolution} {t s : ℝ} (x : Space)
    (h : u t = v s) : laplacian u t x = laplacian v s x := by
  show ∑ i : Fin 3, fderiv ℝ (fun y : Space => fderiv ℝ (u t) y (basisVector i)) x
        (basisVector i)
      = ∑ i : Fin 3, fderiv ℝ (fun y : Space => fderiv ℝ (v s) y (basisVector i)) x
        (basisVector i)
  rw [h]

private theorem pressureGradient_congr {p q : PressureEvolution} {t s : ℝ} (x : Space)
    (h : p t = q s) : pressureGradient p t x = pressureGradient q s x := by
  show (fun i => fderiv ℝ (p t) x (basisVector i)) = (fun i => fderiv ℝ (q s) x (basisVector i))
  rw [h]

private theorem kineticEnergy_congr {u v : VelocityEvolution} {t s : ℝ} (h : u t = v s) :
    kineticEnergy u t = kineticEnergy v s := by
  unfold Navier.kineticEnergy
  rw [h]

private theorem integrable_energy_iff_slice {u v : VelocityEvolution} {t s : ℝ}
    (h : u t = v s) :
    MeasureTheory.Integrable (fun x : Space => ‖u t x‖ ^ 2) ↔
      MeasureTheory.Integrable (fun x : Space => ‖v s x‖ ^ 2) := by
  refine ⟨fun hu => ?_, fun hv => ?_⟩
  · have heq : (fun x : Space => ‖v s x‖ ^ 2) = (fun x : Space => ‖u t x‖ ^ 2) := by rw [← h]
    rw [heq]; exact hu
  · have heq : (fun x : Space => ‖u t x‖ ^ 2) = (fun x : Space => ‖v s x‖ ^ 2) := by rw [h]
    rw [heq]; exact hv

private theorem timeDerivative_congr_eventually {u v : VelocityEvolution} {t : ℝ}
    (h : ∀ᶠ s in nhdsWithin t (Set.Ici (0 : ℝ)), u s = v s)
    (hpt : u t = v t) (x : Space) :
    timeDerivative u t x = timeDerivative v t x := by
  have hev : (fun s : ℝ => u s x) =ᶠ[nhdsWithin t (Set.Ici (0 : ℝ))]
      fun s : ℝ => v s x :=
    h.mono fun s hs => congrFun hs x
  simpa [timeDerivative] using congrArg (fun L : ℝ →L[ℝ] Space => L 1)
    (Filter.EventuallyEq.fderivWithin_eq hev (congrFun hpt x))

/-! ## The paste with its glued pair exposed -/

/-- **The interior-time paste, with the glued pair explicit.**  Same content as
`RestartPaste.restart_paste` (whose conclusion is existential and hides the
glued functions), stated for `glueAt T u w` / `glueAt T p q` so that a class
law can be applied to the result.  Pressure agreement is needed only on the open
overlap `(T₀, T)`. -/
theorem restart_paste_glueAt {ν T T₀ h : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    {w : VelocityEvolution} {q : PressureEvolution}
    (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T) (_hh : 0 < h)
    (hsol : SolvesBefore ν T u p) (hnorm : PressureNormalizedBefore T p)
    (hw : SolvesFrom ν T₀ (T - T₀ + h) w q)
    (hq_norm : ∀ t : ℝ, T₀ ≤ t → t < T + h → q t 0 = 0)
    (hagree_v : ∀ t : ℝ, T₀ ≤ t → t < T → u t = w t)
    (hagree_p : ∀ t : ℝ, T₀ < t → t < T → p t = q t) :
    SolvesBefore ν (T + h) (glueAt T u w) (glueAt T p q) ∧
      PressureNormalizedBefore (T + h) (glueAt T p q) ∧
        VelocityAgreesBefore T u (glueAt T u w) ∧ PressureAgreesBefore T p (glueAt T p q) := by
  have hstrip : T₀ + (T - T₀ + h) = T + h := by ring
  obtain ⟨hu, hp, hinc, heq⟩ := hsol.classical
  obtain ⟨wv, wp, winc, weq, wfe, wel⟩ := hw
  rw [hstrip] at wv wp winc weq wfe wel
  set u' : VelocityEvolution := glueAt T u w with hu'_def
  set p' : PressureEvolution := glueAt T p q with hp'_def
  have hTpos : 0 < T := lt_of_le_of_lt hT₀ hT₀T
  have hu' : ∀ s : ℝ, s < T → u' s = u s := fun s hs => by
    simp only [hu'_def, glueAt, hs, ↓reduceIte]
  have hp' : ∀ s : ℝ, s < T → p' s = p s := fun s hs => by
    simp only [hp'_def, glueAt, hs, ↓reduceIte]
  have hw' : ∀ s : ℝ, T ≤ s → u' s = w s := fun s hs => by
    simp only [hu'_def, glueAt, not_lt.mpr hs, ↓reduceIte]
  have hq' : ∀ s : ℝ, T ≤ s → p' s = q s := fun s hs => by
    simp only [hp'_def, glueAt, not_lt.mpr hs, ↓reduceIte]
  have hw_on : ∀ s : ℝ, T₀ < s → u' s = w s := by
    intro s hs
    rcases lt_or_ge s T with hsT | hsT
    · rw [hu' s hsT, hagree_v s (le_of_lt hs) hsT]
    · exact hw' s hsT
  have hq_on : ∀ s : ℝ, T₀ < s → p' s = q s := by
    intro s hs
    rcases lt_or_ge s T with hsT | hsT
    · rw [hp' s hsT, hagree_p s hs hsT]
    · exact hq' s hsT
  have hvel_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u' z.1 z.2)
      (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) := by
    intro z hz
    rcases lt_or_ge z.1 T with htT | htT
    · have hbase : ContDiffWithinAt ℝ ∞ (fun zz : ℝ × Space => u zz.1 zz.2)
          (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) z := by
        refine' (hu z ⟨⟨hz.1.1, htT⟩, hz.2⟩).mono_of_mem_nhdsWithin ?_
        refine' mem_nhdsWithin.mpr ⟨Set.Iio T ×ˢ Set.univ, IsOpen.prod isOpen_Iio isOpen_univ,
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ _⟩, ?_⟩
        rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨⟨hle, hlt⟩, _⟩⟩
        exact ⟨⟨hle, Set.mem_Iio.mp ha1⟩, Set.mem_univ _⟩
      refine' hbase.congr_of_eventuallyEq_of_mem ?_ hz
      refine' eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Iio isOpen_univ).mem_nhds
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ _⟩)) fun z' hz' => _
      exact congrFun (hu' z'.1 (Set.mem_Iio.mp hz'.1)) z'.2
    · have hT₀z : T₀ < z.1 := lt_of_lt_of_le hT₀T htT
      have hbase : ContDiffWithinAt ℝ ∞ (fun zz : ℝ × Space => w zz.1 zz.2)
          (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) z := by
        refine' (wv z ⟨⟨le_of_lt hT₀z, hz.1.2⟩, hz.2⟩).mono_of_mem_nhdsWithin ?_
        refine' mem_nhdsWithin.mpr ⟨Set.Ioi T₀ ×ˢ Set.univ, IsOpen.prod isOpen_Ioi isOpen_univ,
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩, ?_⟩
        rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨⟨hle, hlt⟩, _⟩⟩
        exact ⟨⟨le_of_lt (Set.mem_Ioi.mp ha1), hlt⟩, Set.mem_univ _⟩
      refine' hbase.congr_of_eventuallyEq_of_mem ?_ hz
      refine' eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Ioi isOpen_univ).mem_nhds
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩)) fun z' hz' => _
      exact congrFun (hw_on z'.1 (Set.mem_Ioi.mp hz'.1)) z'.2
  have hpres_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p' z.1 z.2)
      (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) := by
    intro z hz
    rcases lt_or_ge z.1 T with htT | htT
    · have hbase : ContDiffWithinAt ℝ ∞ (fun zz : ℝ × Space => p zz.1 zz.2)
          (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) z := by
        refine' (hp z ⟨⟨hz.1.1, htT⟩, hz.2⟩).mono_of_mem_nhdsWithin ?_
        refine' mem_nhdsWithin.mpr ⟨Set.Iio T ×ˢ Set.univ, IsOpen.prod isOpen_Iio isOpen_univ,
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ _⟩, ?_⟩
        rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨⟨hle, hlt⟩, _⟩⟩
        exact ⟨⟨hle, Set.mem_Iio.mp ha1⟩, Set.mem_univ _⟩
      refine' hbase.congr_of_eventuallyEq_of_mem ?_ hz
      refine' eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Iio isOpen_univ).mem_nhds
          ⟨Set.mem_Iio.mpr htT, Set.mem_univ _⟩)) fun z' hz' => _
      exact congrFun (hp' z'.1 (Set.mem_Iio.mp hz'.1)) z'.2
    · have hT₀z : T₀ < z.1 := lt_of_lt_of_le hT₀T htT
      have hbase : ContDiffWithinAt ℝ ∞ (fun zz : ℝ × Space => q zz.1 zz.2)
          (Set.Ico (0 : ℝ) (T + h) ×ˢ (Set.univ : Set Space)) z := by
        refine' (wp z ⟨⟨le_of_lt hT₀z, hz.1.2⟩, hz.2⟩).mono_of_mem_nhdsWithin ?_
        refine' mem_nhdsWithin.mpr ⟨Set.Ioi T₀ ×ˢ Set.univ, IsOpen.prod isOpen_Ioi isOpen_univ,
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩, ?_⟩
        rintro ⟨a, b⟩ ⟨⟨ha1, _⟩, ⟨⟨hle, hlt⟩, _⟩⟩
        exact ⟨⟨le_of_lt (Set.mem_Ioi.mp ha1), hlt⟩, Set.mem_univ _⟩
      refine' hbase.congr_of_eventuallyEq_of_mem ?_ hz
      refine' eventuallyEq_of_mem
        (mem_nhdsWithin_of_mem_nhds ((IsOpen.prod isOpen_Ioi isOpen_univ).mem_nhds
          ⟨Set.mem_Ioi.mpr hT₀z, Set.mem_univ _⟩)) fun z' hz' => _
      exact congrFun (hq_on z'.1 (Set.mem_Ioi.mp hz'.1)) z'.2
  have hinc' : IncompressibleBefore (T + h) u' := by
    intro t ht htTh x
    rcases lt_or_ge t T with htT | htT
    · rw [divergence_congr x (hu' t htT), hinc t ht htT x]
    · rw [divergence_congr x (hw' t htT),
        winc t (le_of_lt (lt_of_lt_of_le hT₀T htT)) htTh x]
  have heq' : SatisfiesNavierStokesBefore ν zeroForce (T + h) u' p' := by
    intro t ht htTh x
    rcases lt_or_ge t T with htT | htT
    · have hev : ∀ᶠ s in nhdsWithin t (Set.Ici (0 : ℝ)), u' s = u s := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
          (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr htT))] with s hs
        exact hu' s (Set.mem_Iio.mp hs)
      rw [timeDerivative_congr_eventually hev (hu' t htT) x,
        convection_congr x (hu' t htT), laplacian_congr x (hu' t htT),
        pressureGradient_congr x (hp' t htT)]
      exact heq t ht htT x
    · have hT₀t : T₀ < t := lt_of_lt_of_le hT₀T htT
      have hev : ∀ᶠ s in nhdsWithin t (Set.Ici (0 : ℝ)), u' s = w s := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
          (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hT₀t))] with s hs
        exact hw_on s (Set.mem_Ioi.mp hs)
      rw [timeDerivative_congr_eventually hev (hw' t htT) x,
        convection_congr x (hw' t htT), laplacian_congr x (hw' t htT),
        pressureGradient_congr x (hq' t htT)]
      exact (weq t hT₀t htTh x).trans
        (by rw [show zeroForce t x = (0 : Space) from rfl, add_zero])
  have hfe' : ∀ t : ℝ, 0 ≤ t → t < T + h →
      MeasureTheory.Integrable (fun x : Space => ‖u' t x‖ ^ 2) := by
    intro t ht htTh
    rcases lt_or_ge t T with htT | htT
    · exact (integrable_energy_iff_slice (hu' t htT)).mpr (hsol.finite_energy t ht htT)
    · exact (integrable_energy_iff_slice (hw' t htT)).mpr
        (wfe t (le_of_lt (lt_of_lt_of_le hT₀T htT)) htTh)
  have heli' : ∀ t : ℝ, 0 ≤ t → t < T + h →
      kineticEnergy u' t ≤ kineticEnergy u' 0 := by
    intro t ht htTh
    rcases lt_or_ge t T with htT | htT
    · calc kineticEnergy u' t = kineticEnergy u t := kineticEnergy_congr (hu' t htT)
        _ ≤ kineticEnergy u 0 := hsol.energy_le_initial t ht htT
        _ = kineticEnergy u' 0 := (kineticEnergy_congr (hu' 0 hTpos)).symm
    · calc kineticEnergy u' t = kineticEnergy w t := kineticEnergy_congr (hw' t htT)
        _ ≤ kineticEnergy w T₀ :=
          wel t (le_of_lt (lt_of_lt_of_le hT₀T htT)) htTh
        _ = kineticEnergy u T₀ := (kineticEnergy_congr (hagree_v T₀ (le_refl T₀) hT₀T)).symm
        _ ≤ kineticEnergy u 0 := hsol.energy_le_initial T₀ hT₀ hT₀T
        _ = kineticEnergy u' 0 := (kineticEnergy_congr (hu' 0 hTpos)).symm
  have hpnorm : PressureNormalizedBefore (T + h) p' := by
    intro t ht htTh
    rcases lt_or_ge t T with htT | htT
    · rw [hp' t htT]; exact hnorm t ht htT
    · rw [hq' t htT]; exact hq_norm t (le_of_lt (lt_of_lt_of_le hT₀T htT)) htTh
  exact ⟨⟨⟨hvel_smooth, hpres_smooth, hinc', heq'⟩, hfe', heli'⟩, hpnorm,
    fun t _ htT => (hu' t htT).symm, fun t _ htT => (hp' t htT).symm⟩

/-- **Class restart engine ⟹ class continuation leaf**, through the explicit
paste and the class glue law. -/
theorem datumContinuationIn_of_datumRestartIn {C : SolutionClass} {N : CriticalQuantity}
    (hN : DatumRestartIn C N) : DatumContinuationIn C N := by
  intro ν hν u₀ hu₀ M
  obtain ⟨h, hh, heng⟩ := hN ν hν u₀ hu₀ M
  refine ⟨h, hh, fun T hT u p hinit hsol hmem hnorm hNbound => ?_⟩
  obtain ⟨T₀, hT₀, hT₀T, w, q, hv, hp, hw, hq, hwmem⟩ :=
    heng T hT u p hinit hsol hmem hnorm hNbound
  obtain ⟨hsol', hnorm', hv', hp'⟩ := restart_paste_glueAt hT₀ hT₀T hh hsol hnorm hw hq hv hp
  exact ⟨glueAt T u w, glueAt T p q, hsol', hnorm', hv', hp',
    C.glue hT₀ hT₀T hh hmem hwmem hv⟩

/-! ## The class-threaded composition -/

/-- One rung of the restart ladder inside a class. -/
structure ClassStage (C : SolutionClass) (ν : ℝ) (u₀ : SchwartzVelocity) where
  horizon : ℝ
  vel : VelocityEvolution
  pres : PressureEvolution
  horizon_pos : 0 < horizon
  init : ∀ x : Space, vel 0 x = u₀ x
  solves : SolvesBefore ν horizon vel pres
  pressure_normalized : PressureNormalizedBefore horizon pres
  mem : C.mem 0 horizon vel

/-- **The composition, threaded by an arbitrary solution class.**  Local
existence in the class, datum-dependent class continuation, and the a priori
bound on class solutions give the whole-space endpoint.  The proof is the one of
`CriticalControlDecomposition.wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori`
with the class membership carried along each rung; the endpoint itself carries
no class. -/
theorem wholeSpaceGlobalRegularity_of_localIn_datumContinuationIn_aprioriIn
    (C : SolutionClass) (N : CriticalQuantity)
    (hlocal : LocalExistenceIn C)
    (hcont : DatumContinuationIn C N)
    (hapriori : APrioriCriticalControlIn C N) :
    ProblemStatements.WholeSpaceGlobalRegularity := by
  intro ν hν u₀ hdiv
  obtain ⟨M, hM⟩ := hapriori ν hν u₀ hdiv
  obtain ⟨δ, hδ, hstep⟩ := hcont ν hν u₀ hdiv M
  obtain ⟨T₀, hT₀, v₀, q₀, hinit₀, hsolves₀, hmem₀⟩ := hlocal ν hν u₀ hdiv
  let base : ClassStage C ν u₀ :=
    { horizon := T₀, vel := v₀, pres := normalizePressure q₀, horizon_pos := hT₀,
      init := hinit₀, solves := hsolves₀.normalizePressure,
      pressure_normalized := normalizePressure_normalizedBefore T₀ q₀, mem := hmem₀ }
  have advance : ∀ s : ClassStage C ν u₀, ∃ s' : ClassStage C ν u₀,
      s'.horizon = s.horizon + δ ∧
        VelocityAgreesBefore s.horizon s.vel s'.vel ∧
        PressureAgreesBefore s.horizon s.pres s'.pres := by
    intro s
    obtain ⟨u', p', hsolve', hpnormalized', hvagree, hpagree, hmem'⟩ :=
      hstep s.horizon s.horizon_pos s.vel s.pres s.init s.solves s.mem
        s.pressure_normalized
        (hM s.horizon s.horizon_pos s.vel s.pres s.init s.solves s.mem)
    refine ⟨{ horizon := s.horizon + δ, vel := u', pres := p',
              horizon_pos := by linarith [s.horizon_pos],
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

/-- Conservativity: the existing datum-dependent composition is the
trivial-class instance of the threaded one. -/
theorem wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_viaClass
    (N : CriticalQuantity)
    (hlocal : LocalClassicalExistence)
    (hcont : DatumContinuationFromCriticalControl N)
    (hapriori : APrioriCriticalControl N) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_localIn_datumContinuationIn_aprioriIn trivialClass N
    (localExistenceIn_trivial_iff.mpr hlocal)
    ((datumContinuationIn_trivial_iff N).mpr hcont)
    ((aPrioriCriticalControlIn_trivial_iff N).mpr hapriori)

/-! ## The restart engine from budget existence, budget propagation, uniqueness -/

/-- Right truncation of a restart strip. -/
theorem solvesFrom_mono_right {ν T₀ L L' : ℝ} {w : VelocityEvolution}
    {q : PressureEvolution} (hw : SolvesFrom ν T₀ L w q) (hle : L' ≤ L) :
    SolvesFrom ν T₀ L' w q := by
  obtain ⟨wv, wp, winc, weq, wfe, wel⟩ := hw
  have hsub : Set.Ico T₀ (T₀ + L') ×ˢ (Set.univ : Set Space) ⊆
      Set.Ico T₀ (T₀ + L) ×ˢ (Set.univ : Set Space) :=
    Set.prod_mono (Set.Ico_subset_Ico_right (by linarith)) (subset_refl _)
  exact ⟨wv.mono hsub, wp.mono hsub,
    fun t ht htL x => winc t ht (by linarith) x,
    fun t ht htL x => weq t ht (by linarith) x,
    fun t ht htL => wfe t ht (by linarith),
    fun t ht htL => wel t ht (by linarith)⟩

/-- Slice differentiability of a jointly smooth scalar field at a time of its
strip (the slice map `x ↦ p t x` is the composition with `x ↦ (t, x)`, whose
image lies in the strip, so no interior condition on `t` is needed). -/
private theorem differentiable_slice {a b : ℝ} {p : PressureEvolution}
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2)
      (Set.Ico a b ×ˢ (Set.univ : Set Space)))
    {t : ℝ} (ht : t ∈ Set.Ico a b) : Differentiable ℝ (p t) := by
  have hd : DifferentiableOn ℝ (fun z : ℝ × Space => p z.1 z.2)
      (Set.Ico a b ×ˢ (Set.univ : Set Space)) :=
    hp.differentiableOn (by simp)
  have hc : DifferentiableOn ℝ (fun x : Space => ((t, x) : ℝ × Space)) Set.univ :=
    (differentiableOn_const t).prodMk differentiableOn_id
  have hmaps : Set.MapsTo (fun x : Space => ((t, x) : ℝ × Space)) Set.univ
      (Set.Ico a b ×ˢ (Set.univ : Set Space)) :=
    fun x _ => ⟨ht, Set.mem_univ x⟩
  exact differentiableOn_univ.mp (hd.comp hc hmaps)

/-- A linear functional on `ℝ³` is determined by its values on the three
coordinate vectors: equal pressure gradients give equal Fréchet derivatives. -/
private theorem fderiv_eq_of_pressureGradient_eq {p q : PressureEvolution} {t : ℝ} {x : Space}
    (h : pressureGradient p t x = pressureGradient q t x) :
    fderiv ℝ (p t) x = fderiv ℝ (q t) x := by
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.pi_ext
  intro i c
  have hi : fderiv ℝ (p t) x (basisVector i) = fderiv ℝ (q t) x (basisVector i) := congrFun h i
  have hs : (Pi.single i c : Space) = c • basisVector i := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [basisVector]
    · simp [basisVector, hj]
  simp only [ContinuousLinearMap.coe_coe]
  rw [hs, map_smul, map_smul, hi]

/-- **Pressure agreement from velocity agreement on an open overlap.**  Where
a `SolvesBefore` piece and a `SolvesFrom` strip carry the same velocity on an
open time window, the equation identifies their pressure gradients, so the
pressure difference is spatially constant, and the normalization `p(t,0) = 0`
of both makes it zero.  The window must be open at `T₀` because the strip's
equation clause is. -/
theorem pressure_eq_of_velocity_eq_interior {ν T T₀ L : ℝ} {u w : VelocityEvolution}
    {p q : PressureEvolution} (hT₀ : 0 ≤ T₀)
    (hsol : SolvesBefore ν T u p) (hw : SolvesFrom ν T₀ L w q)
    (hpn : PressureNormalizedBefore T p) (hqn : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → q t 0 = 0)
    (hagree : ∀ t : ℝ, T₀ ≤ t → t < T → t < T₀ + L → u t = w t)
    {t : ℝ} (ht0 : T₀ < t) (htT : t < T) (htL : t < T₀ + L) : p t = q t := by
  obtain ⟨_, hp, _, heq⟩ := hsol.classical
  obtain ⟨_, wp, _, weq, _, _⟩ := hw
  have ht0' : 0 ≤ t := le_trans hT₀ ht0.le
  have hut : u t = w t := hagree t ht0.le htT htL
  have hev : ∀ᶠ s in nhdsWithin t (Set.Ici (0 : ℝ)), u s = w s := by
    have hopen : IsOpen (Set.Ioo T₀ T ∩ Set.Iio (T₀ + L)) := isOpen_Ioo.inter isOpen_Iio
    have hmem : t ∈ Set.Ioo T₀ T ∩ Set.Iio (T₀ + L) := ⟨⟨ht0, htT⟩, htL⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)] with s hs
    exact hagree s hs.1.1.le hs.1.2 hs.2
  have hgrad : ∀ x : Space, pressureGradient p t x = pressureGradient q t x := by
    intro x
    have h1 := heq t ht0' htT x
    have h2 := weq t ht0 htL x
    rw [timeDerivative_congr_eventually hev hut x, convection_congr x hut,
      laplacian_congr x hut, show zeroForce t x = (0 : Space) from rfl, add_zero] at h1
    exact sub_right_injective (h1.symm.trans h2)
  have hpd : Differentiable ℝ (p t) := differentiable_slice hp ⟨ht0', htT⟩
  have hqd : Differentiable ℝ (q t) := differentiable_slice wp ⟨ht0.le, htL⟩
  have hfd : ∀ x : Space, fderiv ℝ (p t - q t) x = 0 := by
    intro x
    rw [fderiv_sub (hpd x) (hqd x), fderiv_eq_of_pressureGradient_eq (hgrad x), sub_self]
  have hconst := is_const_of_fderiv_eq_zero (f := p t - q t) (hpd.sub hqd) hfd
  funext x
  have hx := hconst x 0
  simp only [Pi.sub_apply, hpn t ht0' htT, hqn t ht0.le htL, sub_zero] at hx
  exact sub_eq_zero.mp hx

/-- Restart existence with a budget-controlled horizon (Kato's local theorem in
the class): the restart length depends on the viscosity and a bound `K` on the
budget `B` of the restart datum, not on the horizon or the solution. -/
def BudgetLocalExistenceIn (C : SolutionClass) (B : VelocityField → ℝ≥0∞) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0, ∃ h : ℝ, 0 < h ∧
    ∀ T₀ T : ℝ, 0 ≤ T₀ → T₀ < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      SolvesBefore ν T u p → C.mem 0 T u → B (u T₀) ≤ (K : ℝ≥0∞) →
      ∃ w : VelocityEvolution, ∃ q : PressureEvolution,
        w T₀ = u T₀ ∧ SolvesFrom ν T₀ h w q ∧
          (∀ t : ℝ, T₀ ≤ t → t < T₀ + h → q t 0 = 0) ∧ C.mem T₀ h w

/-- Budget propagation under the control (the BKM Grönwall estimate): on every
class solution from `u₀` with `N T u ≤ M`, the budget of every preterminal slice
is below `K = K(ν, u₀, M)`, uniformly in the horizon. -/
def BudgetPropagationIn (C : SolutionClass) (B : VelocityField → ℝ≥0∞)
    (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ → ∀ M : ℝ≥0,
    ∃ K : ℝ≥0, ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
      (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → C.mem 0 T u →
      N T u ≤ (M : ℝ≥0∞) → ∀ t : ℝ, 0 ≤ t → t < T → B (u t) ≤ (K : ℝ≥0∞)

/-- Restart uniqueness in the class (Kato uniqueness): a class restart strip
started from the slice `u T₀` of a class solution agrees with it on the
overlap. -/
def RestartUniquenessIn (C : SolutionClass) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ T₀ T L : ℝ, 0 ≤ T₀ → T₀ < T → 0 < L →
    ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
    ∀ w : VelocityEvolution, ∀ q : PressureEvolution,
      SolvesBefore ν T u p → C.mem 0 T u → SolvesFrom ν T₀ L w q → C.mem T₀ L w →
      w T₀ = u T₀ → ∀ t : ℝ, T₀ ≤ t → t < T → t < T₀ + L → u t = w t

/-- **The class restart engine from its three classical leaves.**  Restart
length `h/2`, restart time `T₀ = max 0 (T - h/2)`; the budget of `u T₀` is below
`K` by propagation, the restart strip of length `h` from `u T₀` exists by budget
existence and reaches past `T + h/2`, velocity agreement on `[T₀, T)` is
uniqueness, and pressure agreement on `(T₀, T)` is derived. -/
theorem datumRestartIn_of_budget_propagation_uniqueness {C : SolutionClass}
    {B : VelocityField → ℝ≥0∞} {N : CriticalQuantity}
    (hloc : BudgetLocalExistenceIn C B) (hprop : BudgetPropagationIn C B N)
    (huniq : RestartUniquenessIn C) : DatumRestartIn C N := by
  intro ν hν u₀ hu₀ M
  obtain ⟨K, hK⟩ := hprop ν hν u₀ hu₀ M
  obtain ⟨h, hh, hrestart⟩ := hloc ν hν K
  refine ⟨h / 2, by positivity, fun T hT u p hinit hsol hmem hnorm hN => ?_⟩
  set T₀ : ℝ := max 0 (T - h / 2) with hT₀_def
  have hT₀0 : 0 ≤ T₀ := le_max_left _ _
  have hT₀T : T₀ < T := max_lt hT (by linarith)
  have hTle : T - T₀ ≤ h / 2 := by
    have := le_max_right 0 (T - h / 2)
    linarith
  have hB : B (u T₀) ≤ (K : ℝ≥0∞) := hK T hT u p hinit hsol hmem hN T₀ hT₀0 hT₀T
  obtain ⟨w, q, hw0, hw, hqn, hwmem⟩ := hrestart T₀ T hT₀0 hT₀T u p hsol hmem hB
  have hagree_v : ∀ t : ℝ, T₀ ≤ t → t < T → u t = w t := fun t ht htT =>
    huniq ν hν T₀ T h hT₀0 hT₀T hh u p w q hsol hmem hw hwmem hw0 t ht htT (by linarith)
  refine ⟨T₀, hT₀0, hT₀T, w, q, hagree_v, ?_, solvesFrom_mono_right hw (by linarith),
    fun t ht htL => hqn t ht (by linarith), C.mono_right hwmem (by linarith)⟩
  intro t ht0 htT
  exact pressure_eq_of_velocity_eq_interior hT₀0 hsol hw hnorm hqn
    (fun s hs hsT _ => hagree_v s hs hsT) ht0 htT (by linarith)

/-! ## The BKM endpoint in class form -/

/-- **The whole-space endpoint from class leaves.**  Local existence in the
class, the BKM a priori bound on class solutions, and the three classical
restart leaves (budget existence, budget propagation under the BKM integral,
restart uniqueness) give `WholeSpaceGlobalRegularity`.  Compared with
`ContinuationScaleSelfImprovement.wholeSpaceGlobalRegularity_of_localAtOne_bkmAtOne_datumRestart`,
every hypothesis is restricted to a solution class of the prover's choosing,
and the restart input is split into its three classical components. -/
theorem wholeSpaceGlobalRegularity_of_classBudgetRestart
    (C : SolutionClass) (B : VelocityField → ℝ≥0∞)
    (hlocal : LocalExistenceIn C)
    (hbkm : APrioriCriticalControlIn C bkmVorticityControl)
    (hloc : BudgetLocalExistenceIn C B)
    (hprop : BudgetPropagationIn C B bkmVorticityControl)
    (huniq : RestartUniquenessIn C) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  wholeSpaceGlobalRegularity_of_localIn_datumContinuationIn_aprioriIn C bkmVorticityControl
    hlocal
    (datumContinuationIn_of_datumRestartIn
      (datumRestartIn_of_budget_propagation_uniqueness hloc hprop huniq))
    hbkm

/-- The restart-uniqueness leaf at the trivial class, written out: uniqueness of
a restart in the FULL `SolvesBefore`/`SolvesFrom` class.  This is the statement
the full-class restart `DatumHorizonIndependentRestart N` silently contains and
that no classical theorem supplies (ledger F-023). -/
def FullClassRestartUniqueness : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ T₀ T L : ℝ, 0 ≤ T₀ → T₀ < T → 0 < L →
    ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
    ∀ w : VelocityEvolution, ∀ q : PressureEvolution,
      SolvesBefore ν T u p → SolvesFrom ν T₀ L w q →
      w T₀ = u T₀ → ∀ t : ℝ, T₀ ≤ t → t < T → t < T₀ + L → u t = w t

theorem restartUniquenessIn_trivial_iff :
    RestartUniquenessIn trivialClass ↔ FullClassRestartUniqueness := by
  constructor
  · intro h ν hν T₀ T L hT₀ hT₀T hL u p w q hsol hw hw0
    exact h ν hν T₀ T L hT₀ hT₀T hL u p w q hsol trivial hw trivial hw0
  · intro h ν hν T₀ T L hT₀ hT₀T hL u p w q hsol _ hw _ hw0
    exact h ν hν T₀ T L hT₀ hT₀T hL u p w q hsol hw hw0

end Navier.Analysis.ClassRestartDecomposition

set_option pp.fullNames true in
#check @Navier.Analysis.ClassRestartDecomposition.wholeSpaceGlobalRegularity_of_localIn_datumContinuationIn_aprioriIn
set_option pp.fullNames true in
#check @Navier.Analysis.ClassRestartDecomposition.datumRestartIn_of_budget_propagation_uniqueness
set_option pp.fullNames true in
#check @Navier.Analysis.ClassRestartDecomposition.wholeSpaceGlobalRegularity_of_classBudgetRestart
set_option pp.fullNames true in
#check @Navier.Analysis.ClassRestartDecomposition.pressure_eq_of_velocity_eq_interior
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.restart_paste_glueAt
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.datumContinuationIn_of_datumRestartIn
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.wholeSpaceGlobalRegularity_of_localIn_datumContinuationIn_aprioriIn
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.wholeSpaceGlobalRegularity_of_local_datumContinuation_apriori_viaClass
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.pressure_eq_of_velocity_eq_interior
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.datumRestartIn_of_budget_propagation_uniqueness
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.wholeSpaceGlobalRegularity_of_classBudgetRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.datumRestartIn_trivial_of_datumRestart
set_option pp.fullNames true in
#print axioms Navier.Analysis.ClassRestartDecomposition.restartUniquenessIn_trivial_iff
