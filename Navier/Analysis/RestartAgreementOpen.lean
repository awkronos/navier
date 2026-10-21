import Navier.Analysis.RegularUniqueness
import Navier.Analysis.RestartUniqueness
import Navier.Analysis.CriticalControlDecomposition

/-!
# The kernel-side relaxation: strong–strong uniqueness against OPEN-SLAB competitors

`NS-A-ITEM6` (blob `d8854e0f638bdf311613395681ee1637dd189fa7`) reduced the analytic half of
hazard (b) of the ITEM-6 FEASIBILITY AUDIT to one named field, `RestartAgreement`: an `H³`
restart piece driven by the slice `u T₀` of a solution `u ∈ R` must equal `u` on the OPEN
overlap `(T₀, T)`.  Its obstruction, verified by probe: every uniqueness route in the
repository demands joint smoothness **closed at its own start time** —
`RegularUniqueness.uniqueness_R` discharges `SolClass.smooth = SmoothVelocityBefore`
(`ContDiffOn` on `Ico 0 T ×ˢ univ`) and `RestartUniqueness.uniqueness_from` sets
`smooth := smooth_shift hv` over the closed strip — while an `H³` piece is smooth only on
`Ioo 0 L ×ˢ univ`, exactly what `RestartPiece.smooth_vel` states.

This module builds that relaxation on the kernel side, as a SEPARATE object that *consumes* `R`
and never widens it: `RegularOnCompacts` appears only as a hypothesis, `SolClass` is not
mutated, and no clause of `R` is extended (the standing ruling "no further extension of `R`
before item 6" is honored).

## Why the cheap routes fail (measured, not assumed)

* **Shift-to-interior.**  Open-slab smoothness DOES transport through a shift by a strictly
  positive amount to the closed slab (`contDiffOn_shift_open`, kept below as the diagnostic), so
  a shifted pair consists of genuine `SolClass`es and `uniqueness_class` applies verbatim — but
  it then demands the initial condition `shiftE a u 0 = shiftE a v 0`, i.e. `u a = v a`: the very
  agreement being proved.  Circular.
* **Limit from `(ε, T)` to `(0, T)`.**  Needs `E ε → E 0` in `L²`, i.e. right-continuity of the
  *energy*, which pointwise hypotheses cannot give (mass escaping to spatial infinity keeps
  `‖u ε - v ε‖_{L²}` bounded away from `0` while converging pointwise to `0`).
* **Grönwall on the difference** with no fundamental theorem at `0` yields only
  `E s ≤ (liminf_{ε → 0⁺} E ε) · exp(6 K T')`, which collapses to `E ≡ 0` exactly when that
  liminf is `0` — again the energy-continuity field.  (Also barred: the director's mid-flight
  `RX-DUALITY` duality-energy lemma.)

## What the closed-at-start hypothesis is actually used for

Reading `uniqueness_class` leg by leg, every invocation of `hu.smooth`/`hv.smooth` is at a
*strictly positive* time (`Ioc 0 s`/`Ioo 0 T`): `hasDerivAt_sqdiff`, `continuousOn_Fint`,
`time_slice_energy`, `Fint_section`, `Ediff_le`, and the pointwise conclusion.  Exactly two legs
touch the time `0`:

1. the per-space fundamental theorem inside `energy_identity`, which asks
   `ContinuousOn (fun r => ‖u r x - v r x‖²) (Icc 0 s)`;
2. integrability of the endpoint term `Ediff u v 0`, obtained there from `Continuous (u 0)` via
   `integrable_sum_sq_diff`.

Leg 2 disappears under the hypothesis the uniqueness statement already carries — `u 0 = v 0`
makes the endpoint integrand vanish pointwise, hence its integral vanish, with no continuity
assumption at all.  For leg 1, joint smoothness up to `0` was only ever a *sufficient* way to get
continuity at `0` of the single-variable function `r ↦ v r x`; the honest requirement is the
one-sided datum `RightContinuousAtStart` (pointwise in space, along `Ioi 0`), transferred to
`nhdsWithin 0 (Icc 0 s)` by `tendsto_Icc_start` — which needs, and only needs, that the value at
`0` already equals the limit.  `rightContinuousAtStart_of_closed` shows the datum is strictly
weaker than the clause it replaces: closed-slab smoothness implies it.

## Result

`uniqueness_class_open`: strong–strong uniqueness on `[0, T']` for two fields jointly smooth only
on the OPEN slab, each carrying the datum.  The repository's Grönwall engine (`gronwall_zero`) and
the five `R` clauses are consumed unchanged; only the two endpoint-touching legs are reproved.
`agreement_of_open_datum` lands the restart-time form: `u t = vel (t - T₀)` for every
`T₀ < t < T`, for a closed-smooth `R`-solution against an `OpenRestartDatum` piece.

## What hazard (b) now costs

`RestartAgreement` is `agreement_of_open_datum` applied to ITEM6's `RestartPiece` projected onto
`OpenRestartDatum`.  Field by field: `Lpos`, `init`, `smooth_vel`, `smooth_pres`,
`incompressible`, `equation`, `finite_energy`, `energy_le_start`, `rslice` project as-is (the last
already has the `Ioc`-uniform shape the relaxed `R`-clause wants, and `pres0` is not consumed
here — the pressure half stays with `pressure_agree_of_piece`), `RestartPiece.mono` restricts the
lifespan to `T - T₀`, and the closed side comes from `SolClass.of_solvesBefore` plus
`RegularOnCompacts`.  **Exactly one obligation remains**: `RightContinuousAtStart vel`, i.e.

> for the piece produced from the slice `u T₀`, `vel r x → vel 0 x` for every `x`, as `r → 0⁺`.

That is one-sided, pointwise in space, asks nothing on `(T₀, T)` (so it is not an agreement
hypothesis), and is implied by any time-continuity of the producer's output into a space that
embeds in `C⁰` — e.g. `C⁰([0, L); H³(ℝ³))`, since `3 > 3/2` gives `H³ ↪ C⁰`.  It is strictly
weaker than the closed-slab `ContDiffOn` clause that `SolClass`/`SolvesFrom` demand, which is
precisely what an `H³` local-existence theorem cannot ship.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace Navier.Analysis.RestartAgreementOpen

open Navier Navier.Breakdown
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.RegularUniqueness
open Navier.Analysis.RestartUniqueness
open Navier.Analysis.RestartPaste

/-! ## The relaxation -/

/-- **Open-slab joint smoothness of a velocity**: `C^∞` on `(0, T) × ℝ³`, with NOTHING asked at
the initial time.  `SolClass.smooth` asks the same on the closed slab `[0, T) × ℝ³`; this is the
clause hazard (b) forces an `H³` restart piece to weaken. -/
def SmoothVelocityOnOpen (T : ℝ) (u : VelocityEvolution) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Ioo (0 : ℝ) T ×ˢ (univ : Set Space))

/-- Pressure twin of `SmoothVelocityOnOpen`. -/
def SmoothPressureOnOpen (T : ℝ) (p : PressureEvolution) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (Ioo (0 : ℝ) T ×ˢ (univ : Set Space))

theorem smoothVelocityOnOpen_of_before {T : ℝ} {u : VelocityEvolution}
    (h : SmoothVelocityBefore T u) : SmoothVelocityOnOpen T u :=
  h.mono (prod_mono Ioo_subset_Ico_self subset_rfl)

theorem smoothPressureOnOpen_of_before {T : ℝ} {p : PressureEvolution}
    (h : SmoothPressureBefore T p) : SmoothPressureOnOpen T p :=
  h.mono (prod_mono Ioo_subset_Ico_self subset_rfl)

/-- **The one-sided continuity datum**: pointwise right-continuity at the field's own initial
time.  The only trace of the initial time the relaxed uniqueness needs — `energy_identity_open`'s
per-space slice of the fundamental theorem asks continuity of `r ↦ v r x` on `[0, s]`, and away
from `0` open-slab smoothness supplies it. -/
def RightContinuousAtStart (u : VelocityEvolution) : Prop :=
  ∀ x : Space, Tendsto (fun r : ℝ => u r x) (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (u 0 x))

/-- **Admissible class with the smoothness clause relaxed.**  `SolClass` with `smooth` replaced by
`SmoothVelocityOnOpen` (the equation and incompressibility clauses were already stated at strictly
positive times) plus the datum.  A SEPARATE object, consumed alongside the untouched `SolClass`;
neither `SolClass` nor `R = RegularOnCompacts` is widened. -/
structure OpenSolClass (ν T : ℝ) (u : VelocityEvolution) (p : PressureEvolution) (E0 : ℝ) :
    Prop where
  smooth : SmoothVelocityOnOpen T u
  psmooth : SmoothPressureOnOpen T p
  inc : ∀ t : ℝ, 0 < t → t < T → ∀ x : Space, ∑ i : Fin 3, pd (u t) i i x = 0
  eqn : ∀ t : ℝ, 0 < t → t < T → ∀ x : Space,
    timeDerivative u t x = ν • lapF (u t) x - gradF (p t) x - fderiv ℝ (u t) x (u t x)
  fe : ∀ t : ℝ, 0 ≤ t → t < T → Integrable (fun x : Space => ‖u t x‖ ^ 2)
  ebd : ∀ t : ℝ, 0 ≤ t → t < T → kineticEnergy u t ≤ E0
  rc : RightContinuousAtStart u

/-- **The piece fields the relaxed uniqueness consumes.**  ITEM6's `RestartPiece` projects onto
this with exactly one missing obligation, `rc`; `pres0` is not consumed (the pressure half is
`H3RestartSlice.pressure_agree_of_piece`'s).  Stated here so this module compiles against the
committed tree. -/
structure OpenRestartDatum (ν L : ℝ) (v : VelocityField) (vel : ℝ → VelocityField)
    (pres : ℝ → PressureField) : Prop where
  Lpos : 0 < L
  init : vel 0 = v
  smooth_vel : SmoothVelocityOnOpen L vel
  smooth_pres : SmoothPressureOnOpen L pres
  incompressible : ∀ t : ℝ, 0 ≤ t → t < L → ∀ x : Space, divergence vel t x = 0
  equation : ∀ t : ℝ, 0 < t → t < L → ∀ x : Space,
    timeDerivative vel t x + convection vel t x =
      ν • laplacian vel t x - pressureGradient pres t x
  finite_energy : ∀ t : ℝ, 0 ≤ t → t < L → Integrable (fun x : Space => ‖vel t x‖ ^ 2)
  energy_le_start : ∀ t : ℝ, 0 ≤ t → t < L →
    kineticEnergy vel t ≤ kineticEnergy vel 0
  rslice : ∀ T' : ℝ, T' < L → ∃ K : ℝ, ∀ t ∈ Ioc (0 : ℝ) T', Rslice K vel pres t
  rc : RightContinuousAtStart vel

/-! ## The datum is implied by the clause it replaces (satisfiability guard) -/

/-- **Satisfiability guard.**  Closed-slab joint smoothness gives the datum: at the start point the
joint `ContinuousOn` restricts to right-continuity of every spatial slice.  So
`OpenSolClass`/`OpenRestartDatum` are relaxations, not extra assumptions — anything already
qualifying as a `SolClass` qualifies here.  The `ε δ` form is used rather than a filter transfer
because `nhdsWithin 0 (Ioi 0)` and `nhdsWithin 0 (Ico 0 T)` are incomparable: the second also
contains the point `0`. -/
theorem rightContinuousAtStart_of_closed {T : ℝ} {u : VelocityEvolution}
    (hsm : SmoothVelocityBefore T u) (hT : 0 < T) : RightContinuousAtStart u := by
  intro x
  have hc : ContinuousOn (fun z : ℝ × Space => u z.1 z.2)
      (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := continuousOn_vel hsm
  have h0 : Tendsto (fun z : ℝ × Space => u z.1 z.2)
      (nhdsWithin (0, x) (Ico (0 : ℝ) T ×ˢ univ)) (𝓝 (u 0 x)) :=
    hc (0, x) ⟨⟨le_rfl, hT⟩, mem_univ _⟩
  rw [Metric.tendsto_nhdsWithin_nhds] at h0 ⊢
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h0 ε hε
  refine ⟨min δ (T / 2), lt_min hδ (by linarith), fun r hr hrd => ?_⟩
  have hmem : (r, x) ∈ Ico (0 : ℝ) T ×ˢ (univ : Set Space) := by
    refine ⟨⟨hr.le, ?_⟩, mem_univ _⟩
    have h : dist (r : ℝ) (0 : ℝ) < T :=
      lt_of_lt_of_le hrd (le_trans (min_le_right _ _) (by linarith))
    rw [Real.dist_eq, sub_zero] at h
    exact (le_abs_self r).trans_lt h
  have hd : dist ((r, x) : ℝ × Space) (0, x) < δ := by
    show max (dist (r : ℝ) (0 : ℝ)) (dist (x : Space) x) < δ
    rw [dist_self, max_eq_left dist_nonneg]
    exact hrd.trans_le (min_le_left _ _)
  exact hh hmem hd

/-- Every genuine `SolClass` is an `OpenSolClass`. -/
theorem OpenSolClass.of_solClass {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    {E0 : ℝ} (hT : 0 < T) (hu : SolClass ν T u p E0) : OpenSolClass ν T u p E0 where
  smooth := smoothVelocityOnOpen_of_before hu.smooth
  psmooth := smoothPressureOnOpen_of_before hu.psmooth
  inc := hu.inc
  eqn := hu.eqn
  fe := hu.fe
  ebd := hu.ebd
  rc := rightContinuousAtStart_of_closed hu.smooth hT

/-- The datum bundle of an `H³` piece becomes an admissible open-slab field.  `equation` travels
to the `lapF`/`gradF` form exactly as in `RestartUniqueness.solClass_of_solvesFrom`, and
`incompressible` to the `pd` form as in `RegularUniqueness.slice_div` — both by definition. -/
theorem openSolClass_of_datum {ν L : ℝ} {v : VelocityField} {vel : ℝ → VelocityField}
    {pres : ℝ → PressureField} (hp : OpenRestartDatum ν L v vel pres) :
    OpenSolClass ν L vel pres (kineticEnergy vel 0) where
  smooth := hp.smooth_vel
  psmooth := hp.smooth_pres
  inc t ht htL x := hp.incompressible t ht.le htL x
  eqn t ht htL x := by
    have h := hp.equation t ht htL x
    have h' : timeDerivative vel t x = ν • laplacian vel t x - pressureGradient pres t x -
        convection vel t x := by rw [← h]; abel
    exact h'
  fe := hp.finite_energy
  ebd t ht htL := hp.energy_le_start t ht htL
  rc := hp.rc

/-! ## Open-slab calculus: the leaves `RegularUniqueness` derives from closed smoothness -/

theorem contDiff_slice_open {T t : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityOnOpen T u)
    (ht : t ∈ Ioo (0 : ℝ) T) : ContDiff ℝ ∞ (u t) := by
  rw [← contDiffOn_univ]
  exact hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun y _ => ⟨ht, mem_univ _⟩

theorem contDiff_pslice_open {T t : ℝ} {p : PressureEvolution}
    (hsm : SmoothPressureOnOpen T p) (ht : t ∈ Ioo (0 : ℝ) T) : ContDiff ℝ ∞ (p t) := by
  rw [← contDiffOn_univ]
  exact hsm.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun y _ => ⟨ht, mem_univ _⟩

theorem contDiffAt_open {T s : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityOnOpen T u)
    (hs : s ∈ Ioo (0 : ℝ) T) (x : Space) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (s, x) :=
  hsm.contDiffAt ((isOpen_strip T).mem_nhds ⟨hs, mem_univ _⟩)

theorem hasDerivAt_tD_open {T s : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityOnOpen T u)
    (hs : s ∈ Ioo (0 : ℝ) T) (x : Space) : HasDerivAt (fun s' => u s' x) (tD u s x) s := by
  have hF := ((contDiffAt_open hsm hs x).differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun s' : ℝ => ((s', x) : ℝ × Space)) ((1, 0) : ℝ × Space) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hF.comp_hasDerivAt s hl

theorem timeDerivative_eq_tD_open {T s : ℝ} {u : VelocityEvolution}
    (hsm : SmoothVelocityOnOpen T u) (hs : s ∈ Ioo (0 : ℝ) T) (x : Space) :
    timeDerivative u s x = tD u s x := by
  have h := (hasDerivAt_tD_open hsm hs x).hasDerivWithinAt (s := Ici (0 : ℝ))
  exact h.derivWithin (uniqueDiffOn_Ici 0 s hs.1.le)

theorem continuousOn_tD_open {T : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityOnOpen T u) :
    ContinuousOn (fun z : ℝ × Space => tD u z.1 z.2)
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  have h := (hsm.continuousOn_fderiv_of_isOpen (isOpen_strip T) (by simp))
  exact h.clm_apply continuousOn_const

theorem continuousOn_vel_open {T : ℝ} {u : VelocityEvolution} (hsm : SmoothVelocityOnOpen T u) :
    ContinuousOn (fun z : ℝ × Space => u z.1 z.2) (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
  hsm.continuousOn

/-- The open-slab twin of `RegularUniqueness.continuousOn_Fint`: the `Ico` restriction step of the
original exists only because its hypotheses were closed-slab. -/
theorem continuousOn_Fint_open {T : ℝ} {u v : VelocityEvolution}
    (hsu : SmoothVelocityOnOpen T u) (hsv : SmoothVelocityOnOpen T v) :
    ContinuousOn (Fint u v) (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) := by
  have hu := continuousOn_vel_open hsu
  have hv := continuousOn_vel_open hsv
  have htu := continuousOn_tD_open hsu
  have htv := continuousOn_tD_open hsv
  unfold Fint
  refine continuousOn_finsetSum _ fun i _ => ?_
  exact (continuousOn_const.mul (((continuous_apply i).comp_continuousOn hu).sub
    ((continuous_apply i).comp_continuousOn hv))).mul
    (((continuous_apply i).comp_continuousOn htu).sub ((continuous_apply i).comp_continuousOn htv))

/-- The open-slab twin of `RegularUniqueness.hasDerivAt_sqdiff`. -/
theorem hasDerivAt_sqdiff_open {T r : ℝ} {u v : VelocityEvolution}
    (hsu : SmoothVelocityOnOpen T u) (hsv : SmoothVelocityOnOpen T v)
    (hr : r ∈ Ioo (0 : ℝ) T) (x : Space) :
    HasDerivAt (fun r => ∑ i : Fin 3, (u r x i - v r x i) ^ 2)
      (∑ i : Fin 3, 2 * (u r x i - v r x i) * (tD u r x i - tD v r x i)) r := by
  have hc : ∀ i : Fin 3, HasDerivAt (fun r => u r x i - v r x i) (tD u r x i - tD v r x i) r :=
    fun i => ((hasDerivAt_pi.mp (hasDerivAt_tD_open hsu hr x)) i).sub
      ((hasDerivAt_pi.mp (hasDerivAt_tD_open hsv hr x)) i)
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hc i).pow 2
  refine h.congr_deriv (Finset.sum_congr rfl fun i _ => ?_)
  push_cast
  ring

/-- The joint difference-energy integrand `((r, x) ↦ Σᵢ (u r xᵢ - v r xᵢ)²)`; `Ediff u v t` is
definitionally `∫ x, Wdiff u v (t, x)`. -/
def Wdiff (u v : VelocityEvolution) (z : ℝ × Space) : ℝ :=
  ∑ i : Fin 3, (u z.1 z.2 i - v z.1 z.2 i) ^ 2

/-! ## The endpoint leg -/

/-- **Right-continuity plus the value at the start is continuity within `[0, s]`.**  The filters
`nhdsWithin 0 (Ioi 0)` and `nhdsWithin 0 (Icc 0 s)` are incomparable — the second also contains the
point `0` — but because `f 0` already equals the limit, the `ε δ` forms transfer.  This is the
entire analytic content of `RightContinuousAtStart`. -/
theorem tendsto_Icc_start {E : Type*} [PseudoMetricSpace E] {f : ℝ → E} {l : E} (s : ℝ)
    (h : Tendsto f (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 l)) (h0 : f 0 = l) :
    Tendsto f (nhdsWithin 0 (Icc (0 : ℝ) s)) (𝓝 l) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hfd⟩ := h ε hε
  refine ⟨δ, hδ, fun r' hr' hrδ => ?_⟩
  rcases eq_or_ne r' 0 with rfl | hne
  · rw [h0, dist_self]
    exact hε
  · exact hfd (lt_of_le_of_ne hr'.1 (Ne.symm hne)) hrδ

/-- **The per-space difference integrand is continuous on `[0, s]`** for two open-slab fields that
carry the datum: at `0` the datum does it, away from `0` joint open continuity is even enough to
give full continuity, which holds within any set.  This is the leg `energy_identity` needs and
that no open-slab field supplies by itself. -/
theorem continuousOn_Wdiff_open {T s : ℝ} {u v : VelocityEvolution} (x : Space) (hsT : s < T)
    (hu : SmoothVelocityOnOpen T u) (hv : SmoothVelocityOnOpen T v)
    (hrcu : Tendsto (fun r : ℝ => u r x) (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (u 0 x)))
    (hrcv : Tendsto (fun r : ℝ => v r x) (nhdsWithin 0 (Ioi (0 : ℝ))) (𝓝 (v 0 x))) :
    ContinuousOn (fun r : ℝ => Wdiff u v (r, x)) (Icc (0 : ℝ) s) := by
  have hcw : ContinuousOn (Wdiff u v) (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) := by
    have huw := continuousOn_vel_open hu
    have hvw := continuousOn_vel_open hv
    unfold Wdiff
    exact continuousOn_finsetSum _ fun i _ =>
      (((continuous_apply i).comp_continuousOn huw).sub
        ((continuous_apply i).comp_continuousOn hvw)).pow 2
  show ContinuousOn (fun r : ℝ => ∑ i : Fin 3, (u r x i - v r x i) ^ 2) (Icc (0 : ℝ) s)
  intro r hr
  rcases eq_or_ne r 0 with rfl | hne
  · have hg : Continuous (fun w : Space × Space => ∑ i : Fin 3, (w.1 i - w.2 i) ^ 2) :=
      continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).sub ((continuous_apply i).comp continuous_snd)
        |>.pow 2
    have key : Tendsto (fun q : ℝ => (u q x, v q x)) (nhdsWithin 0 (Icc (0 : ℝ) s))
        (𝓝 (u 0 x, v 0 x)) :=
      (tendsto_Icc_start s hrcu rfl).prodMk_nhds (tendsto_Icc_start s hrcv rfl)
    have hres : Tendsto (fun q : ℝ => Wdiff u v (q, x)) (nhdsWithin 0 (Icc (0 : ℝ) s))
        (𝓝 (Wdiff u v (0, x))) :=
      Tendsto.comp (f := fun q : ℝ => (u q x, v q x))
        (g := fun w : Space × Space => ∑ i : Fin 3, (w.1 i - w.2 i) ^ 2)
        (hg.tendsto (u 0 x, v 0 x)) key
    exact hres
  · have hrIoo : r ∈ Ioo (0 : ℝ) T :=
      ⟨lt_of_le_of_ne hr.1 (Ne.symm hne), lt_of_le_of_lt hr.2 hsT⟩
    have hca : ContinuousAt (Wdiff u v) (r, x) :=
      hcw.continuousAt (IsOpen.mem_nhds (isOpen_strip T) ⟨hrIoo, mem_univ _⟩)
    have hin : ContinuousAt (fun q : ℝ => (q, x)) r :=
      continuousAt_id.prodMk continuousAt_const
    have hcomp : ContinuousAt (fun q : ℝ => Wdiff u v (q, x)) r :=
      Tendsto.comp (f := fun q : ℝ => (q, x)) (g := Wdiff u v) hca.tendsto hin.tendsto
    exact hcomp.continuousWithinAt

/-! ## Single-time legs on the open slab -/

/-- `time_slice_energy` for open-slab fields: the four `contDiff_slice` invocations are the only
difference from the original, and all of them sit at a strictly positive time. -/
theorem time_slice_energy_open {ν T K t : ℝ} (hν : 0 ≤ ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} {Eu Ev : ℝ} (hu : OpenSolClass ν T u p Eu)
    (hv : OpenSolClass ν T v q Ev) (ht0 : 0 < t) (htT : t < T)
    (hRu : Rslice K u p t) (hRv : Rslice K v q t) :
    Integrable (fun x => ∑ i : Fin 3, 2 * (u t x i - v t x i) *
        (timeDerivative u t x i - timeDerivative v t x i)) ∧
      ∫ x, ∑ i : Fin 3, 2 * (u t x i - v t x i) *
        (timeDerivative u t x i - timeDerivative v t x i) ≤ 6 * K * Ediff u v t := by
  have h := slice_energy hν (DU := fun x => timeDerivative u t x)
    (DV := fun x => timeDerivative v t x)
    (contDiff_slice_open hu.smooth ⟨ht0, htT⟩) (contDiff_slice_open hv.smooth ⟨ht0, htT⟩)
    (contDiff_pslice_open hu.psmooth ⟨ht0, htT⟩)
    (contDiff_pslice_open hv.psmooth ⟨ht0, htT⟩)
    (hu.fe t ht0.le htT) (hv.fe t ht0.le htT) hRu.1 hRv.1 hRu.2.1 hRv.2.1 hRu.2.2.2.1
    hRv.2.2.2.1 hRu.2.2.2.2 hRv.2.2.2.2 (hu.inc t ht0 htT) (hv.inc t ht0 htT)
    (hu.eqn t ht0 htT) (hv.eqn t ht0 htT)
  have hfun : (fun x => ∑ i : Fin 3, 2 * (u t x i - v t x i) *
      (timeDerivative u t x i - timeDerivative v t x i)) = fun x =>
      2 * ∑ i : Fin 3, (u t x i - v t x i) * (timeDerivative u t x i -
        timeDerivative v t x i) := by
    funext x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun]
  refine ⟨h.1.const_mul 2, ?_⟩
  rw [integral_const_mul]
  unfold Ediff
  linarith [h.2]

/-- `Fint_section` for open-slab fields. -/
theorem Fint_section_open {ν T K r : ℝ} (hν : 0 ≤ ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} {Eu Ev : ℝ} (hu : OpenSolClass ν T u p Eu)
    (hv : OpenSolClass ν T v q Ev) (hr : r ∈ Ioo (0 : ℝ) T) (hRu : Rslice K u p r)
    (hRv : Rslice K v q r) :
    Integrable (fun x => Fint u v (r, x)) ∧
      ∫ x, ‖Fint u v (r, x)‖ ≤ 2 * (Eu + Ev) + 12 * K := by
  have hsu := hu.smooth
  have hsv := hv.smooth
  have htdu : ∀ x, timeDerivative u r x = tD u r x := timeDerivative_eq_tD_open hsu hr
  have htdv : ∀ x, timeDerivative v r x = tD v r x := timeDerivative_eq_tD_open hsv hr
  obtain ⟨hint, -⟩ := time_slice_energy_open hν hu hv hr.1 hr.2 hRu hRv
  have hfun : (fun x => Fint u v (r, x)) = fun x => ∑ i : Fin 3, 2 * (u r x i - v r x i) *
      (timeDerivative u r x i - timeDerivative v r x i) := by
    funext x; unfold Fint; simp only [htdu, htdv]
  refine ⟨hfun ▸ hint, ?_⟩
  -- pointwise domination
  have huc : Continuous (u r) := (contDiff_slice_open hsu hr).continuous
  have hvc : Continuous (v r) := (contDiff_slice_open hsv hr).continuous
  have hdu : Continuous (fun x => timeDerivative u r x) := by
    have : (fun x => timeDerivative u r x) = fun x => tD u r x := funext htdu
    rw [this]
    exact ((continuousOn_tD_open hsu).comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hr, mem_univ _⟩))
  have hdv : Continuous (fun x => timeDerivative v r x) := by
    have : (fun x => timeDerivative v r x) = fun x => tD v r x := funext htdv
    rw [this]
    exact ((continuousOn_tD_open hsv).comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hr, mem_univ _⟩))
  set G : Space → ℝ := fun x => 2 * (∑ i : Fin 3, u r x i ^ 2 + ∑ i : Fin 3, v r x i ^ 2) +
    6 * (‖timeDerivative u r x‖ ^ 2 + ‖timeDerivative v r x‖ ^ 2) with hG
  have hGi : Integrable G :=
    (((integrable_sum_sq huc (hu.fe r hr.1.le hr.2)).add
      (integrable_sum_sq hvc (hv.fe r hr.1.le hr.2))).const_mul 2).add
      ((hRu.2.2.1.1.add hRv.2.2.1.1).const_mul 6)
  have hbd : ∀ x, ‖Fint u v (r, x)‖ ≤ G x := by
    intro x
    rw [congrFun hfun x, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hi : ∀ i : Fin 3, |2 * (u r x i - v r x i) * (timeDerivative u r x i -
        timeDerivative v r x i)| ≤ 2 * (u r x i ^ 2 + v r x i ^ 2) +
          2 * (‖timeDerivative u r x‖ ^ 2 + ‖timeDerivative v r x‖ ^ 2) := by
      intro i
      have a1 := sq_component_le (timeDerivative u r x) i
      have a2 := sq_component_le (timeDerivative v r x) i
      set a := u r x i - v r x i
      set b := timeDerivative u r x i - timeDerivative v r x i
      have hab : |2 * a * b| ≤ a ^ 2 + b ^ 2 := by
        rw [abs_mul, abs_mul, abs_two]
        nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
      have ha : a ^ 2 ≤ 2 * (u r x i ^ 2 + v r x i ^ 2) := by
        nlinarith [sq_nonneg (u r x i + v r x i)]
      have hb : b ^ 2 ≤ 2 * (‖timeDerivative u r x‖ ^ 2 + ‖timeDerivative v r x‖ ^ 2) := by
        nlinarith [sq_nonneg (timeDerivative u r x i + timeDerivative v r x i)]
      linarith
    refine (Finset.sum_le_sum fun i _ => hi i).trans (le_of_eq ?_)
    simp only [hG, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hFn : Integrable (fun x => ‖Fint u v (r, x)‖) := (hfun ▸ hint).norm
  refine (integral_mono hFn hGi hbd).trans ?_
  have iU : Integrable (fun x => ∑ i : Fin 3, u r x i ^ 2) :=
    integrable_sum_sq huc (hu.fe r hr.1.le hr.2)
  have iV : Integrable (fun x => ∑ i : Fin 3, v r x i ^ 2) :=
    integrable_sum_sq hvc (hv.fe r hr.1.le hr.2)
  have iDU : Integrable (fun x => ‖timeDerivative u r x‖ ^ 2) := hRu.2.2.1.1
  have iDV : Integrable (fun x => ‖timeDerivative v r x‖ ^ 2) := hRv.2.2.1.1
  have i1 : Integrable (fun x => 2 * (∑ i : Fin 3, u r x i ^ 2 + ∑ i : Fin 3, v r x i ^ 2)) :=
    (iU.add iV).const_mul 2
  have i2 : Integrable (fun x => 6 * (‖timeDerivative u r x‖ ^ 2 +
      ‖timeDerivative v r x‖ ^ 2)) := (iDU.add iDV).const_mul 6
  show ∫ x, (2 * (∑ i : Fin 3, u r x i ^ 2 + ∑ i : Fin 3, v r x i ^ 2) +
    6 * (‖timeDerivative u r x‖ ^ 2 + ‖timeDerivative v r x‖ ^ 2)) ≤ _
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul, integral_add iU iV,
    integral_add iDU iDV]
  have e1 : ∫ x, ∑ i : Fin 3, u r x i ^ 2 ≤ Eu := hu.ebd r hr.1.le hr.2
  have e2 : ∫ x, ∑ i : Fin 3, v r x i ^ 2 ≤ Ev := hv.ebd r hr.1.le hr.2
  have e3 := hRu.2.2.1.2
  have e4 := hRv.2.2.1.2
  linarith

/-- `Ediff_le` at a strictly positive time for open-slab fields. -/
theorem Ediff_le_open {ν T t Eu Ev : ℝ} {u v : VelocityEvolution} {p q : PressureEvolution}
    (hu : OpenSolClass ν T u p Eu) (hv : OpenSolClass ν T v q Ev) (ht0 : 0 < t)
    (htT : t < T) : Ediff u v t ≤ 2 * (Eu + Ev) := by
  have huc := (contDiff_slice_open hu.smooth ⟨ht0, htT⟩).continuous
  have hvc := (contDiff_slice_open hv.smooth ⟨ht0, htT⟩).continuous
  have iU := integrable_sum_sq huc (hu.fe t ht0.le htT)
  have iV := integrable_sum_sq hvc (hv.fe t ht0.le htT)
  have hmono : Ediff u v t ≤ ∫ x, 2 * (∑ i : Fin 3, u t x i ^ 2 + ∑ i : Fin 3, v t x i ^ 2) := by
    refine integral_mono (integrable_sum_sq_diff huc hvc (hu.fe t ht0.le htT)
      (hv.fe t ht0.le htT)) ((iU.add iV).const_mul 2) (fun x => ?_)
    show ∑ i : Fin 3, (u t x i - v t x i) ^ 2 ≤
      2 * (∑ i : Fin 3, u t x i ^ 2 + ∑ i : Fin 3, v t x i ^ 2)
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (u t x i + v t x i)]
  have e : ∫ x, 2 * (∑ i : Fin 3, u t x i ^ 2 + ∑ i : Fin 3, v t x i ^ 2) =
      2 * (kineticEnergy u t + kineticEnergy v t) := by
    rw [integral_const_mul, integral_add iU iV]; rfl
  have h1 := hu.ebd t ht0.le htT
  have h2 := hv.ebd t ht0.le htT
  linarith

/-- **The energy identity on an open slab.**  `E(s) - E(0) = ∫₀ˢ ∫ 2 W·∂ₜW` for two fields smooth
only on `(0, T) × ℝ³`, each carrying the one-sided datum and agreeing initially.  Versus
`RegularUniqueness.energy_identity`, two legs change: the per-space continuity hypothesis of the
fundamental theorem comes from `continuousOn_Wdiff_open` (datum at `0`, open smoothness elsewhere),
and the endpoint term `Ediff u v 0` is not obtained from `Continuous (u 0)` — open-slab smoothness
says nothing about the spatial continuity of the initial slice — but from the initial agreement
`u 0 = v 0`, under which the endpoint integrand vanishes pointwise.  The horizon is
`s ∈ Ioc 0 T'`: at `s = 0` the identity is `0 = 0` and is discharged in `uniqueness_class_open`. -/
theorem energy_identity_open {ν T T' K s : ℝ} (hν : 0 ≤ ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} {Eu Ev : ℝ} (hu : OpenSolClass ν T u p Eu)
    (hv : OpenSolClass ν T v q Ev) (hT'T : T' < T) (hs : s ∈ Ioc (0 : ℝ) T')
    (h0 : u 0 = v 0)
    (hR : ∀ r ∈ Ioc (0 : ℝ) T', Rslice K u p r ∧ Rslice K v q r) :
    IntegrableOn (fun r => ∫ x, Fint u v (r, x)) (Ioc 0 s) ∧
      Ediff u v s - Ediff u v 0 = ∫ r in Ioc 0 s, ∫ x, Fint u v (r, x) := by
  have hsu := hu.smooth
  have hsv := hv.smooth
  have hsT : s < T := lt_of_le_of_lt hs.2 hT'T
  set μ : Measure ℝ := volume.restrict (Ioc 0 s) with hμ
  have hprod : μ.prod (volume : Measure Space) =
      ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Ioc 0 s ×ˢ univ) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hsub : Ioc (0 : ℝ) s ×ˢ (univ : Set Space) ⊆ Ioo (0 : ℝ) T ×ˢ univ :=
    prod_mono (fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hsT⟩) subset_rfl
  have hmeas : AEStronglyMeasurable (Fint u v) (μ.prod volume) := by
    rw [hprod]
    exact ((continuousOn_Fint_open hsu hsv).mono hsub).aestronglyMeasurable
      (measurableSet_Ioc.prod MeasurableSet.univ)
  set B : ℝ := 2 * (Eu + Ev) + 12 * K
  have hsec : ∀ r ∈ Ioc (0 : ℝ) s, Integrable (fun x => Fint u v (r, x)) ∧
      ∫ x, ‖Fint u v (r, x)‖ ≤ B := fun r hr =>
    Fint_section_open hν hu hv ⟨hr.1, lt_of_le_of_lt hr.2 hsT⟩ (hR r ⟨hr.1, hr.2.trans hs.2⟩).1
      (hR r ⟨hr.1, hr.2.trans hs.2⟩).2
  have hInt : Integrable (Fint u v) (μ.prod volume) := by
    refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using (hsec r hr).1
    · refine (integrableOn_const (C := B) (s := Ioc (0 : ℝ) s)
        (hs := measure_Ioc_lt_top.ne)).mono'
        hmeas.norm.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      exact (hsec r hr).2
  have hJ : Integrable (fun r => ∫ x, Fint u v (r, x)) μ := hInt.integral_prod_left
  refine ⟨hJ, ?_⟩
  have hswap : ∫ r, (∫ x, Fint u v (r, x)) ∂μ = ∫ x, (∫ r, Fint u v (r, x) ∂μ) :=
    integral_integral_swap (f := fun r x => Fint u v (r, x)) hInt
  rw [hswap]
  -- per-point fundamental theorem of calculus, endpoint continuity from the datum
  have hFTC : ∀ᵐ x ∂(volume : Measure Space), ∫ r, Fint u v (r, x) ∂μ =
      Wdiff u v (s, x) - Wdiff u v (0, x) := by
    filter_upwards [hInt.prod_left_ae] with x hx
    have hcont : ContinuousOn (fun r : ℝ => Wdiff u v (r, x)) (Icc (0 : ℝ) s) :=
      continuousOn_Wdiff_open x hsT hsu hsv (hu.rc x) (hv.rc x)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1.le hcont
      (fun r hr => hasDerivAt_sqdiff_open hsu hsv ⟨hr.1, lt_trans hr.2 hsT⟩ x)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1.le).2 hx)
    rw [intervalIntegral.integral_of_le hs.1.le] at h
    exact h
  rw [integral_congr_ae hFTC]
  have hw0 : ∀ y : Space, Wdiff u v (0, y) = (0 : ℝ) := fun y => by
    show ∑ i : Fin 3, (u 0 y i - v 0 y i) ^ 2 = 0
    simp [h0]
  have hE0 : Ediff u v 0 = 0 := by
    show ∫ x, ∑ i : Fin 3, (u 0 x i - v 0 x i) ^ 2 = 0
    simp [h0]
  rw [integral_congr_ae (Eventually.of_forall fun x => by rw [hw0 x, sub_zero]), hE0, sub_zero]
  rfl

/-! ## Strong–strong uniqueness against open-slab competitors -/

/-- **Strong–strong uniqueness for the open-slab energy class**, on `[0, T']` with `T' < T`, from
a uniform `R`-bound at positive times.  The twin of `RegularUniqueness.uniqueness_class` with both
smoothness clauses relaxed to the open slab: the same Grönwall engine (`gronwall_zero`) and the
same five `R` clauses are consumed unchanged, and only the two endpoint legs differ. -/
theorem uniqueness_class_open {ν T T' K Eu Ev : ℝ} (hν : 0 < ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} (hu : OpenSolClass ν T u p Eu) (hv : OpenSolClass ν T v q Ev)
    (hT'T : T' < T) (hK0 : 0 ≤ K)
    (hR : ∀ r ∈ Ioc (0 : ℝ) T', Rslice K u p r ∧ Rslice K v q r) (h0 : u 0 = v 0) :
    ∀ t ∈ Icc (0 : ℝ) T', u t = v t := by
  intro t htI
  have ht0 := htI.1
  have htT' := htI.2
  have htT : t < T := lt_of_le_of_lt htT' hT'T
  have hsu := hu.smooth
  have hsv := hv.smooth
  set E : ℝ → ℝ := Ediff u v
  have hE0 : E 0 = 0 := by
    show ∫ x, ∑ i : Fin 3, (u 0 x i - v 0 x i) ^ 2 = 0
    simp [h0]
  -- measurability of `E`: only the OPEN slab is jointly continuous, so work on `Ioc 0 T'` and
  -- transfer the measure across the endpoint null set `{0}`
  have hEmeas : AEStronglyMeasurable E (volume.restrict (Icc (0 : ℝ) T')) := by
    have hprod : (volume.restrict (Ioc (0 : ℝ) T')).prod (volume : Measure Space) =
        ((volume : Measure ℝ).prod (volume : Measure Space)).restrict (Ioc 0 T' ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hsub : Ioc (0 : ℝ) T' ×ˢ (univ : Set Space) ⊆ Ioo (0 : ℝ) T ×ˢ univ :=
      prod_mono (fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hT'T⟩) subset_rfl
    have hu' := (continuousOn_vel_open hsu).mono hsub
    have hv' := (continuousOn_vel_open hsv).mono hsub
    have hc : ContinuousOn (fun z : ℝ × Space => ∑ i : Fin 3, (u z.1 z.2 i - v z.1 z.2 i) ^ 2)
        (Ioc (0 : ℝ) T' ×ˢ univ) :=
      continuousOn_finsetSum _ fun i _ =>
        (((continuous_apply i).comp_continuousOn hu').sub
          ((continuous_apply i).comp_continuousOn hv')).pow 2
    have hm : AEStronglyMeasurable (fun z : ℝ × Space =>
        ∑ i : Fin 3, (u z.1 z.2 i - v z.1 z.2 i) ^ 2)
        ((volume.restrict (Ioc (0 : ℝ) T')).prod volume) := by
      rw [hprod]
      exact hc.aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
    have hE : (volume : Measure ℝ).restrict (Ioc (0 : ℝ) T') =
        (volume : Measure ℝ).restrict (Icc (0 : ℝ) T') := by
      refine Measure.restrict_congr_set ?_
      exact Ioc_ae_eq_Icc' Real.volume_singleton
    rw [← hE]
    exact hm.integral_prod_right'
  set Bd : ℝ := max 0 (2 * (Eu + Ev))
  have hEB : ∀ r ∈ Icc (0 : ℝ) T', E r ≤ Bd := by
    intro r hr
    rcases eq_or_ne r 0 with rfl | hne
    · rw [hE0]
      exact le_max_left _ _
    · have h1 : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hne)
      have h2 : r < T := lt_of_le_of_lt hr.2 hT'T
      exact (Ediff_le_open hu hv h1 h2).trans (le_max_right _ _)
  have hEint : IntegrableOn E (Icc (0 : ℝ) T') := by
    refine (integrableOn_const (C := Bd) (s := Icc (0 : ℝ) T')
      (hs := measure_Icc_lt_top.ne)).mono' hEmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (Ediff_nonneg u v r)]
    exact hEB r hr
  -- the integral inequality
  have hle : ∀ s ∈ Icc (0 : ℝ) T', E s ≤ 6 * K * ∫ r in (0 : ℝ)..s, E r := by
    intro s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [hE0, intervalIntegral.integral_same, mul_zero]
    · have hss : s ∈ Ioc (0 : ℝ) T' := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
      obtain ⟨hJ, hid⟩ := energy_identity_open hν.le hu hv hT'T hss h0 hR
      have hJle : ∀ r ∈ Ioc (0 : ℝ) s, ∫ x, Fint u v (r, x) ≤ 6 * K * E r := by
        intro r hr
        have hrT : r ∈ Ioo (0 : ℝ) T := ⟨hr.1, lt_of_le_of_lt (hr.2.trans hs.2) hT'T⟩
        have hRr := hR r ⟨hr.1, hr.2.trans hs.2⟩
        have h := (time_slice_energy_open hν.le hu hv hrT.1 hrT.2 hRr.1 hRr.2).2
        have e : ∫ x, Fint u v (r, x) = ∫ x, ∑ i : Fin 3, 2 * (u r x i - v r x i) *
            (timeDerivative u r x i - timeDerivative v r x i) := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [Fint, timeDerivative_eq_tD_open hsu hrT, timeDerivative_eq_tD_open hsv hrT]
        rw [e]
        exact h
      have hEIoc : IntegrableOn E (Ioc (0 : ℝ) s) :=
        hEint.mono_set (fun r hr => ⟨hr.1.le, hr.2.trans hs.2⟩)
      have hmono : ∫ r in Ioc (0 : ℝ) s, ∫ x, Fint u v (r, x) ≤
          ∫ r in Ioc (0 : ℝ) s, 6 * K * E r :=
        setIntegral_mono_on hJ (hEIoc.const_mul _) measurableSet_Ioc hJle
      rw [integral_const_mul] at hmono
      have hE0u : Ediff u v 0 = 0 := hE0
      rw [hE0u, sub_zero] at hid
      show Ediff u v s ≤ _
      rw [hid, intervalIntegral.integral_of_le hs.1]
      exact hmono
  have hzero := gronwall_zero (by positivity) (fun r _ => Ediff_nonneg u v r) hEB hEint hle
    t ⟨ht0, htT'⟩
  -- conclude pointwise equality
  rcases eq_or_ne t 0 with rfl | htne
  · exact h0
  · have ht : t ∈ Ioo (0 : ℝ) T := ⟨lt_of_le_of_ne ht0 (Ne.symm htne), htT⟩
    have huc := (contDiff_slice_open hsu ht).continuous
    have hvc := (contDiff_slice_open hsv ht).continuous
    have hgc : Continuous (fun x => ∑ i : Fin 3, (u t x i - v t x i) ^ 2) :=
      continuous_finsetSum _ fun i _ =>
        (((continuous_apply i).comp huc).sub ((continuous_apply i).comp hvc)).pow 2
    have hgi := integrable_sum_sq_diff huc hvc (hu.fe t ht0 ht.2) (hv.fe t ht0 ht.2)
    have hae : (fun x => ∑ i : Fin 3, (u t x i - v t x i) ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) hgi).1
        hzero
    have hall : (fun x => ∑ i : Fin 3, (u t x i - v t x i) ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq volume hgc continuous_const).1 hae
    funext x i
    have hx := congrFun hall x
    simp only [Pi.zero_apply] at hx
    have hi : (u t x i - v t x i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hx i (Finset.mem_univ i)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hi
    linarith

/-! ## The restart-time consumer: hazard (b), discharged -/

/-- **Hazard (b) closed.**  Let `u` be an energy-class solution in `R` on `[0, T)` and let
`(vel, pres)` be an `OpenRestartDatum` of length `T - T₀` started at the slice `u T₀`.  Then `u`
and the piece agree on the whole OPEN overlap: `u t = vel (t - T₀)` for every `T₀ < t < T`.

This is ITEM6's `RestartAgreement` minus its own `RestartPiece` carrier.  The argument is the
midpoint cut of `RestartUniqueness.uniqueness_from`, with the two sides treated asymmetrically and
for a reason: the closed side `u` is shifted back to start at `0` (open-slab smoothness would not
survive a shift to `0`, but closed does), while the open side is kept unshifted — shifting the
piece to a strictly positive base is legitimate (`contDiffOn_shift_open`) yet useless, since
`uniqueness_class` would then require agreement at that base (see the module header).  The pressure
normalization `pres0` is not used; the velocity agreement is what
`H3RestartSlice.pressure_agree_of_piece` consumes. -/
theorem agreement_of_open_datum {ν T T₀ : ℝ} (hν : 0 < ν) (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T)
    {u : VelocityEvolution} {p : PressureEvolution} {vel : ℝ → VelocityField}
    {pres : ℝ → PressureField} (hsol : SolvesBefore ν T u p) (hRu : RegularOnCompacts T u p)
    (hp : OpenRestartDatum ν (T - T₀) (u T₀) vel pres) :
    ∀ t : ℝ, T₀ < t → t < T → u t = vel (t - T₀) := by
  intro t ht htT
  set M : ℝ := T - T₀ with hM
  have hM0 : 0 < M := sub_pos.mpr hT₀T
  have hu := SolClass.of_solvesBefore hsol
  have hEu : SmoothVelocityBefore T u := hu.smooth
  have hEp : SmoothPressureBefore T p := hu.psmooth
  -- horizon `S`: strictly between the target time and the piece's lifespan
  set S : ℝ := (t - T₀ + M) / 2 with hS
  have hS0 : 0 < S := by linarith
  have hsS : t - T₀ < S := by linarith
  have hSM : S < M := by linarith
  have hstS : t - T₀ ≤ S := by linarith
  obtain ⟨Ku, hKu⟩ := hRu (S + T₀) (by linarith)
  obtain ⟨K0, hK0⟩ := hp.rslice S hSM
  set K : ℝ := max Ku K0
  have hK : 0 ≤ K :=
    (norm_nonneg _).trans ((hK0 (S / 2) ⟨by linarith, by linarith⟩).2.2.2.1.1 0 |>.trans
      (le_max_right _ _))
  -- the closed side, shifted back to start at 0, is a genuine SolClass on [0, M)
  have huL : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2)
      (Ico T₀ (T₀ + M) ×ˢ (univ : Set Space)) :=
    strip_of_before hT₀ (by linarith) hEu
  have hpL : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2)
      (Ico T₀ (T₀ + M) ×ˢ (univ : Set Space)) :=
    strip_of_before hT₀ (by linarith) hEp
  have hushift : SolClass ν M (shiftE T₀ u) (shiftE T₀ p) (kineticEnergy u 0) :=
    solClass_shift hT₀ huL hpL
      (fun t ht htL y => hu.inc t (by linarith) (by linarith) y)
      (fun t ht htL y => hu.eqn t (by linarith) (by linarith) y)
      (fun t ht htM => hu.fe t (by linarith) (by linarith))
      (fun t ht htM => hu.ebd t (by linarith) (by linarith))
  have huo : OpenSolClass ν M (shiftE T₀ u) (shiftE T₀ p) (kineticEnergy u 0) :=
    OpenSolClass.of_solClass hM0 hushift
  have hvo : OpenSolClass ν M vel pres (kineticEnergy vel 0) := openSolClass_of_datum hp
  have hR : ∀ r ∈ Ioc (0 : ℝ) S,
      Rslice K (shiftE T₀ u) (shiftE T₀ p) r ∧ Rslice K vel pres r := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    refine ⟨rslice_shift hT₀ huL ⟨hr1, lt_of_le_of_lt hr2 hSM⟩
        (Rslice.mono (hKu (r + T₀) ⟨by linarith, by linarith⟩) (le_max_left _ _)),
      Rslice.mono (hK0 r ⟨hr1, hr2⟩) (le_max_right _ _)⟩
  have h0 : (shiftE T₀ u) 0 = vel 0 := by
    show u (0 + T₀) = vel 0
    rw [zero_add, hp.init]
  have hc := uniqueness_class_open hν huo hvo (by linarith) hK hR h0 (t - T₀)
    ⟨by linarith, hstS⟩
  have hc' : u (t - T₀ + T₀) = vel (t - T₀) := hc
  rw [sub_add_cancel] at hc'
  exact hc'

/-- **The diagnostic that makes the diagnosis precise.**  Open-slab smoothness DOES transport
through a shift by a strictly positive amount to the closed slab — so every single-time leg of the
engine is available at positive times, and `uniqueness_class` could be applied verbatim to a
shifted pair.  Recording it here names why that is not enough: `uniqueness_class` then asks
`shiftE a u 0 = shiftE a v 0`, i.e. agreement at the shifted base, which is the goal.  The residual
is therefore not a measurability or interior-regularity issue at all; it is the initial-time datum
`RightContinuousAtStart`. -/
theorem contDiffOn_shift_open {T a : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → Space → E} (ha : 0 < a) (_haT : a < T)
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)
      (Ioo (0 : ℝ) T ×ˢ (univ : Set Space))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => shiftE a v z.1 z.2)
      (Ico (0 : ℝ) (T - a) ×ˢ (univ : Set Space)) := by
  refine hv.comp (((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn) ?_
  intro s hs
  obtain ⟨hs1, hs2⟩ := hs.1
  change (0 < s.1 + a ∧ s.1 + a < T) ∧ True
  exact ⟨⟨by linarith, by linarith⟩, trivial⟩

end Navier.Analysis.RestartAgreementOpen

#print axioms Navier.Analysis.RestartAgreementOpen.agreement_of_open_datum
#print axioms Navier.Analysis.RestartAgreementOpen.uniqueness_class_open
#print axioms Navier.Analysis.RestartAgreementOpen.energy_identity_open
#print axioms Navier.Analysis.RestartAgreementOpen.time_slice_energy_open
#print axioms Navier.Analysis.RestartAgreementOpen.rightContinuousAtStart_of_closed
#print axioms Navier.Analysis.RestartAgreementOpen.contDiffOn_shift_open
