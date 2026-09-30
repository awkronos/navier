import Navier.Analysis.LinkedBoxX2Carrier

/-!
# The `hv` leg of the extended box is carrier-bound: the exhibit

`LinkedBoxX2Carrier.boxX2_sourceX2Budget_of_hv` (lane W31-N04) keeps exactly
one hypothetical leg: joint continuity `hv` of the gated field
`boxX2RawRepresentative`.  This module discharges the wave's question "prove
`hv`, falsify the route, or declare it carrier-bound" with a kernel-checked
exhibit for the CARRIER-BOUND verdict, at the granularity of the exact
obligation.

## The mechanism

`boxX2RawRepresentative ν T B1 B2 B3 b t ξ j` evaluates
`((slot t : Xm1Spatial) ξ : FourierCoordinateL1).ofLp j`, where `slot` is an
`L∞` (or `L¹`) time quotient and `Xm1Spatial` is an `L¹` frequency quotient.
Point evaluation of an `Lp` element is `MeasureTheory.Lp.instCoeFun`, which
coerces through `AEEqFun.cast` (Mathlib `AEEqFun.lean`):

* if the class has a constant representative, `Classical.choose` of that
  witness — a provably constant function, but the *value* of the chosen
  constant is pinned only when the measure is nonzero (`0 < T` below);
* otherwise `Quotient.out` — an opaque `AEStronglyMeasurable` member of the
  class with **no pointwise API at all** (Mathlib carries only a.e. facts
  like `MemLp.coeFn_toLp` / `AEEqFun.mk_eq_mk`).

`Navier/Analysis/ContinuousLeiLinCommonRepresentative.lean` says this of its
own representative: "No continuity is asserted for this representative."

## What is proved here

1. `boxX2Constant_boxX2GoodAt` — for `0 < ν` and `0 < T` the extended gate
   `BoxX2GoodAt` holds at EVERY time for the canonical nonzero supplier
   `boxX2Constant`, because all three slots have constant representatives and
   the `a.e.` transport lemmas `representativeGoodAt_ae`, `x2Raw_ae`,
   `x2TimeSlot_norm_ae` plus a positive-measure witness time give the
   pointwise transfer.
2. `boxX2Constant_hv_iff` — for that supplier `hv` is **equivalent** to the
   continuity of `constantChosenRepField u₀`, the `AEEqFun.cast`
   point-evaluation of the single class `[coordinateL1 (fourierDatum u₀)]`.
   The record determines the gated field only through this opaque choice:
   `hv` is not a radius datum `(B1, B2, B3)` nor a linkage datum, and no
   tactic applied to the record can decide it.  This is the carrier-bound
   classification of `research-mathematics.md` §3/§5, not a wrapper premise:
   the equivalence replaces `hv` by the exact choice-dependent obligation.
3. `boxX2Zero_hv` — a positive control: for the zero supplier the gated field
   is at every point the evaluation of a constant-represented class, hence
   literally a constant function, hence continuous, for `0 < T`.  (At `T ≤ 0`
   even this is not established by the record: the vanishing time measure
   lets `Classical.choose` pick ANY constant representative, and the gate
   itself becomes undecidable — the μ = 0 pathology the hypotheses `0 < T`,
   `0 < ν` of the transport lemmas exist to exclude.)

## The front-end change this names

To discharge `hv` the extended record must carry the representative, not the
class: add a field `contRep : ℝ → ES → ComplexSpace` to `ActualLinkedBoxX2`
together with the proof data that each coordinate `fun p => contRep p.2 p.1 j`
is continuous (a Schwartz/`ContRep`-style carrier whose smoothness lemmas
fire), and consume `contRep` instead of the `AEEqFun.cast` evaluation inside
`boxX2RawRepresentative`.  Then the `hv` leg becomes record data and
`boxX2_sourceX2Budget_of_hv` loses its only hypothesis.  A carrier-bound leaf
does not respond to tactic rungs (N05 measured polarity); the escalation is a
definition change (`pattern-discipline.md` Pattern A), and this module is the
scoped artifact that names it.

## Honest scope

* This module does NOT prove `hv` for any nonzero supplier, and does NOT
  refute `hv`: the exhibit shows both would be statements about
  `Quotient.out` choices outside the record's determined data.
* The whole-space global regularity crown stays OPEN; nothing here closes it.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinLinkedComplete
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinCommonRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeIntegrability
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.WholeSpaceRestartX2BudgetWiring
open Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
open Navier.Analysis.LinkedBoxX2Carrier
open scoped FourierTransform SchwartzMap
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
open Navier.Analysis.WholeSpaceRestartMildInterface
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum)

namespace Navier.Analysis.LinkedBoxX2HvIndependence

/-! ## Exponent facts for the spatial `L¹` slots -/

/-- Mathlib's `Lp.SecondCountableTopology` (`MeasureTheory/Measure/
SeparableMeasure.lean`) carries the file-level binders `Fact (1 ≤ p)` and
`Fact (p ≠ ∞)` (lines 54–55, 76); at the exponent `p = 1` of every spatial
slot these are the missing instances that block
`SecondCountableTopology Xm1Spatial`, `SecondCountableTopology
(ViscousX1Spatial ν)`, and `SecondCountableTopology X2Spatial`.  The measure
side is Mathlib-automatic: `CountablyGenerated ES`,
`Measure.withDensity.instSFinite`, hence `IsSeparable` at
`SeparableMeasure.lean:382`, and `SeparableSpace` / `SecondCountableTopology`
on the `PiLp` fibre (probe `scr_sct3.lean`, MacBook, 2026-09-30). -/
local instance spatialExponentNeTop : Fact ((1 : ENNReal) ≠ ∞) := ⟨by simp⟩

local instance spatialExponentOneLe : Fact ((1 : ENNReal) ≤ 1) := ⟨le_refl 1⟩

/-- The three frequency measures are `def`s, opaque to instance unification:
the `IsSeparable` chain (`Measure.withDensity.instSFinite`, hence
`SeparableMeasure.lean:382`) only fires on the unfolded
`volume.withDensity` shape (probes `scr_sct2`/`scr_sct3`, MacBook,
2026-09-30), so each is supplied once here in the opaque spelling. -/
local instance xm1Slot_isSeparable : IsSeparable xm1FrequencyMeasure :=
  inferInstanceAs (IsSeparable (Measure.withDensity volume xm1Density))

local instance viscousX1Slot_isSeparable (ν : ℝ≥0) :
    IsSeparable (viscousX1FrequencyMeasure ν) :=
  inferInstanceAs (IsSeparable (Measure.withDensity volume (viscousX1Density ν)))

local instance x2Slot_isSeparable : IsSeparable x2FrequencyMeasure :=
  inferInstanceAs (IsSeparable (Measure.withDensity volume x2Density))

/-! ## Pointwise behaviour of `Lp` evaluation -/

/-- A finite-horizon time measure with positive horizon is not the zero
measure: `volume (Icc 0 T) = ENNReal.ofReal T ≠ 0`. -/
theorem leiLinTimeMeasure_ne_zero (T : ℝ) (hT : 0 < T) :
    leiLinTimeMeasure T ≠ 0 := by
  intro h
  have hu : (leiLinTimeMeasure T) (Set.univ : Set ℝ) = 0 := by
    rw [h]; simp
  have h2 : (leiLinTimeMeasure T) Set.univ = volume (Icc (0 : ℝ) T) := by
    simp [leiLinTimeMeasure, Measure.restrict_apply, isClosed_Icc.measurableSet]
  rw [h2, Real.volume_Icc, sub_zero] at hu
  rw [ENNReal.ofReal_eq_zero] at hu
  linarith

/-- A full-measure condition over a nonzero measure has a witness point. -/
theorem exists_of_ae {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : Measure α} (h : ∀ᵐ x ∂μ, p x) (hμ : μ ≠ 0) : ∃ x, p x := by
  by_contra hne
  push_neg at hne
  have h0 : μ Set.univ = 0 := by
    have hm2 := MeasureTheory.ae_iff.mp h
    rwa [Set.eq_univ_of_forall hne] at hm2
  exact hμ (Measure.measure_univ_eq_zero.mp h0)

/-- The point evaluation of an `Lp` class with a constant representative is
`AEEqFun.cast`-constant, and with a nonzero measure its value is the supplied
constant.  This is the whole pointwise API that quotient evaluation provides;
for a class without a constant representative `cast` is `Quotient.out` data
and Mathlib has NO pointwise lemma — the carrier boundary. -/
theorem eval_toLp_const {E α : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [SecondCountableTopology E]
    {p : ℝ≥0∞} {μ : Measure α} {c : E} (f : α → E) (hf : f = fun _ => c)
    (hm : MemLp f p μ) (hμ : μ ≠ 0) (a : α) :
    ((MemLp.toLp f hm : Lp E p μ) a) = c := by
  subst hf
  classical
  have hex : ∃ b : E,
      (AEEqFun.mk (fun _ : α => c) hm.1 : α →ₘ[μ] E) =
        AEEqFun.mk (const α b) aestronglyMeasurable_const :=
    ⟨c, AEEqFun.mk_eq_mk.mpr (ae_of_all _ fun _ => rfl)⟩
  have hchoose : Classical.choose hex = c := by
    by_contra hne
    have hae := AEEqFun.mk_eq_mk.mp (Classical.choose_spec hex)
    have hset : {x : α | ¬ ((fun _ : α => c) x =
        (const α (Classical.choose hex)) x)} = Set.univ :=
      Set.eq_univ_of_forall (fun _ hc => hne hc.symm)
    have h0 : μ Set.univ = 0 := by
      have hm2 := MeasureTheory.ae_iff.mp hae
      rwa [hset] at hm2
    exact hμ (Measure.measure_univ_eq_zero.mp h0)
  show (AEEqFun.cast (AEEqFun.mk (fun _ : α => c) hm.1) : α → E) a = c
  simp only [AEEqFun.cast]
  rw [dif_pos hex]
  simpa using hchoose

/-- The zero class evaluates to the zero value at every point of a nonzero
measure.  At measure zero the chosen constant is unpinned, which is why the
`0 < T` hypothesis travels with every supplier statement below. -/
theorem Lp_eval_zero {E α : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [SecondCountableTopology E]
    {p : ℝ≥0∞} {μ : Measure α} (a : α) (hμ : μ ≠ 0) :
    ((0 : Lp E p μ) a) = 0 := by
  classical
  have hex : ∃ b : E, (0 : α →ₘ[μ] E) =
      AEEqFun.mk (const α b) aestronglyMeasurable_const := ⟨0, rfl⟩
  have hchoose : Classical.choose hex = 0 := by
    by_contra hne
    have hzero_mk : (0 : α →ₘ[μ] E) =
        AEEqFun.mk (fun _ : α => (0 : E)) aestronglyMeasurable_const := rfl
    have hae := AEEqFun.mk_eq_mk.mp
        (hzero_mk.symm.trans (Classical.choose_spec hex))
    have hset : {x : α | ¬ ((fun _ : α => (0 : E)) x =
        (const α (Classical.choose hex)) x)} = Set.univ :=
      Set.eq_univ_of_forall (fun _ hc => hne hc.symm)
    have h0 : μ Set.univ = 0 := by
      have hm2 := MeasureTheory.ae_iff.mp hae
      rwa [hset] at hm2
    exact hμ (Measure.measure_univ_eq_zero.mp h0)
  show (AEEqFun.cast (0 : α →ₘ[μ] E) : α → E) a = 0
  simp only [AEEqFun.cast]
  rw [dif_pos hex]
  simpa using hchoose

/-! ## The constant supplier -/

/-- The chosen spatial representative of the time-constant Fourier datum:
the point evaluation of the `L¹(‖ξ‖⁻¹ dξ)` class `[coordinateL1
(fourierDatum u₀)]` built by `toXm1Spatial`.  Its values are `AEEqFun.cast`
data (the `Quotient.out` branch for a non-constant class): nothing in the
box record constrains them. -/
noncomputable def constantChosenRepField (u₀ : SchwartzVelocity) :
    ES → ComplexSpace :=
  fun ξ => ((toXm1Spatial (fourierDatum u₀)
    (fun i => fourierDatum_aestronglyMeasurable u₀ i)
    (fun i => fourierDatum_integrable_Xm1 u₀ i)) ξ : FourierCoordinateL1).ofLp

/-- The `X⁻¹` time slot of the constant supplier evaluated at any time: the
`L∞` quotient has the constant representative `toXm1Spatial (fourierDatum
u₀) …`, so its point value is that class (pinning the chosen constant needs
`0 < T`). -/
theorem boxX2Constant_xm1Slot_eval (ν : ℝ≥0) (T : ℝ) (hT : 0 < T)
    (u₀ : SchwartzVelocity) (t : ℝ) :
    (((boxX2Constant ν T u₀).1.1.1.1.fst : Xm1TimeSlot T) t : Xm1Spatial) =
      toXm1Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_Xm1 u₀ i) := by
  classical
  have hsec :
      (xm1Section (fun _ => fourierDatum u₀)
        (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun t i => fourierDatum_integrable_Xm1 u₀ i)) =
      (fun _ : ℝ => toXm1Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_Xm1 u₀ i)) := by
    funext t
    rfl
  change ((toXm1TimeSlot (fun _ => fourierDatum u₀)
        (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun t i => fourierDatum_integrable_Xm1 u₀ i) T
        (coordinateXm1Mass (fourierDatum u₀))
        (by
          have hsec' :
              (xm1Section (fun _ => fourierDatum u₀)
                (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
                (fun t i => fourierDatum_integrable_Xm1 u₀ i)) =
              (fun _ : ℝ => toXm1Spatial (fourierDatum u₀)
                (fun i => fourierDatum_aestronglyMeasurable u₀ i)
                (fun i => fourierDatum_integrable_Xm1 u₀ i)) := by
            funext t
            rfl
          rw [hsec']
          exact aestronglyMeasurable_const)
        (fun t _ => le_refl _) : Xm1TimeSlot T) t : Xm1Spatial) = _
  simp only [toXm1TimeSlot]
  exact eval_toLp_const _ hsec _ (leiLinTimeMeasure_ne_zero T hT) t

/-- The viscous `X¹` time slot of the constant supplier evaluated at any
time. -/
theorem boxX2Constant_viscousSlot_eval (ν : ℝ≥0) (T : ℝ) (hT : 0 < T)
    (u₀ : SchwartzVelocity) (t : ℝ) :
    (((boxX2Constant ν T u₀).1.1.1.1.snd : ViscousX1TimeSlot ν T) t
      : ViscousX1Spatial ν) =
      toViscousX1Spatial ν (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_X1 u₀ i) := by
  classical
  have hsec :
      (viscousX1Section (fun _ => fourierDatum u₀)
        (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun t i => fourierDatum_integrable_X1 u₀ i) ν) =
      (fun _ : ℝ => toViscousX1Spatial ν (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_X1 u₀ i)) := by
    funext t
    rfl
  change ((toViscousX1TimeSlot (fun _ => fourierDatum u₀)
        (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun t i => fourierDatum_integrable_X1 u₀ i) ν T
        (by
          have hsec' :
              (viscousX1Section (fun _ => fourierDatum u₀)
                (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
                (fun t i => fourierDatum_integrable_X1 u₀ i) ν) =
              (fun _ : ℝ => toViscousX1Spatial ν (fourierDatum u₀)
                (fun i => fourierDatum_aestronglyMeasurable u₀ i)
                (fun i => fourierDatum_integrable_X1 u₀ i)) := by
            funext t
            rfl
          rw [hsec']
          exact aestronglyMeasurable_const)
        (by
          show Integrable (fun _ : ℝ => coordinateX1Mass (fourierDatum u₀))
            (leiLinTimeMeasure T)
          exact integrableOn_const measure_Icc_lt_top.ne)
      : ViscousX1TimeSlot ν T) t : ViscousX1Spatial ν) = _
  simp only [toViscousX1TimeSlot]
  exact eval_toLp_const _ hsec _ (leiLinTimeMeasure_ne_zero T hT) t

/-- The new `X²` time slot of the constant supplier evaluated at any time. -/
theorem boxX2Constant_x2Slot_eval (ν : ℝ≥0) (T : ℝ) (hT : 0 < T)
    (u₀ : SchwartzVelocity) (t : ℝ) :
    (((boxX2Constant ν T u₀).1.2 : X2TimeSlot T) t : X2Spatial) =
      toX2Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (constRawX2_coordInt u₀ 0) := by
  classical
  have hsec :
      (x2Section (fun _ => fourierDatum u₀)
        (fun t i => fourierDatum_aestronglyMeasurable u₀ i)
        (constRawX2_coordInt u₀)) =
      (fun _ : ℝ => toX2Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (constRawX2_coordInt u₀ 0)) := by
    funext t
    rfl
  change ((constRawX2 T u₀ : X2TimeSlot T) t : X2Spatial) = _
  simp only [constRawX2, toX2TimeSlot]
  exact eval_toLp_const _ hsec _ (leiLinTimeMeasure_ne_zero T hT) t

/-- For `0 < ν` and `0 < T` the extended gate `BoxX2GoodAt` holds at EVERY
time for the constant supplier.  Each gate conjunct transfers from its
existing almost-everywhere lemma through a positive-measure witness time,
because all three slot evaluations are time-independent. -/
theorem boxX2Constant_boxX2GoodAt (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : SchwartzVelocity) (t : ℝ) :
    BoxX2GoodAt ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖ ‖constRawX2 T u₀‖
      (boxX2Constant ν T u₀) t := by
  classical
  set b := boxX2Constant ν T u₀ with hb
  have hμne : leiLinTimeMeasure T ≠ 0 := leiLinTimeMeasure_ne_zero T hT
  have hxmSlot : ∀ s : ℝ,
      ((b.1.1.1.1.fst : Xm1TimeSlot T) s : Xm1Spatial) =
        toXm1Spatial (fourierDatum u₀)
          (fun i => fourierDatum_aestronglyMeasurable u₀ i)
          (fun i => fourierDatum_integrable_Xm1 u₀ i) :=
    fun s => boxX2Constant_xm1Slot_eval ν T hT u₀ s
  have hvSlot : ∀ s : ℝ,
      ((b.1.1.1.1.snd : ViscousX1TimeSlot ν T) s : ViscousX1Spatial ν) =
        toViscousX1Spatial ν (fourierDatum u₀)
          (fun i => fourierDatum_aestronglyMeasurable u₀ i)
          (fun i => fourierDatum_integrable_X1 u₀ i) :=
    fun s => boxX2Constant_viscousSlot_eval ν T hT u₀ s
  have hx2Slot : ∀ s : ℝ,
      ((b.1.2 : X2TimeSlot T) s : X2Spatial) =
        toX2Spatial (fourierDatum u₀)
          (fun i => fourierDatum_aestronglyMeasurable u₀ i)
          (constRawX2_coordInt u₀ 0) :=
    fun s => boxX2Constant_x2Slot_eval ν T hT u₀ s
  have hxmRaw : ∀ s : ℝ, xm1RawRepresentative ν T b.1.1 s =
      fun ξ : ES => ((toXm1Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_Xm1 u₀ i)) ξ :
        FourierCoordinateL1).ofLp := by
    intro s
    funext ξ
    show (((b.1.1.1.1.fst : Xm1TimeSlot T) s : Xm1Spatial) ξ :
        FourierCoordinateL1).ofLp = _
    rw [hxmSlot s]
  have hvRaw : ∀ s : ℝ, viscousX1RawRepresentative ν T b.1.1 s =
      fun ξ : ES => ((toViscousX1Spatial ν (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_X1 u₀ i)) ξ :
        FourierCoordinateL1).ofLp := by
    intro s
    funext ξ
    show (((b.1.1.1.1.snd : ViscousX1TimeSlot ν T) s : ViscousX1Spatial ν) ξ :
        FourierCoordinateL1).ofLp = _
    rw [hvSlot s]
  have hx2Raw : ∀ s : ℝ, (fun ξ : ES => ((b.1.2 s : X2Spatial) ξ :
        FourierCoordinateL1).ofLp) =
      fun ξ : ES => ((toX2Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (constRawX2_coordInt u₀ 0)) ξ : FourierCoordinateL1).ofLp := by
    intro s
    funext ξ
    rw [hx2Slot s]
  obtain ⟨t₀, ht₀⟩ :=
    exists_of_ae (representativeGoodAt_ae ν hν T b.1.1) hμne
  have c1 : RepresentativeGoodAt ν T b.1.1 t := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hxmRaw t, hvRaw t]
      have h0 := ht₀.1
      rw [hxmRaw t₀, hvRaw t₀] at h0
      exact h0
    · rw [hxmRaw t]
      have h1 := ht₀.2.1
      rw [hxmRaw t₀] at h1
      exact h1
    · have h2 := ht₀.2.2
      rw [hxmSlot t]
      rw [hxmSlot t₀] at h2
      exact h2
  obtain ⟨t₁, ht₁⟩ :=
    exists_of_ae (x2Raw_ae ν hν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
      ‖constRawX2 T u₀‖ b) hμne
  have c2 : xm1RawRepresentative ν T b.1.1 t =ᵐ[volume]
      fun ξ : ES => ((b.1.2 t : X2Spatial) ξ : FourierCoordinateL1).ofLp := by
    rw [hxmRaw t, hx2Raw t]
    have h0 := ht₁
    rw [hxmRaw t₁, hx2Raw t₁] at h0
    exact h0
  obtain ⟨t₂, ht₂⟩ :=
    exists_of_ae (x2TimeSlot_norm_ae ν T ‖constRawXm T u₀‖
      ‖constRawX1 ν T u₀‖ ‖constRawX2 T u₀‖ b) hμne
  have c3 : ‖(b.1.2 : X2TimeSlot T) t‖ ≤ ‖(b.1.2 : X2TimeSlot T)‖ := by
    rw [hx2Slot t]
    have h0 := ht₂
    rw [hx2Slot t₂] at h0
    exact h0
  exact ⟨c1, c2, c3⟩

/-- The gated field of the constant supplier IS the chosen representative at
every spacetime point (needs `0 < ν` for the gate, `0 < T` to pin the slot
constants). -/
theorem boxX2Constant_field_eq_chosen (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (hT : 0 < T) (u₀ : SchwartzVelocity) (t : ℝ) (ξ : ES) :
    boxX2RawRepresentative ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
      ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀) t ξ =
      constantChosenRepField u₀ ξ := by
  classical
  have hg := boxX2Constant_boxX2GoodAt ν hν T hT u₀ t
  rw [boxX2RawRepresentative_at_good ν T _ _ _ (boxX2Constant ν T u₀) t hg]
  show (((((boxX2Constant ν T u₀).1.1.1.1.fst : Xm1TimeSlot T) t :
      Xm1Spatial) ξ : FourierCoordinateL1).ofLp = _)
  rw [boxX2Constant_xm1Slot_eval ν T hT u₀ t]
  rfl

/-- **The carrier-bound exhibit.**  For the canonical nonzero supplier the
joint-continuity hypothesis `hv` of `boxX2_sourceX2Budget_of_hv` is
equivalent to the continuity of the `AEEqFun.cast`-chosen spatial
representative `constantChosenRepField`.  `hv` is therefore a property of
`Quotient.out` choice data, not of the radii `(B1, B2, B3)` or the linkage;
no tactic applied to the record can decide it, and the route is
carrier-bound.  The record change that would discharge it: an explicit
continuous representative field consumed by the gate instead of the class
evaluation (see the module docstring). -/
theorem boxX2Constant_hv_iff (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : SchwartzVelocity) :
    (∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        boxX2RawRepresentative ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
          ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀) p.2 p.1 j)) ↔
    (∀ j : Fin 3, Continuous (fun ξ => constantChosenRepField u₀ ξ j)) := by
  classical
  set g := fun j => (fun p : ES × ℝ =>
      boxX2RawRepresentative ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
        ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀) p.2 p.1 j)
  set h := fun j => (fun p : ES × ℝ => constantChosenRepField u₀ p.1 j)
  have heq : ∀ j : Fin 3, g j = h j := by
    intro j
    funext p
    show boxX2RawRepresentative ν T _ _ _ (boxX2Constant ν T u₀) p.2 p.1 j = _
    rw [boxX2Constant_field_eq_chosen ν hν T hT u₀ p.2 p.1]
  constructor
  · intro hv j
    have hstep : (fun ξ : ES => constantChosenRepField u₀ ξ j) =
        g j ∘ (fun ξ => (ξ, (0 : ℝ))) := by
      show h j ∘ (fun ξ => (ξ, (0 : ℝ))) = g j ∘ (fun ξ => (ξ, (0 : ℝ)))
      rw [heq j]
    rw [hstep]
    exact (hv j).comp (continuous_id.prodMk continuous_const)
  · intro hc j
    show Continuous (g j)
    have hstep : h j = (fun ξ : ES => constantChosenRepField u₀ ξ j) ∘
        (fun p : ES × ℝ => (p : ES × ℝ).1) := by
      funext p
      rfl
    rw [heq j, hstep]
    exact (hc j).comp continuous_fst

/-- The exhibit's consumer-side corollary: a continuous chosen
representative for the Fourier datum would feed the extended record through
`hv`.  This is the shape the front-end change must make record data. -/
theorem boxX2Constant_sourceL1X1_of_chosenCont (ν : ℝ≥0) (hν : 0 < ν)
    (T : ℝ) (hT : 0 < T) (u₀ : SchwartzVelocity)
    (hcont : ∀ j : Fin 3, Continuous (fun ξ => constantChosenRepField u₀ ξ j)) :
    SourceL1X1 T (boxX2RawRepresentative ν T ‖constRawXm T u₀‖
      ‖constRawX1 ν T u₀‖ ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀)) :=
  boxX2_sourceL1X1_of_hv ν hν T _ _ _ (boxX2Constant ν T u₀)
    ((boxX2Constant_hv_iff ν hν T hT u₀).mpr hcont)

/-! ## The zero supplier: positive control -/

/-- The zero `X⁻¹` slot evaluated at any time. -/
theorem boxX2Zero_xm1Slot_eval (ν : ℝ≥0) (T : ℝ) (hT : 0 < T) (t : ℝ) :
    (((boxX2Zero ν T).1.1.1.1.fst : Xm1TimeSlot T) t : Xm1Spatial) =
      (0 : Xm1Spatial) :=
  Lp_eval_zero t (leiLinTimeMeasure_ne_zero T hT)

/-- The zero viscous `X¹` slot evaluated at any time. -/
theorem boxX2Zero_viscousSlot_eval (ν : ℝ≥0) (T : ℝ) (hT : 0 < T) (t : ℝ) :
    (((boxX2Zero ν T).1.1.1.1.snd : ViscousX1TimeSlot ν T) t
      : ViscousX1Spatial ν) = (0 : ViscousX1Spatial ν) :=
  Lp_eval_zero t (leiLinTimeMeasure_ne_zero T hT)

/-- The zero `X²` slot evaluated at any time. -/
theorem boxX2Zero_x2Slot_eval (ν : ℝ≥0) (T : ℝ) (hT : 0 < T) (t : ℝ) :
    (((boxX2Zero ν T).1.2 : X2TimeSlot T) t : X2Spatial) = (0 : X2Spatial) :=
  Lp_eval_zero t (leiLinTimeMeasure_ne_zero T hT)

/-- The raw fields of the zero supplier: every time section is the point
evaluation of a zero spatial class. -/
theorem boxX2Zero_field_eqs (ν : ℝ≥0) (T : ℝ) (hT : 0 < T) :
    (∀ s : ℝ, xm1RawRepresentative ν T (boxX2Zero ν T).1.1 s =
        fun ξ : ES => ((0 : Xm1Spatial) ξ : FourierCoordinateL1).ofLp) ∧
    (∀ s : ℝ, viscousX1RawRepresentative ν T (boxX2Zero ν T).1.1 s =
        fun ξ : ES => ((0 : ViscousX1Spatial ν) ξ
          : FourierCoordinateL1).ofLp) ∧
    (∀ s : ℝ, (fun ξ : ES => (((boxX2Zero ν T).1.2 s : X2Spatial) ξ :
        FourierCoordinateL1).ofLp) =
        fun ξ : ES => ((0 : X2Spatial) ξ : FourierCoordinateL1).ofLp) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s
    funext ξ
    show (((((boxX2Zero ν T).1.1.1.1.fst : Xm1TimeSlot T) s :
        Xm1Spatial) ξ : FourierCoordinateL1).ofLp = _)
    rw [boxX2Zero_xm1Slot_eval ν T hT s]
  · intro s
    funext ξ
    show (((((boxX2Zero ν T).1.1.1.1.snd : ViscousX1TimeSlot ν T) s :
        ViscousX1Spatial ν) ξ : FourierCoordinateL1).ofLp = _)
    rw [boxX2Zero_viscousSlot_eval ν T hT s]
  · intro s
    funext ξ
    rw [boxX2Zero_x2Slot_eval ν T hT s]

/-- For `0 < ν` and `0 < T` the extended gate `BoxX2GoodAt` holds at EVERY
time for the zero supplier; each conjunct transfers through a
positive-measure witness time because all three slot evaluations are the
zero class at every time. -/
theorem boxX2Zero_boxX2GoodAt (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (t : ℝ) :
    BoxX2GoodAt ν T 0 0 0 (boxX2Zero ν T) t := by
  classical
  obtain ⟨hxm, hvsc, hx2⟩ := boxX2Zero_field_eqs ν T hT
  have hμne : leiLinTimeMeasure T ≠ 0 := leiLinTimeMeasure_ne_zero T hT
  obtain ⟨t₀, ht₀⟩ :=
    exists_of_ae (representativeGoodAt_ae ν hν T (boxX2Zero ν T).1.1) hμne
  have c1 : RepresentativeGoodAt ν T (boxX2Zero ν T).1.1 t := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hxm t, hvsc t]
      have h0 := ht₀.1
      rw [hxm t₀, hvsc t₀] at h0
      exact h0
    · rw [hxm t]
      have h1 := ht₀.2.1
      rw [hxm t₀] at h1
      exact h1
    · have h2 := ht₀.2.2
      rw [boxX2Zero_xm1Slot_eval ν T hT t]
      rw [boxX2Zero_xm1Slot_eval ν T hT t₀] at h2
      exact h2
  obtain ⟨t₁, ht₁⟩ :=
    exists_of_ae (x2Raw_ae ν hν T 0 0 0 (boxX2Zero ν T)) hμne
  have c2 : xm1RawRepresentative ν T (boxX2Zero ν T).1.1 t =ᵐ[volume]
      fun ξ : ES => (((boxX2Zero ν T).1.2 t : X2Spatial) ξ :
        FourierCoordinateL1).ofLp := by
    rw [hxm t, hx2 t]
    have h0 := ht₁
    rw [hxm t₁, hx2 t₁] at h0
    exact h0
  obtain ⟨t₂, ht₂⟩ :=
    exists_of_ae (x2TimeSlot_norm_ae ν T 0 0 0 (boxX2Zero ν T)) hμne
  have c3 : ‖((boxX2Zero ν T).1.2 : X2TimeSlot T) t‖ ≤
      ‖((boxX2Zero ν T).1.2 : X2TimeSlot T)‖ := by
    rw [boxX2Zero_x2Slot_eval ν T hT t]
    have h0 := ht₂
    rw [boxX2Zero_x2Slot_eval ν T hT t₂] at h0
    exact h0
  exact ⟨c1, c2, c3⟩

/-- **Positive control.**  For the zero supplier the gated field is a
constant function at every time (the point evaluation of a zero class is the
value pinned by `0 < T`, and the chosen value of the zero spatial class
enters only as one fixed constant), so `hv` HOLDS.  This is exactly the
record-determined half: when the class has a constant representative the
gated field is continuous.  For the constant supplier the same reduction
lands on `constantChosenRepField`, whose continuity is choice data (see
`boxX2Constant_hv_iff`) — the carrier boundary. -/
theorem boxX2Zero_hv (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    ∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        boxX2RawRepresentative ν T 0 0 0 (boxX2Zero ν T) p.2 p.1 j) := by
  classical
  obtain ⟨hxm, _, _⟩ := boxX2Zero_field_eqs ν T hT
  have hg : ∀ s : ℝ,
      BoxX2GoodAt ν T 0 0 0 (boxX2Zero ν T) s :=
    fun s => boxX2Zero_boxX2GoodAt ν hν T hT s
  have hex : ∃ b : FourierCoordinateL1,
      (0 : ES →ₘ[xm1FrequencyMeasure] FourierCoordinateL1) =
        AEEqFun.mk (const ES b) aestronglyMeasurable_const := ⟨0, rfl⟩
  have hconst : (fun ξ : ES => ((0 : Xm1Spatial) ξ : FourierCoordinateL1)) =
      fun _ : ES => Classical.choose hex := by
    funext ξ
    show (AEEqFun.cast (0 : ES →ₘ[xm1FrequencyMeasure] FourierCoordinateL1)) ξ =
      Classical.choose hex
    simp only [AEEqFun.cast]
    rw [dif_pos hex]
    rfl
  intro j
  have hf : (fun p : ES × ℝ =>
      boxX2RawRepresentative ν T (0 : ℝ) (0 : ℝ) (0 : ℝ) (boxX2Zero ν T)
        p.2 p.1 j) =
      fun _ : ES × ℝ => (Classical.choose hex : FourierCoordinateL1).ofLp j := by
    funext p
    show boxX2RawRepresentative ν T 0 0 0 (boxX2Zero ν T) p.2 p.1 j = _
    rw [boxX2RawRepresentative_at_good ν T 0 0 0 (boxX2Zero ν T) p.2
      (hg p.2), hxm p.2]
    show (((0 : Xm1Spatial) p.1 : FourierCoordinateL1).ofLp j) = _
    rw [congrFun hconst p.1]
  rw [hf]
  exact continuous_const

/-- The zero supplier satisfies the whole `SourceX2Budget` consumer
hypothesis set, so the extended record's budget theorem fires
hypothesis-free on it: the only hypothetical leg `hv` holds there by the
positive control. -/
theorem boxX2Zero_sourceL1X1 (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    SourceL1X1 T (boxX2RawRepresentative ν T 0 0 0 (boxX2Zero ν T)) :=
  boxX2_sourceL1X1_of_hv ν hν T 0 0 0 (boxX2Zero ν T)
    (boxX2Zero_hv ν hν T hT)

#print axioms leiLinTimeMeasure_ne_zero
#print axioms exists_of_ae
#print axioms eval_toLp_const
#print axioms Lp_eval_zero
#print axioms constantChosenRepField
#print axioms boxX2Constant_xm1Slot_eval
#print axioms boxX2Constant_viscousSlot_eval
#print axioms boxX2Constant_x2Slot_eval
#print axioms boxX2Constant_boxX2GoodAt
#print axioms boxX2Constant_field_eq_chosen
#print axioms boxX2Constant_hv_iff
#print axioms boxX2Constant_sourceL1X1_of_chosenCont
#print axioms boxX2Zero_xm1Slot_eval
#print axioms boxX2Zero_viscousSlot_eval
#print axioms boxX2Zero_x2Slot_eval
#print axioms boxX2Zero_field_eqs
#print axioms boxX2Zero_boxX2GoodAt
#print axioms boxX2Zero_hv
#print axioms boxX2Zero_sourceL1X1

end Navier.Analysis.LinkedBoxX2HvIndependence
