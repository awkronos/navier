import Navier.Analysis.ContinuousLeiLinSourceX1MomentBound
import Navier.Analysis.WholeSpaceRestartMildInterface
import Navier.Analysis.ContinuousLeiLinEverywhereRepresentative

/-!
# Wiring the `X⁰·X²` source budget into the whole-space restart records

`ContinuousLeiLinSourceX1MomentBound.sourceL1X1_of_continuous_uniformX0_integrableX2`
supplies the named strengthened input `SourceL1X1` of the mild assembly leaves
from five velocity-side legs: joint continuity `hv`, per-time `X⁰`
integrability `hv0`, per-time `X²` integrability `hv2`, a uniform `X⁰` mass
bound `hbdd`, and time-integrated `X²` moment `hX2`.
`WholeSpaceRestartMildInterface` leaves the exact restart premise
`H : ∀ x : ActualLinkedBox ν T (2R) (2R),
      SourceL1X1 T (everywhereRawRepresentative ν T x.1)`
un discharged — `WholeSpaceCarrierReconstruction` records it as obligation 1.
This module performs the leg-by-leg audit against what a linked-box record
actually carries and wires the budget through to the two restart consumers.

## Leg audit for `v := everywhereRawRepresentative ν T x.1`

The record of `x : ActualLinkedBox ν T B1 B2` is exactly
`‖(x.1.fst : Xm1TimeSlot T)‖ ≤ B1` and
`‖(x.1.snd : ViscousX1TimeSlot ν T)‖ ≤ B2`
(`linkedAdmissibleBoxSet`), transported through the null-set repair of
`ContinuousLeiLinEverywhereRepresentative`.

* `hv0` (per-time `X⁰` integrability): **supplied by the box.**  Every time
  section has the `X⁻¹` and `X¹` coordinate integrabilities
  (`everywhereRawRepresentative_xm1_integrable`,
  `everywhereRawRepresentative_x1_integrable`), and pointwise away from the
  single frequency `η = 0` the unweighted norm is dominated by the sum of the
  two weighted norms: `‖f‖ ≤ ‖η‖⁻¹‖f‖` on `‖η‖ ≤ 1`, `‖f‖ ≤ ‖η‖‖f‖` on
  `1 < ‖η‖`.  Closed as `box_sourceX0_integrable`.
* `hv` (joint continuity of `ξ, t`): **not supplied.**  A box element is an
  `Lp` quotient class with an arbitrary pointwise repair at exceptional
  times; the file constructing the repair states
  "No continuous representative or closedness of continuous representatives
  is assumed."  It is carried as a named budget leg.
* `hbdd` (uniform `X⁰` mass on `[0, T]`): **not supplied.**  The audit
  identity `coordinateMomentMass 0 (v s) ≤ coordinateXm1Mass (v s) +
  coordinateX1Mass (v s)` bounds `X⁰` by the uniform slot bound only up to
  the pointwise `X¹` mass, and the `X¹` slot is `L¹` in time, not `L∞`:
  an `L¹_t` function need not be essentially bounded.  Carried as a leg.
* `hv2`, `hX2` (per-time and time-integrated `X²`): **not supplied.**  The
  box budgets are `L∞_t X⁻¹ ∩ L¹_t X¹`; degree 2 exceeds both weights, and
  the record's own time-integrability theorem
  (`coordinateX1Mass_everywhereRawRepresentative_integrable`) stops at
  degree 1.  This is the exact NS1 residual-1 carrier, stated below as
  `SourceX2Budget`'s fourth leg.

The conditional closure is `sourceL1X1_of_box_sourceX2Budget`: from the
four-leg record `SourceX2Budget` plus box membership, the fifth leg
`hv0` is discharged from the box and the provider yields `SourceL1X1`.
`restartSourceL1X1_of_boxBudget` lifts it to the `H`-shape of
`WholeSpaceRestartMildInterface`, and the two assembly consumers
(`fourierDatumAssemblyLeaves`,
`existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1`) are re-stated over
the budget.  These conditional wires verify the routing; they do not claim
any box satisfies the budget.

## Exact remaining carrier (RESIDUAL, not assumed anywhere here)

For some horizon `T` and box radius `R`, no theorem in this repository
derives from `x : ActualLinkedBox ν T (2R) (2R)` alone the type

    Integrable (fun s => coordinateMomentMass 2
      (everywhereRawRepresentative ν T x.1 s))
      (volume.restrict (Icc (0 : ℝ) T))

together with the joint-continuity and uniform-`X⁰` legs.  This is the
`X⁰·X²` allocation gap, the nonlinear sibling of the `s^{−1/2}` wall
recorded in `ContinuousLeiLinMildAssemblyLeaves`.

## Provider-scope audit (grails `Warp/HeatCarrierRegularity`)

The named provider constructs Schwartz membership of Gaussian-multiplier
slices (`heatGaussianHasTemperateGrowth`, `freeHeatCoordSchwartz`), i.e.
per-time all-moment regularity of the **free heat** carrier
`freeHeatTraj ν u₀ = fun t => heatVec ν t (fourierDatum u₀)`.  That scope is
exactly insufficient for the budget's global-in-time legs: at `s < 0` the
multiplier `exp(+ν|s|‖η‖²)` beats every Schwartz seminorm, so
`∀ s j, Integrable (fun η => ‖v s η j‖)` fails for the unclamped heat flow
and no box representative is a heat flow (a fixed-point representative
carries the Duhamel integral).  What the provider class *does* discharge is
the budget for the time-independent Fourier-datum trajectory — proven as
`sourceX2Budget_constant_fourierDatum`, feeding the provider to re-derive
`SourceL1X1 T (fun _ => fourierDatum u₀)` along the `X⁰·X²` allocation
(`sourceL1X1_constant_fourierDatum_via_sourceX2Budget`).  Same conclusion as
the interface's direct `sourceL1X1_constant_fourierDatum`; the value here is
that every budget leg is *provably discharged by named existing providers*
in a non-box case, so the conditional wire has a populated domain.

## Non-vacuity at `v = 0`

`sourceX2Budget_zeroTraj` constructs all four budget legs for the zero
trajectory, and `sourceL1X1_zero_via_sourceX2Budget` derives
`SourceL1X1 T 0` through the provider — the every-time-input satisfiability
the leaves file records via the zero box, now exhibited through the new
budget route.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators Convolution NNReal FourierTransform SchwartzMap
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinRecentTailInputs
open Navier.Analysis.ContinuousLeiLinMildAssemblyLeaves
open Navier.Analysis.ContinuousLeiLinSourceX1MomentBound
open Navier.Analysis.ContinuousLeiLinMildFixedPoint
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
open Navier.Analysis.WholeSpaceRestartMildInterface
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum)
open Navier.Analysis.FourierMajorant (euclidComponent)

namespace Navier.Analysis.WholeSpaceRestartX2BudgetWiring

/-! ## Leg 2 (`hv0`) is discharged from box data -/

/-- Unweighted coordinate integrability from the two homogeneous coordinate
integrabilities: away from the single frequency `η = 0`, `‖f η j‖` is
dominated by the sum of the `X⁻¹`-weighted and `X¹`-weighted integrands. -/
theorem integrable_norm_coord_of_weighted_coords (f : ES → ComplexSpace)
    (j : Fin 3)
    (hfM : AEStronglyMeasurable (fun η : ES => f η j) volume)
    (hm : Integrable (fun η : ES => ‖η‖⁻¹ * ‖f η j‖))
    (h1 : Integrable (fun η : ES => ‖η‖ * ‖f η j‖)) :
    Integrable (fun η : ES => ‖f η j‖) := by
  refine (hm.add h1).mono' hfM.norm ?_
  have hzero : ∀ᵐ η ∂volume, (η : ES) ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with η hη
  have hpos : 0 < ‖(η : ES)‖ := norm_pos_iff.mpr hη
  have hweight0 : 0 ≤ (‖(η : ES)‖⁻¹ : ℝ) * ‖f η j‖ :=
    mul_nonneg (inv_nonneg.mpr (norm_nonneg η)) (norm_nonneg _)
  have hweight1 : 0 ≤ (‖(η : ES)‖ : ℝ) * ‖f η j‖ :=
    mul_nonneg (norm_nonneg η) (norm_nonneg _)
  rw [Pi.add_apply]
  have hlhs : ‖‖f η j‖‖ = ‖f η j‖ := Real.norm_of_nonneg (norm_nonneg _)
  rw [hlhs]
  rcases lt_or_ge ‖(η : ES)‖ 1 with hlt | hge
  · -- on the ball `‖η‖ ≤ 1` the `X⁻¹` weight dominates: `1 ≤ ‖η‖⁻¹`
    have hw : (1 : ℝ) ≤ ‖(η : ES)‖⁻¹ := (one_le_inv₀ hpos).mpr (le_of_lt hlt)
    calc ‖f η j‖ = (1 : ℝ) * ‖f η j‖ := (one_mul _).symm
      _ ≤ ‖(η : ES)‖⁻¹ * ‖f η j‖ :=
        mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ ≤ ‖(η : ES)‖⁻¹ * ‖f η j‖ + ‖(η : ES)‖ * ‖f η j‖ :=
        le_add_of_nonneg_right hweight1
  · -- outside the ball the `X¹` weight dominates: `1 ≤ ‖η‖`
    calc ‖f η j‖ = (1 : ℝ) * ‖f η j‖ := (one_mul _).symm
      _ ≤ ‖(η : ES)‖ * ‖f η j‖ := mul_le_mul_of_nonneg_right hge (norm_nonneg _)
      _ ≤ ‖(η : ES)‖⁻¹ * ‖f η j‖ + ‖(η : ES)‖ * ‖f η j‖ :=
        le_add_of_nonneg_left hweight0

/-- **Leg 2 closed from the record.**  Every time section of the everywhere
representative of an actual linked-box element is `X⁰`-integrable in each
coordinate: the box's every-time `X⁻¹` and `X¹` integrabilities dominate the
unweighted norm away from `η = 0`.  This is the one of the five provider legs
that the restart record genuinely supplies. -/
theorem box_sourceX0_integrable (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 : ℝ)
    (x : ActualLinkedBox ν T B1 B2) (s : ℝ) (j : Fin 3) :
    Integrable (fun η : ES => ‖everywhereRawRepresentative ν T x.1 s η j‖) :=
  integrable_norm_coord_of_weighted_coords
    (everywhereRawRepresentative ν T x.1 s) j
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1 s j)
    (everywhereRawRepresentative_xm1_integrable ν T x.1 s j)
    (everywhereRawRepresentative_x1_integrable ν T x.1 s j)

/-! ## The four legs the box does not supply, as a named budget -/

/-- **The `X⁰·X²` source budget on a horizon.**  The four provider legs of
`sourceL1X1_of_continuous_uniformX0_integrableX2` that the
`ActualLinkedBox` record (`L∞_t X⁻¹ ∩ L¹_t νX¹` slot norms plus the null-set
repair) does not supply: joint continuity of the trajectory, a uniform
`X⁰` mass bound `U0`, per-time `X²` integrability, and the time-integrated
`X²` moment — the `X⁰·X²` allocation of the frequency-triangle split. -/
def SourceX2Budget (T : ℝ) (v : ℝ → ES → ComplexSpace) : Prop :=
  ∃ U0 : ℝ,
    (∀ j : Fin 3, Continuous (fun p : ES × ℝ => v p.2 p.1 j)) ∧
    (∀ s ∈ Icc (0 : ℝ) T, coordinateMomentMass 0 (v s) ≤ U0) ∧
    (∀ s j, Integrable (fun η : ES => ‖η‖ ^ 2 * ‖v s η j‖)) ∧
    Integrable (fun s => coordinateMomentMass 2 (v s))
      (volume.restrict (Icc (0 : ℝ) T))

/-- **The WIRE.**  For an actual linked-box element whose everywhere
representative satisfies the `X⁰·X²` budget, `SourceL1X1` follows: the
fifth leg `hv0` is discharged from the box itself
(`box_sourceX0_integrable`) and the other four are read off the budget.
This is the exact conditional closure of the restart wall by the moment
budget, no `SourceL1X1`-shaped hypothesis. -/
theorem sourceL1X1_of_box_sourceX2Budget
    (ν : ℝ≥0) (hν : 0 < ν) (T B1 B2 : ℝ)
    (x : ActualLinkedBox ν T B1 B2)
    (Hb : SourceX2Budget T (everywhereRawRepresentative ν T x.1)) :
    SourceL1X1 T (everywhereRawRepresentative ν T x.1) := by
  obtain ⟨U0, hv, hbdd, hv2, hX2⟩ := Hb
  exact sourceL1X1_of_continuous_uniformX0_integrableX2
    T (everywhereRawRepresentative ν T x.1) U0 hv
    (box_sourceX0_integrable ν hν T B1 B2 x) hv2 hbdd hX2

/-- Budget-to-`H` lift: a budget for every box element is exactly the
undischarged premise `H` of `fourierDatumAssemblyLeaves` and
`existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1`. -/
theorem restartSourceL1X1_of_boxBudget
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (Hb : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
        SourceX2Budget T (everywhereRawRepresentative ν T x.1)) :
    ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      SourceL1X1 T (everywhereRawRepresentative ν T x.1) :=
  fun x => sourceL1X1_of_box_sourceX2Budget ν hν T (2 * R) (2 * R) x (Hb x)

/-! ## The restart records re-stated over the budget -/

/-- Assembly leaves for the Fourier transform of a small Schwartz restart
trace, over the `X⁰·X²` budget instead of the raw `SourceL1X1` premise:
the named wall is now read at the velocity-side moment-budget surface. -/
theorem fourierDatumAssemblyLeaves_of_sourceX2Budget
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SchwartzVelocity)
    (hsmall : restartRadius u₀ ≤ (ν : ℝ) / 16)
    (Hb : ∀ x : ActualLinkedBox ν T (2 * restartRadius u₀)
        (2 * restartRadius u₀),
        SourceX2Budget T (everywhereRawRepresentative ν T x.1)) :
    MildAssemblyLeaves ν hν T (restartRadius u₀) hT (fourierDatum u₀)
      (fourierDatum_aestronglyMeasurable u₀)
      (fourierDatum_integrable_Xm1 u₀)
      (fourierDatum_integrable_X1 u₀) (by rfl) :=
  fourierDatumAssemblyLeaves ν hν T hT u₀ hsmall
    (fun x => sourceL1X1_of_box_sourceX2Budget ν hν T
      (2 * restartRadius u₀) (2 * restartRadius u₀) x (Hb x))

/-- Unique mild fixed point with prescribed Schwartz restart trace, over
the `X⁰·X²` budget: identical conclusion to
`existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1`, premise routed
through `restartSourceL1X1_of_boxBudget`. -/
theorem existsUnique_mildFixedPoint_fourierDatum_of_sourceX2Budget
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SchwartzVelocity)
    (hsmall : restartRadius u₀ ≤ (ν : ℝ) / 16)
    (Hb : ∀ x : ActualLinkedBox ν T (2 * restartRadius u₀)
        (2 * restartRadius u₀),
        SourceX2Budget T (everywhereRawRepresentative ν T x.1)) :
    ∃ x : ActualLinkedBox ν T (2 * restartRadius u₀) (2 * restartRadius u₀),
      actualMildSelfMap ν hν T (restartRadius u₀) hT (fourierDatum u₀)
          (fourierDatum_aestronglyMeasurable u₀)
          (fourierDatum_integrable_Xm1 u₀)
          (fourierDatum_integrable_X1 u₀) (by rfl)
          (fourierDatumAssemblyLeaves ν hν T hT u₀ hsmall
            (restartSourceL1X1_of_boxBudget ν hν T (restartRadius u₀) Hb)) x = x ∧
      physicalVelocity
          (fixedPointTrajectory ν hν T (restartRadius u₀)
            (fourierDatum u₀) x) 0 = u₀ ∧
      ∀ y : ActualLinkedBox ν T (2 * restartRadius u₀)
          (2 * restartRadius u₀),
        actualMildSelfMap ν hν T (restartRadius u₀) hT (fourierDatum u₀)
            (fourierDatum_aestronglyMeasurable u₀)
            (fourierDatum_integrable_Xm1 u₀)
            (fourierDatum_integrable_X1 u₀) (by rfl)
            (fourierDatumAssemblyLeaves ν hν T hT u₀ hsmall
              (restartSourceL1X1_of_boxBudget ν hν T (restartRadius u₀) Hb)) y = y →
          y = x :=
  existsUnique_mildFixedPoint_fourierDatum_of_sourceL1X1 ν hν T hT u₀ hsmall
    (restartSourceL1X1_of_boxBudget ν hν T (restartRadius u₀) Hb)

/-! ## Provider-scope inhabitation: the budget is discharged by named
providers in the non-box constant-datum case -/

/-- **The budget has a populated, provider-discharged domain.**  The
time-independent Fourier-datum trajectory `fun _ => fourierDatum u₀` of any
Schwartz restart trace satisfies the full `X⁰·X²` budget: joint continuity
from Schwartz continuity, uniform `X⁰` mass by the constant `X⁰` mass, and
per-time `X²` integrability from the degree-two Schwartz moment — the same
`SchwartzMap.integrable_pow_mul` API whose HTG-multiplier extension the
grails `Warp/HeatCarrierRegularity` provider uses for the heat flow.  The
`hX2` leg is then the constant function of an `L¹` number, integrable on
`[0, T]`.  Scope note: this discharges the budget for the constant
trajectory, not for box representatives (a box representative need not be a
time-independent Schwartz slice) nor for the unclamped heat flow (whose
multiplier violates the `∀ s` legs at `s < 0`). -/
theorem sourceX2Budget_constant_fourierDatum (T : ℝ) (u₀ : SchwartzVelocity) :
    SourceX2Budget T (fun _ => fourierDatum u₀) := by
  refine ⟨coordinateMomentMass 0 (fourierDatum u₀), ?_, ?_, ?_, ?_⟩
  · intro j
    convert
      ((𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ).continuous.comp continuous_fst)
    rfl
  · intro s hs
    exact le_refl _
  · intro s j
    simpa [fourierDatum] using
      (𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ).integrable_pow_mul volume 2
  · show Integrable (fun _ : ℝ => coordinateMomentMass 2 (fourierDatum u₀))
        (volume.restrict (Icc (0 : ℝ) T))
    exact integrableOn_const measure_Icc_lt_top.ne

/-- The same `SourceL1X1` conclusion as
`WholeSpaceRestartMildInterface.sourceL1X1_constant_fourierDatum`, reached
through the `X⁰·X²` budget and the moment-bound provider: the budget legs
are provable from named providers and the wiring consumes them. -/
theorem sourceL1X1_constant_fourierDatum_via_sourceX2Budget
    (T : ℝ) (u₀ : SchwartzVelocity) :
    SourceL1X1 T (fun _ => fourierDatum u₀) := by
  obtain ⟨U0, hv, hbdd, hv2, hX2⟩ := sourceX2Budget_constant_fourierDatum T u₀
  refine sourceL1X1_of_continuous_uniformX0_integrableX2
    T (fun _ => fourierDatum u₀) U0 hv ?_ hv2 hbdd hX2
  intro s j
  simpa [fourierDatum] using
    (𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ).integrable.norm

/-! ## Non-vacuity: the zero trajectory satisfies the budget, and
`SourceL1X1 T 0` is derived through the provider -/

/-- All four budget legs for the zero velocity: joint continuity, the
uniform bound `0`, and vanishing moment integrabilities. -/
theorem sourceX2Budget_zeroTraj (T : ℝ) :
    SourceX2Budget T (fun _ => (0 : ES → ComplexSpace)) := by
  refine ⟨0, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa using (continuous_const : Continuous (fun _ : ES × ℝ => (0 : ℂ)))
  · intro s hs
    simp [coordinateMomentMass]
  · intro s j
    simp
  · simp

/-- **Non-vacuity through the new provider.**  The zero trajectory meets
all five legs of
`sourceL1X1_of_continuous_uniformX0_integrableX2` — the budget four
(`sourceX2Budget_zeroTraj`) and per-time `X⁰` integrability (`hv0`,
vanishing) — and `SourceL1X1 T 0` is derived from the provider itself.
The leaves file records satisfiability of `SourceL1X1` via the zero box;
this exhibits the same satisfiability through the strengthened
velocity-side budget. -/
theorem sourceL1X1_zero_via_sourceX2Budget (T : ℝ) :
    SourceL1X1 T (fun _ => (0 : ES → ComplexSpace)) := by
  obtain ⟨U0, hv, hbdd, hv2, hX2⟩ := sourceX2Budget_zeroTraj T
  refine sourceL1X1_of_continuous_uniformX0_integrableX2
    T (fun _ => (0 : ES → ComplexSpace)) U0 hv ?_ hv2 hbdd hX2
  intro s j
  simp

end Navier.Analysis.WholeSpaceRestartX2BudgetWiring

#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.integrable_norm_coord_of_weighted_coords
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.box_sourceX0_integrable
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.sourceL1X1_of_box_sourceX2Budget
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.restartSourceL1X1_of_boxBudget
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.fourierDatumAssemblyLeaves_of_sourceX2Budget
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.existsUnique_mildFixedPoint_fourierDatum_of_sourceX2Budget
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.sourceX2Budget_constant_fourierDatum
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.sourceL1X1_constant_fourierDatum_via_sourceX2Budget
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.sourceX2Budget_zeroTraj
#print axioms Navier.Analysis.WholeSpaceRestartX2BudgetWiring.sourceL1X1_zero_via_sourceX2Budget

set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceRestartX2BudgetWiring.sourceL1X1_of_box_sourceX2Budget
set_option pp.fullNames true in
#check @Navier.Analysis.WholeSpaceRestartX2BudgetWiring.sourceL1X1_zero_via_sourceX2Budget
