import Navier.Analysis.LinkedBoxX2ContRepCarrier

/-!
# `pinProdAe`: the Fubini/exceptional-set upgrade of the fiberwise contRep pin

Lane W31-N08, MacBook, base `498ac0ce` (the pushed `lane/W31-N07-0930`
head).  N07 named `ActualLinkedBoxX2ContRep.pinProdAe` — the
product-measure a.e. upgrade of the fiberwise pin `hPin` — as the exact
remaining gap.  This module:

* proves the Fubini/exceptional-set keystone
  `pinProdAe_of_measurable` (ladder (b)): fiberwise pin + measurability of
  the agreement set ⇒ product-a.e., via
  `MeasureTheory.ae_prod_iff_ae_ae` + `MeasureTheory.ae_ae_comm`
  (`Mathlib/MeasureTheory/Measure/Prod.lean:445,706`);
* CLOSES `pinProdAe` for BOTH N07 suppliers.  `boxX2ZeroContRep`:
  `contRep := raw` so the predicate is reflexive pointwise (`ae_of_all`).
  `boxX2ConstantContRep`: no joint measurability of the gated choice-data
  field is needed, because the disagreement factors into two
  coordinate-rectangles: `fourierDatum_classPin` pins the FREQUENCY
  exceptional set and `boxX2GoodAt_ae` the TIME exceptional set, while
  `boxX2Constant_xm1Slot_eval` pins the slot evaluation POINTWISE in time
  (`0 < T`), so at good times `raw t = Φ` literally and the fiber
  disagreement lands in the fixed classPin exceptional set.

## Honest scope

The downstream half of the N07 target — the a.e.-invariance of
`SourceL1X1` (def `ContinuousLeiLinMildAssemblyLeaves.lean:1880`) through
`continuousNavierSource` (`ContinuousLeiLinTimeDuhamel.lean:29`) — is NOT
proven here: `pinProdAe` is its hypothesis-ready input, and convolution
fibers depend on whole frequency slices, so a.e. substitution of `v`
under `‖ξ‖ * ‖continuousNavierSource v v t ξ i‖` product-integrability is
its own estimate, not a measurability lemma.  For GENERAL records the
remaining obligation is exactly the keystone hypothesis: the raw coordinate
field `(ξ, t) ↦ boxX2RawRepresentative ν T B1 B2 B3 b.toBox t ξ j` must be
measurable-agreement/AEMeasurable on `volume.prod (leiLinTimeMeasure T)`
(it is choice data through the `Lp` quotients; nothing here claims it).
No wrapper premise is taken; N07's module is untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinCommonRepresentative
open Navier.Analysis.LinkedBoxX2Carrier
open Navier.Analysis.LinkedBoxX2HvIndependence
open Navier.Analysis.LinkedBoxX2ContRepCarrier
open Navier.Analysis.WholeSpaceRestartMildInterface
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum)

namespace Navier.Analysis.ContRepPinProdAe

/-! ## The Fubini/exceptional-set keystone (ladder (b)) -/

/-- **Fubini/exceptional-set keystone.**  The exact statement N07 named:
the fiberwise pin `hPin` upgrades to `pinProdAe` once the agreement set of
the two coordinate fields is measurable (equivalently: once the
exceptional set is).  Proof: `ae_prod_iff_ae_ae` (product ⇄ fibers under
measurability) + `ae_ae_comm` (fiber order swap under measurability) —
the measurability transport of `hPin` from the full `ComplexSpace` value
to a fixed coordinate `j` is `congrFun`.  For general records the raw side
is gated `Lp`-choice data; THIS is the named gap. -/
theorem ActualLinkedBoxX2ContRep.pinProdAe_of_measurable
    (ν : ℝ≥0) (T B1 B2 B3 : ℝ) (b : ActualLinkedBoxX2ContRep ν T B1 B2 B3)
    (hSet : ∀ j : Fin 3, MeasurableSet
      {x : ES × ℝ | b.contRep x.2 x.1 j =
        boxX2RawRepresentative ν T B1 B2 B3 b.toBox x.2 x.1 j}) :
    b.pinProdAe := by
  intro j
  have hSet_j := hSet j
  -- fiberwise pin at the single coordinate j
  have hfiber : ∀ᵐ t ∂leiLinTimeMeasure T, ∀ᵐ ξ ∂volume,
      b.contRep t ξ j = boxX2RawRepresentative ν T B1 B2 B3 b.toBox t ξ j := by
    filter_upwards [b.hPin] with t ht
    filter_upwards [ht] with ξ hξ
    exact congrFun hξ j
  -- the swapped predicate on ℝ × ES is measurable (preimage of swap)
  have hSwap : MeasurableSet {z : ℝ × ES | b.contRep z.1 z.2 j =
      boxX2RawRepresentative ν T B1 B2 B3 b.toBox z.1 z.2 j} := by
    have hpre : {z : ℝ × ES | b.contRep z.1 z.2 j =
        boxX2RawRepresentative ν T B1 B2 B3 b.toBox z.1 z.2 j}
        = Prod.swap ⁻¹' {x : ES × ℝ | b.contRep x.2 x.1 j =
            boxX2RawRepresentative ν T B1 B2 B3 b.toBox x.2 x.1 j} := rfl
    rw [hpre]
    exact hSet_j.preimage (by fun_prop)
  -- swap the fiber order (μT-first → volume-first), then upgrade to the product
  have hcomm := (MeasureTheory.Measure.ae_ae_comm (p := fun (t : ℝ) (ξ : ES) =>
      b.contRep t ξ j = boxX2RawRepresentative ν T B1 B2 B3 b.toBox t ξ j)
      hSwap).mp hfiber
  exact (MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun x : ES × ℝ =>
      b.contRep x.2 x.1 j = boxX2RawRepresentative ν T B1 B2 B3 b.toBox x.2 x.1 j)
      hSet_j).mpr hcomm

/-! ## The zero supplier: reflexive -/

/-- **Zero control: `pinProdAe` CLOSED.**  `boxX2ZeroContRep` carries the
gated field itself as `contRep`, so the product-measure predicate is
reflexive at EVERY point — the empty exceptional set, no Fubini, no
measurability. -/
theorem boxX2ZeroContRep_pinProdAe (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    (boxX2ZeroContRep ν hν T hT).pinProdAe := by
  intro j
  exact ae_of_all _ fun _ => rfl

/-! ## The constant supplier: rectangle domination, no joint measurability -/

/-- **Constant supplier: `pinProdAe` CLOSED.**  The disagreement set of the
two coordinate fields factors through coordinate rectangles: the frequency
rectangle of `fourierDatum_classPin` (fixed representative `Φ`, the
`L¹`-class chosen member of the constant datum) and the time rectangle of
`boxX2GoodAt_ae`.  At good times `boxX2RawRepresentative_at_good` rewrites
the gated field to `xm1RawRepresentative`, and
`boxX2Constant_xm1Slot_eval` (POINTWISE in time, needing `0 < T`)
identifies the slot evaluation with `toXm1Spatial (fourierDatum u₀) …` —
so `raw t ξ j = Φ ξ j` literally, and the fiber disagreement is covered by
the classPin exceptional set coordinatewise.  No measurability of the
gated choice-data field is claimed or needed. -/
theorem boxX2ConstantContRep_pinProdAe (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (hT : 0 < T) (u₀ : SchwartzVelocity) :
    (boxX2ConstantContRep ν hν T hT u₀).pinProdAe := by
  classical
  intro j
  set Φ := fun ξ : ES => ((toXm1Spatial (fourierDatum u₀)
      (fun i => fourierDatum_aestronglyMeasurable u₀ i)
      (fun i => fourierDatum_integrable_Xm1 u₀ i)) ξ :
      FourierCoordinateL1).ofLp with hΦ
  -- frequency coordinate of the disagreement is volume-a.e. controlled:
  have hfiberAe : ∀ᵐ ξ ∂volume, fourierDatum u₀ ξ j = Φ ξ j := by
    filter_upwards [fourierDatum_classPin ν hν u₀] with ξ hξ
    exact (congrFun hξ j).symm
  -- lift both controls to the product measure through the coordinates:
  have h1 : ∀ᵐ x : ES × ℝ ∂(Measure.prod volume (leiLinTimeMeasure T)),
      fourierDatum u₀ x.1 j = Φ x.1 j :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst).ae hfiberAe
  have h2 : ∀ᵐ t ∂leiLinTimeMeasure T,
      BoxX2GoodAt ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
        ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀) t :=
    boxX2GoodAt_ae ν hν T _ _ _ (boxX2Constant ν T u₀)
  have h2' : ∀ᵐ x : ES × ℝ ∂(Measure.prod volume (leiLinTimeMeasure T)),
      BoxX2GoodAt ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
        ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀) x.2 :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd).ae h2
  filter_upwards [h1, h2'] with x hx1 hx2
  -- at good times the gated field IS Φ, pointwise:
  have hraw : boxX2RawRepresentative ν T ‖constRawXm T u₀‖
      ‖constRawX1 ν T u₀‖ ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀) x.2 x.1 =
      Φ x.1 := by
    rw [boxX2RawRepresentative_at_good ν T _ _ _ (boxX2Constant ν T u₀) x.2 hx2]
    change (((boxX2Constant ν T u₀).1.1.1.1.fst : Xm1TimeSlot T) x.2 x.1 :
        FourierCoordinateL1).ofLp = Φ x.1
    rw [boxX2Constant_xm1Slot_eval ν T hT u₀ x.2]
  change fourierDatum u₀ x.1 j =
      boxX2RawRepresentative ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
        ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀) x.2 x.1 j
  rw [hraw]
  exact hx1

set_option pp.fullNames true in
#check @Navier.Analysis.ContRepPinProdAe.ActualLinkedBoxX2ContRep.pinProdAe_of_measurable
set_option pp.fullNames true in
#check @Navier.Analysis.ContRepPinProdAe.boxX2ZeroContRep_pinProdAe
set_option pp.fullNames true in
#check @Navier.Analysis.ContRepPinProdAe.boxX2ConstantContRep_pinProdAe

#print axioms Navier.Analysis.ContRepPinProdAe.ActualLinkedBoxX2ContRep.pinProdAe_of_measurable
#print axioms Navier.Analysis.ContRepPinProdAe.boxX2ZeroContRep_pinProdAe
#print axioms Navier.Analysis.ContRepPinProdAe.boxX2ConstantContRep_pinProdAe

end Navier.Analysis.ContRepPinProdAe
