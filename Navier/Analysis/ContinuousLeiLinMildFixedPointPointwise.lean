import Navier.Analysis.ContinuousLeiLinMildFixedPointPressure
import Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply

/-!
# The mild fixed point has an exact pointwise representative

`actual_existsUnique_mildFixedPoint` produces its fixed point as an element of
the completed linked box: `Φ x = x` is equality of two slot quotients, and
`ContinuousLeiLinMildAssemblyLeaves` records that a general box element's
everywhere representative carries NO joint continuity.  The obligation-4
residual `hcont` (fibre continuity of the reweighted source) is not
invariant under null-set re-representativization, so no slot datum implies
it; the route this forces is a POINTWISE representative.

This module constructs that representative.  For a box fixed point `x` the
mild image of its everywhere representative,
`u := mildImage ν hν a (everywhereRawRepresentative ν T x.1)`, is an EXACT
pointwise mild fixed point on the horizon:

`∀ t ∈ Icc 0 T, ∀ ξ, u t ξ = continuousMildImage ν hν a u t ξ`

(`fixedPoint_pointwiseMild`).  Mechanism: the fixed-point equation forces
the outer `X⁻¹` slot of the rebuilt image to equal the slot of `x`, whence
`nested_ae_eq_of_toXm1TimeSlot_eq` gives `u t =ᵐ rep t` for a.e. horizon
time (`fixedPoint_rep_ae_eq_mildImage`); the Duhamel source reads its input
only through spacetime integrals, so
`continuousMildImage_congr_ae_on_horizon` turns `mildImage a u = mildImage a
rep = u` into an identity at EVERY time and frequency.

Consumption: `hcont_fixedPoint` feeds this pointwise identity — together with
the fixed point's slice measurability `L.hmM` and the datum's `L¹` mass from
its `X⁻¹`/`X¹` moments — into
`ContinuousLeiLinOb4FrequencyODESupply.ae_ContinuousOn_weightedSource_of_mildFixed`,
so the fibre continuity residual of obligation 4 holds at the actual mild
fixed point under exactly the window bundle and the recent-window `X⁻¹`
source moment at its representative.  What still travels: those two moment
inputs at the fixed point (the degree-2 recent moment is beyond the box
slots, as the `ContinuousLeiLinODEDominationSupply` header records) and the
`MildAssemblyLeaves` record itself.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap (continuousMildImage)
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeInvariant
open Navier.Analysis.ContinuousLeiLinMildFixedPoint
open Navier.Analysis.ContinuousLeiLinMildFixedPointPressure
  (integrable_norm_continuousCoordinate_of_Xm1_X1)
open Navier.Analysis.ContinuousLeiLinFrequencyODE (weightedSource)
open Navier.Analysis.ContinuousLeiLinODEDominationSupply (PhysicalODEWindowSupply)
open Navier.Analysis.ContinuousLeiLinOb4FrequencyODESupply

namespace Navier.Analysis.ContinuousLeiLinMildFixedPointPointwise

/-- **The fixed point's representative agrees a.e. with its own mild image.**
The `X⁻¹`-slot half of the fixed-point equation, unfolded through
`nested_ae_eq_of_toXm1TimeSlot_eq` (the same bridge as
`fixedPoint_pressureEq`, stated here at the raw field level). -/
theorem fixedPoint_rep_ae_eq_mildImage (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x : ActualLinkedBox ν T (2 * R) (2 * R))
    (hx : actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x = x) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      mildImage ν hν a (everywhereRawRepresentative ν T x.1) t =ᵐ[volume]
        everywhereRawRepresentative ν T x.1 t := by
  set w : ℝ → ES → ComplexSpace :=
    mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) with hw_def
  have hMw := mildImageIcc_aestronglyMeasurable ν hν T a
    (everywhereRawRepresentative ν T x.1) (L.hmM x)
  have hXm1w := mildImageIcc_integrableXm1 ν hν T a
    (everywhereRawRepresentative ν T x.1) (L.hmXm1 x)
  have hbIcc := selfMapEstimate_Icc ν hν T R hT a haM ha ha1 haR L x
  have hval : (actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x).1 = x.1 :=
    congrArg Subtype.val hx
  have h0 : (mildLift ν hν T R hT a haM ha ha1 haR L x).1.fst = x.1.1.fst :=
    congrArg (fun c : ActualLinkedCarrier ν T => c.1.fst) hval
  have hkey : (mildLift ν hν T R hT a haM ha ha1 haR L x).1.fst =
      toXm1TimeSlot w hMw hXm1w T (2 * R) (L.hmXm1Time x) hbIcc := rfl
  have hevery : everywhereXm1TimeSlot ν hν T x.1 =
      toXm1TimeSlot (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1)
        (everywhereRawRepresentative_xm1_integrable ν T x.1) T
        ‖(x.1.1.fst : Xm1TimeSlot T)‖
        (everywhereXm1Section_aestronglyMeasurable ν hν T x.1)
        (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t) := rfl
  have hslot : toXm1TimeSlot w hMw hXm1w T (2 * R) (L.hmXm1Time x) hbIcc =
      toXm1TimeSlot (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1)
        (everywhereRawRepresentative_xm1_integrable ν T x.1) T
        ‖(x.1.1.fst : Xm1TimeSlot T)‖
        (everywhereXm1Section_aestronglyMeasurable ν hν T x.1)
        (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t) := by
    rw [← hkey, h0, ← hevery]
    exact (everywhereXm1TimeSlot_eq ν hν T x.1).symm
  have hae := nested_ae_eq_of_toXm1TimeSlot_eq ν hν T (2 * R) ‖(x.1.1.fst : Xm1TimeSlot T)‖
    w (everywhereRawRepresentative ν T x.1)
    hMw (everywhereRawRepresentative_aestronglyMeasurable ν hν T x.1)
    hXm1w (everywhereRawRepresentative_xm1_integrable ν T x.1)
    (L.hmXm1Time x) (everywhereXm1Section_aestronglyMeasurable ν hν T x.1)
    hbIcc (fun t _ => coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t) hslot
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet, hae] with t htI ht
  have hpoint : (fun ξ : ES => mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ)
      =ᵐ[volume] w t :=
    ae_of_all _ fun ξ =>
      (mildImageIcc_of_mem ν hν T a (everywhereRawRepresentative ν T x.1) t htI ξ).symm
  exact hpoint.trans ht

/-- **The exact pointwise mild fixed point.**  The mild image of the fixed
point's everywhere representative is its own mild image at every horizon
time and every frequency — not merely as a box element.  The Duhamel source
reads its input only through spacetime integrals, so the a.e. identity of
`fixedPoint_rep_ae_eq_mildImage` transports to equality everywhere
(`continuousMildImage_congr_ae_on_horizon`). -/
theorem fixedPoint_pointwiseMild (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x : ActualLinkedBox ν T (2 * R) (2 * R))
    (hx : actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x = x)
    (hν' : (0 : ℝ) < (ν : ℝ)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ : ES,
      mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ =
        continuousMildImage (ν : ℝ) hν' a
          (mildImage ν hν a (everywhereRawRepresentative ν T x.1)) t ξ := by
  intro t ht ξ
  have huv := fixedPoint_rep_ae_eq_mildImage ν hν T R hT a haM ha ha1 haR L x hx
  exact (continuousMildImage_congr_ae_on_horizon (ν : ℝ) hν' T a
    (mildImage ν hν a (everywhereRawRepresentative ν T x.1))
    (everywhereRawRepresentative ν T x.1) huv t ht ξ).symm

/-- **The obligation-4 fibre-continuity residual holds at the actual mild fixed
point.**  With `u` the pointwise representative of `fixedPoint_pointwiseMild`,
on every window `(τ', t₁) ⊆ [0, T]` with `τ < τ'`, the reweighted source of
`u` is fibre-continuous for almost every output frequency, given only the
window bundle at every coordinate and the recent-window `X⁻¹` source moment
at `u`.  Slice measurability is the leaves field `L.hmM`; the datum's `L¹`
mass follows from its `X⁻¹`/`X¹` moments; the pointwise mild identity is the
theorem above.  This is the `hcont` hypothesis of
`hdvDiff_of_windowMoments_and_sourceContinuous` discharged at the fixed point. -/
theorem hcont_fixedPoint (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x : ActualLinkedBox ν T (2 * R) (2 * R))
    (hx : actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x = x)
    (hν' : (0 : ℝ) < (ν : ℝ)) (i : Fin 3)
    (τ τ' t₁ : ℝ) (hτ : 0 ≤ τ) (hττ' : τ < τ') (ht₁ : t₁ ≤ T)
    (sup : ∀ j : Fin 3, PhysicalODEWindowSupply
      (mildImage ν hν a (everywhereRawRepresentative ν T x.1)) j τ t₁)
    (hsrcm1 : ∀ j : Fin 3, Integrable (fun p : ES × ℝ =>
        ‖p.1‖⁻¹ * ‖continuousNavierSource
          (mildImage ν hν a (everywhereRawRepresentative ν T x.1))
          (mildImage ν hν a (everywhereRawRepresentative ν T x.1)) p.2 p.1 j‖)
      (volume.prod (volume.restrict (Icc τ t₁)))) :
    ∀ᵐ ξ ∂volume, ContinuousOn
      (weightedSource (ν : ℝ) (mildImage ν hν a (everywhereRawRepresentative ν T x.1))
        (mildImage ν hν a (everywhereRawRepresentative ν T x.1)) ξ i) (Ioo τ' t₁) := by
  refine ae_ContinuousOn_weightedSource_of_mildFixed (ν : ℝ) hν' a
    (mildImage ν hν a (everywhereRawRepresentative ν T x.1)) i τ τ' t₁ hτ hττ'
    (Ioo τ' t₁) subset_rfl ?_ sup hsrcm1 ?_ ?_
  · intro j
    exact integrable_norm_continuousCoordinate_of_Xm1_X1 a j (haM j) (ha j) (ha1 j)
  · intro s hs j
    exact L.hmM x s ⟨by linarith [hs.1], hs.2.le.trans ht₁⟩ j
  · refine ae_of_all _ fun η s hs j => ?_
    exact congrFun (fixedPoint_pointwiseMild ν hν T R hT a haM ha ha1 haR L x hx hν' s
      ⟨by linarith [hs.1], hs.2.le.trans ht₁⟩ η) j

end Navier.Analysis.ContinuousLeiLinMildFixedPointPointwise

#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPointwise.fixedPoint_rep_ae_eq_mildImage
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPointwise.fixedPoint_pointwiseMild
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointPointwise.hcont_fixedPoint
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPointwise.fixedPoint_pointwiseMild
#check @Navier.Analysis.ContinuousLeiLinMildFixedPointPointwise.hcont_fixedPoint
