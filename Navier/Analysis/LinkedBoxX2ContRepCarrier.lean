import Navier.Analysis.LinkedBoxX2HvIndependence

/-!
# The `contRep` front-end: pinning continuous spatial representatives as data

Lane W31-N07, MacBook cone `/private/tmp/wt-W31-N04-navier` @ base `648c81c3`.
This module executes the front-end change that N06's exhibit
(`Navier/Analysis/LinkedBoxX2HvIndependence.lean`, "The front-end change this
names") declared necessary: `hv` joint continuity of
`LinkedBoxX2Carrier.boxX2RawRepresentative` is `AEEqFun.cast` /
`Quotient.out` choice data on the class-based carrier
`ActualLinkedBoxX2` — `boxX2Constant_hv_iff` exhibits it as equivalent to the
continuity of the opaque chosen field `constantChosenRepField`, and nothing
in the radii `(B1, B2, B3)` or the linkage constrains it.

## Shape decision (one-search, MacBook, 2026-09-30)

Searched before constructing, at the exact type shapes:
1. Mathlib continuous-representative API for a.e.-equal `Lp`/`AEEqFun` data
   (`exists_rep`-style choice of a continuous member): NO such API exists —
   the estate grep hits only `ModelTheory`/`CategoryTheory` name collisions.
   The `AEEqFun.cast` branch for non-constant classes is `Quotient.out` with
   no pointwise lemma (N06 root cause 2, `aesm↔continuous` direction: only
   `Continuous.aestronglyMeasurable`, `AEStronglyMeasurable.lean:239`,
   exists — no converse).
2. aesm↔continuous bridges: one-way only (continuous ⟹ aesm).
3. Local navier decls pinning pointwise continuous fields: the `hTimeM`
   explicit-data constructor style (`LinkedBoxX2Carrier.lean:812,824`,
   `ContinuousLeiLinTrajectoryLift.lean:305-352`) is the estate's chosen
   escape; the Fourier-side continuity proof pattern
   `(𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ).continuous` is already
   used inline at `WholeSpaceRestartX2BudgetWiring.lean:290` and
   `WholeSpaceCarrierReconstruction.lean:227` but is NOT a named lemma —
   this module names it (`continuous_fourierDatum_coord`).

Decision: shape (a) — EXTEND the carrier family with a `contRep` structure
mirroring the gated-raw + explicit-data style. No main-resident decl is
rewritten; no in-place signature edit (shape (b) not exercised). The gated
commit adds ONE new file.

## What is proved here

* `ActualLinkedBoxX2ContRep` — the Pattern-A carrier wrapped with a pointwise
  representative `contRep : ℝ → ES → ComplexSpace`, continuity as explicit
  record data (the `hCont` field, constructor argument, exactly like
  `hTimeM`), and `hPin`: the representative agrees with the old gated field
  `boxX2RawRepresentative` at `leiLinTimeMeasure`-a.e. time, `volume`-a.e.
  frequency — so `contRep` is a REPRESENTATIVE of the same record, not a
  decoration.
* `boxX2ConstantContRep` — the constant supplier on the new carrier. Its
  `hCont` datum is FIRED, not assumed: `fourierDatum u₀` coordinates are
  Schwartz Fourier transforms, hence pointwise continuous
  (`continuous_fourierDatum_coord`). Its `hPin` datum is the exhibit's
  `boxX2Constant_xm1Slot_eval` slot pin composed with
  `fourierDatum_classPin` (`coeFn_toXm1Spatial` transported along
  `volume ≪ commonX2FrequencyMeasure ν ≪ xm1FrequencyMeasure` at `0 < ν`).
* `boxX2ConstantContRep_hv` — **the discharge**: `hv` joint continuity for
  the constant supplier as an exact theorem (NOT an `↔`) on the
  pinned-representative carrier.  `boxX2ZeroContRep` /
  `boxX2ZeroContRep_hv` preserve the zero control: the exhibit's
  untouched-strict `boxX2Zero_hv` proof is consumed as constructor data.

## Honest scope

* This does NOT prove `hv` for the OLD gated field
  `boxX2RawRepresentative` of the constant supplier — the exhibit's
  `boxX2Constant_hv_iff` still makes that `Quotient.out` choice data, and
  this module leaves that file untouched.
* What still blocks the full crown is NAMED below with its exact type:
  `ActualLinkedBoxX2ContRep.pinProdAe` — the fiberwise pin `hPin` is not
  product-measure a.e. without exceptional-set measurability (Fubini), and
  `SourceL1X1`-through-`continuousNavierSource` a.e. transport on top of
  that.  No wrapper premise is taken for it.
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
open Navier.Analysis.FourierMajorant
open Navier.Analysis.LinkedBoxX2Carrier
open Navier.Analysis.LinkedBoxX2HvIndependence
open scoped FourierTransform SchwartzMap
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
open Navier.Analysis.WholeSpaceRestartMildInterface
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier (fourierDatum)

namespace Navier.Analysis.LinkedBoxX2ContRepCarrier

/-! ## The pinned-representative carrier -/

/-- **The `contRep` front-end carrier (Pattern A).**  An extended box record
`ActualLinkedBoxX2` together with a pointwise representative field
`contRep : ℝ → ES → ComplexSpace`, whose per-coordinate continuity on
`ES × ℝ` is explicit constructor data (the carrier's own `hTimeM`
explicit-data style, `LinkedBoxX2Carrier.lean:812,824`), pinned to the
record's gated field `boxX2RawRepresentative` at a.e. time, `volume`-a.e.
frequency — so `contRep` is a representative of the same record and not a
decoration.  On this carrier the `hv` leg is record data and
`boxX2_sourceX2Budget_of_hv`'s hypothesis is replaced, not wrapped. -/
structure ActualLinkedBoxX2ContRep (ν : ℝ≥0) (T B1 B2 B3 : ℝ) where
  /-- The underlying extended box record. -/
  toBox : ActualLinkedBoxX2 ν T B1 B2 B3
  /-- The pinned pointwise representative field. -/
  contRep : ℝ → ES → ComplexSpace
  /-- Explicit-data continuity of the representative (constructor argument,
  mirroring `hTimeM`'s role in the slot constructors). -/
  hCont : ∀ j : Fin 3, Continuous (fun p : ES × ℝ => contRep p.2 p.1 j)
  /-- The representative IS a representative of the record: at a.e. time it
  agrees with the gated field `volume`-a.e. in frequency. -/
  hPin : ∀ᵐ t ∂leiLinTimeMeasure T,
    contRep t =ᵐ[volume] boxX2RawRepresentative ν T B1 B2 B3 toBox t

/-- The pinned field of a `contRep` record: the record data that replaces
the `AEEqFun.cast` point evaluation on the `hv` leg. -/
def boxX2ContRepField (ν : ℝ≥0) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2ContRep ν T B1 B2 B3) : ℝ → ES → ComplexSpace :=
  b.contRep

/-- On the pinned carrier `hv` is record data: discharged by projection,
with no hypothesis and no `↔`. -/
theorem boxX2ContRep_hv_of_record (ν : ℝ≥0) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2ContRep ν T B1 B2 B3) :
    ∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        boxX2ContRepField ν T B1 B2 B3 b p.2 p.1 j) :=
  b.hCont

/-! ## The consumed subkeystone: Fourier-side pointwise continuity -/

/-- **Subkeystone (named here; previously only inline usage).**  Each
frequency coordinate of the Fourier datum is the Schwartz-space Fourier
transform `𝓕 (euclidComponent u₀ j)`, hence a continuous function of
`ξ`; the spacetime coordinate field `(ξ, t) ↦ fourierDatum u₀ ξ j` is
continuous.  Inline uses: `WholeSpaceRestartX2BudgetWiring.lean:290`,
`WholeSpaceCarrierReconstruction.lean:227`.  This is the datum that fires
the supplier's `hCont` without any pointwise fact about chosen `Lp`
representatives. -/
theorem continuous_fourierDatum_coord (u₀ : SchwartzVelocity) (j : Fin 3) :
    Continuous (fun p : ES × ℝ => fourierDatum u₀ p.1 j) := by
  have hfun : (fun p : ES × ℝ => fourierDatum u₀ p.1 j) =
      (fun p : ES × ℝ => (𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ) p.1) := by
    funext p
    rfl
  rw [hfun]
  exact ((𝓕 (euclidComponent u₀ j) : SchwartzMap ES ℂ).continuous).comp
    continuous_fst

/-- The Fourier datum is a `volume`-a.e. member of its own spatial `X⁻¹`
class: composing `coeFn_toXm1Spatial` (the `MemLp.toLp` a.e. lemma) with the
definitional `WithLp.ofLp`/`WithLp.toLp` collapse and pulling the a.e.
relation back along the absolute-continuity chain
`volume ≪ commonX2FrequencyMeasure ν ≪ xm1FrequencyMeasure` (needs `0 < ν`,
the chain of `x2Raw_ae`).  This is the honest content of "representative":
pointwise pins of the class EVALUATION remain choice data (`AEEqFun.cast`
`dif`-branch), but the class's chosen member is a.e.-equated to the datum. -/
theorem fourierDatum_classPin (ν : ℝ≥0) (hν : 0 < ν) (u₀ : SchwartzVelocity) :
    (fun ξ : ES => ((toXm1Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_Xm1 u₀ i)) ξ :
        FourierCoordinateL1).ofLp) =ᵐ[volume] fourierDatum u₀ := by
  classical
  have hxm : (fun ξ : ES => ((toXm1Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_Xm1 u₀ i)) ξ :
        FourierCoordinateL1)) =ᵐ[xm1FrequencyMeasure]
        coordinateL1 (fourierDatum u₀) :=
    coeFn_toXm1Spatial (fourierDatum u₀)
      (fun i => fourierDatum_aestronglyMeasurable u₀ i)
      (fun i => fourierDatum_integrable_Xm1 u₀ i)
  have h : (fun ξ : ES => ((toXm1Spatial (fourierDatum u₀)
        (fun i => fourierDatum_aestronglyMeasurable u₀ i)
        (fun i => fourierDatum_integrable_Xm1 u₀ i)) ξ :
        FourierCoordinateL1).ofLp) =ᵐ[xm1FrequencyMeasure]
        fourierDatum u₀ := by
    filter_upwards [hxm] with ξ hξ
    rw [hξ]
    exact rfl
  have hac : volume ≪ xm1FrequencyMeasure :=
    (volume_absolutelyContinuous_commonX2FrequencyMeasure ν hν).trans
      (Measure.absolutelyContinuous_of_le (commonX2FrequencyMeasure_le_xm1 ν))
  exact hac.ae_eq h

/-! ## The constant supplier on the pinned carrier -/

/-- **The constant supplier on the `contRep` carrier.**  `toBox` is the
exhibit's `boxX2Constant ν T u₀`; `contRep` is the time-independent
pointwise Fourier-side field `fourierDatum u₀`; `hCont` is fired by
`continuous_fourierDatum_coord` (Schwartz continuity — proved, not
assumed); `hPin` composes the exhibit's committed slot pin
`boxX2Constant_xm1Slot_eval` (pointwise-in-time identity of the slot
evaluation with the spatial class, for `0 < T`) with
`fourierDatum_classPin` on the good-time set of `boxX2GoodAt_ae`. -/
noncomputable def boxX2ConstantContRep (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (hT : 0 < T) (u₀ : SchwartzVelocity) :
    ActualLinkedBoxX2ContRep ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
      ‖constRawX2 T u₀‖ where
  toBox := boxX2Constant ν T u₀
  contRep := fun _ => fourierDatum u₀
  hCont := fun j => continuous_fourierDatum_coord u₀ j
  hPin := by
    classical
    filter_upwards [boxX2GoodAt_ae ν hν T _ _ _ (boxX2Constant ν T u₀)] with t ht
    rw [boxX2RawRepresentative_at_good ν T _ _ _ (boxX2Constant ν T u₀) t ht]
    change fourierDatum u₀ =ᵐ[volume] fun ξ : ES =>
        (((boxX2Constant ν T u₀).1.1.1.1.fst : Xm1TimeSlot T) t ξ :
          FourierCoordinateL1).ofLp
    refine (fourierDatum_classPin ν hν u₀).symm.trans ?_
    have hfn : (fun ξ : ES => ((toXm1Spatial (fourierDatum u₀)
          (fun i => fourierDatum_aestronglyMeasurable u₀ i)
          (fun i => fourierDatum_integrable_Xm1 u₀ i)) ξ :
          FourierCoordinateL1).ofLp) =
        (fun ξ : ES => (((boxX2Constant ν T u₀).1.1.1.1.fst : Xm1TimeSlot T) t ξ :
          FourierCoordinateL1).ofLp) := by
      funext ξ
      rw [← boxX2Constant_xm1Slot_eval ν T hT u₀ t]
    rw [← hfn]

/-- **The discharge (acceptance ladder (a)).**  `hv` joint continuity for
the canonical nonzero supplier, on the pinned-representative carrier, as an
EXACT theorem (not an `↔`): the continuity leg `boxX2_sourceX2Budget_of_hv`
carried as a hypothesis on the class-based carrier becomes record data here,
and record data was fired at construction from the Schwartz-side pointwise
continuity. -/
theorem boxX2ConstantContRep_hv (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : SchwartzVelocity) :
    ∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        boxX2ContRepField ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
          ‖constRawX2 T u₀‖ (boxX2ConstantContRep ν hν T hT u₀) p.2 p.1 j) :=
  (boxX2ConstantContRep ν hν T hT u₀).hCont

/-- The pin survives as a theorem about the supplier: the new representative
and the old gated field agree at a.e. time, a.e. frequency — the same record,
two field realizations. -/
theorem boxX2ConstantContRep_pin (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T)
    (u₀ : SchwartzVelocity) :
    ∀ᵐ t ∂leiLinTimeMeasure T, fourierDatum u₀ =ᵐ[volume]
      boxX2RawRepresentative ν T ‖constRawXm T u₀‖ ‖constRawX1 ν T u₀‖
        ‖constRawX2 T u₀‖ (boxX2Constant ν T u₀) t :=
  (boxX2ConstantContRep ν hν T hT u₀).hPin

/-! ## The zero control, preserved on the new carrier -/

/-- **Zero control on the pinned carrier.**  The zero supplier carries its
gated field itself as the pinned representative: continuity is the exhibit's
UNTouched-strict `boxX2Zero_hv` proof consumed as constructor data, and the
pin is reflexive a.e.  (Deliberately not `contRep := 0`: at good times the
zero-class evaluation is a `Classical.choose` constant which the frequency
measure cannot pin to the value `0` from the record, exactly the `μ = 0`
pathology the exhibit names — the gated field itself is the honest pinned
representative here.) -/
noncomputable def boxX2ZeroContRep (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    ActualLinkedBoxX2ContRep ν T 0 0 0 where
  toBox := boxX2Zero ν T
  contRep := fun t => boxX2RawRepresentative ν T 0 0 0 (boxX2Zero ν T) t
  hCont := boxX2Zero_hv ν hν T hT
  hPin :=
    ae_of_all (leiLinTimeMeasure T) fun _ => ae_of_all volume fun _ => rfl

/-- The preserved zero control row: `hv` on the new carrier for the zero
supplier — the same statement as the exhibit's `boxX2Zero_hv`, now as a
projection of the new record. -/
theorem boxX2ZeroContRep_hv (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    ∀ j : Fin 3, Continuous (fun p : ES × ℝ =>
        boxX2ContRepField ν T 0 0 0 (boxX2ZeroContRep ν hν T hT) p.2 p.1 j) :=
  (boxX2ZeroContRep ν hν T hT).hCont

/-! ## The named further leaf (acceptance ladder (b)) -/

/-- **The named further leaf — exact type of what still blocks (NOT proven
here; no wrapper premise taken).**  The consumer
`boxX2_sourceX2Budget_of_hv` attaches its conclusions to the OLD gated
field; `SourceL1X1 T v` (def `ContinuousLeiLinMildAssemblyLeaves.lean:1880`)
is an integrability statement over the PRODUCT measure
`volume.prod (volume.restrict (Icc 0 T))` of
`continuousNavierSource v v`.  The carrier's `hPin` is fiberwise a.e.
(`∀ᵐ t, =ᵐ[volume]`); upgrading it to product-measure a.e. needs the
measurability of the exceptional set (Fubini) — that upgrade alone is this
`Prop`, and it is the named leaf:

`hPin → pinProdAe` is a Fubini/measurability statement, and `pinProdAe` +
`a.e.`-invariance of `SourceL1X1`-through-`continuousNavierSource` would
give `SourceL1X1 T (b.contRep)` hypothesis-free for the suppliers, i.e. the
contRep-anchored budget theorem replacing the `hv` argument of
`boxX2_sourceX2Budget_of_hv`.  Neither leg is proven here. -/
def ActualLinkedBoxX2ContRep.pinProdAe (ν : ℝ≥0) (T B1 B2 B3 : ℝ)
    (b : ActualLinkedBoxX2ContRep ν T B1 B2 B3) : Prop :=
  ∀ j : Fin 3, ∀ᵐ x ∂(Measure.prod volume (leiLinTimeMeasure T)),
    b.contRep x.2 x.1 j =
      boxX2RawRepresentative ν T B1 B2 B3 b.toBox x.2 x.1 j

set_option pp.fullNames true in
#check @Navier.Analysis.LinkedBoxX2ContRepCarrier.ActualLinkedBoxX2ContRep
#check @Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ConstantContRep
#check @Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ConstantContRep_hv
#check @Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ConstantContRep_pin
#check @Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ZeroContRep_hv
#check @Navier.Analysis.LinkedBoxX2ContRepCarrier.continuous_fourierDatum_coord
#check @Navier.Analysis.LinkedBoxX2ContRepCarrier.fourierDatum_classPin
#check @Navier.Analysis.LinkedBoxX2ContRepCarrier.ActualLinkedBoxX2ContRep.pinProdAe

#print axioms Navier.Analysis.LinkedBoxX2ContRepCarrier.continuous_fourierDatum_coord
#print axioms Navier.Analysis.LinkedBoxX2ContRepCarrier.fourierDatum_classPin
#print axioms Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ConstantContRep
#print axioms Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ConstantContRep_hv
#print axioms Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ConstantContRep_pin
#print axioms Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ZeroContRep
#print axioms Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ZeroContRep_hv
#print axioms Navier.Analysis.LinkedBoxX2ContRepCarrier.boxX2ContRep_hv_of_record

end Navier.Analysis.LinkedBoxX2ContRepCarrier
