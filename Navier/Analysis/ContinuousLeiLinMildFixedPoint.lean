import Navier.Analysis.ContinuousLeiLinBoxSelfMap
import Navier.Analysis.ContinuousLeiLinActualContraction
import Navier.Analysis.ContinuousLeiLinActualMixedB1
import Navier.Analysis.ContinuousLeiLinActualMixedRightB1
import Navier.Analysis.ContinuousLeiLinActualMixedD3
import Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right

/-!
# Consumer-facing mild fixed-point assembly at the `ε = ν₀/16` threshold

This module assembles the actual Banach fixed point on the completed
`VelocityEvolution × Viscous-X¹` linked carrier `ActualLinkedBox ν T (2R) (2R)`
whose self-map is the concrete mild image.  Everything except three named
measurability/identity leaves is derived here from the existing sorry-free
modules:

* box-valuedness of the mild lift is obtained from
  `ContinuousLeiLinBoxSelfMap.continuousMildImage_self_map_ball_twoR_of_actualBox_joint`
  (the `ε = ν₀/16` threshold enters only through that theorem's hypothesis
  `R ≤ ν/16`);
* the slot contraction is obtained from the four joint-source polarization
  budgets (`ActualMixedB1`, `ActualMixedRightB1`, `ActualMixedD3`, and the
  right-ordered `ActualMixedD3` companion proved in
  `ContinuousLeiLinMildFixedPointD3Right`) transported through the
  distance converters of `ContinuousLeiLinActualContraction`;
* uniqueness and existence are the existing complete-box Banach consumer
  `actual_existsUnique_fixedPoint_of_lifted_coordinate_contraction`.

The record `MildAssemblyLeaves` packages exactly the leaves that are currently
produced NOWHERE in the repository for general (quotient-represented) box
elements:

1. `hjointDiag`, `hjointL`, `hjointR` — joint `(ξ,t)` a.e. strong measurability
   of the diagonal and both ordered mixed Navier sources of the everywhere
   representatives.  Existing suppliers (`RecentTailInputs`) require joint
   CONTINUITY of the driving fields, which a box element's representative does
   not carry.
2. `hmM`, `hmXm1`, `hmX1`, `hmXm1Time`, `hmX1Time`, `hmX1Int` — the
   measurability/integrability fields that lift the mild image itself into the
   completed slots.  The three pointwise fields are quantified over the
   horizon `t ∈ Icc 0 T`: at `t < 0` the backward heat multiplier explodes and
   no admissible-datum hypothesis controls it, so an unrestricted `∀ t`
   reading was a FALSE premise; the restriction weakens the travelling
   premise and is exactly the horizon the slot/section API reads.  The
   section leaves are stated for the horizon-truncated mild image
   `mildImageIcc` (equal to the mild image on `Icc 0 T`, zero off it), whose
   all-times pointwise fields are promoted from the horizon-restricted ones by
   `mildImageIcc_aestronglyMeasurable` / `mildImageIcc_integrableXm1` /
   `mildImageIcc_integrableX1`.  The only existing supplier
   (`actualLinkedContinuousMildImage_of_continuous`) again needs joint
   continuity of the mild image.
3. `hXmDiff`, `hX1Diff` — the polarization decomposition of the mild-image
   DIFFERENCE mass into the two Duhamel slots (the pointwise algebra of
   `continuousDuhamel_self_sub_self`).  Note these fields carry NO budget and
   NO contraction factor: they are the bare identity, strictly weaker than the
   conclusion.

What this file deliberately does NOT assume: no fixed point, no contraction
factor estimate, no self-map budget, and no mild-solution proposition is taken
as an input.  Its only non-derived inputs are the three leaves above, and the
threshold `R ≤ ν/16` is consumed, never re-derived.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology BigOperators
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinCommonRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeDistance
open Navier.Analysis.ContinuousLeiLinPhysicalIntegrability
open Navier.Analysis.ContinuousLeiLinBoxInterpolation
open Navier.Analysis.ContinuousLeiLinBoxProduct
open Navier.Analysis.ContinuousLeiLinBoxSelfMap
open Navier.Analysis.ContinuousLeiLinCommonContraction
open Navier.Analysis.ContinuousLeiLinActualPolarization
open Navier.Analysis.ContinuousLeiLinActualMixedSource
open Navier.Analysis.ContinuousLeiLinActualMixedJoint
open Navier.Analysis.ContinuousLeiLinActualMixedRightJoint
open Navier.Analysis.ContinuousLeiLinActualMixedB1
open Navier.Analysis.ContinuousLeiLinActualMixedRightB1
open Navier.Analysis.ContinuousLeiLinActualMixedD3
open Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinBoxD3Measurability
open Navier.Analysis.ContinuousLeiLinBoxD3Maximal
open Navier.Analysis.ContinuousLeiLinLiftDistance
open Navier.Analysis.ContinuousLeiLinActualContraction

namespace Navier.Analysis.ContinuousLeiLinMildFixedPoint

/-- The concrete mild image on the actual linked carrier: the free heat
evolution of the datum plus the self-interacting Duhamel integral driven by
the field itself.  Assumes nothing about fixed points or solutions. -/
def mildImage (ν : ℝ≥0) (hν : 0 < ν) (a : ES → ComplexSpace)
    (v : ℝ → ES → ComplexSpace) (t : ℝ) (ξ : ES) : ComplexSpace :=
  ContinuousLeiLinSelfMap.continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a v t ξ

/-! ### Horizon truncation

The completed slots read time sections only `leiLinTimeMeasure T`-a.e., i.e.
inside `Icc 0 T`; the `∀ t` pointwise fields that feed the section
constructors are a definitional requirement of `xm1Section` /
`viscousX1Section`, not a mathematical one.  The truncation below makes that
definitional requirement inhabited from horizon-restricted control: off the
horizon every truncated section value is the literal zero, whose
measurability and integrability need no hypothesis. -/

/-- The mild image truncated off the horizon: it equals `mildImage` on
`Icc 0 T` and vanishes off it. -/
def mildImageIcc (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (a : ES → ComplexSpace)
    (v : ℝ → ES → ComplexSpace) (t : ℝ) (ξ : ES) : ComplexSpace :=
  if t ∈ Icc (0 : ℝ) T then mildImage ν hν a v t ξ else 0

theorem mildImageIcc_of_mem (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (ξ : ES) :
    mildImageIcc ν hν T a v t ξ = mildImage ν hν a v t ξ := ite_eq_left ht

theorem mildImageIcc_of_not_mem (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (t : ℝ) (ht : t ∉ Icc (0 : ℝ) T) (ξ : ES) :
    mildImageIcc ν hν T a v t ξ = 0 := ite_eq_right ht

/-- Horizon-restricted pointwise measurability of the mild image promotes to
all times for the truncated image. -/
theorem mildImageIcc_aestronglyMeasurable (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      AEStronglyMeasurable (fun ξ : ES => mildImage ν hν a v t ξ i) volume)
    (t : ℝ) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : ES => mildImageIcc ν hν T a v t ξ i) volume := by
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · refine (hM t ht i).congr (ae_of_all _ fun ξ => ?_)
    exact congrArg (fun z : ComplexSpace => z i)
      (mildImageIcc_of_mem ν hν T a v t ht ξ).symm
  · have hw : (fun ξ : ES => mildImageIcc ν hν T a v t ξ i) = fun _ => (0 : ℂ) := by
      funext ξ
      rw [mildImageIcc_of_not_mem ν hν T a v t ht ξ]
      simp
    rw [hw]
    exact aestronglyMeasurable_const

/-- Horizon-restricted pointwise `X⁻¹` integrability of the mild image
promotes to all times for the truncated image. -/
theorem mildImageIcc_integrableXm1 (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (hXm1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖mildImage ν hν a v t ξ i‖))
    (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖mildImageIcc ν hν T a v t ξ i‖) := by
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · refine (hXm1 t ht i).congr (ae_of_all _ fun ξ => ?_)
    exact congrArg (fun z : ComplexSpace => ‖ξ‖⁻¹ * ‖z i‖)
      (mildImageIcc_of_mem ν hν T a v t ht ξ).symm
  · have hw : (fun ξ : ES => ‖ξ‖⁻¹ * ‖mildImageIcc ν hν T a v t ξ i‖) =
      fun _ => (0 : ℝ) := by
      funext ξ
      rw [mildImageIcc_of_not_mem ν hν T a v t ht]
      simp
    rw [hw]
    simp

/-- Horizon-restricted pointwise `X¹` integrability of the mild image
promotes to all times for the truncated image. -/
theorem mildImageIcc_integrableX1 (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (hX1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      Integrable (fun ξ : ES => ‖ξ‖ * ‖mildImage ν hν a v t ξ i‖))
    (t : ℝ) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖mildImageIcc ν hν T a v t ξ i‖) := by
  by_cases ht : t ∈ Icc (0 : ℝ) T
  · refine (hX1 t ht i).congr (ae_of_all _ fun ξ => ?_)
    exact congrArg (fun z : ComplexSpace => ‖ξ‖ * ‖z i‖)
      (mildImageIcc_of_mem ν hν T a v t ht ξ).symm
  · have hw : (fun ξ : ES => ‖ξ‖ * ‖mildImageIcc ν hν T a v t ξ i‖) =
      fun _ => (0 : ℝ) := by
      funext ξ
      rw [mildImageIcc_of_not_mem ν hν T a v t ht]
      simp
    rw [hw]
    simp

/-- The truncated and raw mild images have the same `X⁻¹` mass on the
horizon. -/
theorem coordinateXm1Mass_mildImageIcc (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    coordinateXm1Mass (mildImageIcc ν hν T a v t) =
      coordinateXm1Mass (mildImage ν hν a v t) :=
  congrArg coordinateXm1Mass
    (funext (mildImageIcc_of_mem ν hν T a v t ht))

/-- **The leaves of the mild fixed-point assembly.**  This record is the exact,
complete list of hypotheses this module does not derive.  It carries no fixed
point, no self-map property, no contraction estimate, and no numerical budget:
those are all proved downstream from it. -/
structure MildAssemblyLeaves
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R) where
  /-- The threshold consumed from the self-map/contraction doctrine. -/
  hRν : R ≤ (ν : ℝ) / 16
  /-- Leaf 1a: joint a.e. measurability of the diagonal source of every box
  element over the full horizon. -/
  hjointDiag : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (everywhereRawRepresentative ν T x.1)
          (everywhereRawRepresentative ν T x.1) p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T)))
  /-- Leaf 2a: spatial measurability of the mild image at every horizon time.
  Quantified over `t ∈ Icc 0 T` only: the backward heat multiplier
  `exp(ν ‖ξ‖² |t|)` destroys every `X^{±1}` moment at `t < 0` for a general
  admissible datum, so an unrestricted `∀ t` reading of this leaf is a false
  premise (structural witness: `a ξ i = exp(-‖ξ‖²)` at `ν = 1`, `t = -1`).
  The restriction WEAKENS the travelling premise; the horizon is exactly what
  the completed slots read. -/
  hmM : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      AEStronglyMeasurable (fun ξ : ES =>
        mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i) volume
  /-- Leaf 2b: `X⁻¹` integrability of the mild image at every horizon time
  (horizon-restricted for the same reason as leaf 2a). -/
  hmXm1 : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖)
  /-- Leaf 2c: `X¹` integrability of the mild image at every horizon time
  (horizon-restricted for the same reason as leaf 2a). -/
  hmX1 : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R), ∀ t ∈ Icc (0 : ℝ) T, ∀ i,
      Integrable (fun ξ : ES => ‖ξ‖ *
        ‖mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ i‖)
  /-- Leaf 2d: strong measurability of the `X⁻¹`-valued time section of the
  horizon-truncated mild image. -/
  hmXm1Time : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable
        (xm1Section (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1))
          (mildImageIcc_aestronglyMeasurable ν hν T a
            (everywhereRawRepresentative ν T x.1) (hmM x))
          (mildImageIcc_integrableXm1 ν hν T a
            (everywhereRawRepresentative ν T x.1) (hmXm1 x)))
        (leiLinTimeMeasure T)
  /-- Leaf 2e: strong measurability of the viscous `X¹`-valued time section of
  the horizon-truncated mild image. -/
  hmX1Time : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable
        (viscousX1Section (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1))
          (mildImageIcc_aestronglyMeasurable ν hν T a
            (everywhereRawRepresentative ν T x.1) (hmM x))
          (mildImageIcc_integrableX1 ν hν T a
            (everywhereRawRepresentative ν T x.1) (hmX1 x)) ν)
        (leiLinTimeMeasure T)
  /-- Leaf 2f: time integrability of the horizon-truncated mild image's `X¹`
  mass. -/
  hmX1Int : ∀ x : ActualLinkedBox ν T (2 * R) (2 * R),
      Integrable (fun t : ℝ => coordinateX1Mass
        (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) t))
        (leiLinTimeMeasure T)
  /-- Leaf 1b: joint a.e. measurability of the LEFT ordered mixed source
  `(rep x − rep y, rep x)`. -/
  hjointL : ∀ x y : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (commonRepresentativeDifference ν T x.1 y.1)
          (everywhereRawRepresentative ν T x.1) p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T)))
  /-- Leaf 1c: joint a.e. measurability of the RIGHT ordered mixed source
  `(rep y, rep x − rep y)`. -/
  hjointR : ∀ x y : ActualLinkedBox ν T (2 * R) (2 * R),
      AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (everywhereRawRepresentative ν T y.1)
          (commonRepresentativeDifference ν T x.1 y.1) p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T)))
  /-- Leaf 3a: the polarization decomposition of the `X⁻¹` mass of the mild
  difference into the two Duhamel slots, a.e. in time.  Carries no budget. -/
  hXmDiff : ∀ x y : ActualLinkedBox ν T (2 * R) (2 * R),
      ∀ᵐ t ∂leiLinTimeMeasure T,
        coordinateXm1Mass (fun ξ : ES =>
            mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ -
              mildImage ν hν a (everywhereRawRepresentative ν T y.1) t ξ) ≤
          coordinateXm1Mass (continuousDuhamel (ν : ℝ)
            (commonRepresentativeDifference ν T x.1 y.1)
            (everywhereRawRepresentative ν T x.1) t) +
            coordinateXm1Mass (continuousDuhamel (ν : ℝ)
              (everywhereRawRepresentative ν T y.1)
              (commonRepresentativeDifference ν T x.1 y.1) t)
  /-- Leaf 3b: the same decomposition for the viscous `X¹` spacetime budget.
  Carries no budget. -/
  hX1Diff : ∀ x y : ActualLinkedBox ν T (2 * R) (2 * R),
      (ν : ℝ) * ∫ t, coordinateX1Mass (fun ξ : ES =>
          mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ -
            mildImage ν hν a (everywhereRawRepresentative ν T y.1) t ξ)
          ∂(volume.restrict (Icc (0 : ℝ) T)) ≤
        (ν : ℝ) * ∫ t, coordinateX1Mass (continuousDuhamel (ν : ℝ)
            (commonRepresentativeDifference ν T x.1 y.1)
            (everywhereRawRepresentative ν T x.1) t)
          ∂(volume.restrict (Icc (0 : ℝ) T)) +
          (ν : ℝ) * ∫ t, coordinateX1Mass (continuousDuhamel (ν : ℝ)
            (everywhereRawRepresentative ν T y.1)
            (commonRepresentativeDifference ν T x.1 y.1) t)
          ∂(volume.restrict (Icc (0 : ℝ) T))

/-- The two radii of the completed box obeyed by the mild image, from the one
diagonal joint-source fact and the `ε = ν₀/16` threshold.  Assumes no fixed
point and derives no new budget: it is the existing joint-source self-map
theorem consumed verbatim. -/
theorem selfMapEstimate (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    (∀ t ∈ Icc (0 : ℝ) T,
        coordinateXm1Mass (mildImage ν hν a
          (everywhereRawRepresentative ν T x.1) t) ≤ 2 * R) ∧
      (∫ t in Icc (0 : ℝ) T, coordinateX1Mass (mildImage ν hν a
          (everywhereRawRepresentative ν T x.1) t)) ≤ 2 * (ν : ℝ)⁻¹ * R := by
  have hR : 0 ≤ R := le_trans (coordinateXm1Mass_nonneg a) haR
  exact continuousMildImage_self_map_ball_twoR_of_actualBox_joint
    ν hν R T hR hT L.hRν a haM ha ha1 haR x (L.hjointDiag x)

/-- The pointwise budget of `selfMapEstimate` transported to the truncated
mild image: the two agree on the horizon. -/
theorem selfMapEstimate_Icc (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (mildImageIcc ν hν T a
        (everywhereRawRepresentative ν T x.1) t) ≤ 2 * R := by
  intro t ht
  rw [coordinateXm1Mass_mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) t ht]
  exact ((selfMapEstimate ν hν T R hT a haM ha ha1 haR L x).1) t ht

/-- The (horizon-truncated) mild image of a box element, lifted to the
completed linked carrier by the leaf measurability fields and the self-map
budget.  Assumes no fixed point. -/
def mildLift (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) : ActualLinkedCarrier ν T :=
  actualLinkedOfRaw ν T (2 * R)
    (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1))
    (mildImageIcc_aestronglyMeasurable ν hν T a
      (everywhereRawRepresentative ν T x.1) (L.hmM x))
    (mildImageIcc_integrableXm1 ν hν T a
      (everywhereRawRepresentative ν T x.1) (L.hmXm1 x))
    (mildImageIcc_integrableX1 ν hν T a
      (everywhereRawRepresentative ν T x.1) (L.hmX1 x))
    (L.hmXm1Time x) (L.hmX1Time x)
    (selfMapEstimate_Icc ν hν T R hT a haM ha ha1 haR L x) (L.hmX1Int x)

/-- The lifted mild image lies in the same completed box: the `X⁻¹` radius
from the essential supremum of the pointwise budget, the viscous `X¹` radius
from the integrated budget multiplied by `ν`.  This is the DERIVED self-map
property, not an assumption. -/
theorem mildLift_mem (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    ‖(mildLift ν hν T R hT a haM ha ha1 haR L x).1.fst‖ ≤ 2 * R ∧
      ‖(mildLift ν hν T R hT a haM ha ha1 haR L x).1.snd‖ ≤ 2 * R := by
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hR : 0 ≤ R := le_trans (coordinateXm1Mass_nonneg a) haR
  have hb := selfMapEstimate ν hν T R hT a haM ha ha1 haR L x
  have hbIcc := selfMapEstimate_Icc ν hν T R hT a haM ha ha1 haR L x
  set u := mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) with hu_def
  set hMw := mildImageIcc_aestronglyMeasurable ν hν T a
    (everywhereRawRepresentative ν T x.1) (L.hmM x) with hMw_def
  set hXm1w := mildImageIcc_integrableXm1 ν hν T a
    (everywhereRawRepresentative ν T x.1) (L.hmXm1 x) with hXm1w_def
  set hX1w := mildImageIcc_integrableX1 ν hν T a
    (everywhereRawRepresentative ν T x.1) (L.hmX1 x) with hX1w_def
  refine ⟨?_, ?_⟩
  · have key : (mildLift ν hν T R hT a haM ha ha1 haR L x).1.fst =
      toXm1TimeSlot u hMw hXm1w T (2 * R) (L.hmXm1Time x) hbIcc := rfl
    rw [key]
    have hpoint : ∀ᵐ t ∂leiLinTimeMeasure T,
        ‖(toXm1TimeSlot u hMw hXm1w T (2 * R) (L.hmXm1Time x) hbIcc :
          ℝ → Xm1Spatial) t‖ ≤ 2 * R := by
      filter_upwards [coeFn_toXm1TimeSlot u hMw hXm1w T (2 * R)
          (L.hmXm1Time x) hbIcc,
        ae_restrict_mem isClosed_Icc.measurableSet] with t ht htI
      rw [ht, norm_xm1Section]
      exact hbIcc t htI
    have h := Lp.norm_le_of_ae_bound (f :=
        toXm1TimeSlot u hMw hXm1w T (2 * R) (L.hmXm1Time x) hbIcc)
      (mul_nonneg zero_le_two hR) hpoint
    simpa using h
  · have key : (mildLift ν hν T R hT a haM ha ha1 haR L x).1.snd =
      toViscousX1TimeSlot u hMw hX1w ν T (L.hmX1Time x)
        (L.hmX1Int x) := rfl
    rw [key, L1.norm_eq_integral_norm]
    have hrew : (∫ t, ‖(toViscousX1TimeSlot u hMw hX1w ν T
          (L.hmX1Time x) (L.hmX1Int x) : ℝ → ViscousX1Spatial ν) t‖
          ∂leiLinTimeMeasure T) =
        ∫ t, (ν : ℝ) * coordinateX1Mass (u t) ∂leiLinTimeMeasure T := by
      apply integral_congr_ae
      filter_upwards [coeFn_toViscousX1TimeSlot u hMw hX1w ν T
          (L.hmX1Time x) (L.hmX1Int x)] with t ht
      rw [ht, norm_viscousX1Section]
    rw [hrew, integral_const_mul]
    have hIcc : (∫ t, coordinateX1Mass (u t) ∂leiLinTimeMeasure T) =
        ∫ t in Icc (0 : ℝ) T,
          coordinateX1Mass (mildImage ν hν a
            (everywhereRawRepresentative ν T x.1) t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
      exact congrArg coordinateX1Mass
        (funext (mildImageIcc_of_mem ν hν T a
          (everywhereRawRepresentative ν T x.1) t ht))
    rw [hIcc]
    refine (mul_le_mul_of_nonneg_left hb.2 hνR.le).trans (le_of_eq ?_)
    field_simp [hνR.ne']

/-- The mild self-map on the completed box.  It is not assumed to map into the
box nor to be a contraction; both are derived facts (`mildLift_mem`,
`mildLift_contraction`). -/
def actualMildSelfMap (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR) :
    ActualLinkedBox ν T (2 * R) (2 * R) →
      ActualLinkedBox ν T (2 * R) (2 * R) :=
  fun x => ⟨mildLift ν hν T R hT a haM ha ha1 haR L x,
    mildLift_mem ν hν T R hT a haM ha ha1 haR L x⟩

/-- **The `ε = ν₀/16` slot contraction of the mild self-map.**  Consuming the
four joint-source polarization budgets (two pointwise `X⁻¹`, two spacetime
`X¹`, the right-ordered spacetime one being
`ContinuousLeiLinMildFixedPointD3Right`), the threshold arithmetic
`6 · ν⁻¹R ≤ 3/8`, and the distance converter
`ContinuousLeiLinActualContraction.actualLinkedOfRaw_coordinate_sum_le`, the
sum of the two completed slot distances contracts with factor `3/4`.  No
fixed-point statement is assumed. -/
theorem mildLift_contraction (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR)
    (x y : ActualLinkedBox ν T (2 * R) (2 * R)) :
    dist (mildLift ν hν T R hT a haM ha ha1 haR L x).1.fst
        (mildLift ν hν T R hT a haM ha ha1 haR L y).1.fst +
      dist (mildLift ν hν T R hT a haM ha ha1 haR L x).1.snd
        (mildLift ν hν T R hT a haM ha ha1 haR L y).1.snd ≤
      (3 / 4 : ℝ) *
        (dist x.1.1.fst y.1.1.fst + dist x.1.1.snd y.1.1.snd) := by
  set D : ℝ := dist x.1.1.fst y.1.1.fst + dist x.1.1.snd y.1.1.snd
  have hD : 0 ≤ D := by positivity
  have hR : 0 ≤ R := le_trans (coordinateXm1Mass_nonneg a) haR
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hνinvR : (ν : ℝ)⁻¹ * R ≤ 1 / 16 := by
    refine (mul_le_mul_of_nonneg_left L.hRν (inv_nonneg.mpr hνR.le)).trans
      (le_of_eq ?_)
    field_simp [hνR.ne']
  have hcoef : 6 * ((ν : ℝ)⁻¹ * R) ≤ 3 / 8 := by linarith
  have hprefixL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (commonRepresentativeDifference ν T x.1 y.1)
          (everywhereRawRepresentative ν T x.1) p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))) :=
    (L.hjointL x y).mono_measure
      (Measure.prod_mono le_rfl
        (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
  have hprefixR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (everywhereRawRepresentative ν T y.1)
          (commonRepresentativeDifference ν T x.1 y.1) p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))) :=
    (L.hjointR x y).mono_measure
      (Measure.prod_mono le_rfl
        (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl))
  have hslotL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      coordinateXm1Mass (continuousDuhamel (ν : ℝ)
        (commonRepresentativeDifference ν T x.1 y.1)
        (everywhereRawRepresentative ν T x.1) t) ≤
        3 * (ν : ℝ)⁻¹ * R * D :=
    coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance_of_jointSource
      ν hν T R t hR ht x.1 y.1 x (hprefixL t ht)
  have hslotR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      coordinateXm1Mass (continuousDuhamel (ν : ℝ)
        (everywhereRawRepresentative ν T y.1)
        (commonRepresentativeDifference ν T x.1 y.1) t) ≤
        3 * (ν : ℝ)⁻¹ * R * D :=
    coordinateXm1Mass_continuousDuhamel_right_sub_le_linked_distance_of_jointSource
      ν hν T R t hR ht x.1 y.1 y (hprefixR t ht)
  have hXm : ∀ᵐ t ∂leiLinTimeMeasure T,
      coordinateXm1Mass (fun ξ : ES =>
          mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) t ξ -
            mildImageIcc ν hν T a (everywhereRawRepresentative ν T y.1) t ξ) ≤
        (3 / 8 : ℝ) * D := by
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet, L.hXmDiff x y]
      with t ht hdiff
    have hconv : (fun ξ : ES => mildImageIcc ν hν T a
          (everywhereRawRepresentative ν T x.1) t ξ -
            mildImageIcc ν hν T a (everywhereRawRepresentative ν T y.1) t ξ) =
        (fun ξ : ES => mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ -
            mildImage ν hν a (everywhereRawRepresentative ν T y.1) t ξ) :=
      funext fun ξ => by
        rw [mildImageIcc_of_mem ν hν T a (everywhereRawRepresentative ν T x.1) t ht ξ,
          mildImageIcc_of_mem ν hν T a (everywhereRawRepresentative ν T y.1) t ht ξ]
    rw [hconv]
    refine hdiff.trans ?_
    refine (add_le_add (hslotL t ht) (hslotR t ht)).trans ?_
    have hsum : 3 * (ν : ℝ)⁻¹ * R * D + 3 * (ν : ℝ)⁻¹ * R * D =
        6 * ((ν : ℝ)⁻¹ * R) * D := by ring
    rw [hsum]
    exact mul_le_mul_of_nonneg_right hcoef hD
  have hintL : (∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel (ν : ℝ)
      (commonRepresentativeDifference ν T x.1 y.1)
      (everywhereRawRepresentative ν T x.1) t)) ≤
      3 * (ν : ℝ)⁻¹ * ((ν : ℝ)⁻¹ * R) * D :=
    integral_coordinateX1Mass_continuousDuhamel_sub_left_le_linked_distance_of_jointSource
      ν hν T R hR hT x.1 y.1 x (L.hjointL x y)
  have hintR : (∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel (ν : ℝ)
      (everywhereRawRepresentative ν T y.1)
      (commonRepresentativeDifference ν T x.1 y.1) t)) ≤
      3 * (ν : ℝ)⁻¹ * ((ν : ℝ)⁻¹ * R) * D :=
    integral_coordinateX1Mass_continuousDuhamel_right_sub_le_linked_distance_of_jointSource
      ν hν T R hT hR x.1 y.1 y (L.hjointR x y)
  have hX1 : (ν : ℝ) * ∫ t, coordinateX1Mass (fun ξ : ES =>
        mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) t ξ -
          mildImageIcc ν hν T a (everywhereRawRepresentative ν T y.1) t ξ)
        ∂leiLinTimeMeasure T ≤ (3 / 8 : ℝ) * D := by
    have htr : (∫ t, coordinateX1Mass (fun ξ : ES =>
          mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1) t ξ -
            mildImageIcc ν hν T a (everywhereRawRepresentative ν T y.1) t ξ)
          ∂(leiLinTimeMeasure T)) =
        (∫ t, coordinateX1Mass (fun ξ : ES =>
            mildImage ν hν a (everywhereRawRepresentative ν T x.1) t ξ -
              mildImage ν hν a (everywhereRawRepresentative ν T y.1) t ξ)
          ∂(volume.restrict (Icc (0 : ℝ) T))) := by
      unfold leiLinTimeMeasure
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
      refine congrArg coordinateX1Mass (funext fun ξ => ?_)
      rw [mildImageIcc_of_mem ν hν T a (everywhereRawRepresentative ν T x.1) t ht ξ,
        mildImageIcc_of_mem ν hν T a (everywhereRawRepresentative ν T y.1) t ht ξ]
    rw [htr]
    refine (L.hX1Diff x y).trans ?_
    have hDLν : (ν : ℝ) * ∫ t, coordinateX1Mass (continuousDuhamel (ν : ℝ)
          (commonRepresentativeDifference ν T x.1 y.1)
          (everywhereRawRepresentative ν T x.1) t)
          ∂leiLinTimeMeasure T ≤ 3 * ((ν : ℝ)⁻¹ * R) * D :=
      (mul_le_mul_of_nonneg_left hintL hνR.le).trans
        (le_of_eq (by field_simp [hνR.ne']))
    have hDRν : (ν : ℝ) * ∫ t, coordinateX1Mass (continuousDuhamel (ν : ℝ)
          (everywhereRawRepresentative ν T y.1)
          (commonRepresentativeDifference ν T x.1 y.1) t)
          ∂leiLinTimeMeasure T ≤ 3 * ((ν : ℝ)⁻¹ * R) * D :=
      (mul_le_mul_of_nonneg_left hintR hνR.le).trans
        (le_of_eq (by field_simp [hνR.ne']))
    refine add_le_add hDLν hDRν |>.trans ?_
    have hsum : 3 * ((ν : ℝ)⁻¹ * R) * D + 3 * ((ν : ℝ)⁻¹ * R) * D =
        6 * ((ν : ℝ)⁻¹ * R) * D := by ring
    rw [hsum]
    exact mul_le_mul_of_nonneg_right hcoef hD
  exact (actualLinkedOfRaw_coordinate_sum_le ν T (2 * R) (2 * R)
      ((3 / 8 : ℝ) * D) ((3 / 8 : ℝ) * D) (mul_nonneg (by positivity) hD)
      (mildImageIcc ν hν T a (everywhereRawRepresentative ν T x.1))
      (mildImageIcc ν hν T a (everywhereRawRepresentative ν T y.1))
      (mildImageIcc_aestronglyMeasurable ν hν T a
        (everywhereRawRepresentative ν T x.1) (L.hmM x))
      (mildImageIcc_aestronglyMeasurable ν hν T a
        (everywhereRawRepresentative ν T y.1) (L.hmM y))
      (mildImageIcc_integrableXm1 ν hν T a
        (everywhereRawRepresentative ν T x.1) (L.hmXm1 x))
      (mildImageIcc_integrableXm1 ν hν T a
        (everywhereRawRepresentative ν T y.1) (L.hmXm1 y))
      (mildImageIcc_integrableX1 ν hν T a
        (everywhereRawRepresentative ν T x.1) (L.hmX1 x))
      (mildImageIcc_integrableX1 ν hν T a
        (everywhereRawRepresentative ν T y.1) (L.hmX1 y))
      (L.hmXm1Time x) (L.hmXm1Time y) (L.hmX1Time x) (L.hmX1Time y)
      (selfMapEstimate_Icc ν hν T R hT a haM ha ha1 haR L x)
      (selfMapEstimate_Icc ν hν T R hT a haM ha ha1 haR L y)
      (L.hmX1Int x) (L.hmX1Int y) hXm hX1).trans
    (le_of_eq (by ring))

/-- **The mild fixed point exists and is unique on the completed linked box,
at the `ε = ν₀/16` threshold.**  The self-map `actualMildSelfMap` is built
from the concrete mild image, its box property is derived (`mildLift_mem`),
and its contraction is derived (`mildLift_contraction`); the only additional
input is the `MildAssemblyLeaves` record, whose fields are local
measurability/integrability facts and the bare polarization identity.  The
fixed point is a velocity-type mild solution: `actualMildSelfMap ... x = x`
states equality of completed linked carriers, i.e. equality of both slot
distances to zero.  The downstream pointwise PDE and pressure clauses are NOT
part of this theorem's statement. -/
theorem actual_existsUnique_mildFixedPoint (ν : ℝ≥0) (hν : 0 < ν)
    (T R : ℝ) (hT : 0 ≤ T) (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (L : MildAssemblyLeaves ν hν T R hT a haM ha ha1 haR) :
    ∃ x : ActualLinkedBox ν T (2 * R) (2 * R),
      actualMildSelfMap ν hν T R hT a haM ha ha1 haR L x = x ∧
        ∀ y : ActualLinkedBox ν T (2 * R) (2 * R),
          actualMildSelfMap ν hν T R hT a haM ha ha1 haR L y = y → y = x := by
  have hR : 0 ≤ R := le_trans (coordinateXm1Mass_nonneg a) haR
  refine actual_existsUnique_fixedPoint_of_lifted_coordinate_contraction
    ν T (2 * R) (mul_nonneg zero_le_two hR)
    (actualMildSelfMap ν hν T R hT a haM ha ha1 haR L)
    (3 / 4 : ℝ≥0) ?_ ?_
  · norm_cast
    norm_num
  · intro u v
    exact mildLift_contraction ν hν T R hT a haM ha ha1 haR L u v

end Navier.Analysis.ContinuousLeiLinMildFixedPoint

set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImage
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPoint.MildAssemblyLeaves
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPoint.actualMildSelfMap
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPoint.actual_existsUnique_mildFixedPoint

set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc
set_option pp.fullNames true in
#check @Navier.Analysis.ContinuousLeiLinMildFixedPoint.selfMapEstimate_Icc

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.MildAssemblyLeaves
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildLift
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.actualMildSelfMap
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_of_mem
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_of_not_mem
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_aestronglyMeasurable
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_integrableXm1
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildImageIcc_integrableX1
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.coordinateXm1Mass_mildImageIcc
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.selfMapEstimate_Icc
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.selfMapEstimate
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildLift_mem
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.mildLift_contraction
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPoint.actual_existsUnique_mildFixedPoint
