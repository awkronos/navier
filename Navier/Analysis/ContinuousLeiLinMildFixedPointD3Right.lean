import Navier.Analysis.ContinuousLeiLinActualMixedD3
import Navier.Analysis.ContinuousLeiLinActualMixedRightJoint

/-!
# Right-ordered mixed spacetime `X¹` estimate and mixed-integrability companions

`ContinuousLeiLinActualMixedD3` packaged the LEFT polarization slot
`continuousDuhamel ν (rep x − rep y) (rep z)` from one joint-source fact.  The
mild-difference identity decomposes `mild u − mild v` into the LEFT slot
`Duhamel(u−v, u)` and the RIGHT slot `Duhamel(v, u−v)`; the right-ordered slot
had no joint-source packaging anywhere in the repo (only the raw
`integral_coordinateX1Mass_continuousDuhamel_right_sub_le_linked_distance`
with twelve explicit inputs existed).  This module supplies the missing
right-ordered packaging, plus the two mixed-Duhamel time-`X¹` integrability
companions (left and right orders) that the fixed-point assembly needs to
chain the `L¹_t` distance converter through the sum of the two slots.

What this file deliberately does NOT assume: no fixed point, no self-map, no
contraction, and no mild-solution proposition.  Its only structural input is
the a.e. joint measurability of the single ordered source it estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

open MeasureTheory Set Filter Topology BigOperators
open scoped NNReal ENNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinMixedX1
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeDistance
open Navier.Analysis.ContinuousLeiLinPhysicalIntegrability
open Navier.Analysis.ContinuousLeiLinBoxInterpolation
open Navier.Analysis.ContinuousLeiLinCommonContraction
open Navier.Analysis.ContinuousLeiLinActualPolarization
open Navier.Analysis.ContinuousLeiLinActualMixedSource
open Navier.Analysis.ContinuousLeiLinActualMixedJoint
open Navier.Analysis.ContinuousLeiLinActualMixedRightJoint
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinBoxD3Measurability
open Navier.Analysis.ContinuousLeiLinBoxD3Maximal

namespace Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right

/-- The right-ordered mixed source `(rep z, rep x − rep y)` is jointly `a.e.`
measurable in `(ξ,t)` and `Integrable` against the `X⁻¹` weight on the product;
this discharges every fixed-time and Fubini input of the right `X¹` maximal
estimate below. -/
theorem integrable_coordinateX1Mass_continuousDuhamel_right_sub_of_jointSource
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T) (_hR : 0 ≤ R)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    Integrable (fun t : ℝ => coordinateX1Mass (continuousDuhamel (ν : ℝ)
      (everywhereRawRepresentative ν T z.1)
      (commonRepresentativeDifference ν T x y) t))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T z.1
  let w : ℝ → ES → ComplexSpace := commonRepresentativeDifference ν T x y
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hcoord (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u w p.2 p.1 i) (volume.prod μ) :=
    continuousNavierSource_coord_aestronglyMeasurable u w 0 T
      (by simpa [u, w, μ] using hjoint) i
  have hDjoint (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel (ν : ℝ) u w p.2 p.1 i) (volume.prod μ) :=
    continuousDuhamel_coord_joint_aestronglyMeasurable (ν : ℝ) T u w i (hcoord i)
  have hsource := integrable_weightedContinuousNavierSource_right_sub_of_actualBox
    ν hν T R T ⟨hT, le_rfl⟩ x y z hjoint
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_right_sub_coord_of_actualBox
      ν hν T R T ⟨hT, le_rfl⟩ x y z hjoint i
  have hg (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource u w s ξ i)) μ := by
    apply (hsourceCoord i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg
      (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
  have hJ (i : Fin 3) : AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u w p.2 p.1 i‖))
      (volume.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod μ) by fun_prop).mul (hcoord i).norm).aemeasurable)
  obtain ⟨hs1, hb0⟩ := continuousNavierSource_right_sub_fixedTime_inputs_of_actualBox
    ν hν T (2 * R) (2 * R) x y z
  have hW1 (i : Fin 3) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) : AEMeasurable
      (fun p : ES × ℝ => mixedKernelFun u w i (ν : ℝ) p.1 r p.2)
      (volume.prod μ) := by
    change AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal ‖continuousNavierSource u w p.2 p.1 i‖ *
        (if p.2 ≤ r then ENNReal.ofReal
          (‖p.1‖ * Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (r - p.2)))) else 0))
      (volume.prod μ)
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcoord i).norm.aemeasurable).mul
        ((Measurable.ite (measurableSet_le measurable_snd measurable_const)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hW (i : Fin 3) : AEMeasurable
      (fun q : ℝ × (ES × ℝ) => mixedKernelFun u w i (ν : ℝ) q.2.1 q.1 q.2.2)
      (μ.prod (volume.prod μ)) := by
    have hcoord3 : AEStronglyMeasurable (fun q : ℝ × (ES × ℝ) =>
        continuousNavierSource u w q.2.2 q.2.1 i) (μ.prod (volume.prod μ)) :=
      (hcoord i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    change AEMeasurable (fun q : ℝ × (ES × ℝ) =>
      ENNReal.ofReal ‖continuousNavierSource u w q.2.2 q.2.1 i‖ *
        (if q.2.2 ≤ q.1 then ENNReal.ofReal
          (‖q.2.1‖ * Real.exp (-((ν : ℝ) * ‖q.2.1‖ ^ 2 *
            (q.1 - q.2.2)))) else 0)) (μ.prod (volume.prod μ))
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      hcoord3.norm.aemeasurable).mul
        ((Measurable.ite
          (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hDfacts (i : Fin 3) := continuousDuhamel_X1_integrability
    u w (ν : ℝ) T i hνR (hDjoint i) (hW1 i) (hW i)
      (fun s _ => hb0 s i) (hg i) (hJ i)
  have hD0 (i : Fin 3) := (hDfacts i).1
  unfold coordinateX1Mass
  exact integrable_finsetSum
    (f := fun i (t : ℝ) => normX1 (fun ξ : ES =>
      continuousDuhamel (ν : ℝ) u w t ξ i)) Finset.univ (fun i _ => hD0 i)

/-- The left-ordered companion.  `ContinuousLeiLinActualMixedD3` proved the
estimate but kept the mixed-Duhamel time integrability inside its proof body;
the assembly needs it as a conclusion, so the maximal-regularity segment is
replayed here for the left order. -/
theorem integrable_coordinateX1Mass_continuousDuhamel_sub_left_of_jointSource
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T) (_hR : 0 ≤ R)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    Integrable (fun t : ℝ => coordinateX1Mass (continuousDuhamel (ν : ℝ)
      (commonRepresentativeDifference ν T x y)
      (everywhereRawRepresentative ν T z.1) t))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  let w : ℝ → ES → ComplexSpace := commonRepresentativeDifference ν T x y
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T z.1
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hcoord (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource w u p.2 p.1 i) (volume.prod μ) :=
    continuousNavierSource_coord_aestronglyMeasurable w u 0 T
      (by simpa [w, u, μ] using hjoint) i
  have hDjoint (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel (ν : ℝ) w u p.2 p.1 i) (volume.prod μ) :=
    continuousDuhamel_coord_joint_aestronglyMeasurable (ν : ℝ) T w u i (hcoord i)
  have hsource := integrable_weightedContinuousNavierSource_sub_left_of_actualBox
    ν hν T R T ⟨hT, le_rfl⟩ x y z hjoint
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_sub_left_coord_of_actualBox
      ν hν T R T ⟨hT, le_rfl⟩ x y z hjoint i
  have hg (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource w u s ξ i)) μ := by
    apply (hsourceCoord i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg
      (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
  have hJ (i : Fin 3) : AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource w u p.2 p.1 i‖))
      (volume.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod μ) by fun_prop).mul (hcoord i).norm).aemeasurable)
  obtain ⟨hs1, hb0⟩ := continuousNavierSource_sub_left_fixedTime_inputs_of_actualBox
    ν hν T (2 * R) (2 * R) x y z
  have hW1 (i : Fin 3) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) : AEMeasurable
      (fun p : ES × ℝ => mixedKernelFun w u i (ν : ℝ) p.1 r p.2)
      (volume.prod μ) := by
    change AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal ‖continuousNavierSource w u p.2 p.1 i‖ *
        (if p.2 ≤ r then ENNReal.ofReal
          (‖p.1‖ * Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (r - p.2)))) else 0))
      (volume.prod μ)
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcoord i).norm.aemeasurable).mul
        ((Measurable.ite (measurableSet_le measurable_snd measurable_const)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hW (i : Fin 3) : AEMeasurable
      (fun q : ℝ × (ES × ℝ) => mixedKernelFun w u i (ν : ℝ) q.2.1 q.1 q.2.2)
      (μ.prod (volume.prod μ)) := by
    have hcoord3 : AEStronglyMeasurable (fun q : ℝ × (ES × ℝ) =>
        continuousNavierSource w u q.2.2 q.2.1 i) (μ.prod (volume.prod μ)) :=
      (hcoord i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    change AEMeasurable (fun q : ℝ × (ES × ℝ) =>
      ENNReal.ofReal ‖continuousNavierSource w u q.2.2 q.2.1 i‖ *
        (if q.2.2 ≤ q.1 then ENNReal.ofReal
          (‖q.2.1‖ * Real.exp (-((ν : ℝ) * ‖q.2.1‖ ^ 2 *
            (q.1 - q.2.2)))) else 0)) (μ.prod (volume.prod μ))
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      hcoord3.norm.aemeasurable).mul
        ((Measurable.ite
          (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hDfacts (i : Fin 3) := continuousDuhamel_X1_integrability
    w u (ν : ℝ) T i hνR (hDjoint i) (hW1 i) (hW i)
      (fun s _ => hb0 s i) (hg i) (hJ i)
  have hD0 (i : Fin 3) := (hDfacts i).1
  unfold coordinateX1Mass
  exact integrable_finsetSum
    (f := fun i (t : ℝ) => normX1 (fun ξ : ES =>
      continuousDuhamel (ν : ℝ) w u t ξ i)) Finset.univ (fun i _ => hD0 i)

/-- **Right-ordered mixed spacetime `X¹` budget from one joint source.**  The
companion of
`ContinuousLeiLinActualMixedD3.integral_coordinateX1Mass_continuousDuhamel_sub_left_le_linked_distance_of_jointSource`
for the ordering `continuousDuhamel ν (rep z) (rep x − rep y)` required by the
second polarization half of the mild difference.  -/
theorem integral_coordinateX1Mass_continuousDuhamel_right_sub_le_linked_distance_of_jointSource
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    (∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel (ν : ℝ)
      (everywhereRawRepresentative ν T z.1)
      (commonRepresentativeDifference ν T x y) t)) ≤
      3 * (ν : ℝ)⁻¹ * ((ν : ℝ)⁻¹ * R) *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T z.1
  let w : ℝ → ES → ComplexSpace := commonRepresentativeDifference ν T x y
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hcoord (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u w p.2 p.1 i) (volume.prod μ) :=
    continuousNavierSource_coord_aestronglyMeasurable u w 0 T
      (by simpa [u, w, μ] using hjoint) i
  have hDjoint (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel (ν : ℝ) u w p.2 p.1 i) (volume.prod μ) :=
    continuousDuhamel_coord_joint_aestronglyMeasurable (ν : ℝ) T u w i (hcoord i)
  have hsource := integrable_weightedContinuousNavierSource_right_sub_of_actualBox
    ν hν T R T ⟨hT, le_rfl⟩ x y z hjoint
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_right_sub_coord_of_actualBox
      ν hν T R T ⟨hT, le_rfl⟩ x y z hjoint i
  have hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u w s ξ)) μ := by
    apply hsource.integral_norm_prod_right.congr
    filter_upwards with s
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (by
      unfold complexEuclideanNorm
      exact norm_nonneg _))
  have hg (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource u w s ξ i)) μ := by
    apply (hsourceCoord i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg
      (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
  have hJ (i : Fin 3) : AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u w p.2 p.1 i‖))
      (volume.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod μ) by fun_prop).mul (hcoord i).norm).aemeasurable)
  obtain ⟨hs1, hb0⟩ := continuousNavierSource_right_sub_fixedTime_inputs_of_actualBox
    ν hν T (2 * R) (2 * R) x y z
  have hW1 (i : Fin 3) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) : AEMeasurable
      (fun p : ES × ℝ => mixedKernelFun u w i (ν : ℝ) p.1 r p.2)
      (volume.prod μ) := by
    change AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal ‖continuousNavierSource u w p.2 p.1 i‖ *
        (if p.2 ≤ r then ENNReal.ofReal
          (‖p.1‖ * Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (r - p.2)))) else 0))
      (volume.prod μ)
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcoord i).norm.aemeasurable).mul
        ((Measurable.ite (measurableSet_le measurable_snd measurable_const)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hW (i : Fin 3) : AEMeasurable
      (fun q : ℝ × (ES × ℝ) => mixedKernelFun u w i (ν : ℝ) q.2.1 q.1 q.2.2)
      (μ.prod (volume.prod μ)) := by
    have hcoord3 : AEStronglyMeasurable (fun q : ℝ × (ES × ℝ) =>
        continuousNavierSource u w q.2.2 q.2.1 i) (μ.prod (volume.prod μ)) :=
      (hcoord i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    change AEMeasurable (fun q : ℝ × (ES × ℝ) =>
      ENNReal.ofReal ‖continuousNavierSource u w q.2.2 q.2.1 i‖ *
        (if q.2.2 ≤ q.1 then ENNReal.ofReal
          (‖q.2.1‖ * Real.exp (-((ν : ℝ) * ‖q.2.1‖ ^ 2 *
            (q.1 - q.2.2)))) else 0)) (μ.prod (volume.prod μ))
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      hcoord3.norm.aemeasurable).mul
        ((Measurable.ite
          (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hDfacts (i : Fin 3) := continuousDuhamel_X1_integrability
    u w (ν : ℝ) T i hνR (hDjoint i) (hW1 i) (hW i)
      (fun s _ => hb0 s i) (hg i) (hJ i)
  have hD0 (i : Fin 3) := (hDfacts i).1
  have hDξ (i : Fin 3) := (hDfacts i).2
  obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T (2 * R) (2 * R) z
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  have hw0 : ∀ r i, Integrable (fun η : ES => ‖w r η i‖) := fun r i =>
    integrable_norm_of_integrable_Xm1_X1 (fun η : ES => w r η i)
      (by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hwm1 r i)
      (by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hw1 r i)
  have hfull := integrable_coordinateX0Mass_sub_mul_everywhere
    ν hν T (2 * R) (2 * R) x y z
  have hprod : Integrable (fun r => coordinateX0Mass (u r) * coordinateX0Mass (w r))
      (leiLinTimeMeasure T) := by
    apply hfull.congr
    filter_upwards with r
    simp only [w, u]
    exact mul_comm _ _
  have hgeneral :=
    integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product_ae
      u w (ν : ℝ) T hνR hD0 hDξ (fun i r hr => hW1 i r hr) (fun i => hW i)
      (fun i s _ => hb0 s i) hg (fun i => hJ i) (fun s _ => hs1 s) hi
      (by simpa [u] using huM)
      (fun r i => by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hwM r i)
      (by simpa [u] using hu0) hw0
      (by
        change Integrable (fun r => coordinateX0Mass (u r) * coordinateX0Mass (w r))
          (volume.restrict (Icc (0 : ℝ) T))
        simpa [leiLinTimeMeasure] using hprod)
  have hfeed := integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance
    ν hν T R hR x y z
  have hswap : (∫ s in Icc (0 : ℝ) T,
      coordinateX0Mass (u s) * coordinateX0Mass (w s)) =
      ∫ s in Icc (0 : ℝ) T,
        coordinateX0Mass (w s) * coordinateX0Mass (u s) := by
    apply integral_congr_ae
    filter_upwards with s
    exact mul_comm _ _
  refine hgeneral.trans ?_
  rw [hswap]
  have hgoal : (∫ s in Icc (0 : ℝ) T, coordinateX0Mass (w s) * coordinateX0Mass (u s)) ≤
      (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
    rw [show w = (fun r ξ => everywhereRawRepresentative ν T x r ξ -
      everywhereRawRepresentative ν T y r ξ) from rfl]
    exact hfeed
  have := mul_le_mul_of_nonneg_left hgoal
    (mul_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (inv_nonneg.mpr hνR.le))
  simpa [mul_assoc] using this

end Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right.integrable_coordinateX1Mass_continuousDuhamel_right_sub_of_jointSource
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right.integrable_coordinateX1Mass_continuousDuhamel_sub_left_of_jointSource
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMildFixedPointD3Right.integral_coordinateX1Mass_continuousDuhamel_right_sub_le_linked_distance_of_jointSource
