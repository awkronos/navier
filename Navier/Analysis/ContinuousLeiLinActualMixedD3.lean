import Navier.Analysis.ContinuousLeiLinActualMixedB1
import Navier.Analysis.ContinuousLeiLinBoxD3Maximal

/-!
# Actual mixed spacetime `X¹` estimate from one joint source

Maximal regularity supplies the mixed Duhamel section only almost everywhere
in output time.  The strengthened mixed `X¹` theorem consumes exactly that
fact, so no exceptional section is promoted to an all-time statement.
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
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinBoxD3Measurability
open Navier.Analysis.ContinuousLeiLinBoxD3Maximal

namespace Navier.Analysis.ContinuousLeiLinActualMixedD3

/-- The left mixed Duhamel spacetime `X¹` budget on the actual carrier follows
from one a.e. joint source fact.  Maximal regularity produces both the time
integrability and the almost-everywhere spatial sections used below. -/
theorem integral_coordinateX1Mass_continuousDuhamel_sub_left_le_linked_distance_of_jointSource
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    (∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel (ν : ℝ)
      (commonRepresentativeDifference ν T x y)
      (everywhereRawRepresentative ν T z.1) t)) ≤
      3 * (ν : ℝ)⁻¹ * ((ν : ℝ)⁻¹ * R) *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let w := commonRepresentativeDifference ν T x y
  let u := everywhereRawRepresentative ν T z.1
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
  have hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource w u s ξ)) μ := by
    apply hsource.integral_norm_prod_right.congr
    filter_upwards with s
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (by
      unfold complexEuclideanNorm
      exact norm_nonneg _))
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
  obtain ⟨hs1, hb0⟩ :=
    continuousNavierSource_sub_left_fixedTime_inputs_of_actualBox
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
  have hDξ (i : Fin 3) := (hDfacts i).2
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T (2 * R) (2 * R) z
  have hw0 : ∀ r i, Integrable (fun η : ES => ‖w r η i‖) := fun r i =>
    integrable_norm_of_integrable_Xm1_X1 (fun η : ES => w r η i)
      (by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hwm1 r i)
      (by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hw1 r i)
  have hprod := integrable_coordinateX0Mass_sub_mul_everywhere
    ν hν T (2 * R) (2 * R) x y z
  have hprod' : IntegrableOn (fun r =>
      coordinateX0Mass (w r) * coordinateX0Mass (u r)) (Icc (0 : ℝ) T) := by
    change Integrable (fun r => coordinateX0Mass (w r) * coordinateX0Mass (u r))
      (leiLinTimeMeasure T)
    rw [show w = (fun r ξ => everywhereRawRepresentative ν T x r ξ -
      everywhereRawRepresentative ν T y r ξ) from rfl]
    exact hprod
  have hgeneral :=
    integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product_ae
      w u (ν : ℝ) T hνR hD0 hDξ hW1 hW
      (fun i s _ => hb0 s i) hg hJ (fun s _ => hs1 s) hi
      (fun r i => by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hwM r i)
      (by simpa [u] using huM) hw0 (by simpa [u] using hu0)
      hprod'
  have hfeed := integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance
    ν hν T R hR x y z
  have hfeed' : (∫ s in Icc (0 : ℝ) T,
      coordinateX0Mass (w s) * coordinateX0Mass (u s)) ≤
      (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
    rw [show w = (fun r ξ => everywhereRawRepresentative ν T x r ξ -
      everywhereRawRepresentative ν T y r ξ) from rfl]
    exact hfeed
  refine hgeneral.trans ?_
  have := mul_le_mul_of_nonneg_left hfeed'
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (inv_nonneg.mpr hνR.le))
  simpa [mul_assoc] using this

end Navier.Analysis.ContinuousLeiLinActualMixedD3

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinActualMixedD3.integral_coordinateX1Mass_continuousDuhamel_sub_left_le_linked_distance_of_jointSource
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinMixedX1.integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product_ae
