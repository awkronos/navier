import Navier.Analysis.ContinuousLeiLinBoxB1Joint

/-!
# Joint-source input for the actual Lei--Lin `D₃` estimate

This module feeds one joint nonlinear-source measurability fact into the
existing spacetime `X¹` mild-image estimate.  Product-measure composition
constructs both causal kernel measurability families, while the `B₁` joint
source theorem supplies every source-side integrability premise.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinBoxProduct
open Navier.Analysis.ContinuousLeiLinBoxInterpolation
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinBoxB1Joint

namespace Navier.Analysis.ContinuousLeiLinBoxD3Joint

/-- Exact `D₃` output estimate with all source-side and kernel-measurability
premises generated from one joint nonlinear-source measurability fact.  The
remaining four integrability assumptions concern the actual output trajectory
and expose the next maximal-regularity step. -/
theorem integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (hIt : Integrable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hHt : Integrable (fun t : ℝ => coordinateX1Mass
      (heatVec (ν : ℝ) t a)) (volume.restrict (Icc (0 : ℝ) T)))
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ =>
      normX1 (fun ξ : ES => continuousDuhamel (ν : ℝ)
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) t ξ i))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T,
      Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousDuhamel (ν : ℝ)
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) t ξ i‖))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    ∫ t in Icc (0 : ℝ) T, coordinateX1Mass
      (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t) ≤
      (ν : ℝ)⁻¹ * coordinateXm1Mass a +
        (3 : ℝ) * (ν : ℝ)⁻¹ * ∫ s in Icc (0 : ℝ) T,
          coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
            coordinateX1Mass (everywhereRawRepresentative ν T x.1 s) := by
  let u := everywhereRawRepresentative ν T x.1
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hcoordMeas (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u u p.2 p.1 i) (volume.prod μ) :=
    continuousNavierSource_coord_aestronglyMeasurable u u 0 T
      (by simpa [u, μ] using hjoint) i
  have hsource := integrable_weightedContinuousNavierSource_of_actualBox
    ν hν T xm1Radius x1WeightedRadius x T ⟨hT, le_rfl⟩ hjoint
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_coord_of_actualBox
      ν hν T xm1Radius x1WeightedRadius x T ⟨hT, le_rfl⟩ hjoint i

  have hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u u s ξ)) μ := by
    apply hsource.integral_norm_prod_right.congr
    filter_upwards with s
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (by
      unfold complexEuclideanNorm
      exact norm_nonneg _))
  have hg (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) μ := by
    apply (hsourceCoord i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg
      (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
  have hJ (i : Fin 3) : AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖))
      (volume.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
          (volume.prod μ) by fun_prop).mul (hcoordMeas i).norm).aemeasurable)
  obtain ⟨hs1, hb0⟩ := continuousNavierSource_fixedTime_inputs_of_actualBox
    ν hν T xm1Radius x1WeightedRadius x
  obtain ⟨hu, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T xm1Radius x1WeightedRadius x
  refine integral_coordinateX1Mass_continuousMildImage_le
    (ν : ℝ) (by exact_mod_cast hν) a ha ha1 u T hT hIt hHt hD0 hDξ ?_ ?_
      (fun i s _ => hb0 s i) hg hJ (fun s _ => hs1 s) hi hu hu0
      (everywhereRawRepresentative_xm1_integrable ν T x.1)
      (everywhereRawRepresentative_x1_integrable ν T x.1)
      (integrableOn_coordinateX0Mass_sq_everywhere_of_mem_box
        ν hν T xm1Radius x1WeightedRadius x T ?_)
      (integrable_coordinateXm1_mul_X1_everywhere_of_mem_box
        ν hν T xm1Radius x1WeightedRadius x)
  · intro i r hr
    change AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal ‖continuousNavierSource u u p.2 p.1 i‖ *
        (if p.2 ≤ r then ENNReal.ofReal
          (‖p.1‖ * Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (r - p.2)))) else 0))
      (volume.prod μ)
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcoordMeas i).norm.aemeasurable).mul
        ((Measurable.ite (measurableSet_le measurable_snd measurable_const)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  · intro i
    have hcoord3 : AEStronglyMeasurable (fun z : ℝ × (ES × ℝ) =>
        continuousNavierSource u u z.2.2 z.2.1 i)
        (μ.prod (volume.prod μ)) :=
      (hcoordMeas i).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd
    change AEMeasurable (fun z : ℝ × (ES × ℝ) =>
      ENNReal.ofReal ‖continuousNavierSource u u z.2.2 z.2.1 i‖ *
        (if z.2.2 ≤ z.1 then ENNReal.ofReal
          (‖z.2.1‖ * Real.exp (-((ν : ℝ) * ‖z.2.1‖ ^ 2 *
            (z.1 - z.2.2)))) else 0))
      (μ.prod (volume.prod μ))
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      hcoord3.norm.aemeasurable).mul
        ((Measurable.ite
          (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  · exact ⟨hT, le_rfl⟩

end Navier.Analysis.ContinuousLeiLinBoxD3Joint

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Joint.integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinSelfMap.integral_coordinateX1Mass_continuousMildImage_le
