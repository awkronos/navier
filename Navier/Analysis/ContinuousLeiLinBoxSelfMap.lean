import Navier.Analysis.ContinuousLeiLinBoxD3AE

/-!
# Actual Lei--Lin box self-map from one joint source input

The full-horizon joint measurability of the nonlinear source restricts to each
causal prefix.  It therefore feeds both the pointwise `B₁` estimate and the
almost-everywhere maximal-regularity `D₃` estimate, closing the two analytic
premises of the existing actual-box self-map consumer.
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
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinBoxProduct
open Navier.Analysis.ContinuousLeiLinBoxB1Joint
open Navier.Analysis.ContinuousLeiLinBoxD3AE

namespace Navier.Analysis.ContinuousLeiLinBoxSelfMap

/-- The actual mild image obeys both radii of the complete Lei--Lin box from a
single full-horizon joint-source measurability fact. -/
theorem continuousMildImage_self_map_ball_twoR_of_actualBox_joint
    (ν : ℝ≥0) (hν : 0 < ν) (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRν : R ≤ (ν : ℝ) / 16)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (x : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    (∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t) ≤ 2 * R) ∧
      (∫ t in Icc (0 : ℝ) T,
        coordinateX1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
          (everywhereRawRepresentative ν T x.1) t)) ≤
            2 * (ν : ℝ)⁻¹ * R := by
  have hprefix (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanPoint (continuousNavierSource
          (everywhereRawRepresentative ν T x.1)
          (everywhereRawRepresentative ν T x.1) p.2 p.1))
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))) := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
      Icc_subset_Icc le_rfl ht.2
    exact hjoint.mono_measure
      (Measure.prod_mono le_rfl (Measure.restrict_mono hsub le_rfl))
  have hB1 : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t) ≤
        coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
            coordinateX1Mass (everywhereRawRepresentative ν T x.1 s) := by
    intro t ht
    exact continuousMildImage_coordinateXm1Mass_le_of_actualBox_joint
      ν hν T (2 * R) (2 * R) a ha x t ht (hprefix t ht)
  have hD3 := integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_ae
    ν hν T (2 * R) (2 * R) hT a haM ha ha1 x hjoint
  exact continuousMildImage_self_map_ball_twoR_of_actualBox
    ν hν R T hR hT hRν a x haR hB1 hD3

end Navier.Analysis.ContinuousLeiLinBoxSelfMap

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxSelfMap.continuousMildImage_self_map_ball_twoR_of_actualBox_joint
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxProduct.continuousMildImage_self_map_ball_twoR_of_actualBox
