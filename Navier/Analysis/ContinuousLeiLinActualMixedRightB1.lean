import Navier.Analysis.ContinuousLeiLinActualMixedRightJoint

/-! # Reverse terminal mixed estimate from one joint source -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Set Filter BigOperators
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinActualPolarization
open Navier.Analysis.ContinuousLeiLinActualMixedSource
open Navier.Analysis.ContinuousLeiLinActualMixedRightJoint

namespace Navier.Analysis.ContinuousLeiLinActualMixedRightB1

/-- The reverse ordered terminal polarization bound follows from one a.e.
joint source fact, with every source-section, Fubini, and heat input generated
on the actual quotient carrier. -/
theorem coordinateXm1Mass_continuousDuhamel_right_sub_le_linked_distance_of_jointSource
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ) (hR : 0 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) T) (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t)))) :
    coordinateXm1Mass (continuousDuhamel (ν : ℝ)
      (everywhereRawRepresentative ν T z.1)
      (commonRepresentativeDifference ν T x y) t) ≤
      3 * (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let u := everywhereRawRepresentative ν T z.1
  let w := commonRepresentativeDifference ν T x y
  let μ := volume.restrict (Icc (0 : ℝ) t)
  have hsource := integrable_weightedContinuousNavierSource_right_sub_of_actualBox
    ν hν T R t ht x y z hjoint
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_right_sub_coord_of_actualBox
      ν hν T R t ht x y z hjoint i
  have hb (i : Fin 3) :=
    integrable_weightedHeatContinuousNavierSource_right_sub_coord_of_actualBox
      ν hν T R t ht x y z hjoint i
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
  have hf (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (heatMode (ν : ℝ) (t - s)
        (fun ζ : ES => continuousNavierSource u w s ζ i))) μ := by
    apply (hb i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ))]
  obtain ⟨hs1, hb0⟩ :=
    continuousNavierSource_right_sub_fixedTime_inputs_of_actualBox
      ν hν T (2 * R) (2 * R) x y z
  have hdiff : commonRepresentativeDifference ν T x y =
      (fun s ξ => everywhereRawRepresentative ν T x s ξ -
        everywhereRawRepresentative ν T y s ξ) := rfl
  dsimp [w, u, μ] at hf hg hi
  rw [hdiff] at hf hg hi hb0 hs1 ⊢
  exact coordinateXm1Mass_continuousDuhamel_right_sub_le_linked_distance
    ν hν T R t hR ht x y z hb hf hg
    (fun s _ i => hb0 s i) (fun s _ => hs1 s) hi

end Navier.Analysis.ContinuousLeiLinActualMixedRightB1

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinActualMixedRightB1.coordinateXm1Mass_continuousDuhamel_right_sub_le_linked_distance_of_jointSource
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinActualPolarization.coordinateXm1Mass_continuousDuhamel_right_sub_le_linked_distance
