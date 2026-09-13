import Navier.Analysis.ContinuousLeiLinActualMixedJoint

/-!
# Terminal mixed estimate from one actual joint source

The product-measure mixed source constructed in the preceding module supplies
all Fubini, source-section, and forward-heat inputs of the left terminal
polarization bound.  Only the natural a.e. joint measurability of that source
remains explicit.
-/

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
open Navier.Analysis.ContinuousLeiLinActualMixedJoint

namespace Navier.Analysis.ContinuousLeiLinActualMixedB1

/-- The left terminal polarization estimate on the actual carrier requires a
single a.e. joint source-measurability input.  In particular, there are no
all-frequency convolution-existence or separate heat/Fubini assumptions. -/
theorem coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance_of_jointSource
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ) (hR : 0 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) T)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t)))) :
    coordinateXm1Mass (continuousDuhamel (ν : ℝ)
      (commonRepresentativeDifference ν T x y)
      (everywhereRawRepresentative ν T z.1) t) ≤
      3 * (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let w := commonRepresentativeDifference ν T x y
  let u := everywhereRawRepresentative ν T z.1
  let μ := volume.restrict (Icc (0 : ℝ) t)
  have hsource := integrable_weightedContinuousNavierSource_sub_left_of_actualBox
    ν hν T R t ht x y z hjoint
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_sub_left_coord_of_actualBox
      ν hν T R t ht x y z hjoint i
  have hb (i : Fin 3) :=
    integrable_weightedHeatContinuousNavierSource_sub_left_coord_of_actualBox
      ν hν T R t ht x y z hjoint i
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
  have hf (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (heatMode (ν : ℝ) (t - s)
        (fun ζ : ES => continuousNavierSource w u s ζ i))) μ := by
    apply (hb i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ))]
  exact coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance_of_actualSource
    ν hν T R t hR ht x y z
    (by simpa [w, u, μ] using hb)
    (by simpa [w, u, μ] using hf)
    (by simpa [w, u, μ] using hg)
    (by simpa [w, u, μ] using hi)

end Navier.Analysis.ContinuousLeiLinActualMixedB1

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinActualMixedB1.coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance_of_jointSource
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinActualPolarization.coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance
