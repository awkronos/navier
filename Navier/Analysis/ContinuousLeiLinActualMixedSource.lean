import Navier.Analysis.ContinuousLeiLinActualPolarization

/-!
# Fixed-time mixed Navier sources on the actual quotient carrier

The difference of two repaired representatives and an actual box
representative have enough spatial integrability to define both ordered mixed
Navier sources in `X⁻¹` at every time.  This removes the two fixed-frequency
source hypotheses from the polarization Duhamel estimates without promoting
an almost-everywhere convolution statement to a pointwise one.
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
open Navier.Analysis.ContinuousLeiLinRepresentativeDistance
open Navier.Analysis.ContinuousLeiLinPhysicalIntegrability
open Navier.Analysis.ContinuousLeiLinBoxInterpolation
open Navier.Analysis.ContinuousLeiLinActualPolarization

namespace Navier.Analysis.ContinuousLeiLinActualMixedSource

/-- A reusable fixed-time conversion: unweighted integrability of two vector
fields gives both the Euclidean and coordinate `X⁻¹` source integrability
families. -/
private theorem fixedTimeSourceInputs
    (u v : ℝ → ES → ComplexSpace)
    (huM : ∀ s i, AEStronglyMeasurable (fun ξ => u s ξ i) volume)
    (hvM : ∀ s i, AEStronglyMeasurable (fun ξ => v s ξ i) volume)
    (hu0 : ∀ s i, Integrable (fun ξ => ‖u s ξ i‖))
    (hv0 : ∀ s i, Integrable (fun ξ => ‖v s ξ i‖)) :
    (∀ s : ℝ, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u v s ξ))) ∧
    (∀ s : ℝ, ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖continuousNavierSource u v s ξ i‖)) := by
  have hs1 (s : ℝ) : Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u v s ξ)) := by
    exact integrable_normXm1_continuousNavierBilinear
      (u s) (v s) (huM s) (hvM s) (hu0 s) (hv0 s)
  refine ⟨hs1, ?_⟩
  intro s i
  have hvec := continuousNavierBilinear_aestronglyMeasurable
    (u s) (v s) (huM s) (hvM s) (hu0 s) (hv0 s)
  have hcoord : AEStronglyMeasurable
      (fun ξ : ES => continuousNavierSource u v s ξ i) volume := by
    have h := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) i).aestronglyMeasurable
      |>.comp_aemeasurable hvec.aemeasurable
    exact h.congr (Eventually.of_forall fun ξ =>
      complexEuclideanPoint_apply (continuousNavierSource u v s ξ) i)
  apply (hs1 s).mono'
    (continuous_norm.aestronglyMeasurable.inv₀.mul hcoord.norm)
  filter_upwards with ξ
  change ‖‖ξ‖⁻¹ * ‖continuousNavierSource u v s ξ i‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ))
    (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (show ‖continuousNavierSource u v s ξ i‖ ≤
        complexEuclideanNorm (continuousNavierSource u v s ξ) by
      calc
        _ = ‖complexEuclideanPoint (continuousNavierSource u v s ξ) i‖ := by
          rw [complexEuclideanPoint_apply]
        _ ≤ ‖complexEuclideanPoint (continuousNavierSource u v s ξ)‖ :=
          PiLp.norm_apply_le _ i)
    (inv_nonneg.mpr (norm_nonneg ξ))

/-- The ordered source `(x-y,z)` is `X⁻¹`-integrable at every time on the
actual carrier. -/
theorem continuousNavierSource_sub_left_fixedTime_inputs_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T xm1Radius x1WeightedRadius) :
    (∀ s : ℝ, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) s ξ))) ∧
    (∀ s : ℝ, ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖continuousNavierSource (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) s ξ i‖)) := by
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T xm1Radius x1WeightedRadius z
  have hw0 : ∀ s i, Integrable (fun ξ : ES =>
      ‖commonRepresentativeDifference ν T x y s ξ i‖) := fun s i =>
    integrable_norm_of_integrable_Xm1_X1
      (fun ξ : ES => commonRepresentativeDifference ν T x y s ξ i)
      (by simpa only [commonRepresentativeDifference, Pi.sub_apply] using hwm1 s i)
      (by simpa only [commonRepresentativeDifference, Pi.sub_apply] using hw1 s i)
  exact fixedTimeSourceInputs
    (commonRepresentativeDifference ν T x y)
    (everywhereRawRepresentative ν T z.1)
    (fun s i => by
      simpa only [commonRepresentativeDifference, Pi.sub_apply] using hwM s i)
    huM hw0 hu0

/-- The reverse ordered source `(z,x-y)` is likewise `X⁻¹`-integrable at every
time; no commutativity of the vector-valued Navier source is used. -/
theorem continuousNavierSource_right_sub_fixedTime_inputs_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T xm1Radius x1WeightedRadius) :
    (∀ s : ℝ, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) s ξ))) ∧
    (∀ s : ℝ, ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖continuousNavierSource (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) s ξ i‖)) := by
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T xm1Radius x1WeightedRadius z
  have hw0 : ∀ s i, Integrable (fun ξ : ES =>
      ‖commonRepresentativeDifference ν T x y s ξ i‖) := fun s i =>
    integrable_norm_of_integrable_Xm1_X1
      (fun ξ : ES => commonRepresentativeDifference ν T x y s ξ i)
      (by simpa only [commonRepresentativeDifference, Pi.sub_apply] using hwm1 s i)
      (by simpa only [commonRepresentativeDifference, Pi.sub_apply] using hw1 s i)
  exact fixedTimeSourceInputs
    (everywhereRawRepresentative ν T z.1)
    (commonRepresentativeDifference ν T x y)
    huM
    (fun s i => by
      simpa only [commonRepresentativeDifference, Pi.sub_apply] using hwM s i)
    hu0 hw0

/-- The actual mixed source families remove both fixed-time source hypotheses
from the left terminal polarization estimate.  The remaining assumptions are
the genuinely joint time/heat integrability inputs. -/
theorem coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance_of_actualSource
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ) (hR : 0 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) T)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hb : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
      (‖p.1‖⁻¹ : ℝ) • heatMode (ν : ℝ) (t - p.2)
        (fun ζ : ES => continuousNavierSource
          (commonRepresentativeDifference ν T x y)
          (everywhereRawRepresentative ν T z.1) p.2 ζ i) p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ i : Fin 3, Integrable (fun s : ℝ =>
      normXm1 (heatMode (ν : ℝ) (t - s)
        (fun ζ : ES => continuousNavierSource
          (commonRepresentativeDifference ν T x y)
          (everywhereRawRepresentative ν T z.1) s ζ i)))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
      normXm1 (fun ζ : ES => continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) s ζ i))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
      (continuousNavierSource (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) s ξ))
      (volume.restrict (Icc (0 : ℝ) t))) :
    coordinateXm1Mass (continuousDuhamel (ν : ℝ)
      (commonRepresentativeDifference ν T x y)
      (everywhereRawRepresentative ν T z.1) t) ≤
      3 * (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  have hdiff : commonRepresentativeDifference ν T x y =
      (fun s ξ => everywhereRawRepresentative ν T x s ξ -
        everywhereRawRepresentative ν T y s ξ) := rfl
  obtain ⟨hs1, hb0⟩ :=
    continuousNavierSource_sub_left_fixedTime_inputs_of_actualBox
      ν hν T (2 * R) (2 * R) x y z
  rw [hdiff] at hb hf hg hi hb0 hs1 ⊢
  exact coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance
    ν hν T R t hR ht x y z hb hf hg
    (fun s _ i => hb0 s i) (fun s _ => hs1 s) hi

end Navier.Analysis.ContinuousLeiLinActualMixedSource

#print axioms Navier.Analysis.ContinuousLeiLinActualMixedSource.continuousNavierSource_sub_left_fixedTime_inputs_of_actualBox
#print axioms Navier.Analysis.ContinuousLeiLinActualMixedSource.continuousNavierSource_right_sub_fixedTime_inputs_of_actualBox
#print axioms Navier.Analysis.ContinuousLeiLinActualMixedSource.coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance_of_actualSource
#print axioms Navier.Analysis.ContinuousLeiLinActualPolarization.coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance
