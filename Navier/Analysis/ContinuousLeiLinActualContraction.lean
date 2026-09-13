import Navier.Analysis.ContinuousLeiLinLiftDistance

/-!
# Coordinate contraction for lifted actual trajectories

Analytic raw-field bounds are transported through the concrete `actualLinkedOfRaw`
constructor to the exact coordinate sum used by the complete-box Banach theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Set Filter BigOperators
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinLiftDistance

namespace Navier.Analysis.ContinuousLeiLinActualContraction

/-- The concrete linked lift preserves an analytic two-slot contraction
estimate.  Its conclusion is exactly the premise of
`actual_existsUnique_fixedPoint_of_coordinate_sum`. -/
theorem actualLinkedOfRaw_coordinate_sum_le
    (ν : ℝ≥0) (T Ru Rv A B : ℝ) (hA : 0 ≤ A)
    (u v : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (hvM : ∀ t i, AEStronglyMeasurable (fun ξ => v t ξ i) volume)
    (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
    (hvXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖v t ξ i‖))
    (huX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖u t ξ i‖))
    (hvX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖v t ξ i‖))
    (huXmTime : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hvXmTime : AEStronglyMeasurable (xm1Section v hvM hvXm1)
      (leiLinTimeMeasure T))
    (huX1Time : AEStronglyMeasurable (viscousX1Section u huM huX1 ν)
      (leiLinTimeMeasure T))
    (hvX1Time : AEStronglyMeasurable (viscousX1Section v hvM hvX1 ν)
      (leiLinTimeMeasure T))
    (huR : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ Ru)
    (hvR : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (v t) ≤ Rv)
    (huInt : Integrable (fun t => coordinateX1Mass (u t))
      (leiLinTimeMeasure T))
    (hvInt : Integrable (fun t => coordinateX1Mass (v t))
      (leiLinTimeMeasure T))
    (hXm : ∀ᵐ t ∂leiLinTimeMeasure T,
      coordinateXm1Mass (fun ξ => u t ξ - v t ξ) ≤ A)
    (hX1 : (ν : ℝ) * ∫ t, coordinateX1Mass (fun ξ => u t ξ - v t ξ)
      ∂leiLinTimeMeasure T ≤ B) :
    dist ((actualLinkedOfRaw ν T Ru u huM huXm1 huX1 huXmTime huX1Time huR huInt).1.fst)
        ((actualLinkedOfRaw ν T Rv v hvM hvXm1 hvX1 hvXmTime hvX1Time hvR hvInt).1.fst) +
      dist ((actualLinkedOfRaw ν T Ru u huM huXm1 huX1 huXmTime huX1Time huR huInt).1.snd)
        ((actualLinkedOfRaw ν T Rv v hvM hvXm1 hvX1 hvXmTime hvX1Time hvR hvInt).1.snd) ≤
      A + B := by
  have hm := dist_toXm1TimeSlot_le_of_ae_coordinateXm1Mass_sub
    T Ru Rv A hA u v huM hvM huXm1 hvXm1 huXmTime hvXmTime huR hvR hXm
  have h1eq := dist_toViscousX1TimeSlot_eq_integral_coordinateX1Mass_sub
    ν T u v huM hvM huX1 hvX1 huX1Time hvX1Time huInt hvInt
  change
    dist (toXm1TimeSlot u huM huXm1 T Ru huXmTime huR)
        (toXm1TimeSlot v hvM hvXm1 T Rv hvXmTime hvR) +
      dist (toViscousX1TimeSlot u huM huX1 ν T huX1Time huInt)
        (toViscousX1TimeSlot v hvM hvX1 ν T hvX1Time hvInt) ≤ A + B
  exact add_le_add hm (h1eq.trans_le hX1)

/-- Direct Banach consumer: a self-map of the actual complete box with the
coordinate estimate produced above has a unique fixed point. -/
theorem actual_existsUnique_fixedPoint_of_lifted_coordinate_contraction
    (ν : ℝ≥0) (T radius : ℝ) (hradius : 0 ≤ radius)
    (Φ : ActualLinkedBox ν T radius radius → ActualLinkedBox ν T radius radius)
    (K : ℝ≥0) (hK : K < 1)
    (hΦ : ∀ u v,
      dist (Φ u).1.1.fst (Φ v).1.1.fst +
          dist (Φ u).1.1.snd (Φ v).1.1.snd ≤
        (K : ℝ) * (dist u.1.1.fst v.1.1.fst +
          dist u.1.1.snd v.1.1.snd)) :
    ∃ x, Φ x = x ∧ ∀ y, Φ y = y → y = x := by
  exact actual_existsUnique_fixedPoint_of_coordinate_sum
    ν T radius radius hradius hradius Φ K hK hΦ

end Navier.Analysis.ContinuousLeiLinActualContraction

#print axioms Navier.Analysis.ContinuousLeiLinActualContraction.actualLinkedOfRaw_coordinate_sum_le
#print axioms Navier.Analysis.ContinuousLeiLinActualContraction.actual_existsUnique_fixedPoint_of_lifted_coordinate_contraction
