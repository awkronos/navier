import Navier.Analysis.ContinuousLeiLinEverywhereRepresentative

/-!
# Quantitative bounds of the everywhere representative

This file reads the two actual completed-slot norms back as the pointwise
`X⁻¹` and time-integrated `X¹` bounds used by the existing nonlinear mild-map
estimates.  It removes the gap between coordinatewise ball membership in the
complete quotient carrier and the raw representative hypotheses.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative

namespace Navier.Analysis.ContinuousLeiLinBoxRepresentative

/-- The norm of the actual viscous time slot is exactly viscosity times the
unscaled coordinate `X¹` integral of the everywhere representative. -/
theorem norm_viscousX1TimeSlot_eq_integral_everywhere
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    ‖(x.1.snd : ViscousX1TimeSlot ν T)‖ =
      (ν : ℝ) * ∫ t, coordinateX1Mass
        (everywhereRawRepresentative ν T x t) ∂leiLinTimeMeasure T := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ t, ‖((x.1.snd : ViscousX1TimeSlot ν T) t)‖ ∂leiLinTimeMeasure T) =
        ∫ t, ‖everywhereViscousX1Section ν hν T x t‖ ∂leiLinTimeMeasure T := by
          apply integral_congr_ae
          filter_upwards [everywhereViscousX1Section_eq_ae ν hν T x] with t ht
          rw [ht]
    _ = ∫ t, (ν : ℝ) * coordinateX1Mass
          (everywhereRawRepresentative ν T x t) ∂leiLinTimeMeasure T := by
        apply integral_congr_ae
        filter_upwards with t
        exact norm_viscousX1Section
          (everywhereRawRepresentative ν T x)
          (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
          (everywhereRawRepresentative_x1_integrable ν T x) ν t
    _ = (ν : ℝ) * ∫ t, coordinateX1Mass
          (everywhereRawRepresentative ν T x t) ∂leiLinTimeMeasure T := by
        exact integral_const_mul (ν : ℝ) _

/-- Membership in an actual linked box supplies the raw pointwise `X⁻¹`
bound at every time, including the originally exceptional times. -/
theorem coordinateXm1Mass_everywhere_le_of_mem_box
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius) (t : ℝ) :
    coordinateXm1Mass (everywhereRawRepresentative ν T x.1 t) ≤ xm1Radius := by
  exact (coordinateXm1Mass_everywhereRawRepresentative_le ν hν T x.1 t).trans
    x.property.1

/-- Membership in an actual linked box supplies the raw time-integrated `X¹`
bound with the exact inverse-viscosity scaling. -/
theorem integral_coordinateX1Mass_everywhere_le_of_mem_box
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius) :
    ∫ t, coordinateX1Mass (everywhereRawRepresentative ν T x.1 t)
        ∂leiLinTimeMeasure T ≤ (ν : ℝ)⁻¹ * x1WeightedRadius := by
  have hscale := norm_viscousX1TimeSlot_eq_integral_everywhere ν hν T x.1
  have hνR : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  calc
    (∫ t, coordinateX1Mass (everywhereRawRepresentative ν T x.1 t)
        ∂leiLinTimeMeasure T) = (ν : ℝ)⁻¹ * ‖(x.1.1.snd : ViscousX1TimeSlot ν T)‖ := by
          rw [hscale]
          field_simp
    _ ≤ (ν : ℝ)⁻¹ * x1WeightedRadius :=
      mul_le_mul_of_nonneg_left x.property.2 (inv_nonneg.mpr hνR.le)

/-- Exact input-bounds consumer for the existing `2R` mild self-map theorem:
an element of the complete quotient box has a representative satisfying its
pointwise `X⁻¹` and spacetime `X¹` ball hypotheses. -/
theorem everywhereRawRepresentative_twoR_bounds
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    (∀ t ∈ Icc (0 : ℝ) T,
        coordinateXm1Mass (everywhereRawRepresentative ν T x.1 t) ≤ 2 * R) ∧
      (∫ t in Icc (0 : ℝ) T,
        coordinateX1Mass (everywhereRawRepresentative ν T x.1 t)) ≤
          2 * (ν : ℝ)⁻¹ * R := by
  constructor
  · intro t _
    exact coordinateXm1Mass_everywhere_le_of_mem_box ν hν T (2 * R) (2 * R) x t
  · have h := integral_coordinateX1Mass_everywhere_le_of_mem_box
      ν hν T (2 * R) (2 * R) x
    simpa [leiLinTimeMeasure, mul_assoc, mul_left_comm, mul_comm] using h

end Navier.Analysis.ContinuousLeiLinBoxRepresentative

#print axioms Navier.Analysis.ContinuousLeiLinBoxRepresentative.norm_viscousX1TimeSlot_eq_integral_everywhere
#print axioms Navier.Analysis.ContinuousLeiLinBoxRepresentative.coordinateXm1Mass_everywhere_le_of_mem_box
#print axioms Navier.Analysis.ContinuousLeiLinBoxRepresentative.integral_coordinateX1Mass_everywhere_le_of_mem_box
#print axioms Navier.Analysis.ContinuousLeiLinBoxRepresentative.everywhereRawRepresentative_twoR_bounds
