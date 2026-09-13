import Navier.Analysis.ContinuousLeiLinActualPolarization

/-!
# Distance bounds for raw fields lifted to the actual Lei--Lin carrier

This file connects analytic difference estimates for two raw spacetime
Fourier fields to the two completed time-slot distances used by Banach's
fixed-point theorem.
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
open Navier.Analysis.ContinuousLeiLinRepresentativeDistance

namespace Navier.Analysis.ContinuousLeiLinLiftDistance

/-- An a.e. raw `X⁻¹` difference bound becomes the distance bound in the
completed `L∞_t X⁻¹` slot. -/
theorem dist_toXm1TimeSlot_le_of_ae_coordinateXm1Mass_sub
    (T Ru Rv A : ℝ) (hA : 0 ≤ A) (u v : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (hvM : ∀ t i, AEStronglyMeasurable (fun ξ => v t ξ i) volume)
    (huXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u t ξ i‖))
    (hvXm1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖v t ξ i‖))
    (huTimeM : AEStronglyMeasurable (xm1Section u huM huXm1)
      (leiLinTimeMeasure T))
    (hvTimeM : AEStronglyMeasurable (xm1Section v hvM hvXm1)
      (leiLinTimeMeasure T))
    (huR : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ Ru)
    (hvR : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (v t) ≤ Rv)
    (hdist : ∀ᵐ t ∂leiLinTimeMeasure T,
      coordinateXm1Mass (fun ξ => u t ξ - v t ξ) ≤ A) :
    dist (toXm1TimeSlot u huM huXm1 T Ru huTimeM huR)
      (toXm1TimeSlot v hvM hvXm1 T Rv hvTimeM hvR) ≤ A := by
  let xu := toXm1TimeSlot u huM huXm1 T Ru huTimeM huR
  let xv := toXm1TimeSlot v hvM hvXm1 T Rv hvTimeM hvR
  rw [dist_eq_norm]
  have hcoeU := coeFn_toXm1TimeSlot u huM huXm1 T Ru huTimeM huR
  have hcoeV := coeFn_toXm1TimeSlot v hvM hvXm1 T Rv hvTimeM hvR
  have hcoeSub := Lp.coeFn_sub xu xv
  have hpoint : ∀ᵐ t ∂leiLinTimeMeasure T, ‖(xu - xv : Xm1TimeSlot T) t‖ ≤ A := by
    filter_upwards [hcoeU, hcoeV, hcoeSub, hdist] with t hu hv hs hd
    have hu' : xu t = xm1Section u huM huXm1 t := by simpa only [xu] using hu
    have hv' : xv t = xm1Section v hvM hvXm1 t := by simpa only [xv] using hv
    rw [hs]
    simp only [Pi.sub_apply, hu', hv']
    rw [← dist_eq_norm]
    exact (dist_toXm1Spatial_eq_coordinateXm1Mass_sub
      (u t) (v t) (huM t) (hvM t) (huXm1 t) (hvXm1 t)).trans_le hd
  have h := Lp.norm_le_of_ae_bound (f := xu - xv) hA hpoint
  simpa [xu, xv] using h

/-- The completed viscous `L¹_t X¹` distance of two lifted raw fields is
exactly viscosity times the integral of their literal coordinate difference.
-/
theorem dist_toViscousX1TimeSlot_eq_integral_coordinateX1Mass_sub
    (ν : ℝ≥0) (T : ℝ) (u v : ℝ → ES → ComplexSpace)
    (huM : ∀ t i, AEStronglyMeasurable (fun ξ => u t ξ i) volume)
    (hvM : ∀ t i, AEStronglyMeasurable (fun ξ => v t ξ i) volume)
    (huX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖u t ξ i‖))
    (hvX1 : ∀ t i, Integrable (fun ξ : ES => ‖ξ‖ * ‖v t ξ i‖))
    (huTimeM : AEStronglyMeasurable (viscousX1Section u huM huX1 ν)
      (leiLinTimeMeasure T))
    (hvTimeM : AEStronglyMeasurable (viscousX1Section v hvM hvX1 ν)
      (leiLinTimeMeasure T))
    (huInt : Integrable (fun t => coordinateX1Mass (u t))
      (leiLinTimeMeasure T))
    (hvInt : Integrable (fun t => coordinateX1Mass (v t))
      (leiLinTimeMeasure T)) :
    dist (toViscousX1TimeSlot u huM huX1 ν T huTimeM huInt)
      (toViscousX1TimeSlot v hvM hvX1 ν T hvTimeM hvInt) =
      (ν : ℝ) * ∫ t, coordinateX1Mass (fun ξ => u t ξ - v t ξ)
        ∂leiLinTimeMeasure T := by
  let xu := toViscousX1TimeSlot u huM huX1 ν T huTimeM huInt
  let xv := toViscousX1TimeSlot v hvM hvX1 ν T hvTimeM hvInt
  rw [dist_eq_norm, L1.norm_eq_integral_norm, ← integral_const_mul]
  have hcoeU := coeFn_toViscousX1TimeSlot u huM huX1 ν T huTimeM huInt
  have hcoeV := coeFn_toViscousX1TimeSlot v hvM hvX1 ν T hvTimeM hvInt
  have hcoeSub := Lp.coeFn_sub xu xv
  apply integral_congr_ae
  filter_upwards [hcoeU, hcoeV, hcoeSub] with t hu hv hs
  have hu' : xu t = viscousX1Section u huM huX1 ν t := by
    simpa only [xu] using hu
  have hv' : xv t = viscousX1Section v hvM hvX1 ν t := by
    simpa only [xv] using hv
  rw [hs]
  simp only [Pi.sub_apply, hu', hv']
  rw [← dist_eq_norm]
  exact dist_toViscousX1Spatial_eq_coordinateX1Mass_sub ν
    (u t) (v t) (huM t) (hvM t) (huX1 t) (hvX1 t)

end Navier.Analysis.ContinuousLeiLinLiftDistance

#print axioms Navier.Analysis.ContinuousLeiLinLiftDistance.dist_toXm1TimeSlot_le_of_ae_coordinateXm1Mass_sub
#print axioms Navier.Analysis.ContinuousLeiLinLiftDistance.dist_toViscousX1TimeSlot_eq_integral_coordinateX1Mass_sub
