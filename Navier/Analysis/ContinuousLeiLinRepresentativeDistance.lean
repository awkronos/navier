import Navier.Analysis.ContinuousLeiLinEverywhereRepresentative

/-!
# Exact raw-representative formulas for the linked-carrier distance

The repaired everywhere representatives are used by the nonlinear estimates.
This module identifies their weighted difference masses with the two completed
slot distances, almost everywhere for the `L∞_t X⁻¹` coordinate and exactly
after time integration for the `L¹_t νX¹` coordinate.
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
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative

namespace Navier.Analysis.ContinuousLeiLinRepresentativeDistance

private theorem weighted_norm_sub_integrable
    (w : ES → ℝ) (hw : AEStronglyMeasurable w volume) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (u v : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (hvM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => v ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ => w ξ * ‖u ξ i‖))
    (hvI : ∀ i : Fin 3, Integrable (fun ξ => w ξ * ‖v ξ i‖))
    (i : Fin 3) : Integrable (fun ξ => w ξ * ‖u ξ i - v ξ i‖) := by
  have hmeas : AEStronglyMeasurable (fun ξ => w ξ * ‖u ξ i - v ξ i‖) volume :=
    hw.mul ((huM i).sub (hvM i)).norm
  apply ((huI i).add (hvI i)).mono' hmeas
  filter_upwards with ξ
  rw [Real.norm_of_nonneg (mul_nonneg (hw0 ξ) (norm_nonneg _))]
  change w ξ * ‖u ξ i - v ξ i‖ ≤
    w ξ * ‖u ξ i‖ + w ξ * ‖v ξ i‖
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (hw0 ξ)

private theorem xm1_sub_integrable
    (u v : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (hvM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => v ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (hvI : ∀ i : Fin 3, Integrable (fun ξ => ‖ξ‖⁻¹ * ‖v ξ i‖))
    (i : Fin 3) : Integrable (fun ξ => ‖ξ‖⁻¹ * ‖u ξ i - v ξ i‖) :=
  weighted_norm_sub_integrable (fun ξ : ES => ‖ξ‖⁻¹) (by fun_prop)
    (fun ξ => inv_nonneg.mpr (norm_nonneg ξ)) u v huM hvM huI hvI i

private theorem x1_sub_integrable
    (u v : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (hvM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => v ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ => ‖ξ‖ * ‖u ξ i‖))
    (hvI : ∀ i : Fin 3, Integrable (fun ξ => ‖ξ‖ * ‖v ξ i‖))
    (i : Fin 3) : Integrable (fun ξ => ‖ξ‖ * ‖u ξ i - v ξ i‖) :=
  weighted_norm_sub_integrable (fun ξ : ES => ‖ξ‖) (by fun_prop)
    (fun ξ => norm_nonneg ξ) u v huM hvM huI hvI i

/-- The `X⁻¹` spatial quotient distance is exactly the coordinate mass of the
raw field difference. -/
theorem dist_toXm1Spatial_eq_coordinateXm1Mass_sub
    (u v : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (hvM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => v ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (hvI : ∀ i : Fin 3, Integrable (fun ξ => ‖ξ‖⁻¹ * ‖v ξ i‖)) :
    dist (toXm1Spatial u huM huI) (toXm1Spatial v hvM hvI) =
      coordinateXm1Mass (fun ξ => u ξ - v ξ) := by
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  calc
    (∫ ξ, ‖((toXm1Spatial u huM huI - toXm1Spatial v hvM hvI : Xm1Spatial) ξ)‖
        ∂xm1FrequencyMeasure) =
      ∫ ξ, ‖coordinateL1 (fun ζ => u ζ - v ζ) ξ‖ ∂xm1FrequencyMeasure := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (toXm1Spatial u huM huI)
            (toXm1Spatial v hvM hvI),
          coeFn_toXm1Spatial u huM huI,
          coeFn_toXm1Spatial v hvM hvI] with ξ hsub huξ hvξ
        rw [hsub, Pi.sub_apply, huξ, hvξ]
        rfl
    _ = coordinateXm1Mass (fun ξ => u ξ - v ξ) :=
      integral_norm_coordinateL1_xm1_eq _
        (xm1_sub_integrable u v huM hvM huI hvI)

/-- The viscosity-weighted `X¹` spatial quotient distance is exactly viscosity
times the coordinate `X¹` mass of the raw field difference. -/
theorem dist_toViscousX1Spatial_eq_coordinateX1Mass_sub
    (ν : ℝ≥0) (u v : ES → ComplexSpace)
    (huM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => u ξ i) volume)
    (hvM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ => v ξ i) volume)
    (huI : ∀ i : Fin 3, Integrable (fun ξ => ‖ξ‖ * ‖u ξ i‖))
    (hvI : ∀ i : Fin 3, Integrable (fun ξ => ‖ξ‖ * ‖v ξ i‖)) :
    dist (toViscousX1Spatial ν u huM huI) (toViscousX1Spatial ν v hvM hvI) =
      (ν : ℝ) * coordinateX1Mass (fun ξ => u ξ - v ξ) := by
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  calc
    (∫ ξ, ‖((toViscousX1Spatial ν u huM huI -
        toViscousX1Spatial ν v hvM hvI : ViscousX1Spatial ν) ξ)‖
        ∂viscousX1FrequencyMeasure ν) =
      ∫ ξ, ‖coordinateL1 (fun ζ => u ζ - v ζ) ξ‖
        ∂viscousX1FrequencyMeasure ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (toViscousX1Spatial ν u huM huI)
            (toViscousX1Spatial ν v hvM hvI),
          coeFn_toViscousX1Spatial ν u huM huI,
          coeFn_toViscousX1Spatial ν v hvM hvI] with ξ hsub huξ hvξ
        rw [hsub, Pi.sub_apply, huξ, hvξ]
        rfl
    _ = (ν : ℝ) * coordinateX1Mass (fun ξ => u ξ - v ξ) :=
      integral_norm_coordinateL1_viscousX1_eq ν _
        (x1_sub_integrable u v huM hvM huI hvI)

/-- The repaired representatives' `X⁻¹` difference is bounded almost
everywhere by the exact distance of the completed `L∞` slots. -/
theorem coordinateXm1Mass_everywhere_sub_le_dist_ae
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) :
    ∀ᵐ t ∂leiLinTimeMeasure T,
      coordinateXm1Mass (fun ξ => everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ) ≤
      dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) := by
  let xs : Xm1TimeSlot T := x.1.fst
  let ys : Xm1TimeSlot T := y.1.fst
  have htop := ae_le_lpNorm_exponent_top (Lp.memLp (xs - ys))
  have hnorm : lpNorm (fun t => (xs - ys) t) ∞ (leiLinTimeMeasure T) =
      ‖xs - ys‖ := by
    rw [← toReal_eLpNorm (Lp.aestronglyMeasurable (xs - ys)), ← Lp.norm_def]
  filter_upwards [htop, Lp.coeFn_sub xs ys,
    everywhereXm1Section_eq_ae ν hν T x,
    everywhereXm1Section_eq_ae ν hν T y] with t ht hsub hx hy
  have hsp := dist_toXm1Spatial_eq_coordinateXm1Mass_sub
    (everywhereRawRepresentative ν T x t)
    (everywhereRawRepresentative ν T y t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t)
    (everywhereRawRepresentative_xm1_integrable ν T x t)
    (everywhereRawRepresentative_xm1_integrable ν T y t)
  change dist (everywhereXm1Section ν hν T x t)
      (everywhereXm1Section ν hν T y t) = _ at hsp
  calc
    coordinateXm1Mass (fun ξ => everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ) =
        dist (everywhereXm1Section ν hν T x t)
          (everywhereXm1Section ν hν T y t) := hsp.symm
    _ = dist (xs t) (ys t) := by rw [hx, hy]
    _ = ‖(xs - ys) t‖ := by
      rw [dist_eq_norm]
      simpa only [Pi.sub_apply] using congrArg norm hsub.symm
    _ ≤ ‖xs - ys‖ := by simpa only [hnorm] using ht
    _ = dist xs ys := (dist_eq_norm xs ys).symm

/-- The raw difference of two repaired representatives has both weighted
spatial moments at every time. -/
theorem everywhereRawRepresentative_sub_fixedTime_inputs
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) :
    (∀ t (i : Fin 3), AEStronglyMeasurable (fun ξ =>
      everywhereRawRepresentative ν T x t ξ i -
        everywhereRawRepresentative ν T y t ξ i) volume) ∧
    (∀ t (i : Fin 3), Integrable (fun ξ => ‖ξ‖⁻¹ * ‖
      everywhereRawRepresentative ν T x t ξ i -
        everywhereRawRepresentative ν T y t ξ i‖)) ∧
    (∀ t (i : Fin 3), Integrable (fun ξ => ‖ξ‖ * ‖
      everywhereRawRepresentative ν T x t ξ i -
        everywhereRawRepresentative ν T y t ξ i‖)) := by
  refine ⟨fun t i =>
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t i).sub
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t i), ?_, ?_⟩
  · exact fun t i => xm1_sub_integrable
      (everywhereRawRepresentative ν T x t)
      (everywhereRawRepresentative ν T y t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t)
      (everywhereRawRepresentative_xm1_integrable ν T x t)
      (everywhereRawRepresentative_xm1_integrable ν T y t) i
  · exact fun t i => x1_sub_integrable
      (everywhereRawRepresentative ν T x t)
      (everywhereRawRepresentative ν T y t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t)
      (everywhereRawRepresentative_x1_integrable ν T x t)
      (everywhereRawRepresentative_x1_integrable ν T y t) i

/-- The raw `X⁻¹` difference mass is strongly measurable in time. -/
theorem coordinateXm1Mass_everywhere_sub_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) :
    AEStronglyMeasurable (fun t => coordinateXm1Mass (fun ξ =>
      everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ)) (leiLinTimeMeasure T) := by
  let xs : Xm1TimeSlot T := x.1.fst
  let ys : Xm1TimeSlot T := y.1.fst
  apply (Lp.aestronglyMeasurable (xs - ys)).norm.congr
  filter_upwards [Lp.coeFn_sub xs ys,
    everywhereXm1Section_eq_ae ν hν T x,
    everywhereXm1Section_eq_ae ν hν T y] with t hsub hx hy
  have hsp := dist_toXm1Spatial_eq_coordinateXm1Mass_sub
    (everywhereRawRepresentative ν T x t)
    (everywhereRawRepresentative ν T y t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t)
    (everywhereRawRepresentative_xm1_integrable ν T x t)
    (everywhereRawRepresentative_xm1_integrable ν T y t)
  change dist (everywhereXm1Section ν hν T x t)
      (everywhereXm1Section ν hν T y t) = _ at hsp
  calc
    ‖(xs - ys) t‖ = dist (xs t) (ys t) := by
      rw [dist_eq_norm]
      simpa only [Pi.sub_apply] using congrArg norm hsub
    _ = dist (everywhereXm1Section ν hν T x t)
        (everywhereXm1Section ν hν T y t) := by rw [hx, hy]
    _ = _ := hsp

/-- The raw `X¹` difference mass is strongly measurable in time. -/
theorem coordinateX1Mass_everywhere_sub_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) :
    AEStronglyMeasurable (fun t => coordinateX1Mass (fun ξ =>
      everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ)) (leiLinTimeMeasure T) := by
  let xs : ViscousX1TimeSlot ν T := x.1.snd
  let ys : ViscousX1TimeSlot ν T := y.1.snd
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hscaled : AEStronglyMeasurable (fun t => (ν : ℝ) *
      coordinateX1Mass (fun ξ => everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ)) (leiLinTimeMeasure T) := by
    apply (Lp.aestronglyMeasurable (xs - ys)).norm.congr
    filter_upwards [Lp.coeFn_sub xs ys,
      everywhereViscousX1Section_eq_ae ν hν T x,
      everywhereViscousX1Section_eq_ae ν hν T y] with t hsub hx hy
    have hsp := dist_toViscousX1Spatial_eq_coordinateX1Mass_sub ν
      (everywhereRawRepresentative ν T x t)
      (everywhereRawRepresentative ν T y t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t)
      (everywhereRawRepresentative_x1_integrable ν T x t)
      (everywhereRawRepresentative_x1_integrable ν T y t)
    change dist (everywhereViscousX1Section ν hν T x t)
        (everywhereViscousX1Section ν hν T y t) = _ at hsp
    calc
      ‖(xs - ys) t‖ = dist (xs t) (ys t) := by
        rw [dist_eq_norm]
        simpa only [Pi.sub_apply] using congrArg norm hsub
      _ = dist (everywhereViscousX1Section ν hν T x t)
          (everywhereViscousX1Section ν hν T y t) := by rw [hx, hy]
      _ = _ := hsp
  have hunscaled := hscaled.const_mul (ν : ℝ)⁻¹
  apply hunscaled.congr
  filter_upwards with t
  field_simp

/-- The unscaled `X¹` mass of the repaired representative difference is
time-integrable. -/
theorem coordinateX1Mass_everywhere_sub_integrable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) :
    Integrable (fun t => coordinateX1Mass (fun ξ =>
      everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ)) (leiLinTimeMeasure T) := by
  let xs : ViscousX1TimeSlot ν T := x.1.snd
  let ys : ViscousX1TimeSlot ν T := y.1.snd
  have hnorm : Integrable (fun t => ‖(xs - ys) t‖) (leiLinTimeMeasure T) :=
    (memLp_one_iff_integrable.mp (Lp.memLp (xs - ys))).norm
  have heq : ∀ᵐ t ∂leiLinTimeMeasure T,
      ‖(xs - ys) t‖ = (ν : ℝ) * coordinateX1Mass (fun ξ =>
        everywhereRawRepresentative ν T x t ξ -
          everywhereRawRepresentative ν T y t ξ) := by
    filter_upwards [Lp.coeFn_sub xs ys,
      everywhereViscousX1Section_eq_ae ν hν T x,
      everywhereViscousX1Section_eq_ae ν hν T y] with t hsub hx hy
    have hsp := dist_toViscousX1Spatial_eq_coordinateX1Mass_sub ν
      (everywhereRawRepresentative ν T x t)
      (everywhereRawRepresentative ν T y t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t)
      (everywhereRawRepresentative_x1_integrable ν T x t)
      (everywhereRawRepresentative_x1_integrable ν T y t)
    change dist (everywhereViscousX1Section ν hν T x t)
        (everywhereViscousX1Section ν hν T y t) = _ at hsp
    calc
      ‖(xs - ys) t‖ = dist (xs t) (ys t) := by
        rw [dist_eq_norm]
        simpa only [Pi.sub_apply] using congrArg norm hsub
      _ = dist (everywhereViscousX1Section ν hν T x t)
          (everywhereViscousX1Section ν hν T y t) := by rw [hx, hy]
      _ = _ := hsp
  have hscaled : Integrable (fun t => (ν : ℝ) * coordinateX1Mass (fun ξ =>
      everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ)) (leiLinTimeMeasure T) :=
    hnorm.congr heq
  have hunscaled := hscaled.const_mul (ν : ℝ)⁻¹
  apply hunscaled.congr
  filter_upwards with t
  field_simp

/-- The viscosity-weighted time integral of the raw `X¹` difference is the
exact distance of the completed `L¹` slots. -/
theorem mul_integral_coordinateX1Mass_everywhere_sub_eq_dist
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) :
    (ν : ℝ) * ∫ t, coordinateX1Mass (fun ξ =>
      everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ) ∂leiLinTimeMeasure T =
      dist (x.1.snd : ViscousX1TimeSlot ν T)
        (y.1.snd : ViscousX1TimeSlot ν T) := by
  let xs : ViscousX1TimeSlot ν T := x.1.snd
  let ys : ViscousX1TimeSlot ν T := y.1.snd
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub xs ys,
    everywhereViscousX1Section_eq_ae ν hν T x,
    everywhereViscousX1Section_eq_ae ν hν T y] with t hsub hx hy
  have hsp := dist_toViscousX1Spatial_eq_coordinateX1Mass_sub ν
    (everywhereRawRepresentative ν T x t)
    (everywhereRawRepresentative ν T y t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t)
    (everywhereRawRepresentative_x1_integrable ν T x t)
    (everywhereRawRepresentative_x1_integrable ν T y t)
  change dist (everywhereViscousX1Section ν hν T x t)
      (everywhereViscousX1Section ν hν T y t) = _ at hsp
  calc
    (ν : ℝ) * coordinateX1Mass (fun ξ =>
        everywhereRawRepresentative ν T x t ξ -
          everywhereRawRepresentative ν T y t ξ) =
        dist (everywhereViscousX1Section ν hν T x t)
          (everywhereViscousX1Section ν hν T y t) := hsp.symm
    _ = dist (xs t) (ys t) := by rw [hx, hy]
    _ = ‖(xs - ys) t‖ := by
      rw [dist_eq_norm]
      simpa only [Pi.sub_apply] using congrArg norm hsub.symm

end Navier.Analysis.ContinuousLeiLinRepresentativeDistance

#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeDistance.dist_toXm1Spatial_eq_coordinateXm1Mass_sub
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeDistance.dist_toViscousX1Spatial_eq_coordinateX1Mass_sub
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeDistance.coordinateXm1Mass_everywhere_sub_le_dist_ae
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeDistance.everywhereRawRepresentative_sub_fixedTime_inputs
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeDistance.coordinateXm1Mass_everywhere_sub_aestronglyMeasurable
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeDistance.coordinateX1Mass_everywhere_sub_aestronglyMeasurable
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeDistance.coordinateX1Mass_everywhere_sub_integrable
#print axioms Navier.Analysis.ContinuousLeiLinRepresentativeDistance.mul_integral_coordinateX1Mass_everywhere_sub_eq_dist
