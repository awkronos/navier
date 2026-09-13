import Navier.Analysis.ContinuousLeiLinBoxRepresentative

/-!
# Automatic time-product integrability on the actual Lei--Lin box

The nonlinear self-map estimate asks separately for local time integrability
of the `X¹` mass and of `X⁻¹·X¹`.  For the everywhere representative of an
actual quotient-box element, both follow from the completed slots: the `X¹`
mass is globally integrable on the finite horizon, while the `X⁻¹` mass is
pointwise bounded by the box radius.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinBoxRepresentative

namespace Navier.Analysis.ContinuousLeiLinBoxProduct

theorem coordinateXm1Mass_nonneg (u : ES → ComplexSpace) :
    0 ≤ coordinateXm1Mass u := by
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun ξ =>
    mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg (u ξ i))

theorem coordinateX1Mass_nonneg (u : ES → ComplexSpace) :
    0 ≤ coordinateX1Mass u := by
  exact Finset.sum_nonneg fun i _ => integral_nonneg fun ξ =>
    mul_nonneg (norm_nonneg ξ) (norm_nonneg (u ξ i))

/-- Time measurability of the pointwise `X⁻¹` mass is inherited from the
strongly measurable rebuilt spatial section. -/
theorem coordinateXm1Mass_everywhere_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x : ActualLinkedCarrier ν T) :
    AEStronglyMeasurable (fun t => coordinateXm1Mass
      (everywhereRawRepresentative ν T x t)) (leiLinTimeMeasure T) := by
  have hnorm := (everywhereXm1Section_aestronglyMeasurable ν hν T x).norm
  apply hnorm.congr
  filter_upwards with t
  exact norm_xm1Section
    (everywhereRawRepresentative ν T x)
    (everywhereRawRepresentative_aestronglyMeasurable ν hν T x)
    (everywhereRawRepresentative_xm1_integrable ν T x) t

/-- The nonlinear `X⁻¹·X¹` time feed is integrable on the whole finite
horizon for every element of the actual quotient box. -/
theorem integrable_coordinateXm1_mul_X1_everywhere_of_mem_box
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius) :
    Integrable (fun t =>
      coordinateXm1Mass (everywhereRawRepresentative ν T x.1 t) *
      coordinateX1Mass (everywhereRawRepresentative ν T x.1 t))
      (leiLinTimeMeasure T) := by
  have hx1 := coordinateX1Mass_everywhereRawRepresentative_integrable ν hν T x.1
  apply hx1.bdd_mul
    (coordinateXm1Mass_everywhere_aestronglyMeasurable ν hν T x.1)
  filter_upwards with t
  rw [Real.norm_of_nonneg (coordinateXm1Mass_nonneg _)]
  exact coordinateXm1Mass_everywhere_le_of_mem_box
    ν hν T xm1Radius x1WeightedRadius x t

/-- The two local-in-time integrability hypotheses used by the existing
self-map theorem follow on every causal subinterval of a `2R` quotient box. -/
theorem everywhereRawRepresentative_local_integrability_inputs
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ)
    (x : ActualLinkedBox ν T (2 * R) (2 * R)) :
    (∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s => coordinateX1Mass
        (everywhereRawRepresentative ν T x.1 s)) (Icc (0 : ℝ) t) volume) ∧
    (∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s =>
        coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
        coordinateX1Mass (everywhereRawRepresentative ν T x.1 s))
        (Icc (0 : ℝ) t) volume) := by
  have hx1 := coordinateX1Mass_everywhereRawRepresentative_integrable ν hν T x.1
  have hprod := integrable_coordinateXm1_mul_X1_everywhere_of_mem_box
    ν hν T (2 * R) (2 * R) x
  change Integrable _ (volume.restrict (Icc (0 : ℝ) T)) at hx1 hprod
  constructor
  · intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
      fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
    exact hx1.mono_measure (Measure.restrict_mono hsub le_rfl)
  · intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
      fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
    exact hprod.mono_measure (Measure.restrict_mono hsub le_rfl)

/-- Existing nonlinear self-map consumer with all four raw input-box
hypotheses discharged by membership in the actual complete quotient box.  The
remaining two hypotheses are precisely the analytic estimates for the mild
image itself. -/
theorem continuousMildImage_self_map_ball_twoR_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRν : R ≤ (ν : ℝ) / 16) (a : ES → ComplexSpace)
    (x : ActualLinkedBox ν T (2 * R) (2 * R))
    (haR : coordinateXm1Mass a ≤ R)
    (hB1 : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t) ≤
        coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
            coordinateX1Mass (everywhereRawRepresentative ν T x.1 s))
    (hD3 : ∫ t in Icc (0 : ℝ) T,
      coordinateX1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t) ≤
        (ν : ℝ)⁻¹ * coordinateXm1Mass a +
          (3 : ℝ) * (ν : ℝ)⁻¹ * ∫ s in Icc (0 : ℝ) T,
            coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
              coordinateX1Mass (everywhereRawRepresentative ν T x.1 s)) :
    (∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t) ≤ 2 * R) ∧
      (∫ t in Icc (0 : ℝ) T,
        coordinateX1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
          (everywhereRawRepresentative ν T x.1) t)) ≤
            2 * (ν : ℝ)⁻¹ * R := by
  obtain ⟨hballXm1, hballX1⟩ :=
    everywhereRawRepresentative_twoR_bounds ν hν T R x
  obtain ⟨hX1i, hprod⟩ :=
    everywhereRawRepresentative_local_integrability_inputs ν hν T R x
  exact continuousMildImage_self_map_ball_twoR (ν : ℝ) R T
    (by exact_mod_cast hν) hR hT hRν a
    (everywhereRawRepresentative ν T x.1) haR hballXm1 hballX1
    hX1i hprod hB1 hD3

end Navier.Analysis.ContinuousLeiLinBoxProduct

#print axioms Navier.Analysis.ContinuousLeiLinBoxProduct.coordinateXm1Mass_everywhere_aestronglyMeasurable
#print axioms Navier.Analysis.ContinuousLeiLinBoxProduct.integrable_coordinateXm1_mul_X1_everywhere_of_mem_box
#print axioms Navier.Analysis.ContinuousLeiLinBoxProduct.everywhereRawRepresentative_local_integrability_inputs
#print axioms Navier.Analysis.ContinuousLeiLinBoxProduct.continuousMildImage_self_map_ball_twoR_of_actualBox
