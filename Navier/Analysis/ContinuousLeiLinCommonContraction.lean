import Navier.Analysis.ContinuousLeiLinRepresentativeDistance
import Navier.Analysis.ContinuousLeiLinBanachContraction
import Navier.Analysis.ContinuousLeiLinBoxInterpolation
import Navier.Analysis.Ladyzhenskaya

/-!
# Common-representative contraction feed

This module transports the completed linked-carrier distance to the raw
Fourier representative used by the nonlinear estimates.  The essential-sup
`X⁻¹` bound is used almost everywhere, matching the quotient carrier exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Set Filter BigOperators
open scoped ENNReal NNReal Topology
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinAdmissibleContraction
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinTrajectoryLift
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeDistance
open Navier.Analysis.ContinuousLeiLinPhysicalIntegrability
open Navier.Analysis.ContinuousLeiLinBoxRepresentative
open Navier.Analysis.ContinuousLeiLinBoxProduct
open Navier.Analysis.ContinuousLeiLinBoxInterpolation

namespace Navier.Analysis.ContinuousLeiLinCommonContraction

private theorem coordinateXm1Mass_nonneg (u : ES → ComplexSpace) :
    0 ≤ coordinateXm1Mass u :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)

private theorem coordinateX1Mass_nonneg (u : ES → ComplexSpace) :
    0 ≤ coordinateX1Mass u :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- A bounded-frequency `X⁰` norm of the raw difference is the norm of the
same continuous restriction applied to the difference of the two completed
`X⁻¹` sections. -/
private theorem norm_xm1ToTruncatedX0_everywhere_sub_eq
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x y : ActualLinkedCarrier ν T)
    (n : ℕ) (t : ℝ) :
    ‖xm1ToTruncatedX0 n (everywhereXm1Section ν hν T x t -
        everywhereXm1Section ν hν T y t)‖ =
      ∑ i : Fin 3, ∫ ξ in x0TruncationSet n,
        ‖everywhereRawRepresentative ν T x t ξ i -
          everywhereRawRepresentative ν T y t ξ i‖ := by
  rw [L1.norm_eq_integral_norm]
  have hout : xm1ToTruncatedX0 n
      (everywhereXm1Section ν hν T x t - everywhereXm1Section ν hν T y t)
      =ᵐ[volume.restrict (x0TruncationSet n)]
        (fun ξ => ((everywhereXm1Section ν hν T x t -
          everywhereXm1Section ν hν T y t : Xm1Spatial) ξ)) := by
    exact Lp.coeFn_LpToLpOfMeasureLeSMul
      (p := (1 : ℝ≥0∞)) (c := (n + 1 : ℝ≥0∞)) (by simp)
      (x0TruncationMeasure_le n) _
  have hac : volume.restrict (x0TruncationSet n) ≪ xm1FrequencyMeasure :=
    Measure.absolutelyContinuous_of_le_smul (x0TruncationMeasure_le n)
  have hx : everywhereXm1Section ν hν T x t
      =ᵐ[volume.restrict (x0TruncationSet n)]
        coordinateL1 (everywhereRawRepresentative ν T x t) := by
    apply hac.ae_eq
    exact coeFn_toXm1Spatial
      (everywhereRawRepresentative ν T x t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T x t)
      (everywhereRawRepresentative_xm1_integrable ν T x t)
  have hy : everywhereXm1Section ν hν T y t
      =ᵐ[volume.restrict (x0TruncationSet n)]
        coordinateL1 (everywhereRawRepresentative ν T y t) := by
    apply hac.ae_eq
    exact coeFn_toXm1Spatial
      (everywhereRawRepresentative ν T y t)
      (everywhereRawRepresentative_aestronglyMeasurable ν hν T y t)
      (everywhereRawRepresentative_xm1_integrable ν T y t)
  have hsub : (fun ξ => ((everywhereXm1Section ν hν T x t -
      everywhereXm1Section ν hν T y t : Xm1Spatial) ξ))
      =ᵐ[volume.restrict (x0TruncationSet n)]
        (fun ξ => everywhereXm1Section ν hν T x t ξ -
          everywhereXm1Section ν hν T y t ξ) := by
    apply hac.ae_eq
    exact Lp.coeFn_sub (everywhereXm1Section ν hν T x t)
      (everywhereXm1Section ν hν T y t)
  calc
    (∫ ξ, ‖xm1ToTruncatedX0 n
        (everywhereXm1Section ν hν T x t - everywhereXm1Section ν hν T y t) ξ‖
        ∂volume.restrict (x0TruncationSet n)) =
        ∫ ξ, ‖coordinateL1 (fun ζ => everywhereRawRepresentative ν T x t ζ -
          everywhereRawRepresentative ν T y t ζ) ξ‖
          ∂volume.restrict (x0TruncationSet n) := by
      apply integral_congr_ae
      filter_upwards [hout, hsub, hx, hy] with ξ houtξ hsubξ hxξ hyξ
      rw [houtξ, hsubξ, hxξ, hyξ]
      rfl
    _ = ∫ ξ in x0TruncationSet n, ∑ i : Fin 3,
        ‖everywhereRawRepresentative ν T x t ξ i -
          everywhereRawRepresentative ν T y t ξ i‖ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [norm_coordinateL1]
      simp only [Pi.sub_apply]
    _ = ∑ i : Fin 3, ∫ ξ in x0TruncationSet n,
        ‖everywhereRawRepresentative ν T x t ξ i -
          everywhereRawRepresentative ν T y t ξ i‖ := by
      obtain ⟨_, hwm1, hw1⟩ :=
        everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
      exact integral_finsetSum Finset.univ fun i _ =>
        (integrable_norm_of_integrable_Xm1_X1
          (fun ξ : ES => everywhereRawRepresentative ν T x t ξ i -
            everywhereRawRepresentative ν T y t ξ i)
          (hwm1 t i) (hw1 t i)).integrableOn

/-- The unweighted mass of the repaired raw difference is strongly measurable
in time.  The proof reads it as the monotone limit of continuous bounded-
frequency restrictions of the completed `X⁻¹` sections. -/
theorem coordinateX0Mass_everywhere_sub_aestronglyMeasurable
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ) (x y : ActualLinkedCarrier ν T) :
    AEStronglyMeasurable (fun t => coordinateX0Mass (fun ξ =>
      everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ)) (leiLinTimeMeasure T) := by
  let f : ℕ → ℝ → ℝ := fun n t =>
    ‖xm1ToTruncatedX0 n (everywhereXm1Section ν hν T x t -
      everywhereXm1Section ν hν T y t)‖
  have hf (n : ℕ) : AEStronglyMeasurable (f n) (leiLinTimeMeasure T) := by
    exact (((xm1ToTruncatedX0 n).continuous.comp_aestronglyMeasurable
      ((everywhereXm1Section_aestronglyMeasurable ν hν T x).sub
        (everywhereXm1Section_aestronglyMeasurable ν hν T y))).norm)
  apply aestronglyMeasurable_of_tendsto_ae atTop hf
  exact Eventually.of_forall fun t => by
    obtain ⟨_, hwm1, hw1⟩ :=
      everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
    have hi (i : Fin 3) : Tendsto (fun n => ∫ ξ in x0TruncationSet n,
        ‖everywhereRawRepresentative ν T x t ξ i -
          everywhereRawRepresentative ν T y t ξ i‖) atTop
        (𝓝 (∫ ξ : ES, ‖everywhereRawRepresentative ν T x t ξ i -
          everywhereRawRepresentative ν T y t ξ i‖)) := by
      have hInt : IntegrableOn (fun ξ : ES =>
          ‖everywhereRawRepresentative ν T x t ξ i -
            everywhereRawRepresentative ν T y t ξ i‖)
          (⋃ n : ℕ, x0TruncationSet n) := by
        rw [iUnion_x0TruncationSet]
        simpa using integrable_norm_of_integrable_Xm1_X1
          (fun ξ : ES => everywhereRawRepresentative ν T x t ξ i -
            everywhereRawRepresentative ν T y t ξ i)
          (hwm1 t i) (hw1 t i)
      have h := tendsto_setIntegral_of_monotone
        (f := fun ξ : ES => ‖everywhereRawRepresentative ν T x t ξ i -
          everywhereRawRepresentative ν T y t ξ i‖)
        (fun n => Metric.isClosed_closedBall.measurableSet)
        x0TruncationSet_monotone hInt
      have hu : (⋃ n : ℕ, Metric.closedBall (0 : ES) (n + 1 : ℝ)) = Set.univ := by
        simpa [x0TruncationSet] using iUnion_x0TruncationSet
      rw [hu] at h
      simpa [x0TruncationSet] using h
    have hsum := tendsto_finsetSum Finset.univ fun i _ => hi i
    apply hsum.congr'
    filter_upwards with n
    exact (norm_xm1ToTruncatedX0_everywhere_sub_eq ν hν T x y n t).symm

/-- The mixed admissible feed only needs its `X⁻¹` bound almost everywhere in
time. -/
theorem integral_Xm1_mul_X1_le_admissible_bounds_ae
    (A B t : ℝ) (hA : 0 ≤ A) (w : ℝ → ES → ComplexSpace)
    (hmixed : Integrable (fun s : ℝ =>
      coordinateXm1Mass (w s) * coordinateX1Mass (w s))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) t),
      coordinateXm1Mass (w s) ≤ A)
    (hX1int : Integrable (fun s : ℝ => coordinateX1Mass (w s))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (w s) ≤ B) :
    (∫ s in Icc (0 : ℝ) t,
      coordinateXm1Mass (w s) * coordinateX1Mass (w s)) ≤ A * B := by
  have hstep : (∫ s in Icc (0 : ℝ) t,
      coordinateXm1Mass (w s) * coordinateX1Mass (w s)) ≤
      ∫ s in Icc (0 : ℝ) t, A * coordinateX1Mass (w s) := by
    refine integral_mono_ae hmixed (hX1int.const_mul A) ?_
    filter_upwards [hdist] with s hs
    exact mul_le_mul_of_nonneg_right hs (coordinateX1Mass_nonneg (w s))
  refine hstep.trans ?_
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hX1 hA

/-- The admissible square-root interpolation estimate with the faithful
almost-everywhere `X⁻¹` distance input. -/
theorem sqrt_integral_X0_sq_le_admissible_ae
    (w : ℝ → ES → ComplexSpace) (ν t A B : ℝ) (hν : 0 < ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hwm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖w r η j‖))
    (hw1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖w r η j‖))
    (hmixed : Integrable (fun s : ℝ =>
      coordinateXm1Mass (w s) * coordinateX1Mass (w s))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) t),
      coordinateXm1Mass (w s) ≤ A)
    (hX1int : Integrable (fun s : ℝ => coordinateX1Mass (w s))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (w s) ≤ B) :
    Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (w s) ^ 2) ≤
      admissibleNorm ν A B / (2 * Real.sqrt ν) := by
  refine (sqrt_X0_sq_le_sqrt_Xm1_mul_X1 w t hwm1 hw1 hmixed).trans ?_
  refine (Real.sqrt_le_sqrt
    (integral_Xm1_mul_X1_le_admissible_bounds_ae A B t hA w hmixed
      hdist hX1int hX1)).trans ?_
  exact sqrt_mul_le_admissible_norm ν A B hν hA hB

/-- For two elements of the actual linked carrier, the `L²_t X⁰` size of the
repaired raw difference is controlled by the exact sum of their two completed
slot distances. -/
theorem sqrt_integral_coordinateX0Mass_sub_sq_le_linked_distance
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) :
    Real.sqrt (∫ t, coordinateX0Mass (fun ξ =>
      everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ) ^ 2 ∂leiLinTimeMeasure T) ≤
      (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
        dist (x.1.snd : ViscousX1TimeSlot ν T)
          (y.1.snd : ViscousX1TimeSlot ν T)) /
        (2 * Real.sqrt (ν : ℝ)) := by
  let w : ℝ → ES → ComplexSpace := fun t ξ =>
    everywhereRawRepresentative ν T x t ξ -
      everywhereRawRepresentative ν T y t ξ
  let A := dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T)
  let D := dist (x.1.snd : ViscousX1TimeSlot ν T)
    (y.1.snd : ViscousX1TimeSlot ν T)
  let B := (ν : ℝ)⁻¹ * D
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hA : 0 ≤ A := dist_nonneg
  have hD : 0 ≤ D := dist_nonneg
  have hB : 0 ≤ B := mul_nonneg (inv_nonneg.mpr hνR.le) hD
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  have hXmM := coordinateXm1Mass_everywhere_sub_aestronglyMeasurable ν hν T x y
  have hX1M := coordinateX1Mass_everywhere_sub_aestronglyMeasurable ν hν T x y
  have hX1int := coordinateX1Mass_everywhere_sub_integrable ν hν T x y
  have hdist : ∀ᵐ t ∂leiLinTimeMeasure T, coordinateXm1Mass (w t) ≤ A := by
    simpa [w, A] using coordinateXm1Mass_everywhere_sub_le_dist_ae ν hν T x y
  have hX1eq : (∫ t, coordinateX1Mass (w t) ∂leiLinTimeMeasure T) = B := by
    have hmul := mul_integral_coordinateX1Mass_everywhere_sub_eq_dist ν hν T x y
    calc
      (∫ t, coordinateX1Mass (w t) ∂leiLinTimeMeasure T) =
          (ν : ℝ)⁻¹ * ((ν : ℝ) * ∫ t,
            coordinateX1Mass (w t) ∂leiLinTimeMeasure T) := by
              field_simp
      _ = (ν : ℝ)⁻¹ * D := by simpa [w, D] using congrArg ((ν : ℝ)⁻¹ * ·) hmul
      _ = B := rfl
  have hmixed : Integrable (fun t =>
      coordinateXm1Mass (w t) * coordinateX1Mass (w t))
      (leiLinTimeMeasure T) := by
    have hmeas : AEStronglyMeasurable (fun t =>
        coordinateXm1Mass (w t) * coordinateX1Mass (w t))
        (leiLinTimeMeasure T) := by
      exact hXmM.mul hX1M
    apply (hX1int.const_mul A).mono' hmeas
    filter_upwards [hdist] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (coordinateXm1Mass_nonneg (w t))
      (coordinateX1Mass_nonneg (w t)))]
    simpa only [w] using
      mul_le_mul_of_nonneg_right ht (coordinateX1Mass_nonneg (w t))
  have hcore := sqrt_integral_X0_sq_le_admissible_ae
    w (ν : ℝ) T A B hνR hA hB hwm1 hw1 hmixed hdist hX1int hX1eq.le
  have hAB : admissibleNorm (ν : ℝ) A B = A + D := by
    rw [admissibleNorm]
    dsimp [B]
    field_simp
  rw [hAB] at hcore
  simpa only [leiLinTimeMeasure, w, A, D] using hcore

/-- The square of the unweighted mass of a repaired representative difference
is integrable on the faithful finite-horizon time measure. -/
theorem integrable_coordinateX0Mass_everywhere_sub_sq
    (ν : ℝ≥0) (hν : 0 < ν) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) :
    Integrable (fun t => coordinateX0Mass (fun ξ =>
      everywhereRawRepresentative ν T x t ξ -
        everywhereRawRepresentative ν T y t ξ) ^ 2)
      (leiLinTimeMeasure T) := by
  let w : ℝ → ES → ComplexSpace := fun t ξ =>
    everywhereRawRepresentative ν T x t ξ -
      everywhereRawRepresentative ν T y t ξ
  obtain ⟨_, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  have hXmM := coordinateXm1Mass_everywhere_sub_aestronglyMeasurable ν hν T x y
  have hX1M := coordinateX1Mass_everywhere_sub_aestronglyMeasurable ν hν T x y
  have hX1int := coordinateX1Mass_everywhere_sub_integrable ν hν T x y
  let A := dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T)
  have hdist : ∀ᵐ t ∂leiLinTimeMeasure T, coordinateXm1Mass (w t) ≤ A := by
    simpa [w, A] using coordinateXm1Mass_everywhere_sub_le_dist_ae ν hν T x y
  have hmixed : Integrable (fun t =>
      coordinateXm1Mass (w t) * coordinateX1Mass (w t))
      (leiLinTimeMeasure T) := by
    apply (hX1int.const_mul A).mono' (hXmM.mul hX1M)
    filter_upwards [hdist] with t ht
    simp only [Pi.mul_apply]
    rw [Real.norm_of_nonneg (mul_nonneg (coordinateXm1Mass_nonneg (w t))
      (coordinateX1Mass_nonneg (w t)))]
    simpa only [w] using
      mul_le_mul_of_nonneg_right ht (coordinateX1Mass_nonneg (w t))
  apply hmixed.mono'
    ((coordinateX0Mass_everywhere_sub_aestronglyMeasurable ν hν T x y).pow 2)
  filter_upwards with t
  simp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg (coordinateX0Mass (w t)))]
  exact coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass
    (w t) (hwm1 t) (hw1 t)

/-- An actual `2R` box element has the exact ball-side `L²_t X⁰` bound used
by both polarization slots of the contraction. -/
theorem sqrt_integral_coordinateX0Mass_sq_le_actual_twoR_box
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hR : 0 ≤ R)
    (z : ActualLinkedBox ν T (2 * R) (2 * R)) :
    Real.sqrt (∫ t, coordinateX0Mass
      (everywhereRawRepresentative ν T z.1 t) ^ 2 ∂leiLinTimeMeasure T) ≤
      2 * R * Real.sqrt (ν : ℝ)⁻¹ := by
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hzmixed := integrable_coordinateXm1_mul_X1_everywhere_of_mem_box
    ν hν T (2 * R) (2 * R) z
  have hzX1 := coordinateX1Mass_everywhereRawRepresentative_integrable ν hν T z.1
  obtain ⟨hzXm1, hzX1b⟩ := everywhereRawRepresentative_twoR_bounds ν hν T R z
  have hbase := sqrt_X0_sq_le_sqrt_Xm1_mul_X1
    (everywhereRawRepresentative ν T z.1) T
    (everywhereRawRepresentative_xm1_integrable ν T z.1)
    (everywhereRawRepresentative_x1_integrable ν T z.1)
    (by simpa only [leiLinTimeMeasure] using hzmixed)
  have hbase' : Real.sqrt (∫ t, coordinateX0Mass
      (everywhereRawRepresentative ν T z.1 t) ^ 2 ∂leiLinTimeMeasure T) ≤
      Real.sqrt (∫ t, coordinateXm1Mass (everywhereRawRepresentative ν T z.1 t) *
        coordinateX1Mass (everywhereRawRepresentative ν T z.1 t)
        ∂leiLinTimeMeasure T) := by
    simpa only [leiLinTimeMeasure] using hbase
  refine hbase'.trans ?_
  refine ((Real.sqrt_le_sqrt ?_).trans_eq
    (Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR)
      (Real.sqrt_nonneg _))))
  calc
    (∫ t, coordinateXm1Mass (everywhereRawRepresentative ν T z.1 t) *
        coordinateX1Mass (everywhereRawRepresentative ν T z.1 t)
        ∂leiLinTimeMeasure T) ≤
        (2 * R) * (2 * (ν : ℝ)⁻¹ * R) := by
      apply integral_Xm1_mul_X1_le_admissible_bounds_ae
        (2 * R) (2 * (ν : ℝ)⁻¹ * R) T (by positivity)
        (everywhereRawRepresentative ν T z.1)
        (by simpa only [leiLinTimeMeasure] using hzmixed)
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact hzXm1 t ht
      · simpa only [leiLinTimeMeasure] using hzX1
      · exact hzX1b
    _ = 4 * (ν : ℝ)⁻¹ * R ^ 2 := by ring
    _ = (2 * R * Real.sqrt (ν : ℝ)⁻¹) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (inv_nonneg.mpr hνR.le)]
      ring

/-- The two mixed polarization products are integrable for actual quotient
representatives.  This is Hölder in time at `(2,2)`, with both `L²` facts
constructed above from the completed slots. -/
theorem integrable_coordinateX0Mass_sub_mul_everywhere
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T xm1Radius x1WeightedRadius) :
    Integrable (fun t => coordinateX0Mass (fun ξ =>
        everywhereRawRepresentative ν T x t ξ -
          everywhereRawRepresentative ν T y t ξ) *
      coordinateX0Mass (everywhereRawRepresentative ν T z.1 t))
      (leiLinTimeMeasure T) := by
  let f : ℝ → ℝ := fun t => coordinateX0Mass (fun ξ =>
    everywhereRawRepresentative ν T x t ξ -
      everywhereRawRepresentative ν T y t ξ)
  let g : ℝ → ℝ := fun t =>
    coordinateX0Mass (everywhereRawRepresentative ν T z.1 t)
  have hfM := coordinateX0Mass_everywhere_sub_aestronglyMeasurable ν hν T x y
  have hgM := coordinateX0Mass_everywhere_aestronglyMeasurable ν hν T z.1
  have hf2 := integrable_coordinateX0Mass_everywhere_sub_sq ν hν T x y
  have hg2 := integrable_coordinateX0Mass_sq_everywhere_of_mem_box
    ν hν T xm1Radius x1WeightedRadius z
  have hfLp : MemLp f 2 (leiLinTimeMeasure T) :=
    (memLp_two_iff_integrable_sq (by simpa only [f] using hfM)).mpr
      (by simpa only [f] using hf2)
  have hgLp : MemLp g 2 (leiLinTimeMeasure T) :=
    (memLp_two_iff_integrable_sq (by simpa only [g] using hgM)).mpr
      (by simpa only [g] using hg2)
  change Integrable (f * g) (leiLinTimeMeasure T)
  exact hfLp.integrable_mul hgLp

/-- The actual common representative supplies the two polarization feeds
with the completed linked-carrier distance, without any representative-level
distance or product-integrability hypothesis. -/
theorem integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hR : 0 ≤ R)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R)) :
    (∫ t, coordinateX0Mass (fun ξ =>
        everywhereRawRepresentative ν T x t ξ -
          everywhereRawRepresentative ν T y t ξ) *
      coordinateX0Mass (everywhereRawRepresentative ν T z.1 t)
      ∂leiLinTimeMeasure T) ≤
      (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let f : ℝ → ℝ := fun t => coordinateX0Mass (fun ξ =>
    everywhereRawRepresentative ν T x t ξ -
      everywhereRawRepresentative ν T y t ξ)
  let g : ℝ → ℝ := fun t =>
    coordinateX0Mass (everywhereRawRepresentative ν T z.1 t)
  have hf2 := integrable_coordinateX0Mass_everywhere_sub_sq ν hν T x y
  have hg2 := integrable_coordinateX0Mass_sq_everywhere_of_mem_box
    ν hν T (2 * R) (2 * R) z
  have hcs := Navier.Analysis.Ladyzhenskaya.integral_mul_le_sqrt_mul_sqrt
    (μ := leiLinTimeMeasure T) (f := f) (g := g)
    (fun t => by exact Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
    (fun t => by exact Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
    (coordinateX0Mass_everywhere_sub_aestronglyMeasurable ν hν T x y)
    (coordinateX0Mass_everywhere_aestronglyMeasurable ν hν T z.1)
    hf2 hg2
  have hfB := sqrt_integral_coordinateX0Mass_sub_sq_le_linked_distance
    ν hν T x y
  have hgB := sqrt_integral_coordinateX0Mass_sq_le_actual_twoR_box
    ν hν T R hR z
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hdist0 : 0 ≤
      dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
        dist (x.1.snd : ViscousX1TimeSlot ν T)
          (y.1.snd : ViscousX1TimeSlot ν T) := add_nonneg dist_nonneg dist_nonneg
  refine hcs.trans ?_
  calc
    Real.sqrt (∫ t, f t ^ 2 ∂leiLinTimeMeasure T) *
        Real.sqrt (∫ t, g t ^ 2 ∂leiLinTimeMeasure T) ≤
      ((dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) / (2 * Real.sqrt (ν : ℝ))) *
        Real.sqrt (∫ t, g t ^ 2 ∂leiLinTimeMeasure T) := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [f] using hfB
      · exact Real.sqrt_nonneg _
    _ ≤ ((dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) / (2 * Real.sqrt (ν : ℝ))) *
        (2 * R * Real.sqrt (ν : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [g] using hgB
      · positivity
    _ = (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
      have hsinv : Real.sqrt (ν : ℝ)⁻¹ = (Real.sqrt (ν : ℝ))⁻¹ := by
        rw [← Real.sqrt_inv]
      have hss : Real.sqrt (ν : ℝ) * Real.sqrt (ν : ℝ) = (ν : ℝ) :=
        Real.mul_self_sqrt hνR.le
      have hinv2 : (Real.sqrt (ν : ℝ))⁻¹ * (Real.sqrt (ν : ℝ))⁻¹ =
          (ν : ℝ)⁻¹ := by
        rw [← mul_inv, hss]
      rw [hsinv, div_eq_mul_inv, mul_inv]
      rw [← hinv2]
      ring

/-- The same polarization budget on every causal prefix of the carrier
horizon.  This is the form consumed by terminal-time Duhamel estimates. -/
theorem integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance_on
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ) (hR : 0 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) T) (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R)) :
    (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (fun ξ =>
        everywhereRawRepresentative ν T x s ξ -
          everywhereRawRepresentative ν T y s ξ) *
      coordinateX0Mass (everywhereRawRepresentative ν T z.1 s)) ≤
      (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let f : ℝ → ℝ := fun s => coordinateX0Mass (fun ξ =>
      everywhereRawRepresentative ν T x s ξ -
        everywhereRawRepresentative ν T y s ξ) *
    coordinateX0Mass (everywhereRawRepresentative ν T z.1 s)
  have hf := integrable_coordinateX0Mass_sub_mul_everywhere
    ν hν T (2 * R) (2 * R) x y z
  change IntegrableOn f (Icc (0 : ℝ) T) volume at hf
  have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hmono : (∫ s in Icc (0 : ℝ) t, f s) ≤
      ∫ s in Icc (0 : ℝ) T, f s := by
    apply setIntegral_mono_set hf
    · filter_upwards with s
      exact mul_nonneg
        (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _)
    · exact hsub.eventuallyLE
  exact hmono.trans (by
    simpa only [f, leiLinTimeMeasure] using
      integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance
        ν hν T R hR x y z)

end Navier.Analysis.ContinuousLeiLinCommonContraction

#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.integral_Xm1_mul_X1_le_admissible_bounds_ae
#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.sqrt_integral_X0_sq_le_admissible_ae
#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.sqrt_integral_coordinateX0Mass_sub_sq_le_linked_distance
#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.coordinateX0Mass_everywhere_sub_aestronglyMeasurable
#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.integrable_coordinateX0Mass_everywhere_sub_sq
#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.sqrt_integral_coordinateX0Mass_sq_le_actual_twoR_box
#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.integrable_coordinateX0Mass_sub_mul_everywhere
#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance
#print axioms Navier.Analysis.ContinuousLeiLinCommonContraction.integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance_on
