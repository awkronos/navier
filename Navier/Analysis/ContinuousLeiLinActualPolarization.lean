import Navier.Analysis.ContinuousLeiLinCommonContraction

/-!
# Actual quotient inputs for the polarization Duhamel bounds

The raw difference of two repaired linked representatives is paired with one
actual box representative.  The completed slot geometry supplies all spatial
measurability, unweighted integrability, time-product integrability, and the
sharp causal product budget required by the mixed Duhamel estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory Set Filter BigOperators
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinMixedX1
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinRepresentativeDistance
open Navier.Analysis.ContinuousLeiLinPhysicalIntegrability
open Navier.Analysis.ContinuousLeiLinBoxInterpolation
open Navier.Analysis.ContinuousLeiLinCommonContraction

namespace Navier.Analysis.ContinuousLeiLinActualPolarization

/-- The literal repaired representative difference used by both ordered
polarization slots. -/
def commonRepresentativeDifference (ν : ℝ≥0) (T : ℝ)
    (x y : ActualLinkedCarrier ν T) : ℝ → ES → ComplexSpace :=
  fun t ξ => everywhereRawRepresentative ν T x t ξ -
    everywhereRawRepresentative ν T y t ξ

/-- The left polarization slot `(x-y,x)` has its terminal `X⁻¹` Duhamel
budget controlled by the exact sum of the two completed slot distances.  All
representative-side hypotheses of the general mixed estimate are discharged.
-/
theorem coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ) (hR : 0 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) T)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hb : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) • heatMode (ν : ℝ) (t - p.2)
          (fun ζ : ES => continuousNavierSource
            (fun s ξ => everywhereRawRepresentative ν T x s ξ -
              everywhereRawRepresentative ν T y s ξ)
            (everywhereRawRepresentative ν T z.1) p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode (ν : ℝ) (t - s)
          (fun ζ : ES => continuousNavierSource
            (fun r ξ => everywhereRawRepresentative ν T x r ξ -
              everywhereRawRepresentative ν T y r ξ)
            (everywhereRawRepresentative ν T z.1) s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource
          (fun r ξ => everywhereRawRepresentative ν T x r ξ -
            everywhereRawRepresentative ν T y r ξ)
          (everywhereRawRepresentative ν T z.1) s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousNavierSource
        (fun r η => everywhereRawRepresentative ν T x r η -
          everywhereRawRepresentative ν T y r η)
        (everywhereRawRepresentative ν T z.1) s ξ i‖))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) t,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ * complexEuclideanNorm
        (continuousNavierSource
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η)
          (everywhereRawRepresentative ν T z.1) s ξ)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
        (continuousNavierSource
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η)
          (everywhereRawRepresentative ν T z.1) s ξ))
        (volume.restrict (Icc (0 : ℝ) t))) :
    coordinateXm1Mass (continuousDuhamel (ν : ℝ)
      (fun s ξ => everywhereRawRepresentative ν T x s ξ -
        everywhereRawRepresentative ν T y s ξ)
      (everywhereRawRepresentative ν T z.1) t) ≤
      3 * (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let w : ℝ → ES → ComplexSpace := fun s ξ =>
    everywhereRawRepresentative ν T x s ξ -
      everywhereRawRepresentative ν T y s ξ
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T z.1
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T (2 * R) (2 * R) z
  have hw0 : ∀ r i, Integrable (fun η : ES => ‖w r η i‖) := fun r i => by
    exact integrable_norm_of_integrable_Xm1_X1 (fun η : ES => w r η i)
      (hwm1 r i) (hw1 r i)
  have hprod : IntegrableOn (fun r =>
      coordinateX0Mass (w r) * coordinateX0Mass (u r))
      (Icc (0 : ℝ) t) := by
    have hfull := integrable_coordinateX0Mass_sub_mul_everywhere
      ν hν T (2 * R) (2 * R) x y z
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
      fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
    change Integrable (fun r => coordinateX0Mass (w r) * coordinateX0Mass (u r))
      (volume.restrict (Icc (0 : ℝ) t))
    simpa only [w, u] using hfull.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgeneral := coordinateXm1Mass_continuousDuhamel_le_integral_X0_product
    w u (ν : ℝ) t hνR
    (by simpa only [w, u] using hb) (by simpa only [w, u] using hf)
    (by simpa only [w, u] using hg) (by simpa only [w, u] using hb0)
    (by simpa only [w, u] using hs1) (by simpa only [w, u] using hi)
    (fun r j => by simpa only [w, Pi.sub_apply] using hwM r j)
    (by simpa only [u] using huM)
    hw0 (by simpa only [u] using hu0) hprod
  have hfeed := integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance_on
    ν hν T R t hR ht x y z
  refine hgeneral.trans ?_
  have := mul_le_mul_of_nonneg_left hfeed (by norm_num : (0 : ℝ) ≤ 3)
  simpa only [w, u, mul_assoc] using this

/-- The companion right polarization slot `(z,x-y)` obeys the same completed
distance bound.  Commutativity is used only for the scalar `X⁰` majorant; the
ordered Navier source and Duhamel operator remain unchanged. -/
theorem coordinateXm1Mass_continuousDuhamel_right_sub_le_linked_distance
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ) (hR : 0 ≤ R)
    (ht : t ∈ Icc (0 : ℝ) T)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hb : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) • heatMode (ν : ℝ) (t - p.2)
          (fun ζ : ES => continuousNavierSource
            (everywhereRawRepresentative ν T z.1)
            (fun s ξ => everywhereRawRepresentative ν T x s ξ -
              everywhereRawRepresentative ν T y s ξ) p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode (ν : ℝ) (t - s)
          (fun ζ : ES => continuousNavierSource
            (everywhereRawRepresentative ν T z.1)
            (fun r ξ => everywhereRawRepresentative ν T x r ξ -
              everywhereRawRepresentative ν T y r ξ) s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource
          (everywhereRawRepresentative ν T z.1)
          (fun r ξ => everywhereRawRepresentative ν T x r ξ -
            everywhereRawRepresentative ν T y r ξ) s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousNavierSource
        (everywhereRawRepresentative ν T z.1)
        (fun r η => everywhereRawRepresentative ν T x r η -
          everywhereRawRepresentative ν T y r η) s ξ i‖))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) t,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ * complexEuclideanNorm
        (continuousNavierSource (everywhereRawRepresentative ν T z.1)
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η) s ξ)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
        (continuousNavierSource (everywhereRawRepresentative ν T z.1)
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η) s ξ))
        (volume.restrict (Icc (0 : ℝ) t))) :
    coordinateXm1Mass (continuousDuhamel (ν : ℝ)
      (everywhereRawRepresentative ν T z.1)
      (fun s ξ => everywhereRawRepresentative ν T x s ξ -
        everywhereRawRepresentative ν T y s ξ) t) ≤
      3 * (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let w : ℝ → ES → ComplexSpace := fun s ξ =>
    everywhereRawRepresentative ν T x s ξ -
      everywhereRawRepresentative ν T y s ξ
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T z.1
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T (2 * R) (2 * R) z
  have hw0 : ∀ r i, Integrable (fun η : ES => ‖w r η i‖) := fun r i => by
    exact integrable_norm_of_integrable_Xm1_X1 (fun η : ES => w r η i)
      (hwm1 r i) (hw1 r i)
  have hprod : IntegrableOn (fun r =>
      coordinateX0Mass (u r) * coordinateX0Mass (w r))
      (Icc (0 : ℝ) t) := by
    have hfull := integrable_coordinateX0Mass_sub_mul_everywhere
      ν hν T (2 * R) (2 * R) x y z
    have hswap : Integrable (fun r =>
        coordinateX0Mass (u r) * coordinateX0Mass (w r))
        (leiLinTimeMeasure T) := by
      apply hfull.congr
      filter_upwards with r
      simp only [w, u]
      exact mul_comm _ _
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
      fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
    change Integrable (fun r => coordinateX0Mass (u r) * coordinateX0Mass (w r))
      (volume.restrict (Icc (0 : ℝ) t))
    exact hswap.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hgeneral := coordinateXm1Mass_continuousDuhamel_le_integral_X0_product
    u w (ν : ℝ) t hνR
    (by simpa only [w, u] using hb) (by simpa only [w, u] using hf)
    (by simpa only [w, u] using hg) (by simpa only [w, u] using hb0)
    (by simpa only [w, u] using hs1) (by simpa only [w, u] using hi)
    (by simpa only [u] using huM)
    (fun r j => by simpa only [w, Pi.sub_apply] using hwM r j)
    (by simpa only [u] using hu0) hw0 hprod
  have hfeed := integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance_on
    ν hν T R t hR ht x y z
  have hswap : (∫ s in Icc (0 : ℝ) t,
      coordinateX0Mass (u s) * coordinateX0Mass (w s)) =
      ∫ s in Icc (0 : ℝ) t,
        coordinateX0Mass (w s) * coordinateX0Mass (u s) := by
    apply integral_congr_ae
    filter_upwards with s
    exact mul_comm _ _
  refine hgeneral.trans ?_
  rw [hswap]
  have := mul_le_mul_of_nonneg_left hfeed (by norm_num : (0 : ℝ) ≤ 3)
  simpa only [w, u, mul_assoc] using this

/-- The left polarization slot also has its spacetime `X¹` budget controlled
by the completed linked distance.  Hölder/product inputs are reconstructed
from the quotient carrier; only the genuine mixed heat/source hypotheses
remain. -/
theorem integral_coordinateX1Mass_continuousDuhamel_sub_left_le_linked_distance
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hR : 0 ≤ R)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ => normX1 (fun ξ : ES =>
        continuousDuhamel (ν : ℝ)
          (fun s η => everywhereRawRepresentative ν T x s η -
            everywhereRawRepresentative ν T y s η)
          (everywhereRawRepresentative ν T z.1) t ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel (ν : ℝ)
          (fun s η => everywhereRawRepresentative ν T x s η -
            everywhereRawRepresentative ν T y s η)
          (everywhereRawRepresentative ν T z.1) t ξ i‖))
    (hW1 : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable
        (fun p : ES × ℝ => mixedKernelFun
          (fun s η => everywhereRawRepresentative ν T x s η -
            everywhereRawRepresentative ν T y s η)
          (everywhereRawRepresentative ν T z.1) i (ν : ℝ) p.1 t p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW : ∀ i : Fin 3, AEMeasurable
        (fun q : ℝ × (ES × ℝ) => mixedKernelFun
          (fun s η => everywhereRawRepresentative ν T x s η -
            everywhereRawRepresentative ν T y s η)
          (everywhereRawRepresentative ν T z.1) i (ν : ℝ) q.2.1 q.1 q.2.2)
        ((volume.restrict (Icc (0 : ℝ) T)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) T)))))
    (hb0 : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η)
          (everywhereRawRepresentative ν T z.1) s ξ i‖))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ => normXm1 (fun ξ : ES =>
        continuousNavierSource
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η)
          (everywhereRawRepresentative ν T z.1) s ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hJ : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ => ENNReal.ofReal
        (‖p.1‖⁻¹ * ‖continuousNavierSource
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η)
          (everywhereRawRepresentative ν T z.1) p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η)
          (everywhereRawRepresentative ν T z.1) s ξ)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
        (continuousNavierSource
          (fun r η => everywhereRawRepresentative ν T x r η -
            everywhereRawRepresentative ν T y r η)
          (everywhereRawRepresentative ν T z.1) s ξ))
        (volume.restrict (Icc (0 : ℝ) T))) :
    (∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel (ν : ℝ)
      (fun s η => everywhereRawRepresentative ν T x s η -
        everywhereRawRepresentative ν T y s η)
      (everywhereRawRepresentative ν T z.1) t)) ≤
      3 * (ν : ℝ)⁻¹ * ((ν : ℝ)⁻¹ * R) *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let w : ℝ → ES → ComplexSpace := fun s ξ =>
    everywhereRawRepresentative ν T x s ξ -
      everywhereRawRepresentative ν T y s ξ
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T z.1
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T (2 * R) (2 * R) z
  have hw0 : ∀ r i, Integrable (fun η : ES => ‖w r η i‖) := fun r i =>
    integrable_norm_of_integrable_Xm1_X1 (fun η : ES => w r η i)
      (hwm1 r i) (hw1 r i)
  have hprod := integrable_coordinateX0Mass_sub_mul_everywhere
    ν hν T (2 * R) (2 * R) x y z
  have hprod' : IntegrableOn (fun r =>
      coordinateX0Mass (w r) * coordinateX0Mass (u r)) (Icc (0 : ℝ) T) := by
    change Integrable (fun r => coordinateX0Mass (w r) * coordinateX0Mass (u r))
      (leiLinTimeMeasure T)
    simpa only [w, u] using hprod
  have hgeneral :=
    integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product
      w u (ν : ℝ) T hνR
      (by simpa only [w, u] using hD0) (by simpa only [w, u] using hDξ)
      (by simpa only [w, u] using hW1) (by simpa only [w, u] using hW)
      (by simpa only [w, u] using hb0) (by simpa only [w, u] using hg)
      (by simpa only [w, u] using hJ) (by simpa only [w, u] using hs1)
      (by simpa only [w, u] using hi)
      (fun r j => by simpa only [w, Pi.sub_apply] using hwM r j)
      (by simpa only [u] using huM) hw0 (by simpa only [u] using hu0)
      hprod'
  have hfeed := integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance
    ν hν T R hR x y z
  refine hgeneral.trans ?_
  have := mul_le_mul_of_nonneg_left hfeed
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (inv_nonneg.mpr hνR.le))
  simpa only [leiLinTimeMeasure, w, u, mul_assoc] using this

/-- The ordered right polarization slot has the same spacetime `X¹` distance
budget.  This closes the second mixed input needed by the Banach estimate. -/
theorem integral_coordinateX1Mass_continuousDuhamel_right_sub_le_linked_distance
    (ν : ℝ≥0) (hν : 0 < ν) (T R : ℝ) (hR : 0 ≤ R)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ => normX1 (fun ξ : ES =>
      continuousDuhamel (ν : ℝ) (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) t ξ i))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
      ‖ξ‖ * ‖continuousDuhamel (ν : ℝ) (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) t ξ i‖))
    (hW1 : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable
      (fun p : ES × ℝ => mixedKernelFun (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) i (ν : ℝ) p.1 t p.2)
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW : ∀ i : Fin 3, AEMeasurable
      (fun q : ℝ × (ES × ℝ) => mixedKernelFun (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) i (ν : ℝ) q.2.1 q.1 q.2.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod
        (volume.prod (volume.restrict (Icc (0 : ℝ) T)))))
    (hb0 : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖continuousNavierSource (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) s ξ i‖))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ => normXm1 (fun ξ : ES =>
      continuousNavierSource (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) s ξ i))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hJ : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ => ENNReal.ofReal
      (‖p.1‖⁻¹ * ‖continuousNavierSource (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) p.2 p.1 i‖))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) s ξ)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm
      (continuousNavierSource (everywhereRawRepresentative ν T z.1)
        (commonRepresentativeDifference ν T x y) s ξ))
      (volume.restrict (Icc (0 : ℝ) T))) :
    (∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel (ν : ℝ)
      (everywhereRawRepresentative ν T z.1)
      (commonRepresentativeDifference ν T x y) t)) ≤
      3 * (ν : ℝ)⁻¹ * ((ν : ℝ)⁻¹ * R) *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
  let w := commonRepresentativeDifference ν T x y
  let u : ℝ → ES → ComplexSpace := everywhereRawRepresentative ν T z.1
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  obtain ⟨hwM, hwm1, hw1⟩ :=
    everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
  obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
    ν hν T (2 * R) (2 * R) z
  have hw0 : ∀ r i, Integrable (fun η : ES => ‖w r η i‖) := fun r i =>
    integrable_norm_of_integrable_Xm1_X1 (fun η : ES => w r η i)
      (hwm1 r i) (hw1 r i)
  have hforward := integrable_coordinateX0Mass_sub_mul_everywhere
    ν hν T (2 * R) (2 * R) x y z
  have hprod : IntegrableOn (fun r =>
      coordinateX0Mass (u r) * coordinateX0Mass (w r)) (Icc (0 : ℝ) T) := by
    change Integrable (fun r => coordinateX0Mass (u r) * coordinateX0Mass (w r))
      (leiLinTimeMeasure T)
    apply hforward.congr
    filter_upwards with r
    simp only [w, u]
    exact mul_comm _ _
  have hgeneral :=
    integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product
      u w (ν : ℝ) T hνR
      (by simpa only [w, u] using hD0) (by simpa only [w, u] using hDξ)
      (by simpa only [w, u] using hW1) (by simpa only [w, u] using hW)
      (by simpa only [w, u] using hb0) (by simpa only [w, u] using hg)
      (by simpa only [w, u] using hJ) (by simpa only [w, u] using hs1)
      (by simpa only [w, u] using hi) (by simpa only [u] using huM)
      (fun r j => by
        simpa only [w, commonRepresentativeDifference, Pi.sub_apply] using hwM r j)
      (by simpa only [u] using hu0) hw0 hprod
  have hfeed := integral_coordinateX0Mass_sub_mul_everywhere_le_linked_distance
    ν hν T R hR x y z
  have hfeed' : (∫ s, coordinateX0Mass (w s) * coordinateX0Mass (u s)
      ∂leiLinTimeMeasure T) ≤
      (ν : ℝ)⁻¹ * R *
        (dist (x.1.fst : Xm1TimeSlot T) (y.1.fst : Xm1TimeSlot T) +
          dist (x.1.snd : ViscousX1TimeSlot ν T)
            (y.1.snd : ViscousX1TimeSlot ν T)) := by
    change (∫ s, coordinateX0Mass (fun ξ =>
      everywhereRawRepresentative ν T x s ξ -
        everywhereRawRepresentative ν T y s ξ) *
      coordinateX0Mass (everywhereRawRepresentative ν T z.1 s)
      ∂leiLinTimeMeasure T) ≤ _
    exact hfeed
  have hswap : (∫ s in Icc (0 : ℝ) T,
      coordinateX0Mass (u s) * coordinateX0Mass (w s)) =
      ∫ s in Icc (0 : ℝ) T,
        coordinateX0Mass (w s) * coordinateX0Mass (u s) := by
    apply integral_congr_ae
    filter_upwards with s
    exact mul_comm _ _
  refine hgeneral.trans ?_
  rw [hswap]
  have := mul_le_mul_of_nonneg_left hfeed'
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (inv_nonneg.mpr hνR.le))
  simpa only [leiLinTimeMeasure, w, u, commonRepresentativeDifference, mul_assoc]
    using this

end Navier.Analysis.ContinuousLeiLinActualPolarization

#print axioms Navier.Analysis.ContinuousLeiLinActualPolarization.coordinateXm1Mass_continuousDuhamel_sub_left_le_linked_distance
#print axioms Navier.Analysis.ContinuousLeiLinActualPolarization.coordinateXm1Mass_continuousDuhamel_right_sub_le_linked_distance
#print axioms Navier.Analysis.ContinuousLeiLinActualPolarization.integral_coordinateX1Mass_continuousDuhamel_sub_left_le_linked_distance
#print axioms Navier.Analysis.ContinuousLeiLinActualPolarization.integral_coordinateX1Mass_continuousDuhamel_right_sub_le_linked_distance
