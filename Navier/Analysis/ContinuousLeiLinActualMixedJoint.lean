import Navier.Analysis.ContinuousLeiLinActualMixedSource
import Navier.Analysis.ContinuousLeiLinBoxB1Joint

/-!
# Joint mixed source input on the actual quotient carrier

One almost-everywhere joint measurability fact for an ordered mixed source is
enough to generate its weighted product integrability, every weighted
coordinate, and the forward heat family.  Thus the terminal polarization
estimate no longer carries separate Fubini and heat integrability hypotheses.
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
open Navier.Analysis.ContinuousLeiLinCommonContraction
open Navier.Analysis.ContinuousLeiLinActualPolarization
open Navier.Analysis.ContinuousLeiLinActualMixedSource
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinBoxB1Joint

namespace Navier.Analysis.ContinuousLeiLinActualMixedJoint

/-- The ordered mixed source `(x-y,z)` is integrable on frequency times every
causal subinterval once its natural Euclidean realization is jointly
measurable there. -/
theorem integrable_weightedContinuousNavierSource_sub_left_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T)
    (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t)))) :
    Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) := by
  let w := commonRepresentativeDifference ν T x y
  let u := everywhereRawRepresentative ν T z.1
  let μ := volume.restrict (Icc (0 : ℝ) t)
  let F : ES × ℝ → ℝ := fun p => ‖p.1‖⁻¹ *
    complexEuclideanNorm (continuousNavierSource w u p.2 p.1)
  have hFmeas : AEStronglyMeasurable F (volume.prod μ) := by
    have hw : AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod μ) := by fun_prop
    have hn : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanNorm (continuousNavierSource w u p.2 p.1))
        (volume.prod μ) := by
      simpa [w, u, μ, complexEuclideanNorm] using hjoint.norm
    exact hw.mul hn
  apply (integrable_prod_iff' hFmeas).2
  constructor
  · exact Eventually.of_forall fun s =>
      (continuousNavierSource_sub_left_fixedTime_inputs_of_actualBox
        ν hν T (2 * R) (2 * R) x y z).1 s
  · have hsec : AEStronglyMeasurable (fun s : ℝ => ∫ ξ : ES, ‖F (ξ, s)‖) μ :=
      hFmeas.norm.prod_swap.integral_prod_right'
    have hdom : Integrable (fun s : ℝ =>
        coordinateX0Mass (w s) * coordinateX0Mass (u s)) μ := by
      have hfull := integrable_coordinateX0Mass_sub_mul_everywhere
        ν hν T (2 * R) (2 * R) x y z
      have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
        fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
      change Integrable (fun s : ℝ => coordinateX0Mass (fun ξ =>
        everywhereRawRepresentative ν T x s ξ -
          everywhereRawRepresentative ν T y s ξ) *
        coordinateX0Mass (everywhereRawRepresentative ν T z.1 s))
        (volume.restrict (Icc (0 : ℝ) t))
      exact hfull.mono_measure (Measure.restrict_mono hsub le_rfl)
    obtain ⟨hwM, hwm1, hw1⟩ :=
      everywhereRawRepresentative_sub_fixedTime_inputs ν hν T x y
    obtain ⟨huM, hu0⟩ := everywhereRawRepresentative_fixedTime_inputs
      ν hν T (2 * R) (2 * R) z
    have hw0 : ∀ r i, Integrable (fun ξ : ES => ‖w r ξ i‖) := fun r i =>
      integrable_norm_of_integrable_Xm1_X1 (fun ξ : ES => w r ξ i)
        (by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hwm1 r i)
        (by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hw1 r i)
    apply hdom.mono' hsec
    filter_upwards with s
    have hnonneg (ξ : ES) : 0 ≤ F (ξ, s) :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (by
        unfold complexEuclideanNorm
        exact norm_nonneg _)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun ξ => norm_nonneg (F (ξ, s)))]
    have heq : (∫ ξ : ES, ‖F (ξ, s)‖) = ∫ ξ : ES, F (ξ, s) := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact Real.norm_of_nonneg (hnonneg ξ)
    rw [heq]
    simpa [F] using normXm1_continuousNavierSource_le_coordinateX0Mass
      w u s
      (fun r i => by simpa [w, commonRepresentativeDifference, Pi.sub_apply] using hwM r i)
      (by simpa [u] using huM) hw0 (by simpa [u] using hu0)

/-- Every coordinate of the preceding weighted mixed source is integrable on
the same product domain. -/
theorem integrable_weightedContinuousNavierSource_sub_left_coord_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t)))) (i : Fin 3) :
    Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ *
      ‖continuousNavierSource (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) := by
  have hvec := integrable_weightedContinuousNavierSource_sub_left_of_actualBox
    ν hν T R t ht x y z hjoint
  have hcoord := continuousNavierSource_coord_aestronglyMeasurable
    (commonRepresentativeDifference ν T x y)
    (everywhereRawRepresentative ν T z.1) 0 t hjoint i
  apply hvec.mono'
    ((show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))) by fun_prop).mul hcoord.norm)
  filter_upwards with p
  change ‖‖p.1‖⁻¹ * ‖continuousNavierSource
    (commonRepresentativeDifference ν T x y)
    (everywhereRawRepresentative ν T z.1) p.2 p.1 i‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg p.1))
    (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (norm_coord_le_complexEuclideanNorm (continuousNavierSource
      (commonRepresentativeDifference ν T x y)
      (everywhereRawRepresentative ν T z.1) p.2 p.1) i)
    (inv_nonneg.mpr (norm_nonneg p.1))

/-- Forward heat multiplication preserves the weighted mixed coordinate on
the causal product domain. -/
theorem integrable_weightedHeatContinuousNavierSource_sub_left_coord_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T R t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) (x y : ActualLinkedCarrier ν T)
    (z : ActualLinkedBox ν T (2 * R) (2 * R))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t)))) (i : Fin 3) :
    Integrable (fun p : ES × ℝ => (‖p.1‖⁻¹ : ℝ) •
      heatMode (ν : ℝ) (t - p.2) (fun ζ : ES => continuousNavierSource
        (commonRepresentativeDifference ν T x y)
        (everywhereRawRepresentative ν T z.1) p.2 ζ i) p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) := by
  let w := commonRepresentativeDifference ν T x y
  let u := everywhereRawRepresentative ν T z.1
  let μ := volume.restrict (Icc (0 : ℝ) t)
  have hsrc := integrable_weightedContinuousNavierSource_sub_left_coord_of_actualBox
    ν hν T R t ht x y z hjoint i
  have hcoord := continuousNavierSource_coord_aestronglyMeasurable
    w u 0 t (by simpa [w, u, μ] using hjoint) i
  have hLmeas : AEStronglyMeasurable (fun p : ES × ℝ => (‖p.1‖⁻¹ : ℝ) •
      heatMode (ν : ℝ) (t - p.2)
        (fun ζ : ES => continuousNavierSource w u p.2 ζ i) p.1)
      (volume.prod μ) := by
    unfold heatMode
    have hfactor : AEStronglyMeasurable (fun p : ES × ℝ =>
        ((‖p.1‖⁻¹ * Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (t - p.2))) : ℝ) : ℂ))
        (volume.prod μ) := by fun_prop
    convert hfactor.mul hcoord using 1
    ext p
    simp only [Pi.mul_apply, Complex.real_smul]
    push_cast
    ring
  apply hsrc.mono' hLmeas
  have htime : ∀ᵐ p : ES × ℝ ∂volume.prod μ, p.2 ∈ Icc (0 : ℝ) t := by
    rw [Measure.ae_prod_iff_ae_ae
      (isClosed_Icc.measurableSet.preimage measurable_snd)]
    filter_upwards with ξ
    exact ae_restrict_mem isClosed_Icc.measurableSet
  filter_upwards [htime] with p hp
  exact norm_weightedHeatMode_le (ν : ℝ) t p.2 (by exact_mod_cast hν) hp.2
    p.1 (fun ζ : ES => continuousNavierSource w u p.2 ζ i)

end Navier.Analysis.ContinuousLeiLinActualMixedJoint

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinActualMixedJoint.integrable_weightedContinuousNavierSource_sub_left_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinActualMixedJoint.integrable_weightedContinuousNavierSource_sub_left_coord_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinActualMixedJoint.integrable_weightedHeatContinuousNavierSource_sub_left_coord_of_actualBox
