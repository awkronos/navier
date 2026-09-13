import Navier.Analysis.ContinuousLeiLinBoxInterpolation
import Navier.Analysis.ContinuousLeiLinRecentTailJoint

/-!
# Joint-source input for the actual Lei--Lin `B₁` estimate

One joint measurability fact for the nonlinear source, together with the
actual box budgets, makes its full `L¹_t X⁻¹_ξ` majorant integrable.  The same
product-measure fact then supplies every coordinate source, heat-kernel, and
Duhamel integrability premise in the existing `B₁` consumer.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinBoxInterpolation
open Navier.Analysis.ContinuousLeiLinRecentTailJoint

namespace Navier.Analysis.ContinuousLeiLinBoxB1Joint

/-- The actual box and one joint source-measurability input give the literal
weighted source integrability on frequency times a causal interval. -/
theorem integrable_weightedContinuousNavierSource_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t)))) :
    Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) := by
  let u := everywhereRawRepresentative ν T x.1
  let μ := volume.restrict (Icc (0 : ℝ) t)
  let F : ES × ℝ → ℝ := fun p => ‖p.1‖⁻¹ *
    complexEuclideanNorm (continuousNavierSource u u p.2 p.1)
  have hFmeas : AEStronglyMeasurable F (volume.prod μ) := by
    have hw : AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod μ) := by fun_prop
    have hn : AEStronglyMeasurable (fun p : ES × ℝ =>
        complexEuclideanNorm (continuousNavierSource u u p.2 p.1))
        (volume.prod μ) := by
      simpa [u, μ, complexEuclideanNorm] using hjoint.norm
    exact hw.mul hn
  apply (integrable_prod_iff' hFmeas).2
  constructor
  · exact Eventually.of_forall fun s =>
      (continuousNavierSource_fixedTime_inputs_of_actualBox
        ν hν T xm1Radius x1WeightedRadius x).1 s
  · have hsec : AEStronglyMeasurable (fun s : ℝ => ∫ ξ : ES, ‖F (ξ, s)‖) μ :=
      hFmeas.norm.prod_swap.integral_prod_right'
    have hdom := integrableOn_coordinateX0Mass_sq_everywhere_of_mem_box
      ν hν T xm1Radius x1WeightedRadius x t ht
    apply hdom.mono' hsec
    filter_upwards with s
    have hnonneg (ξ : ES) : 0 ≤ F (ξ, s) :=
      mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (by
        unfold complexEuclideanNorm
        exact norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ξ => norm_nonneg (F (ξ, s)))]
    have heq : (∫ ξ : ES, ‖F (ξ, s)‖) = ∫ ξ : ES, F (ξ, s) := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact Real.norm_of_nonneg (hnonneg ξ)
    rw [heq]
    exact normXm1_continuousNavierSource_self_le_of_actualBox
      ν hν T xm1Radius x1WeightedRadius x s

/-- Every weighted coordinate of the same jointly measurable source is
integrable on frequency times the causal interval. -/
theorem integrable_weightedContinuousNavierSource_coord_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (i : Fin 3) :
    Integrable (fun p : ES × ℝ => ‖p.1‖⁻¹ *
      ‖continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) := by
  have hvec := integrable_weightedContinuousNavierSource_of_actualBox
    ν hν T xm1Radius x1WeightedRadius x t ht hjoint
  have hcoord := continuousNavierSource_coord_aestronglyMeasurable
    (everywhereRawRepresentative ν T x.1)
    (everywhereRawRepresentative ν T x.1) 0 t hjoint i
  apply hvec.mono'
    ((show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))) by fun_prop).mul hcoord.norm)
  filter_upwards with p
  change ‖‖p.1‖⁻¹ * ‖continuousNavierSource
    (everywhereRawRepresentative ν T x.1)
    (everywhereRawRepresentative ν T x.1) p.2 p.1 i‖‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg p.1))
    (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (norm_coord_le_complexEuclideanNorm (continuousNavierSource
      (everywhereRawRepresentative ν T x.1)
      (everywhereRawRepresentative ν T x.1) p.2 p.1) i)
    (inv_nonneg.mpr (norm_nonneg p.1))

/-- The forward heat multiplier contracts the pointwise `X⁻¹` weight. -/
theorem norm_weightedHeatMode_le (ν t s : ℝ) (hν : 0 < ν) (hst : s ≤ t)
    (ξ : ES) (g : ES → ℂ) :
    ‖(‖ξ‖⁻¹ : ℝ) • heatMode ν (t - s) g ξ‖ ≤ ‖ξ‖⁻¹ * ‖g ξ‖ := by
  simp only [heatMode, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ)), Complex.norm_mul,
    Complex.norm_real]
  rw [abs_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg
      (mul_nonneg hν.le (sq_nonneg ‖ξ‖)) (sub_nonneg.mpr hst)))
  calc
    ‖ξ‖⁻¹ * (Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) * ‖g ξ‖) =
        Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) * (‖ξ‖⁻¹ * ‖g ξ‖) := by ring
    _ ≤ 1 * (‖ξ‖⁻¹ * ‖g ξ‖) := mul_le_mul_of_nonneg_right hexp
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
    _ = _ := one_mul _

/-- Forward heat multiplication preserves the preceding weighted coordinate
source integrability on the causal product domain. -/
theorem integrable_weightedHeatContinuousNavierSource_coord_of_actualBox
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (i : Fin 3) :
    Integrable (fun p : ES × ℝ => (‖p.1‖⁻¹ : ℝ) •
      heatMode (ν : ℝ) (t - p.2) (fun ζ : ES => continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 ζ i) p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))) := by
  let u := everywhereRawRepresentative ν T x.1
  let μ := volume.restrict (Icc (0 : ℝ) t)
  have hsrc := integrable_weightedContinuousNavierSource_coord_of_actualBox
    ν hν T xm1Radius x1WeightedRadius x t ht hjoint i
  have hcoord := continuousNavierSource_coord_aestronglyMeasurable
    u u 0 t (by simpa [u, μ] using hjoint) i
  have hLmeas : AEStronglyMeasurable (fun p : ES × ℝ => (‖p.1‖⁻¹ : ℝ) •
      heatMode (ν : ℝ) (t - p.2)
        (fun ζ : ES => continuousNavierSource u u p.2 ζ i) p.1)
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
    p.1 (fun ζ : ES => continuousNavierSource u u p.2 ζ i)

/-- The exact `B₁` output estimate on the actual box now follows from one
joint measurability fact for the nonlinear source.  In particular, the five
separate Duhamel/product/time integrability families of the preceding
consumer are generated here by Fubini and forward heat domination. -/
theorem continuousMildImage_coordinateXm1Mass_le_of_actualBox_joint
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (a : ES → ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) t)))) :
    coordinateXm1Mass (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
      (everywhereRawRepresentative ν T x.1) t) ≤
      coordinateXm1Mass a + 3 * ∫ s in Icc (0 : ℝ) t,
        coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
          coordinateX1Mass (everywhereRawRepresentative ν T x.1 s) := by
  let u := everywhereRawRepresentative ν T x.1
  let μ := volume.restrict (Icc (0 : ℝ) t)
  have hsource := integrable_weightedContinuousNavierSource_of_actualBox
    ν hν T xm1Radius x1WeightedRadius x t ht hjoint
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_coord_of_actualBox
      ν hν T xm1Radius x1WeightedRadius x t ht hjoint i
  have hb (i : Fin 3) :=
    integrable_weightedHeatContinuousNavierSource_coord_of_actualBox
      ν hν T xm1Radius x1WeightedRadius x t ht hjoint i
  have hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
      complexEuclideanNorm (continuousNavierSource u u s ξ)) μ := by
    apply hsource.integral_norm_prod_right.congr
    filter_upwards with s
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (by
      unfold complexEuclideanNorm
      exact norm_nonneg _))
  have hg (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) μ := by
    apply (hsourceCoord i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg
      (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
  have hf (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (heatMode (ν : ℝ) (t - s)
        (fun ζ : ES => continuousNavierSource u u s ζ i))) μ := by
    apply (hb i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg ξ))]
  have hd (i : Fin 3) : Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
      ‖continuousDuhamel (ν : ℝ) u u t ξ i‖) := by
    have hinner := (hb i).integral_prod_left.norm
    apply hinner.congr
    filter_upwards with ξ
    change ‖∫ s, (‖ξ‖⁻¹ : ℝ) • heatMode (ν : ℝ) (t - s)
        (fun ζ : ES => continuousNavierSource u u s ζ i) ξ ∂μ‖ =
      ‖ξ‖⁻¹ * ‖continuousDuhamel (ν : ℝ) u u t ξ i‖
    rw [integral_smul, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.mpr (norm_nonneg ξ))]
    rfl
  exact continuousMildImage_coordinateXm1Mass_le_of_actualBox
    ν hν T xm1Radius x1WeightedRadius a ha x t ht hd hb hf hg hi

end Navier.Analysis.ContinuousLeiLinBoxB1Joint

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxB1Joint.integrable_weightedContinuousNavierSource_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxB1Joint.integrable_weightedContinuousNavierSource_coord_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxB1Joint.norm_weightedHeatMode_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxB1Joint.integrable_weightedHeatContinuousNavierSource_coord_of_actualBox
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxB1Joint.continuousMildImage_coordinateXm1Mass_le_of_actualBox_joint
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinSelfMap.continuousMildImage_coordinateXm1Mass_le
