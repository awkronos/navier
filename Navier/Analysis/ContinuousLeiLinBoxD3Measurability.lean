import Navier.Analysis.ContinuousLeiLinBoxD3Output

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinBoxB1Joint
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinBoxD3Output

namespace Navier.Analysis.ContinuousLeiLinBoxD3Measurability

/-- Joint measurability of one Duhamel coordinate follows from joint
measurability of the corresponding nonlinear source coordinate. -/
theorem continuousDuhamel_coord_joint_aestronglyMeasurable
    (ν T : ℝ) (u v : ℝ → ES → ComplexSpace) (i : Fin 3)
    (hsource : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel ν u v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) := by
  let μ := volume.restrict (Icc (0 : ℝ) T)
  let K : (ES × ℝ) × ℝ → ℂ := fun z =>
    if z.2 ≤ z.1.2 then
      heatMode ν (z.1.2 - z.2)
        (fun ζ : ES => continuousNavierSource u v z.2 ζ i) z.1.1
    else 0
  have hmap : MeasureTheory.Measure.QuasiMeasurePreserving
      (Prod.map Prod.fst id : (ES × ℝ) × ℝ → ES × ℝ)
      ((volume.prod μ).prod μ) (volume.prod μ) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap
      MeasureTheory.Measure.quasiMeasurePreserving_fst
      (MeasureTheory.Measure.QuasiMeasurePreserving.id μ)
  have hsrc3 : AEStronglyMeasurable (fun z : (ES × ℝ) × ℝ =>
      continuousNavierSource u v z.2 z.1.1 i) ((volume.prod μ).prod μ) := by
    apply (hsource.comp_quasiMeasurePreserving hmap).congr
    filter_upwards with z
    rfl
  have hcausal : MeasurableSet {z : (ES × ℝ) × ℝ | z.2 ≤ z.1.2} :=
    measurableSet_le measurable_snd (measurable_snd.comp measurable_fst)
  have hreal : Measurable (fun z : (ES × ℝ) × ℝ =>
      if z.2 ≤ z.1.2 then
        Real.exp (-(ν * ‖z.1.1‖ ^ 2 * (z.1.2 - z.2))) else 0) :=
    Measurable.ite hcausal (by fun_prop) measurable_const
  have hfactor : AEStronglyMeasurable (fun z : (ES × ℝ) × ℝ =>
      ((if z.2 ≤ z.1.2 then
        Real.exp (-(ν * ‖z.1.1‖ ^ 2 * (z.1.2 - z.2))) else 0 : ℝ) : ℂ))
      ((volume.prod μ).prod μ) :=
    (Complex.continuous_ofReal.measurable.comp hreal).aestronglyMeasurable
  have hK : AEStronglyMeasurable K ((volume.prod μ).prod μ) := by
    apply (hfactor.mul hsrc3).congr
    filter_upwards with z
    change ((if z.2 ≤ z.1.2 then
      Real.exp (-(ν * ‖z.1.1‖ ^ 2 * (z.1.2 - z.2))) else 0 : ℝ) : ℂ) *
        continuousNavierSource u v z.2 z.1.1 i =
      if z.2 ≤ z.1.2 then
        ((Real.exp (-(ν * ‖z.1.1‖ ^ 2 * (z.1.2 - z.2))) : ℝ) : ℂ) *
          continuousNavierSource u v z.2 z.1.1 i else 0
    by_cases hz : z.2 ≤ z.1.2 <;> simp [hz]
  have hparam : AEStronglyMeasurable (fun p : ES × ℝ =>
      ∫ s, K (p, s) ∂μ) (volume.prod μ) := hK.integral_prod_right'
  apply hparam.congr
  have htime : ∀ᵐ p : ES × ℝ ∂volume.prod μ, p.2 ∈ Icc (0 : ℝ) T := by
    rw [Measure.ae_prod_iff_ae_ae
      (isClosed_Icc.measurableSet.preimage measurable_snd)]
    filter_upwards with ξ
    exact ae_restrict_mem isClosed_Icc.measurableSet
  filter_upwards [htime] with p hp
  change (∫ s, K (p, s) ∂μ) = ∫ s in Icc (0 : ℝ) p.2,
    heatMode ν (p.2 - s)
      (fun ζ : ES => continuousNavierSource u v s ζ i) p.1
  let F : ℝ → ℂ := fun s => heatMode ν (p.2 - s)
    (fun ζ : ES => continuousNavierSource u v s ζ i) p.1
  have hset : Iic p.2 ∩ Icc (0 : ℝ) T = Icc (0 : ℝ) p.2 := by
    ext s
    simp only [mem_inter_iff, mem_Icc, mem_Iic]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, ⟨h.1, h.2.trans hp.2⟩⟩
  change (∫ s, (if s ≤ p.2 then F s else 0) ∂μ) = ∫ s in Icc (0 : ℝ) p.2, F s
  rw [show (fun s => if s ≤ p.2 then F s else 0) = (Iic p.2).indicator F by
    funext s
    by_cases hs : s ≤ p.2 <;> simp [indicator, hs]]
  rw [integral_indicator measurableSet_Iic]
  change (∫ s, F s ∂(volume.restrict (Icc (0 : ℝ) T)).restrict (Iic p.2)) = _
  rw [Measure.restrict_restrict measurableSet_Iic, hset]


/-- Joint source measurability and measurable datum coordinates make the
scalar `X¹` mass of the actual mild image measurable in time. -/
theorem coordinateX1Mass_continuousMildImage_aestronglyMeasurable
    (ν T : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (u : ℝ → ES → ComplexSpace)
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u u p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    AEStronglyMeasurable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage ν hν a u t))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  let μ := volume.restrict (Icc (0 : ℝ) T)
  unfold coordinateX1Mass
  change AEStronglyMeasurable (∑ i : Fin 3, fun t : ℝ =>
    normX1 (fun ξ : ES => continuousMildImage ν hν a u t ξ i)) μ
  apply Finset.aestronglyMeasurable_sum Finset.univ
  intro i hi
  have hheatFactor : AEStronglyMeasurable (fun p : ES × ℝ =>
      ((Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2)) : ℝ) : ℂ))
      (volume.prod μ) := by fun_prop
  have hheat : AEStronglyMeasurable (fun p : ES × ℝ =>
      heatVec ν p.2 a p.1 i) (volume.prod μ) := by
    apply (hheatFactor.mul (haM i).comp_fst).congr
    filter_upwards with p
    rfl
  have hcoord : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u u p.2 p.1 i) (volume.prod μ) :=
    continuousNavierSource_coord_aestronglyMeasurable u u 0 T
      (by simpa [μ] using hjoint) i
  have hD : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel ν u u p.2 p.1 i) (volume.prod μ) :=
    continuousDuhamel_coord_joint_aestronglyMeasurable ν T u u i hcoord
  have hMild : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousMildImage ν hν a u p.2 p.1 i) (volume.prod μ) := by
    apply (hheat.add hD).congr
    filter_upwards with p
    rfl
  have hweighted : AEStronglyMeasurable (fun p : ES × ℝ =>
      ‖p.1‖ * ‖continuousMildImage ν hν a u p.2 p.1 i‖)
      (volume.prod μ) := by
    exact (show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖)
      (volume.prod μ) by fun_prop).mul hMild.norm
  exact hweighted.prod_swap.integral_prod_right'


/-- Exact actual-box `D₃` estimate with every heat/full-output integrability
and output-measurability input generated.  The remaining analytic output
premises are precisely coordinatewise Duhamel `L¹_t X¹` and fixed-time `X¹`
integrability. -/
theorem integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_measurable
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ =>
      normX1 (fun ξ : ES => continuousDuhamel (ν : ℝ)
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) t ξ i))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T,
      Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousDuhamel (ν : ℝ)
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) t ξ i‖))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource
        (everywhereRawRepresentative ν T x.1)
        (everywhereRawRepresentative ν T x.1) p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    ∫ t in Icc (0 : ℝ) T, coordinateX1Mass
      (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t) ≤
      (ν : ℝ)⁻¹ * coordinateXm1Mass a +
        (3 : ℝ) * (ν : ℝ)⁻¹ * ∫ s in Icc (0 : ℝ) T,
          coordinateXm1Mass (everywhereRawRepresentative ν T x.1 s) *
            coordinateX1Mass (everywhereRawRepresentative ν T x.1 s) := by
  let u := everywhereRawRepresentative ν T x.1
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hImeas : AEStronglyMeasurable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage (ν : ℝ) hνR a u t))
      (volume.restrict (Icc (0 : ℝ) T)) :=
    coordinateX1Mass_continuousMildImage_aestronglyMeasurable
      (ν : ℝ) T hνR a haM u (by simpa [u] using hjoint)
  exact integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_output
    ν hν T xm1Radius x1WeightedRadius hT a ha ha1 x
      (by simpa [u] using hImeas) hD0 hDξ hjoint

end Navier.Analysis.ContinuousLeiLinBoxD3Measurability

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Measurability.continuousDuhamel_coord_joint_aestronglyMeasurable
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Measurability.coordinateX1Mass_continuousMildImage_aestronglyMeasurable
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Measurability.integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_measurable
