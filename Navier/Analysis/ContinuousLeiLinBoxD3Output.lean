import Navier.Analysis.ContinuousLeiLinBoxD3Joint

/-!
# Output-side integrability for the actual Lei--Lin `D₃` estimate

The free heat trajectory is time-integrable in `X¹` on every finite horizon
from the datum's `X¹` integrability.  Together with coordinatewise Duhamel
`L¹_t X¹` control, this reduces the full mild-image integrability input to
measurability of its scalar `X¹` mass.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
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
open Navier.Analysis.ContinuousLeiLinBoxProduct
open Navier.Analysis.ContinuousLeiLinBoxD3Joint

namespace Navier.Analysis.ContinuousLeiLinBoxD3Output

/-- Exact norm of the continuous heat multiplier. -/
theorem norm_heatMode_eq
    (ν t : ℝ) (g : ES → ℂ) (ξ : ES) :
    ‖heatMode ν t g ξ‖ = Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖g ξ‖ := by
  rw [heatMode, Complex.norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- A fixed heat section preserves coordinate `X¹` integrability. -/
theorem integrable_weighted_heatMode_of_X1
    (g : ES → ℂ) (hg : Integrable (fun ξ : ES => ‖ξ‖ * ‖g ξ‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖heatMode ν t g ξ‖) := by
  have hfactor : AEStronglyMeasurable
      (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) := by fun_prop
  have heq (ξ : ES) : ‖ξ‖ * ‖heatMode ν t g ξ‖ =
      Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖ * ‖g ξ‖) := by
    rw [norm_heatMode_eq]
    ring
  apply (hg.mono' (hfactor.mul hg.aestronglyMeasurable) ?_).congr
    (Eventually.of_forall fun ξ => (heq ξ).symm)
  filter_upwards with ξ
  simp only [Pi.mul_apply]
  have hexp_nonneg : 0 ≤ Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) := (Real.exp_pos _).le
  have hexp_le : Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hν.le (sq_nonneg ‖ξ‖)) ht)
  have hbase : 0 ≤ ‖ξ‖ * ‖g ξ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [Real.norm_of_nonneg (mul_nonneg hexp_nonneg hbase)]
  nlinarith

/-- The heat semigroup contracts the coordinate `X¹` mass at nonnegative
 times. -/
theorem normX1_heatMode_le_of_X1
    (g : ES → ℂ) (hg : Integrable (fun ξ : ES => ‖ξ‖ * ‖g ξ‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    normX1 (heatMode ν t g) ≤ normX1 g := by
  unfold normX1
  apply integral_mono (integrable_weighted_heatMode_of_X1 g hg ν t hν ht) hg
  intro ξ
  change ‖ξ‖ * ‖heatMode ν t g ξ‖ ≤ ‖ξ‖ * ‖g ξ‖
  rw [norm_heatMode_eq]
  have hexp_nonneg : 0 ≤ Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) := (Real.exp_pos _).le
  have hexp_le : Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hν.le (sq_nonneg ‖ξ‖)) ht)
  calc
    ‖ξ‖ * (Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖g ξ‖) =
        Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖ * ‖g ξ‖) := by ring
    _ ≤ ‖ξ‖ * ‖g ξ‖ := by
      nlinarith [mul_nonneg (norm_nonneg ξ) (norm_nonneg (g ξ))]

/-- The free heat trajectory is `L¹_t X¹` on every finite horizon.  This uses
only the already-present `X¹` datum input and a bounded-horizon domination. -/
theorem integrable_normX1_heatMode_on_Icc_of_X1
    (g : ES → ℂ) (hg : Integrable (fun ξ : ES => ‖ξ‖ * ‖g ξ‖))
    (ν T : ℝ) (hν : 0 < ν) :
    Integrable (fun t : ℝ => normX1 (heatMode ν t g))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  let μ := volume.restrict (Icc (0 : ℝ) T)
  let J : ES × ℝ → ℝ := fun p =>
    ‖p.1‖ * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2)) * ‖g p.1‖
  have hJ : AEStronglyMeasurable J (volume.prod μ) := by
    have hfactor : AEStronglyMeasurable (fun p : ES × ℝ =>
        Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2))) (volume.prod μ) := by fun_prop
    have hbase : AEStronglyMeasurable (fun p : ES × ℝ =>
        ‖p.1‖ * ‖g p.1‖) (volume.prod μ) :=
      hg.aestronglyMeasurable.comp_fst
    exact (hfactor.mul hbase).congr (Eventually.of_forall fun p => by
      simp only [Pi.mul_apply, J]
      ring)
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      normX1 (heatMode ν t g)) μ := by
    apply hJ.prod_swap.integral_prod_right'.congr
    filter_upwards with t
    unfold normX1
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [J, Prod.swap_prod_mk]
    rw [norm_heatMode_eq]
    ring
  have hconst : Integrable (fun _ : ℝ => normX1 g) μ := by
    exact continuous_const.integrableOn_Icc
  apply hconst.mono' hmeas
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  have hheat_nonneg : 0 ≤ normX1 (heatMode ν t g) :=
    integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hg_nonneg : 0 ≤ normX1 g :=
    integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [Real.norm_of_nonneg hheat_nonneg]
  exact normX1_heatMode_le_of_X1 g hg ν t hν ht.1

/-- Coordinate aggregation of finite-horizon heat `X¹` integrability. -/
theorem integrable_coordinateX1Mass_heatVec_on_Icc
    (a : ES → ComplexSpace)
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (ν T : ℝ) (hν : 0 < ν) :
    Integrable (fun t : ℝ => coordinateX1Mass (heatVec ν t a))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  unfold coordinateX1Mass
  apply integrable_finsetSum Finset.univ
  intro i hi
  exact integrable_normX1_heatMode_on_Icc_of_X1
    (fun ξ : ES => a ξ i) (ha1 i) ν T hν

/-- A measurable mild-image `X¹` mass is integrable once its heat and Duhamel
pieces have their natural coordinate integrability. -/
theorem integrable_coordinateX1Mass_continuousMildImage_of_aestronglyMeasurable
    (ν : ℝ) (hν : 0 < ν) (T : ℝ)
    (a : ES → ComplexSpace)
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (u : ℝ → ES → ComplexSpace)
    (hImeas : AEStronglyMeasurable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage ν hν a u t))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ =>
      normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T,
      Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖)) :
    Integrable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage ν hν a u t))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  have hHt := integrable_coordinateX1Mass_heatVec_on_Icc a ha1 ν T hν
  have hDt : Integrable (fun t : ℝ => coordinateX1Mass
      (continuousDuhamel ν u u t)) (volume.restrict (Icc (0 : ℝ) T)) := by
    unfold coordinateX1Mass
    exact integrable_finsetSum (f := fun i (t : ℝ) =>
      normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i))
      Finset.univ (fun i _ => hD0 i)
  apply (hHt.add hDt).mono' hImeas
  filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
  have hle := coordinateX1Mass_add_le (heatVec ν t a) (continuousDuhamel ν u u t)
    (fun i => integrable_weighted_heatMode_of_X1
      (fun ξ : ES => a ξ i) (ha1 i) ν t hν ht.1)
    (fun i => hDξ i t ht)
  rw [Real.norm_of_nonneg (coordinateX1Mass_nonneg _)]
  change coordinateX1Mass (fun ξ => heatVec ν t a ξ + continuousDuhamel ν u u t ξ) ≤ _
  exact hle

/-- Exact actual-box `D₃` estimate with the heat and full-output integrability
premises generated.  The remaining output assumptions are scalar
measurability of the mild-image `X¹` mass and the two Duhamel maximal-
regularity statements. -/
theorem integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_output
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
    (hImeas : AEStronglyMeasurable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage (ν : ℝ) (by exact_mod_cast hν) a
        (everywhereRawRepresentative ν T x.1) t))
      (volume.restrict (Icc (0 : ℝ) T)))
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
  have hHt : Integrable (fun t : ℝ => coordinateX1Mass
      (heatVec (ν : ℝ) t a)) (volume.restrict (Icc (0 : ℝ) T)) :=
    integrable_coordinateX1Mass_heatVec_on_Icc a ha1 (ν : ℝ) T hνR
  have hIt : Integrable (fun t : ℝ => coordinateX1Mass
      (continuousMildImage (ν : ℝ) hνR a u t))
      (volume.restrict (Icc (0 : ℝ) T)) :=
    integrable_coordinateX1Mass_continuousMildImage_of_aestronglyMeasurable
      (ν : ℝ) hνR T a ha1 u (by simpa [u] using hImeas) hD0 hDξ
  exact integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint
    ν hν T xm1Radius x1WeightedRadius hT a ha ha1 x
      (by simpa [u] using hIt) hHt hD0 hDξ hjoint

end Navier.Analysis.ContinuousLeiLinBoxD3Output

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Output.integrable_normX1_heatMode_on_Icc_of_X1
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Output.integrable_coordinateX1Mass_continuousMildImage_of_aestronglyMeasurable
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Output.integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_output
