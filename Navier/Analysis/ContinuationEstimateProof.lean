import Navier.Analysis.ContinuationEstimateReference

/-!
# Exact quadratic continuation estimate on the whole-space Lei--Lin carrier

`ContinuousLeiLinSelfMap` proves the two analytic mild-image inputs but packages
their final arithmetic only at the conservative lattice-matching threshold
`R ≤ ν / 16`.  This file retains the actual quadratic output

`R + 12 ν⁻¹ R²`

in both the `L∞ₜ X⁻¹` and `L¹ₜ X¹` slots.  Consequently the whole-space mild
image preserves the radius-`2R` ball already at `R ≤ ν / 12`.

The hypotheses below are the existing genuine B1 and D3 estimates and the
input ball bounds.  No fixed point, terminal bound, or continuation conclusion
is assumed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuationEstimateReference

namespace Navier.Analysis.ContinuationEstimateProof

/-- The exact nonlinear output budget: the product integral costs
`4 ν⁻¹R²`, hence the Navier multiplier `3` costs `12 ν⁻¹R²`. -/
theorem exactQuadraticContinuationEstimate :
    ExactQuadraticContinuationEstimate := by
  intro ν R T hν hR hT a u haR hballXm1 hballX1 hX1i hprod hB1 hD3
  have hx1n (v : ES → ComplexSpace) : 0 ≤ coordinateX1Mass v :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun ξ =>
      mul_nonneg (norm_nonneg ξ) (norm_nonneg _)
  have hballX1' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) ≤
        (2 : ℝ) * ν⁻¹ * R :=
    le_trans (setIntegral_mono_set (hX1i T ⟨hT, le_rfl⟩)
      (Eventually.of_forall fun s => hx1n (u s))
      (Icc_subset_Icc le_rfl ht.2).eventuallyLE) hballX1
  have hI1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
        (4 : ℝ) * ν⁻¹ * R * R := by
    have hmt : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
    refine le_trans (setIntegral_mono_on (μ := volume)
        (f := fun s => coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (g := fun s => (2 * R) • coordinateX1Mass (u s))
        (hf := hprod t ht) (hg := (hX1i t ht).smul (2 * R)) hmt ?_) ?_
    · intro s hs
      show coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
        (2 * R) • coordinateX1Mass (u s)
      rw [smul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (hballXm1 s ⟨hs.1, le_trans hs.2 ht.2⟩) (hx1n (u s))
    · rw [MeasureTheory.integral_smul (2 * R)
          (fun s : ℝ => coordinateX1Mass (u s)), smul_eq_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (hballX1' t ht)
        (by nlinarith : (0 : ℝ) ≤ (2 : ℝ) * R)) (le_of_eq (by ring))
  refine ⟨fun t ht => ?_, ?_⟩
  · have h3 : (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
        coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
      (3 : ℝ) * (4 * ν⁻¹ * R * R) :=
      mul_le_mul_of_nonneg_left (hI1 t ht) (by norm_num)
    calc
      coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
          coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s) := hB1 t ht
      _ ≤ R + (3 : ℝ) * (4 * ν⁻¹ * R * R) := add_le_add haR h3
      _ = R + 12 * ν⁻¹ * R ^ 2 := by ring
  · have hy : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
    have h1 : ν⁻¹ * coordinateXm1Mass a ≤ ν⁻¹ * R :=
      mul_le_mul_of_nonneg_left haR hy
    have h3 : (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
        (3 : ℝ) * ν⁻¹ * (4 * ν⁻¹ * R * R) :=
      mul_le_mul_of_nonneg_left (hI1 T ⟨hT, le_rfl⟩)
        (mul_nonneg (by norm_num) hy)
    calc
      ∫ t in Icc (0 : ℝ) T,
          coordinateX1Mass (continuousMildImage ν hν a u t) ≤
        ν⁻¹ * coordinateXm1Mass a +
          (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s) := hD3
      _ ≤ ν⁻¹ * R + (3 : ℝ) * ν⁻¹ * (4 * ν⁻¹ * R * R) :=
        add_le_add h1 h3
      _ = ν⁻¹ * (R + 12 * ν⁻¹ * R ^ 2) := by ring

/-- The exact estimate is consumed at its natural invariant-ball threshold.
This improves the declared whole-space self-map range from `ν/16` to `ν/12`;
the fixed-point contraction and reconstruction leaves remain separate. -/
theorem continuousMildImage_self_map_ball_twelfth
    (ν R T : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRν : R ≤ ν / 12)
    (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace)
    (haR : coordinateXm1Mass a ≤ R)
    (hballXm1 : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (u t) ≤ (2 : ℝ) * R)
    (hballX1 : ∫ s in Icc (0 : ℝ) T, coordinateX1Mass (u s) ≤
      (2 : ℝ) * ν⁻¹ * R)
    (hX1i : ∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s : ℝ => coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume)
    (hprod : ∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (Icc (0 : ℝ) t) volume)
    (hB1 : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
        coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s))
    (hD3 : ∫ t in Icc (0 : ℝ) T,
      coordinateX1Mass (continuousMildImage ν hν a u t) ≤
        ν⁻¹ * coordinateXm1Mass a +
          (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s)) :
    (∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage ν hν a u t) ≤ (2 : ℝ) * R) ∧
      ∫ t in Icc (0 : ℝ) T,
        coordinateX1Mass (continuousMildImage ν hν a u t) ≤
          (2 : ℝ) * ν⁻¹ * R := by
  obtain ⟨hxm1, hx1⟩ := exactQuadraticContinuationEstimate
    ν R T hν hR hT a u haR hballXm1 hballX1 hX1i hprod hB1 hD3
  have hy : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have hscaled : ν⁻¹ * R ≤ (1 / 12 : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_left hRν hy) ?_
    field_simp [hν.ne']
    exact le_rfl
  have hmul := mul_le_mul_of_nonneg_right hscaled hR
  have hbudget : R + 12 * ν⁻¹ * R ^ 2 ≤ 2 * R := by
    nlinarith
  refine ⟨fun t ht => (hxm1 t ht).trans hbudget, ?_⟩
  exact hx1.trans (calc
    ν⁻¹ * (R + 12 * ν⁻¹ * R ^ 2) ≤ ν⁻¹ * (2 * R) :=
      mul_le_mul_of_nonneg_left hbudget hy
    _ = (2 : ℝ) * ν⁻¹ * R := by ring)

/-- Provider-backed form of the `ν/12` self-map estimate.  Its hypotheses are
the section-integrability and measurability inputs of the existing whole-space
`B1` and `D3` estimates; the two analytic bounds are obtained by invoking
those declarations rather than supplied as conclusions by the caller. -/
theorem continuousMildImage_self_map_ball_twelfth_of_provider_inputs
    (ν R T : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hRν : R ≤ ν / 12)
    (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (haR : coordinateXm1Mass a ≤ R)
    (hballXm1 : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (u t) ≤ (2 : ℝ) * R)
    (hballX1 : ∫ s in Icc (0 : ℝ) T, coordinateX1Mass (u s) ≤
      (2 : ℝ) * ν⁻¹ * R)
    (hX1i : ∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s : ℝ => coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3, Integrable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖continuousDuhamel ν u u t ξ i‖))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
      (‖p.1‖⁻¹ : ℝ) •
        heatMode ν (t - p.2) (fun ζ : ES => continuousNavierSource u u p.2 ζ i) p.1)
      (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3, Integrable (fun s : ℝ =>
      normXm1
        (heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u u s ζ i)))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ t ∈ Icc (0 : ℝ) T, ∀ i : Fin 3, Integrable (fun s : ℝ =>
      normXm1 (fun ζ : ES => continuousNavierSource u u s ζ i))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
      Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖))
    (hs1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ s ∈ Icc (0 : ℝ) t,
      Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource u u s ξ)))
    (hi : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun s : ℝ =>
      ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierSource u u s ξ))
      (volume.restrict (Icc (0 : ℝ) t)))
    (hu : ∀ r j, AEStronglyMeasurable (fun η : ES => u r η j))
    (hu0 : ∀ r j, Integrable (fun η : ES => ‖u r η j‖))
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (h0sq : ∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun r => coordinateX0Mass (u r) ^ 2) (Icc (0 : ℝ) t))
    (hmixed : ∀ t ∈ Icc (0 : ℝ) T, IntegrableOn (fun r =>
      coordinateXm1Mass (u r) * coordinateX1Mass (u r)) (Icc (0 : ℝ) t))
    (hIt : Integrable (fun t : ℝ =>
      coordinateX1Mass (continuousMildImage ν hν a u t))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hHt : Integrable (fun t : ℝ => coordinateX1Mass (heatVec ν t a))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ =>
      normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
      ‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖))
    (hjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      complexEuclideanPoint (continuousNavierSource u u p.2 p.1))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hJ : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    (∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage ν hν a u t) ≤ (2 : ℝ) * R) ∧
      ∫ t in Icc (0 : ℝ) T,
        coordinateX1Mass (continuousMildImage ν hν a u t) ≤
          (2 : ℝ) * ν⁻¹ * R := by
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hB1 : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
        coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) := by
    intro t ht
    exact continuousMildImage_coordinateXm1Mass_le
      ν hν a ha u t ht.1 (hd t ht) (hb t ht) (hf t ht) (hg t ht)
        (hb0 t ht) (hs1 t ht) (hi t ht) hu hu0 hum1 hu1
        (h0sq t ht) (hmixed t ht)
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hcoordMeas (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u u p.2 p.1 i) (volume.prod μ) := by
    have h := (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℂ) i).aestronglyMeasurable
      |>.comp_aemeasurable hjoint.aemeasurable
    exact h.congr (Filter.Eventually.of_forall fun p =>
      complexEuclideanPoint_apply (continuousNavierSource u u p.2 p.1) i)
  have hD3 : ∫ t in Icc (0 : ℝ) T,
      coordinateX1Mass (continuousMildImage ν hν a u t) ≤
        ν⁻¹ * coordinateXm1Mass a +
          (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s) := by
    refine integral_coordinateX1Mass_continuousMildImage_le
      ν hν a ha ha1 u T hT hIt hHt hD0 hDξ ?_ ?_
        (fun i s hs => hb0 T hTmem s hs i) (hg T hTmem) hJ
        (hs1 T hTmem) (hi T hTmem) hu hu0 hum1 hu1
        (h0sq T hTmem) (hmixed T hTmem)
    · intro i r hr
      change AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal ‖continuousNavierSource u u p.2 p.1 i‖ *
          (if p.2 ≤ r then ENNReal.ofReal
            (‖p.1‖ * Real.exp (-(ν * ‖p.1‖ ^ 2 * (r - p.2)))) else 0))
        (volume.prod μ)
      exact (ENNReal.measurable_ofReal.comp_aemeasurable
        (hcoordMeas i).norm.aemeasurable).mul
          ((Measurable.ite (measurableSet_le measurable_snd measurable_const)
            (ENNReal.measurable_ofReal.comp (by fun_prop))
            measurable_const).aemeasurable)
    · intro i
      have hcoord3 : AEStronglyMeasurable (fun z : ℝ × (ES × ℝ) =>
          continuousNavierSource u u z.2.2 z.2.1 i)
          (μ.prod (volume.prod μ)) :=
        (hcoordMeas i).comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd
      change AEMeasurable (fun z : ℝ × (ES × ℝ) =>
        ENNReal.ofReal ‖continuousNavierSource u u z.2.2 z.2.1 i‖ *
          (if z.2.2 ≤ z.1 then ENNReal.ofReal
            (‖z.2.1‖ * Real.exp (-(ν * ‖z.2.1‖ ^ 2 *
              (z.1 - z.2.2)))) else 0))
        (μ.prod (volume.prod μ))
      exact (ENNReal.measurable_ofReal.comp_aemeasurable
        hcoord3.norm.aemeasurable).mul
          ((Measurable.ite
            (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst)
            (ENNReal.measurable_ofReal.comp (by fun_prop))
            measurable_const).aemeasurable)
  exact continuousMildImage_self_map_ball_twelfth
    ν R T hν hR hT hRν a u haR hballXm1 hballX1 hX1i hmixed hB1 hD3


/-- Below the natural threshold, the exact estimate lands strictly inside both
components of the radius-`2R` ball.  This strict margin is the form needed by
a continuation/bootstrap argument and is lost by the old fixed `7/4` wrapper. -/
theorem continuousMildImage_strictly_inside_ball_twelfth
    (ν R T : ℝ) (hν : 0 < ν) (hR : 0 < R) (hT : 0 ≤ T)
    (hRν : R < ν / 12)
    (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace)
    (haR : coordinateXm1Mass a ≤ R)
    (hballXm1 : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (u t) ≤ (2 : ℝ) * R)
    (hballX1 : ∫ s in Icc (0 : ℝ) T, coordinateX1Mass (u s) ≤
      (2 : ℝ) * ν⁻¹ * R)
    (hX1i : ∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s : ℝ => coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume)
    (hprod : ∀ t ∈ Icc (0 : ℝ) T,
      IntegrableOn (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (Icc (0 : ℝ) t) volume)
    (hB1 : ∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
        coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s))
    (hD3 : ∫ t in Icc (0 : ℝ) T,
      coordinateX1Mass (continuousMildImage ν hν a u t) ≤
        ν⁻¹ * coordinateXm1Mass a +
          (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s)) :
    (∀ t ∈ Icc (0 : ℝ) T,
      coordinateXm1Mass (continuousMildImage ν hν a u t) < (2 : ℝ) * R) ∧
      (∫ t in Icc (0 : ℝ) T,
        coordinateX1Mass (continuousMildImage ν hν a u t)) <
          (2 : ℝ) * ν⁻¹ * R := by
  obtain ⟨hxm1, hx1⟩ := exactQuadraticContinuationEstimate
    ν R T hν hR.le hT a u haR hballXm1 hballX1 hX1i hprod hB1 hD3
  have hy : 0 < ν⁻¹ := inv_pos.mpr hν
  have hscaled : ν⁻¹ * R < (1 / 12 : ℝ) := by
    rw [inv_mul_eq_div]
    exact (div_lt_iff₀ hν).2 (by nlinarith)
  have hmul := mul_lt_mul_of_pos_right hscaled hR
  have hbudget : R + 12 * ν⁻¹ * R ^ 2 < 2 * R := by
    nlinarith
  refine ⟨fun t ht => (hxm1 t ht).trans_lt hbudget, ?_⟩
  exact hx1.trans_lt (by
    convert mul_lt_mul_of_pos_left hbudget hy using 1 <;> ring)

end Navier.Analysis.ContinuationEstimateProof

#check @Navier.Analysis.ContinuationEstimateProof.exactQuadraticContinuationEstimate
#check @Navier.Analysis.ContinuationEstimateProof.continuousMildImage_self_map_ball_twelfth
#check @Navier.Analysis.ContinuationEstimateProof.continuousMildImage_self_map_ball_twelfth_of_provider_inputs
#check @Navier.Analysis.ContinuationEstimateProof.continuousMildImage_strictly_inside_ball_twelfth
#print axioms Navier.Analysis.ContinuationEstimateProof.exactQuadraticContinuationEstimate
#print axioms Navier.Analysis.ContinuationEstimateProof.continuousMildImage_self_map_ball_twelfth
#print axioms Navier.Analysis.ContinuationEstimateProof.continuousMildImage_self_map_ball_twelfth_of_provider_inputs
#print axioms Navier.Analysis.ContinuationEstimateProof.continuousMildImage_strictly_inside_ball_twelfth
