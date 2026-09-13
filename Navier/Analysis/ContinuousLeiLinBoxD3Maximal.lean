import Navier.Analysis.ContinuousLeiLinBoxD3Measurability
import Navier.Analysis.ContinuousLeiLinMixedX1

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

open MeasureTheory Set Filter Topology BigOperators
open scoped NNReal ENNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinRecentTailJoint
open Navier.Analysis.ContinuousLeiLinMixedX1
open Navier.Analysis.ContinuousLeiLinBoxD3Measurability
open Navier.Analysis.ContinuousLeiLinActualSlots
open Navier.Analysis.ContinuousLeiLinEverywhereRepresentative
open Navier.Analysis.ContinuousLeiLinBoxInterpolation
open Navier.Analysis.ContinuousLeiLinBoxB1Joint

namespace Navier.Analysis.ContinuousLeiLinBoxD3Maximal

private theorem exp_pos_heat (a : ℝ) : 0 < Real.exp (-a) := by
  rw [Real.exp_neg]
  exact inv_pos.mpr (Real.exp_pos _)

private theorem integral_exp_neg_Icc (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    (∫ s in Icc (0 : ℝ) t, Real.exp (-(c * s))) =
      c⁻¹ * (1 - Real.exp (-(c * t))) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  rw [show (fun s : ℝ => Real.exp (-(c * s))) = fun s => Real.exp ((-c) * s) by
    ext s; rw [neg_mul]]
  rw [intervalIntegral.integral_comp_mul_left (hc := neg_ne_zero.mpr hc.ne')]
  rw [integral_exp]
  simp only [neg_mul, mul_zero, smul_eq_mul, Real.exp_zero, inv_neg]
  ring

private theorem heat_budget_pointwise (ν r q t : ℝ) (hν : 0 < ν) (_ht : 0 ≤ t)
    (hr : 0 < r) (hq : 0 ≤ q) :
    r * q * ((ν * r ^ 2)⁻¹ * (1 - Real.exp (-(ν * r ^ 2 * t)))) ≤
      ν⁻¹ * (r⁻¹ * q) := by
  have e1 : 1 - Real.exp (-(ν * r ^ 2 * t)) ≤ 1 := by
    nlinarith [exp_pos_heat (ν * r ^ 2 * t)]
  have hc : 0 < ν * r ^ 2 := mul_pos hν (pow_pos hr 2)
  have hA : 0 ≤ r * q := mul_nonneg hr.le hq
  calc r * q * ((ν * r ^ 2)⁻¹ * (1 - Real.exp (-(ν * r ^ 2 * t))))
      ≤ r * q * ((ν * r ^ 2)⁻¹ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 (inv_nonneg.mpr hc.le)) hA
    _ = r * q * (ν * r ^ 2)⁻¹ := by ring
    _ = ν⁻¹ * (r⁻¹ * q) := by field_simp [hν.ne', hr.ne']

private theorem norm_heatMode (ν t : ℝ) (f : ES → ℂ) (ξ : ES) :
    ‖heatMode ν t f ξ‖ = Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖f ξ‖ := by
  show ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * f ξ‖ = _
  rw [Complex.norm_mul, Complex.norm_real]
  exact congrArg (fun e : ℝ => e * ‖f ξ‖)
    (Real.norm_of_nonneg (exp_pos_heat _).le)

private theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hfi : Integrable f μ
  · exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hf).le
  · rw [integral_undef hfi, ENNReal.ofReal_zero]
    positivity

private theorem kernel_budget (ξ : ES) (s T ν : ℝ) (hν : 0 < ν) :
    (∫ t in Icc s T, ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) ≤
      ν⁻¹ * ‖ξ‖⁻¹ := by
  by_cases hr : ‖ξ‖ = 0
  · rw [hr]
    simp
  · have hw : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm hr)
    have hc : 0 < ν * ‖ξ‖ ^ 2 := mul_pos hν (pow_pos hw 2)
    by_cases hst : s ≤ T
    · have hts : 0 ≤ T - s := by linarith
      have hstep : (∫ t in Icc s T,
          ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) =
          ‖ξ‖ * ∫ x in Icc (0 : ℝ) (T - s),
            Real.exp (-(ν * ‖ξ‖ ^ 2 * x)) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hst,
          intervalIntegral.integral_comp_sub_right
            (fun x : ℝ => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * x))) s,
          sub_self,
          show (fun x : ℝ => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * x))) =
              (fun x : ℝ => ‖ξ‖ • Real.exp (-(ν * ‖ξ‖ ^ 2 * x))) by
            ext x; rw [smul_eq_mul],
          intervalIntegral.integral_smul ‖ξ‖, smul_eq_mul,
          intervalIntegral.integral_of_le hts, ← integral_Icc_eq_integral_Ioc]
      rw [hstep, integral_exp_neg_Icc (ν * ‖ξ‖ ^ 2) (T - s) hc hts]
      have hz := heat_budget_pointwise ν ‖ξ‖ 1 (T - s) hν hts hw zero_le_one
      rw [mul_one, mul_one] at hz
      exact hz
    · have hset : Icc s T = ∅ := Icc_eq_empty hst
      rw [hset]
      simp
      exact mul_nonneg (inv_nonneg.mpr hν.le) (inv_nonneg.mpr (norm_nonneg ξ))

/-- Maximal `L¹_t X¹` regularity before taking spatial sections: a jointly
measurable Duhamel coordinate is integrable on frequency-times-output-time
whenever the nonlinear source is `L¹_t X⁻¹` and the causal Tonelli kernels are
measurable.  No prior Duhamel integrability premise is used. -/
theorem integrable_weighted_continuousDuhamel
    (a b : ℝ → ES → ComplexSpace) (ν T : ℝ) (i : Fin 3) (hν : 0 < ν)
    (hDjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel ν a b p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW1 : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable
      (fun p : ES × ℝ => mixedKernelFun a b i ν p.1 t p.2)
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW : AEMeasurable
      (fun z : ℝ × (ES × ℝ) => mixedKernelFun a b i ν z.2.1 z.1 z.2.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod
        (volume.prod (volume.restrict (Icc (0 : ℝ) T)))))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖continuousNavierSource a b s ξ i‖))
    (hg : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hJ : AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource a b p.2 p.1 i‖))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    Integrable (fun p : ES × ℝ =>
      ‖p.1‖ * ‖continuousDuhamel ν a b p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))) := by
  let μ := volume.restrict (Icc (0 : ℝ) T)
  let G : ES × ℝ → ℝ := fun p =>
    ‖p.1‖ * ‖continuousDuhamel ν a b p.2 p.1 i‖
  have hG : AEStronglyMeasurable G (volume.prod μ) := by
    exact (show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖)
      (volume.prod μ) by fun_prop).mul hDjoint.norm
  have hmT : MeasurableSet (Icc (0 : ℝ) T) := isClosed_Icc.measurableSet
  have hw0 (ξ : ES) : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hw1 (ξ : ES) : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ξ)
  have hbr (ξ : ES) (s : ℝ) :
      ∫⁻ t, mixedKernelFun a b i ν ξ t s ∂μ ≤
        ENNReal.ofReal ‖continuousNavierSource a b s ξ i‖ *
          ENNReal.ofReal (ν⁻¹ * ‖ξ‖⁻¹) := by
    have hc : AEMeasurable (fun t : ℝ => if s ≤ t then
        ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) μ :=
      (Measurable.ite isClosed_Ici.measurableSet
        ((ENNReal.continuous_ofReal.comp
          (continuous_const.mul (Real.continuous_exp.comp
            (Continuous.neg (continuous_const.mul
              (continuous_id.sub continuous_const)))))).measurable)
        measurable_const).aemeasurable
    have hite : (fun t : ℝ => if s ≤ t then
        ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) =
        (Ici s).indicator (fun t : ℝ =>
          ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))))) := by
      funext t
      by_cases h : s ≤ t <;> simp [h, Set.mem_Ici]
    let g : ℝ → ℝ := fun t => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))
    have hgc : Continuous g := continuous_const.mul (Real.continuous_exp.comp
      (Continuous.neg (continuous_const.mul (continuous_id.sub continuous_const))))
    have hig : Integrable g (volume.restrict (Icc s T)) := hgc.integrableOn_Icc
    have hcalc : ∫⁻ t, (if s ≤ t then
          ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) ∂μ ≤
        ENNReal.ofReal (∫ t in Icc s T,
          ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) := by
      rw [hite, MeasureTheory.lintegral_indicator isClosed_Ici.measurableSet]
      change (∫⁻ t, ENNReal.ofReal (g t) ∂μ.restrict (Ici s)) ≤ _
      rw [show μ.restrict (Ici s) =
        volume.restrict (Ici s ∩ Icc (0 : ℝ) T) by
          simp only [μ, Measure.restrict_restrict isClosed_Ici.measurableSet]]
      refine (MeasureTheory.lintegral_mono'
        (Measure.restrict_mono_set volume
          (show Ici s ∩ Icc (0 : ℝ) T ⊆ Icc s T from
            fun x hx => ⟨hx.1, hx.2.2⟩)) le_rfl).trans ?_
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hig
        (ae_of_all _ fun t => mul_nonneg (hw0 ξ) (exp_pos_heat _).le)).symm.le
    simp only [mixedKernelFun]
    rw [MeasureTheory.lintegral_const_mul''
      (ENNReal.ofReal ‖continuousNavierSource a b s ξ i‖) hc]
    exact mul_le_mul_of_nonneg_left
      (hcalc.trans (ENNReal.ofReal_le_ofReal (kernel_budget ξ s T ν hν)))
      (by positivity)
  have hp (ξ : ES) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ENNReal.ofReal (‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖) ≤
        ∫⁻ s, mixedKernelFun a b i ν ξ t s ∂μ := by
    let f' : ℝ → ℂ := fun s => heatMode ν (t - s)
      (fun ζ : ES => continuousNavierSource a b s ζ i) ξ
    have h1 : ‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖ ≤
        ∫ s in Icc (0 : ℝ) t, ‖ξ‖ * ‖f' s‖ := by
      change ‖ξ‖ * ‖∫ s in Icc (0 : ℝ) t, f' s‖ ≤ _
      refine (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm f')
        (norm_nonneg ξ)).trans ?_
      exact (MeasureTheory.integral_smul ‖ξ‖ (fun s : ℝ => ‖f' s‖)).symm.le
    have h2 := ofReal_integral_le_lintegral_ofReal
      (volume.restrict (Icc (0 : ℝ) t)) (fun s : ℝ => ‖ξ‖ * ‖f' s‖)
      (ae_of_all _ fun s => mul_nonneg (hw0 ξ) (norm_nonneg _))
    have h3 : (∫⁻ s, ENNReal.ofReal (‖ξ‖ * ‖f' s‖)
        ∂(volume.restrict (Icc (0 : ℝ) t))) =
        ∫⁻ s, mixedKernelFun a b i ν ξ t s
          ∂(volume.restrict (Icc (0 : ℝ) t)) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with s hs
      rw [show f' s = heatMode ν (t - s)
          (fun ζ : ES => continuousNavierSource a b s ζ i) ξ from rfl,
        norm_heatMode, mixedKernelFun, if_pos hs.2,
        ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact congrArg ENNReal.ofReal (by ring)
    calc ENNReal.ofReal (‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖)
        ≤ ENNReal.ofReal (∫ s in Icc (0 : ℝ) t, ‖ξ‖ * ‖f' s‖) :=
          ENNReal.ofReal_le_ofReal h1
      _ ≤ ∫⁻ s, ENNReal.ofReal (‖ξ‖ * ‖f' s‖)
          ∂(volume.restrict (Icc (0 : ℝ) t)) := h2
      _ = ∫⁻ s, mixedKernelFun a b i ν ξ t s
          ∂(volume.restrict (Icc (0 : ℝ) t)) := h3
      _ ≤ ∫⁻ s, mixedKernelFun a b i ν ξ t s ∂μ :=
        MeasureTheory.lintegral_mono' (Measure.restrict_mono
          (Icc_subset_Icc le_rfl ht.2) (le_refl _)) le_rfl
  have hkey : ∫⁻ p, ENNReal.ofReal ‖G p‖ ∂(volume.prod μ) ≤
      ENNReal.ofReal (ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
        normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) := by
    rw [show (fun p => ENNReal.ofReal ‖G p‖) = fun p => ENNReal.ofReal (G p) by
      funext p
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]]
    calc ∫⁻ p, ENNReal.ofReal (G p) ∂(volume.prod μ)
        = ∫⁻ t, ∫⁻ ξ, ENNReal.ofReal (G (ξ, t)) ∂volume ∂μ :=
          MeasureTheory.lintegral_prod_symm _
            (ENNReal.measurable_ofReal.comp_aemeasurable hG.aemeasurable)
      _ ≤ ∫⁻ t, ∫⁻ p : ES × ℝ,
          mixedKernelFun a b i ν p.1 t p.2 ∂(volume.prod μ) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hmT] with t ht
        refine (lintegral_mono (fun ξ => hp ξ t ht)).trans_eq ?_
        exact MeasureTheory.lintegral_lintegral (hW1 t ht)
      _ = ∫⁻ z : ℝ × (ES × ℝ),
          mixedKernelFun a b i ν z.2.1 z.1 z.2.2 ∂(μ.prod (volume.prod μ)) := by
        rw [← MeasureTheory.lintegral_lintegral
          (f := fun t : ℝ => fun p : ES × ℝ =>
            mixedKernelFun a b i ν p.1 t p.2) (hf := hW)]
      _ = ∫⁻ p : ES × ℝ, ∫⁻ t,
          mixedKernelFun a b i ν p.1 t p.2 ∂μ ∂(volume.prod μ) := by
        exact MeasureTheory.lintegral_prod_symm _ hW
      _ ≤ ∫⁻ p : ES × ℝ,
          ENNReal.ofReal ‖continuousNavierSource a b p.2 p.1 i‖ *
            ENNReal.ofReal (ν⁻¹ * ‖p.1‖⁻¹) ∂(volume.prod μ) :=
        lintegral_mono fun p => hbr p.1 p.2
      _ = ENNReal.ofReal ν⁻¹ * ∫⁻ p : ES × ℝ,
          ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource a b p.2 p.1 i‖)
            ∂(volume.prod μ) := by
        refine Eq.trans (lintegral_congr (fun p => ?_))
          (MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal ν⁻¹) hJ)
        rw [ENNReal.ofReal_mul (inv_nonneg.mpr hν.le),
          ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
        ring
      _ = ENNReal.ofReal ν⁻¹ * ∫⁻ s, ENNReal.ofReal
          (normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) ∂μ := by
        rw [MeasureTheory.lintegral_prod_symm _ hJ]
        refine congrArg (ENNReal.ofReal ν⁻¹ * ·) (lintegral_congr_ae ?_)
        filter_upwards [ae_restrict_mem hmT] with s hs
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hb0 s hs)
          (ae_of_all volume fun ξ => mul_nonneg (hw1 ξ) (norm_nonneg _))).symm.trans
            (congrArg ENNReal.ofReal rfl)
      _ = ENNReal.ofReal ν⁻¹ * ENNReal.ofReal
          (∫ s in Icc (0 : ℝ) T,
            normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) := by
        refine congrArg (ENNReal.ofReal ν⁻¹ * ·) ?_
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg
          (ae_of_all μ fun _ => integral_nonneg fun ξ =>
            mul_nonneg (hw1 ξ) (norm_nonneg _))).symm
      _ = ENNReal.ofReal (ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
          normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) :=
        (ENNReal.ofReal_mul (inv_nonneg.mpr hν.le)).symm
  refine ⟨hG, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  exact hkey.trans_lt ENNReal.ofReal_lt_top


/-- Product integrability gives both the time `L¹(X¹)` input and spatial
`X¹` integrability at almost every output time. -/
theorem continuousDuhamel_X1_integrability
    (a b : ℝ → ES → ComplexSpace) (ν T : ℝ) (i : Fin 3) (hν : 0 < ν)
    (hDjoint : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel ν a b p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW1 : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable
      (fun p : ES × ℝ => mixedKernelFun a b i ν p.1 t p.2)
      (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW : AEMeasurable
      (fun z : ℝ × (ES × ℝ) => mixedKernelFun a b i ν z.2.1 z.1 z.2.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod
        (volume.prod (volume.restrict (Icc (0 : ℝ) T)))))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
      ‖ξ‖⁻¹ * ‖continuousNavierSource a b s ξ i‖))
    (hg : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i))
      (volume.restrict (Icc (0 : ℝ) T)))
    (hJ : AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource a b p.2 p.1 i‖))
      (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    Integrable (fun t : ℝ =>
      normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i))
      (volume.restrict (Icc (0 : ℝ) T)) ∧
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖) := by
  have hprod := integrable_weighted_continuousDuhamel
    a b ν T i hν hDjoint hW1 hW hb0 hg hJ
  constructor
  · apply hprod.integral_prod_right.congr
    filter_upwards with t
    rfl
  · exact hprod.prod_left_ae


/-- Actual-box `D₃` with the time `L¹(X¹)` Duhamel premise generated by
maximal regularity.  The sole remaining Duhamel premise is spatial `X¹`
integrability at every output time; maximal regularity itself supplies it
almost everywhere. -/
theorem integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_maximal
    (ν : ℝ≥0) (hν : 0 < ν) (T xm1Radius x1WeightedRadius : ℝ)
    (hT : 0 ≤ T)
    (a : ES → ComplexSpace)
    (haM : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => a ξ i) volume)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (x : ActualLinkedBox ν T xm1Radius x1WeightedRadius)
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
  let μ := volume.restrict (Icc (0 : ℝ) T)
  have hνR : 0 < (ν : ℝ) := by exact_mod_cast hν
  have hcoord (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u u p.2 p.1 i) (volume.prod μ) :=
    continuousNavierSource_coord_aestronglyMeasurable u u 0 T
      (by simpa [u, μ] using hjoint) i
  have hDjoint (i : Fin 3) : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousDuhamel (ν : ℝ) u u p.2 p.1 i) (volume.prod μ) :=
    continuousDuhamel_coord_joint_aestronglyMeasurable (ν : ℝ) T u u i (hcoord i)
  have hsourceCoord (i : Fin 3) :=
    integrable_weightedContinuousNavierSource_coord_of_actualBox
      ν hν T xm1Radius x1WeightedRadius x T ⟨hT, le_rfl⟩ hjoint i
  have hg (i : Fin 3) : Integrable (fun s : ℝ =>
      normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) μ := by
    apply (hsourceCoord i).integral_norm_prod_right.congr
    filter_upwards with s
    unfold normXm1
    apply integral_congr_ae
    filter_upwards with ξ
    exact Real.norm_of_nonneg (mul_nonneg
      (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
  have hJ (i : Fin 3) : AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖))
      (volume.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((show AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ : ES × ℝ → ℝ)
        (volume.prod μ) by fun_prop).mul (hcoord i).norm).aemeasurable)
  obtain ⟨_, hb0⟩ := continuousNavierSource_fixedTime_inputs_of_actualBox
    ν hν T xm1Radius x1WeightedRadius x
  have hW1 (i : Fin 3) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) : AEMeasurable
      (fun p : ES × ℝ => mixedKernelFun u u i (ν : ℝ) p.1 r p.2)
      (volume.prod μ) := by
    change AEMeasurable (fun p : ES × ℝ =>
      ENNReal.ofReal ‖continuousNavierSource u u p.2 p.1 i‖ *
        (if p.2 ≤ r then ENNReal.ofReal
          (‖p.1‖ * Real.exp (-((ν : ℝ) * ‖p.1‖ ^ 2 * (r - p.2)))) else 0))
      (volume.prod μ)
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      (hcoord i).norm.aemeasurable).mul
        ((Measurable.ite (measurableSet_le measurable_snd measurable_const)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hW (i : Fin 3) : AEMeasurable
      (fun z : ℝ × (ES × ℝ) => mixedKernelFun u u i (ν : ℝ) z.2.1 z.1 z.2.2)
      (μ.prod (volume.prod μ)) := by
    have hcoord3 : AEStronglyMeasurable (fun z : ℝ × (ES × ℝ) =>
        continuousNavierSource u u z.2.2 z.2.1 i)
        (μ.prod (volume.prod μ)) :=
      (hcoord i).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    change AEMeasurable (fun z : ℝ × (ES × ℝ) =>
      ENNReal.ofReal ‖continuousNavierSource u u z.2.2 z.2.1 i‖ *
        (if z.2.2 ≤ z.1 then ENNReal.ofReal
          (‖z.2.1‖ * Real.exp (-((ν : ℝ) * ‖z.2.1‖ ^ 2 *
            (z.1 - z.2.2)))) else 0))
      (μ.prod (volume.prod μ))
    exact (ENNReal.measurable_ofReal.comp_aemeasurable
      hcoord3.norm.aemeasurable).mul
        ((Measurable.ite
          (measurableSet_le (measurable_snd.comp measurable_snd) measurable_fst)
          (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const).aemeasurable)
  have hD0 (i : Fin 3) : Integrable (fun t : ℝ =>
      normX1 (fun ξ : ES => continuousDuhamel (ν : ℝ) u u t ξ i)) μ :=
    (continuousDuhamel_X1_integrability u u (ν : ℝ) T i hνR
      (hDjoint i) (hW1 i) (hW i) (fun s _ => hb0 s i) (hg i) (hJ i)).1
  exact integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_measurable
    ν hν T xm1Radius x1WeightedRadius hT a haM ha ha1 x
      (by simpa [u, μ] using hD0) hDξ hjoint

end Navier.Analysis.ContinuousLeiLinBoxD3Maximal

set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Maximal.integrable_weighted_continuousDuhamel
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Maximal.continuousDuhamel_X1_integrability
set_option pp.fullNames true in
#print axioms Navier.Analysis.ContinuousLeiLinBoxD3Maximal.integral_coordinateX1Mass_continuousMildImage_le_of_actualBox_joint_maximal
