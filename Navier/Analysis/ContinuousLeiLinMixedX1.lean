import Navier.Analysis.ContinuousLeiLinAdmissibleContraction

/-!
# The mixed-slot spacetime `X¹` budget of the whole-space Duhamel term

`ContinuousLeiLinSelfMap` proves the spacetime `X¹` budget of the Duhamel term
only for the DIAGONAL feed `continuousDuhamel ν u u`: its Tonelli kernel
`kernelFun` is hard-wired to the source `continuousNavierSource u u`.  The
Banach contraction of the mild map needs the SAME budget for the two
polarization slots `continuousDuhamel ν (u − v) u` and
`continuousDuhamel ν v (u − v)`, which is the missing primitive named in the
`ContinuousLeiLinAdmissibleContraction` module header.

This module supplies it.  The diagonal argument never used the diagonal: it
uses only `‖continuousNavierSource · · s ξ i‖`, the causal `ite`, the
output-time bracket `kernel_budget`, and one Tonelli swap.  Replacing the
source by the mixed source `continuousNavierSource a b` therefore closes the
mixed case verbatim, and the coordinate aggregation closes against the mixed
`X⁰ × X⁰` feed `integral_normXm1_continuousNavierSource_le` rather than the
diagonal interpolation:

  `∫₀ᵀ X¹(Duhamel ν a b t) dt ≤ 3·ν⁻¹ · ∫₀ᵀ X⁰(a s)·X⁰(b s) ds`.

This is the exact `X¹` companion of the `X⁻¹` mixed budget
`coordinateXm1Mass_continuousDuhamel_le_integral_X0_product`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter Topology BigOperators
open scoped NNReal ENNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinDissipation

namespace Navier.Analysis.ContinuousLeiLinMixedX1

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
    r * q * ((ν * r ^ 2)⁻¹ * (1 - Real.exp (-(ν * r ^ 2 * t)))) ≤ ν⁻¹ * (r⁻¹ * q) := by
  have e1 : 1 - Real.exp (-(ν * r ^ 2 * t)) ≤ 1 := by
    nlinarith [exp_pos_heat (ν * r ^ 2 * t)]
  have hc : 0 < ν * r ^ 2 := mul_pos hν (pow_pos hr 2)
  have hA : 0 ≤ r * q := mul_nonneg hr.le hq
  calc r * q * ((ν * r ^ 2)⁻¹ * (1 - Real.exp (-(ν * r ^ 2 * t))))
      ≤ r * q * ((ν * r ^ 2)⁻¹ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 (inv_nonneg.mpr hc.le)) hA
    _ = r * q * (ν * r ^ 2)⁻¹ := by ring
    _ = ν⁻¹ * (r⁻¹ * q) := by field_simp [hν.ne', hr.ne']

/-- The heat multiplier evaluated pointwise on the complex carrier. -/
private theorem norm_heatMode (ν t : ℝ) (f : ES -> ℂ) (ξ : ES) :
    ‖heatMode ν t f ξ‖ = Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖f ξ‖ := by
  show ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * f ξ‖ = _
  rw [Complex.norm_mul, Complex.norm_real]
  exact congrArg (fun e : ℝ => e * ‖f ξ‖) (Real.norm_of_nonneg (exp_pos_heat _).le)

/-- The `ofReal`-bridge of a real integral to its `lintegral`, valid without
any integrability hypothesis: the non-integrable case collapses both sides. -/
private theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α -> ℝ) (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hfi : Integrable f μ
  · exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hf).le
  · rw [integral_undef hfi, ENNReal.ofReal_zero]
    positivity

/-- The output-time bracket of the heat kernel: integrating `‖ξ‖ * exp`
over the output horizon `[s, T]` costs `ν⁻¹ ‖ξ‖⁻¹`, uniformly in `s`, `T`. -/
private theorem kernel_budget (ξ : ES) (s T ν : ℝ) (hν : 0 < ν) :
    (∫ t in Icc s T, ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) ≤ ν⁻¹ * ‖ξ‖⁻¹ := by
  by_cases hr : ‖ξ‖ = 0
  · rw [hr]
    simp
  · have hw : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm hr)
    have hc : 0 < ν * ‖ξ‖ ^ 2 := mul_pos hν (pow_pos hw 2)
    by_cases hst : s ≤ T
    · have hts : 0 ≤ T - s := by linarith
      have hstep : (∫ t in Icc s T, ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) =
          ‖ξ‖ * ∫ x in Icc (0 : ℝ) (T - s), Real.exp (-(ν * ‖ξ‖ ^ 2 * x)) := by
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
      have hz : (∫ t in Icc s T, ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) = 0 := by
        rw [hset]
        simp
      rw [hz]
      positivity

/-- A single complex coordinate is bounded by the Hermitian Euclidean norm. -/
private theorem norm_coord_le_complexEuclideanNorm (z : ComplexSpace) (i : Fin 3) :
    ‖z i‖ ≤ complexEuclideanNorm z := by
  calc ‖z i‖ = ‖complexEuclideanPoint z i‖ :=
      congrArg (fun w : ℂ => ‖w‖) (complexEuclideanPoint_apply z i).symm
    _ ≤ ‖complexEuclideanPoint z‖ := PiLp.norm_apply_le (complexEuclideanPoint z) i

/-- The MIXED Tonelli kernel of the Duhamel `X¹` budget: the mixed source
`X⁻¹` weight as a `t`-constant factor, the heat weight killed off the causal
half-space by the `ite`. -/
def mixedKernelFun (a b : ℝ -> ES -> ComplexSpace) (i : Fin 3) (ν : ℝ)
    (ξ : ES) (t s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖continuousNavierSource a b s ξ i‖ *
    (if s ≤ t then
      ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0)

/-- **The mixed-slot per-coordinate spacetime `X¹` budget.**  The output-time
integral of the coordinate `X¹` mass of the MIXED Duhamel term is bounded by
`ν⁻¹` times the source-time integral of the coordinate `X⁻¹` mass of the mixed
source.  Mixed-slot generalization of
`ContinuousLeiLinSelfMap.integral_normX1_continuousDuhamel_self_le_source`. -/
theorem integral_normX1_continuousDuhamel_le_source
    (a b : ℝ → ES → ComplexSpace) (ν T : ℝ) (i : Fin 3) (hν : 0 < ν)
    (hD0 : Integrable (fun t : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖))
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
    ∫ t in Icc (0 : ℝ) T, normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i) ≤
      ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
        normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i) := by
  set μ := volume.restrict (Icc (0 : ℝ) T) with hμdef
  have hmT : MeasurableSet (Icc (0 : ℝ) T) := isClosed_Icc.measurableSet
  have hw0 (ξ : ES) : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hw1 (ξ : ES) : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ξ)
  -- bracket: the output-time integral of the causal kernel costs ν⁻¹ ‖ξ‖⁻¹
  have hbr (ξ : ES) (s : ℝ) :
      ∫⁻ t, mixedKernelFun a b i ν ξ t s ∂μ ≤
        ENNReal.ofReal ‖continuousNavierSource a b s ξ i‖ *
          ENNReal.ofReal (ν⁻¹ * ‖ξ‖⁻¹) := by
    have hc : AEMeasurable (fun t : ℝ => if s ≤ t then
        ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) μ :=
      (Measurable.ite (isClosed_Ici.measurableSet)
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
    set g : ℝ -> ℝ := fun t => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) with hgdef
    have hg : Continuous (fun t : ℝ => ‖ξ‖ *
        Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) :=
      continuous_const.mul (Real.continuous_exp.comp
        (Continuous.neg (continuous_const.mul
          (continuous_id.sub continuous_const))))
    have hig : Integrable g (volume.restrict (Icc s T)) :=
      hg.continuousOn.integrableOn_Icc
    have hL : ∫⁻ t, (fun t : ℝ => if s ≤ t then
          ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) t ∂μ
        = ∫⁻ t in Ici s, ENNReal.ofReal (‖ξ‖ *
            Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) ∂μ := by
      rw [hite, MeasureTheory.lintegral_indicator isClosed_Ici.measurableSet]
    have hE : ∫⁻ t in Ici s, ENNReal.ofReal (‖ξ‖ *
          Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) ∂μ
        = ∫⁻ t, (fun x : ℝ => ENNReal.ofReal (‖ξ‖ *
            Real.exp (-(ν * ‖ξ‖ ^ 2 * (x - s))))) t
            ∂(volume.restrict (Ici s ∩ Icc (0 : ℝ) T)) := by
      rw [hμdef, Measure.restrict_restrict isClosed_Ici.measurableSet]
    have hcalc : ∫⁻ t, (fun t : ℝ => if s ≤ t then
          ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) t ∂μ ≤
        ENNReal.ofReal (∫ t in Icc s T, ‖ξ‖ *
          Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) := by
      refine ((le_of_eq hL).trans (le_of_eq hE)).trans
        ((MeasureTheory.lintegral_mono'
            (Measure.restrict_mono_set volume
              (show Ici s ∩ Icc (0 : ℝ) T ⊆ Icc s T
                from fun x hx => ⟨hx.1, hx.2.2⟩)) le_rfl).trans
          ((MeasureTheory.ofReal_integral_eq_lintegral_ofReal hig
              (ae_of_all _ fun t =>
                mul_nonneg (hw0 ξ) (exp_pos_heat _).le)).symm.le.trans
            (le_of_eq rfl)))
    simp only [mixedKernelFun]
    rw [MeasureTheory.lintegral_const_mul''
      (ENNReal.ofReal ‖continuousNavierSource a b s ξ i‖) hc]
    exact mul_le_mul_of_nonneg_left
      (le_trans hcalc
        (ENNReal.ofReal_le_ofReal (kernel_budget ξ s T ν hν))) (by positivity)
  -- pointwise (t): the Duhamel X¹ mass passes through the kernel
  have h1t (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ENNReal.ofReal (normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i)) ≤
        ∫⁻ p : ES × ℝ, mixedKernelFun a b i ν p.1 t p.2 ∂(volume.prod μ) := by
    have hbx : ENNReal.ofReal (normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i)) =
        ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hDξ t ht)
        (ae_of_all volume fun ξ => mul_nonneg (hw0 ξ) (norm_nonneg _))
    have hp (ξ : ES) : ENNReal.ofReal (‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖) ≤
        ∫⁻ s, mixedKernelFun a b i ν ξ t s ∂μ := by
      set f' : ℝ -> ℂ := fun s => heatMode ν (t - s)
          (fun ζ : ES => continuousNavierSource a b s ζ i) ξ with hf'def
      have hD' : continuousDuhamel ν a b t ξ i = ∫ s in Icc (0 : ℝ) t, f' s := rfl
      have h1 : ‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖ ≤
          ∫ s in Icc (0 : ℝ) t, ‖ξ‖ * ‖f' s‖ := by
        rw [hD']
        refine le_trans (mul_le_mul_of_nonneg_left
            (norm_integral_le_integral_norm f') (norm_nonneg ξ)) ?_
        exact (MeasureTheory.integral_smul ‖ξ‖ (fun s : ℝ => ‖f' s‖)).symm.le
      have h2 : ENNReal.ofReal (∫ s in Icc (0 : ℝ) t, ‖ξ‖ * ‖f' s‖) ≤
          ∫⁻ s, ENNReal.ofReal (‖ξ‖ * ‖f' s‖) ∂(volume.restrict (Icc (0 : ℝ) t)) :=
        ofReal_integral_le_lintegral_ofReal (volume.restrict (Icc (0 : ℝ) t))
          (fun s : ℝ => ‖ξ‖ * ‖f' s‖)
          (ae_of_all _ fun s => mul_nonneg (hw0 ξ) (norm_nonneg _))
      have h3 : (∫⁻ s, ENNReal.ofReal (‖ξ‖ * ‖f' s‖)
            ∂(volume.restrict (Icc (0 : ℝ) t))) =
          ∫⁻ s, mixedKernelFun a b i ν ξ t s ∂(volume.restrict (Icc (0 : ℝ) t)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem (isClosed_Icc.measurableSet)] with s hs
        rw [Set.mem_Icc] at hs
        rw [hf'def, norm_heatMode, mixedKernelFun, if_pos hs.2,
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
    rw [hbx]
    refine (lintegral_mono_ae (ae_of_all volume hp)).trans ?_
    rw [← MeasureTheory.lintegral_lintegral
      (f := fun ξ : ES => fun s : ℝ => mixedKernelFun a b i ν ξ t s) (hf := hW1 t ht)]
  have hkey :
      ∫⁻ t, ENNReal.ofReal (normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i)) ∂μ ≤
        ENNReal.ofReal (ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
          normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) := by
    calc ∫⁻ t, ENNReal.ofReal (normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i)) ∂μ
        ≤ ∫⁻ t, ∫⁻ p : ES × ℝ, mixedKernelFun a b i ν p.1 t p.2 ∂(volume.prod μ) ∂μ :=
            (lintegral_mono_ae (by
              filter_upwards [ae_restrict_mem hmT] with t ht
              exact h1t t ht))
      _ = ∫⁻ z : ℝ × (ES × ℝ),
            mixedKernelFun a b i ν z.2.1 z.1 z.2.2 ∂(μ.prod (volume.prod μ)) := by
            rw [← MeasureTheory.lintegral_lintegral
              (f := fun t : ℝ => fun p : ES × ℝ => mixedKernelFun a b i ν p.1 t p.2)
              (hf := hW)]
      _ = ∫⁻ p : ES × ℝ, ∫⁻ t : ℝ, mixedKernelFun a b i ν p.1 t p.2 ∂μ ∂(volume.prod μ) := by
            refine MeasureTheory.lintegral_prod_symm
              (f := fun z : ℝ × (ES × ℝ) => mixedKernelFun a b i ν z.2.1 z.1 z.2.2)
              (hf := hW)
      _ ≤ ∫⁻ p : ES × ℝ, ENNReal.ofReal ‖continuousNavierSource a b p.2 p.1 i‖ *
            ENNReal.ofReal (ν⁻¹ * ‖p.1‖⁻¹) ∂(volume.prod μ) :=
            lintegral_mono_ae (ae_of_all (volume.prod μ) fun p => hbr p.1 p.2)
      _ = ENNReal.ofReal ν⁻¹ *
            ∫⁻ p : ES × ℝ,
              ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource a b p.2 p.1 i‖)
                ∂(volume.prod μ) := by
            refine Eq.trans (lintegral_congr (fun p => ?_))
              (MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal ν⁻¹) hJ)
            rw [ENNReal.ofReal_mul (inv_nonneg.mpr hν.le),
              ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
            ring
      _ = ENNReal.ofReal ν⁻¹ *
            ∫⁻ s, ENNReal.ofReal
              (normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) ∂μ := by
            rw [MeasureTheory.lintegral_prod_symm
              (f := fun p : ES × ℝ =>
                ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource a b p.2 p.1 i‖))
              (hf := hJ)]
            refine congrArg (ENNReal.ofReal ν⁻¹ * ·) (lintegral_congr_ae ?_)
            filter_upwards [ae_restrict_mem hmT] with s hs
            exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hb0 s hs)
                (ae_of_all volume fun ξ =>
                  mul_nonneg (hw1 ξ) (norm_nonneg _))).symm.trans
              (congrArg ENNReal.ofReal rfl)
      _ = ENNReal.ofReal ν⁻¹ * ENNReal.ofReal
            (∫ s in Icc (0 : ℝ) T,
              normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) := by
          refine congrArg (ENNReal.ofReal ν⁻¹ * ·) ?_
          exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg
            (ae_of_all μ fun _ =>
              integral_nonneg fun ξ => mul_nonneg (hw1 ξ) (norm_nonneg _))).symm
      _ = ENNReal.ofReal (ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) :=
          (ENNReal.ofReal_mul (inv_nonneg.mpr hν.le)).symm
  have hne : 0 ≤
      ν⁻¹ * ∫ s in Icc (0 : ℝ) T, normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i) :=
    mul_nonneg (inv_nonneg.mpr hν.le) (integral_nonneg fun s =>
      integral_nonneg fun ξ => mul_nonneg (hw1 ξ) (norm_nonneg _))
  refine (ENNReal.ofReal_le_ofReal_iff hne).mp ?_
  exact ((MeasureTheory.ofReal_integral_eq_lintegral_ofReal hD0
    (ae_of_all μ fun _ => integral_nonneg fun ξ =>
      mul_nonneg (hw0 ξ) (norm_nonneg _)))).le.trans hkey

/-- **The mixed-slot coordinate-aggregated spacetime `X¹` budget.**  Summing
the three coordinate budgets and closing with the MIXED bilinear source
estimate `integral_normXm1_continuousNavierSource_le` gives

  `∫₀ᵀ X¹(Duhamel ν a b t) dt ≤ 3·ν⁻¹ · ∫₀ᵀ X⁰(a s)·X⁰(b s) ds`,

the exact `X¹` companion of the `X⁻¹` mixed budget
`ContinuousLeiLinSelfMap.coordinateXm1Mass_continuousDuhamel_le_integral_X0_product`.
-/
theorem integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product
    (a b : ℝ → ES → ComplexSpace) (ν T : ℝ) (hν : 0 < ν)
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν a b t ξ i‖))
    (hW1 : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable
        (fun p : ES × ℝ => mixedKernelFun a b i ν p.1 t p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW : ∀ i : Fin 3, AEMeasurable
        (fun z : ℝ × (ES × ℝ) => mixedKernelFun a b i ν z.2.1 z.1 z.2.2)
        ((volume.restrict (Icc (0 : ℝ) T)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) T)))))
    (hb0 : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource a b s ξ i‖))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hJ : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource a b p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource a b s ξ)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource a b s ξ))
        (volume.restrict (Icc (0 : ℝ) T)))
    (ha : ∀ r j, AEStronglyMeasurable (fun η : ES => a r η j))
    (hbs : ∀ r j, AEStronglyMeasurable (fun η : ES => b r η j))
    (ha0 : ∀ r j, Integrable (fun η : ES => ‖a r η j‖))
    (hb00 : ∀ r j, Integrable (fun η : ES => ‖b r η j‖))
    (hprod : IntegrableOn (fun r =>
        coordinateX0Mass (a r) * coordinateX0Mass (b r)) (Icc (0 : ℝ) T)) :
    ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel ν a b t) ≤
      (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
        coordinateX0Mass (a s) * coordinateX0Mass (b s) := by
  have hmT : MeasurableSet (Icc (0 : ℝ) T) := isClosed_Icc.measurableSet
  have hw1 (ξ : ES) : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ξ)
  have hsrc (i : Fin 3) :
      (∫ s in Icc (0 : ℝ) T, normXm1 (fun ξ : ES =>
          continuousNavierSource a b s ξ i)) ≤
        ∫ s in Icc (0 : ℝ) T, ∫ ξ : ES, ‖ξ‖⁻¹ *
          complexEuclideanNorm (continuousNavierSource a b s ξ) := by
    refine setIntegral_mono_on (hf := hg i) (hg := hi) hmT fun s hs => ?_
    show (∫ ξ : ES, ‖ξ‖⁻¹ * ‖continuousNavierSource a b s ξ i‖) ≤
      ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierSource a b s ξ)
    exact MeasureTheory.integral_mono (hb0 i s hs) (hs1 s hs) fun ξ =>
      mul_le_mul_of_nonneg_left
        (norm_coord_le_complexEuclideanNorm (continuousNavierSource a b s ξ) i) (hw1 ξ)
  have hL : ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel ν a b t)
      = ∑ i : Fin 3, ∫ t in Icc (0 : ℝ) T,
          normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i) := by
    unfold coordinateX1Mass
    exact integral_finsetSum (f := fun i (t : ℝ) => normX1 (fun ξ : ES =>
      continuousDuhamel ν a b t ξ i)) Finset.univ (fun i _ => hD0 i)
  rw [hL]
  refine (Finset.sum_le_sum
    (f := fun i : Fin 3 => ∫ t in Icc (0 : ℝ) T,
        normX1 (fun ξ : ES => continuousDuhamel ν a b t ξ i))
    (g := fun i : Fin 3 => ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
        normXm1 (fun ξ : ES => continuousNavierSource a b s ξ i)) ?_).trans ?_
  · intro i _
    exact integral_normX1_continuousDuhamel_le_source a b ν T i hν (hD0 i) (hDξ i)
      (hW1 i) (hW i) (hb0 i) (hg i) (hJ i)
  · rw [← Finset.mul_sum]
    have hstep : (∑ i : Fin 3, ∫ s in Icc (0 : ℝ) T, normXm1 (fun ξ : ES =>
          continuousNavierSource a b s ξ i)) ≤
        (3 : ℝ) * ∫ s in Icc (0 : ℝ) T,
          coordinateX0Mass (a s) * coordinateX0Mass (b s) := by
      refine le_trans (Finset.sum_le_sum
        (f := fun i : Fin 3 => ∫ s in Icc (0 : ℝ) T, normXm1 (fun ξ : ES =>
            continuousNavierSource a b s ξ i))
        (g := fun _ : Fin 3 => ∫ s in Icc (0 : ℝ) T, ∫ ξ : ES, ‖ξ‖⁻¹ *
            complexEuclideanNorm (continuousNavierSource a b s ξ))
        (fun i _ => hsrc i)) ?_
      have hsum3 : (∑ _i : Fin 3, ∫ s in Icc (0 : ℝ) T, ∫ ξ : ES, ‖ξ‖⁻¹ *
            complexEuclideanNorm (continuousNavierSource a b s ξ))
          = (3 : ℝ) * ∫ s in Icc (0 : ℝ) T, ∫ ξ : ES, ‖ξ‖⁻¹ *
            complexEuclideanNorm (continuousNavierSource a b s ξ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          show (↑(3 : ℕ) : ℝ) = (3 : ℝ) from rfl]
      rw [hsum3]
      exact mul_le_mul_of_nonneg_left
        (integral_normXm1_continuousNavierSource_le a b (Icc (0 : ℝ) T)
          ha hbs ha0 hb00 hmT hi hprod)
        (by norm_num : (0 : ℝ) ≤ (3 : ℝ))
    refine le_trans (mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hν.le)) ?_
    exact le_of_eq (by ring)

end Navier.Analysis.ContinuousLeiLinMixedX1

#print axioms Navier.Analysis.ContinuousLeiLinMixedX1.integral_normX1_continuousDuhamel_le_source
#print axioms Navier.Analysis.ContinuousLeiLinMixedX1.integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product
