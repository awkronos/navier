import Navier.Analysis.WienerL1Carrier
import Navier.Analysis.LeiLinFixedPoint

/-!
# Large-data local mild solutions on the whole-space Wiener carrier

On the Banach space `C([0,T], L¹(ℝ³; ℂ)³)` of Fourier velocity coefficients,
the Navier–Stokes mild map

`x(t) = e^{tνΔ} a₀ + ∫_{(0,t]} K_σ (x(t-σ) ⊛ x(t-σ)) dσ`,

with `K_σ = e^{-νσ‖ξ‖²} · (Leray-projected Fourier derivative)` (`kernelOp`) and
`⊛` the coordinate convolution tensor (`tensorConv`), has a fixed point for
EVERY datum `a₀ ∈ L¹(ℝ³)³`, on every horizon with `10⁴ T ‖a₀‖² ≤ ν`
(`exists_wienerMildSolution`).  No smallness of the datum is assumed: the
contraction constant is `18 √(T/ν)`, from the operator bound
`‖K_σ‖ ≤ 9 (νσ)^{-1/2}` (`norm_kernelOp_le`) integrated over `(0, T]`
(`integral_singWeight`).  The horizon law is the subcritical scaling
`T ≍ ν / ‖a₀‖²_{L¹}`.

Scope: this is a mild solution in Fourier-coefficient classes.  Its
identification with the pointwise continuous Duhamel image
`ContinuousLeiLinTimeDuhamel.continuousDuhamel` and its regularity lift to
the classical carrier `SolvesBefore` are not claimed here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Navier.Analysis.WienerLocalMild

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerL1Carrier

/-! ## The integrable singular weight -/

/-- `σ ↦ ν^{-1/2} σ^{-1/2}`. -/
def singWeight (ν σ : ℝ) : ℝ := (Real.sqrt ν)⁻¹ * σ ^ (-(1 / 2 : ℝ))

theorem sqrt_mul_inv_eq_singWeight {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ) :
    (Real.sqrt (ν * σ))⁻¹ = singWeight ν σ := by
  unfold singWeight
  rw [Real.sqrt_mul hν.le, mul_inv, Real.rpow_neg hσ.le, Real.sqrt_eq_rpow σ]

theorem singWeight_nonneg (ν σ : ℝ) (hσ : 0 ≤ σ) : 0 ≤ singWeight ν σ := by
  unfold singWeight
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.rpow_nonneg hσ _)

theorem integrableOn_singWeight (ν : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (singWeight ν) (Ioc 0 T) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T)
    (r := -(1 / 2 : ℝ)) (by norm_num)).const_mul (Real.sqrt ν)⁻¹
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp h

theorem integral_singWeight (ν : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ σ in Ioc 0 T, singWeight ν σ = 2 * (Real.sqrt ν)⁻¹ * Real.sqrt T := by
  rw [← intervalIntegral.integral_of_le hT]
  unfold singWeight
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, Real.zero_rpow (by norm_num),
    ← Real.sqrt_eq_rpow]
  ring

/-! ## Paths and the Duhamel integrand -/

variable {ν T : ℝ}

/-- Extension of a path on `[0, T]` to `ℝ` by clamping. -/
def extend (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, V1)) (s : ℝ) : V1 :=
  u (projIcc 0 T hT s)

theorem continuous_extend (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, V1)) :
    Continuous (extend hT u) :=
  u.continuous.comp continuous_projIcc

theorem norm_extend_le (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, V1)) (s : ℝ) :
    ‖extend hT u s‖ ≤ ‖u‖ :=
  u.norm_coe_le_norm _

theorem extend_sub (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1)) (s : ℝ) :
    extend hT (u - v) s = extend hT u s - extend hT v s := rfl

/-- The σ-integrand of the Duhamel term at time `t` (the kernel is applied at
lag `σ` to the nonlinearity at time `t - σ`; zero for `σ > t`). -/
def duhIntegrand (ν : ℝ) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1)) (t σ : ℝ) : V1 :=
  (Iic t).indicator
    (fun σ => kernelOp ν σ (tensorConv (extend hT u (t - σ)) (extend hT v (t - σ)))) σ

/-- The Duhamel term, as a function of `t ∈ ℝ`. -/
def duhamel (ν : ℝ) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1)) (t : ℝ) : V1 :=
  ∫ σ in Ioc 0 T, duhIntegrand ν hT u v t σ

theorem continuous_nonlin (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1)) (t : ℝ) :
    Continuous fun σ : ℝ => tensorConv (extend hT u (t - σ)) (extend hT v (t - σ)) :=
  (tensorConv.continuous.comp ((continuous_extend hT u).comp
    (continuous_const.sub continuous_id))).clm_apply
    ((continuous_extend hT v).comp (continuous_const.sub continuous_id))

theorem norm_duhIntegrand_le (hν : 0 < ν) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1))
    (t : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ‖duhIntegrand ν hT u v t σ‖ ≤ 9 * singWeight ν σ * (‖u‖ * ‖v‖) := by
  unfold duhIntegrand
  by_cases hmem : σ ∈ Iic t
  · rw [indicator_of_mem hmem]
    calc ‖kernelOp ν σ (tensorConv (extend hT u (t - σ)) (extend hT v (t - σ)))‖
        ≤ ‖kernelOp ν σ‖ * ‖tensorConv (extend hT u (t - σ)) (extend hT v (t - σ))‖ :=
          (kernelOp ν σ).le_opNorm _
      _ ≤ (9 * singWeight ν σ) * (‖u‖ * ‖v‖) := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by
            have := singWeight_nonneg ν σ hσ.le; positivity)
          · rw [← sqrt_mul_inv_eq_singWeight hν hσ]; exact norm_kernelOp_le hν hσ
          · exact (norm_tensorConv_apply_le _ _).trans
              (mul_le_mul (norm_extend_le hT u _) (norm_extend_le hT v _) (norm_nonneg _)
                (norm_nonneg _))
  · rw [indicator_of_notMem hmem, norm_zero]
    have := singWeight_nonneg ν σ hσ.le
    positivity

theorem aestronglyMeasurable_duhIntegrand (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : C(Icc (0 : ℝ) T, V1)) (t : ℝ) :
    AEStronglyMeasurable (duhIntegrand ν hT u v t) (volume.restrict (Ioc 0 T)) := by
  have hG : ContinuousOn
      (fun σ => kernelOp ν σ (tensorConv (extend hT u (t - σ)) (extend hT v (t - σ))))
      (Ioc 0 T) :=
    ((continuousOn_kernelOp hν).mono fun σ hσ => hσ.1).clm_apply
      (continuous_nonlin hT u v t).continuousOn
  exact (hG.aestronglyMeasurable measurableSet_Ioc).indicator measurableSet_Iic

theorem ae_norm_duhIntegrand_le (hν : 0 < ν) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1))
    (t : ℝ) :
    ∀ᵐ σ ∂(volume.restrict (Ioc 0 T)),
      ‖duhIntegrand ν hT u v t σ‖ ≤ 9 * singWeight ν σ * (‖u‖ * ‖v‖) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
  exact norm_duhIntegrand_le hν hT u v t hσ.1

theorem integrable_bound (ν : ℝ) (hT : 0 ≤ T) (c : ℝ) :
    Integrable (fun σ => 9 * singWeight ν σ * c) (volume.restrict (Ioc 0 T)) :=
  ((integrableOn_singWeight ν hT).const_mul 9).mul_const c

theorem integrable_duhIntegrand (hν : 0 < ν) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1))
    (t : ℝ) : Integrable (duhIntegrand ν hT u v t) (volume.restrict (Ioc 0 T)) :=
  (integrable_bound ν hT (‖u‖ * ‖v‖)).mono' (aestronglyMeasurable_duhIntegrand hν hT u v t)
    (ae_norm_duhIntegrand_le hν hT u v t)

theorem continuous_duhamel (hν : 0 < ν) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1)) :
    Continuous (duhamel ν hT u v) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  refine continuousAt_of_dominated
    (Eventually.of_forall fun t => aestronglyMeasurable_duhIntegrand hν hT u v t)
    (Eventually.of_forall fun t => ae_norm_duhIntegrand_le hν hT u v t)
    (integrable_bound ν hT (‖u‖ * ‖v‖)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (Measure.ae_ne volume t₀)] with σ _hσ hne
  have hcont : Continuous fun t : ℝ =>
      kernelOp ν σ (tensorConv (extend hT u (t - σ)) (extend hT v (t - σ))) :=
    (kernelOp ν σ).continuous.comp
      ((tensorConv.continuous.comp ((continuous_extend hT u).comp
        (continuous_id.sub continuous_const))).clm_apply
        ((continuous_extend hT v).comp (continuous_id.sub continuous_const)))
  rcases lt_or_gt_of_ne hne with h | h
  · refine hcont.continuousAt.congr ?_
    filter_upwards [lt_mem_nhds h] with t ht
    unfold duhIntegrand
    rw [indicator_of_mem (show σ ∈ Iic t from ht.le)]
  · refine continuousAt_const.congr (?_ : (fun _ : ℝ => (0 : V1)) =ᶠ[𝓝 t₀] _)
    filter_upwards [gt_mem_nhds h] with t ht
    unfold duhIntegrand
    rw [indicator_of_notMem (show σ ∉ Iic t from fun h' => absurd (lt_of_le_of_lt h' ht)
      (lt_irrefl _))]

theorem duhIntegrand_diff (hT : 0 ≤ T) (a b : C(Icc (0 : ℝ) T, V1)) (t σ : ℝ) :
    duhIntegrand ν hT a a t σ - duhIntegrand ν hT b b t σ =
      duhIntegrand ν hT (a - b) a t σ + duhIntegrand ν hT b (a - b) t σ := by
  unfold duhIntegrand
  by_cases hmem : σ ∈ Iic t
  · simp only [indicator_of_mem hmem, extend_sub, map_sub, ContinuousLinearMap.sub_apply]
    abel
  · simp only [indicator_of_notMem hmem, sub_zero, add_zero]

/-! ## The bilinear Duhamel map on `C([0,T], V1)` -/

/-- The Duhamel term as a bilinear map on continuous paths. -/
def duhamelPath (hν : 0 < ν) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1)) :
    C(Icc (0 : ℝ) T, V1) :=
  ⟨fun t => duhamel ν hT u v t, (continuous_duhamel hν hT u v).comp continuous_subtype_val⟩

theorem duhamelPath_apply (hν : 0 < ν) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1))
    (t : Icc (0 : ℝ) T) : duhamelPath hν hT u v t = duhamel ν hT u v t := rfl

/-- **The short-time bilinear estimate**: constant `18 √(T/ν)`. -/
theorem norm_duhamelPath_le (hν : 0 < ν) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1)) :
    ‖duhamelPath hν hT u v‖ ≤ (18 * (Real.sqrt ν)⁻¹ * Real.sqrt T) * (‖u‖ * ‖v‖) := by
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
  rw [duhamelPath_apply]
  calc ‖duhamel ν hT u v t‖
      ≤ ∫ σ in Ioc 0 T, 9 * singWeight ν σ * (‖u‖ * ‖v‖) :=
        norm_integral_le_of_norm_le (integrable_bound ν hT _)
          (ae_norm_duhIntegrand_le hν hT u v t)
    _ = 9 * (∫ σ in Ioc 0 T, singWeight ν σ) * (‖u‖ * ‖v‖) := by
        rw [integral_mul_const, integral_const_mul]
    _ = (18 * (Real.sqrt ν)⁻¹ * Real.sqrt T) * (‖u‖ * ‖v‖) := by
        rw [integral_singWeight ν hT]; ring

theorem duhamelPath_diff (hν : 0 < ν) (hT : 0 ≤ T) (a b : C(Icc (0 : ℝ) T, V1)) :
    duhamelPath hν hT a a - duhamelPath hν hT b b =
      duhamelPath hν hT (a - b) a + duhamelPath hν hT b (a - b) := by
  ext1 t
  simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, duhamelPath_apply, duhamel]
  rw [← integral_sub (integrable_duhIntegrand hν hT a a t) (integrable_duhIntegrand hν hT b b t),
    ← integral_add (integrable_duhIntegrand hν hT (a - b) a t)
      (integrable_duhIntegrand hν hT b (a - b) t)]
  congr 1
  funext σ
  exact duhIntegrand_diff hT a b t σ

/-! ## The free evolution -/

/-- The heat path `t ↦ e^{tνΔ} a₀` on `[0, T]`. -/
def heatPath (hν : 0 < ν) (a₀ : V1) : C(Icc (0 : ℝ) T, V1) :=
  ⟨fun t => heatOp ν t a₀, (continuous_heatOp_apply hν.le a₀).comp continuous_subtype_val⟩

theorem norm_heatPath_le (hν : 0 < ν) (a₀ : V1) :
    ‖(heatPath hν a₀ : C(Icc (0 : ℝ) T, V1))‖ ≤ ‖a₀‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun t => norm_heatOp_apply_le ν t a₀

/-! ## Large-data local existence -/

/-- The Duhamel integral over `Ioc 0 T` with the `Iic t` cut is the causal
integral over `(0, t]`. -/
theorem duhamel_eq_causal (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, V1)) {t : ℝ}
    (htT : t ≤ T) :
    duhamel ν hT u v t = ∫ σ in Ioc 0 t,
      kernelOp ν σ (tensorConv (extend hT u (t - σ)) (extend hT v (t - σ))) := by
  unfold duhamel duhIntegrand
  rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right htT]

/-- **Large-data local mild existence on the whole-space Wiener carrier.**
For every viscosity `ν > 0`, every datum `a₀ ∈ L¹(ℝ³; ℂ)³` (no smallness) and
every horizon `T > 0` with `10⁴ T ‖a₀‖² ≤ ν`, there is a continuous path
`x : [0,T] → L¹(ℝ³; ℂ)³` with `‖x‖ ≤ 2‖a₀‖` solving the Navier–Stokes mild
equation in Fourier variables. -/
theorem exists_wienerMildSolution (hν : 0 < ν) (hT : 0 < T) (a₀ : V1)
    (hsmall : 10 ^ 4 * T * ‖a₀‖ ^ 2 ≤ ν) :
    ∃ x : C(Icc (0 : ℝ) T, V1), ‖x‖ ≤ 2 * ‖a₀‖ ∧
      ∀ t : Icc (0 : ℝ) T, x t = heatOp ν t a₀ + ∫ σ in Ioc 0 (t : ℝ),
        kernelOp ν σ (tensorConv (extend hT.le x (t - σ)) (extend hT.le x (t - σ))) := by
  set C : ℝ := 18 * (Real.sqrt ν)⁻¹ * Real.sqrt T with hC
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hC0 : 0 < C := by rw [hC]; positivity
  set y : C(Icc (0 : ℝ) T, V1) := heatPath hν a₀ with hy
  have hyle : ‖y‖ ≤ ‖a₀‖ := norm_heatPath_le hν a₀
  have hroot : 100 * (Real.sqrt T * ‖a₀‖) ≤ Real.sqrt ν := by
    have h := Real.sqrt_le_sqrt hsmall
    rwa [show (10 : ℝ) ^ 4 * T * ‖a₀‖ ^ 2 = (100 * (Real.sqrt T * ‖a₀‖)) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]; ring,
      Real.sqrt_sq (by positivity)] at h
  have hsmallC : 4 * C * ‖y‖ < 1 := by
    have h1 : 4 * C * ‖y‖ ≤ 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν := by
      rw [hC, div_eq_mul_inv]
      have : 4 * (18 * (Real.sqrt ν)⁻¹ * Real.sqrt T) * ‖y‖ ≤
          4 * (18 * (Real.sqrt ν)⁻¹ * Real.sqrt T) * ‖a₀‖ :=
        mul_le_mul_of_nonneg_left hyle (by positivity)
      nlinarith [this]
    have h2 : 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν < 1 := by
      rw [div_lt_one hsν]
      have : 0 ≤ Real.sqrt T * ‖a₀‖ := by positivity
      nlinarith
    linarith
  obtain ⟨x, hxle, hxeq⟩ := Navier.Analysis.LeiLinFixedPoint.picard_small_data
    (B := duhamelPath hν hT.le) hC0 (norm_duhamelPath_le hν hT.le)
    (duhamelPath_diff hν hT.le) y hsmallC
  refine ⟨x, hxle.trans (by linarith), fun t => ?_⟩
  have := congrArg (fun z : C(Icc (0 : ℝ) T, V1) => z t) hxeq
  simp only [ContinuousMap.add_apply] at this
  rw [this, hy, duhamelPath_apply, duhamel_eq_causal hT.le x x t.2.2]
  rfl

end Navier.Analysis.WienerLocalMild

set_option pp.fullNames true in
#check @Navier.Analysis.WienerLocalMild.exists_wienerMildSolution
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerLocalMild.exists_wienerMildSolution
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerLocalMild.norm_duhamelPath_le
