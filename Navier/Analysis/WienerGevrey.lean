import Navier.Analysis.WienerMoments

/-!
# Gevrey smoothing of the Wiener mild solution

For a datum `a₀ ∈ L¹(ℝ³; ℂ)³` with no moment assumed, the Picard fixed point of the
Fourier mild equation is instantly Gevrey regular:

`∫ e^{√(νt)‖ξ‖} |x(t, ξ)| dξ ≤ 12‖a₀‖` for every `t ∈ [0, T]`, when `10⁶ T ‖a₀‖² ≤ ν`

(`fixedPoint_mem_gevSet`).  The horizon does not depend on any moment of the datum.
Every Fourier moment at a positive time follows:
`momV n (x t) ≤ n! (νt)^{-n/2} · 12‖a₀‖` (`momV_le_of_gevSet`).

This is the smoothing input of item 6 (local existence from `H³` data): `H³` data have
Fourier transform in `L¹` but only moments of order `< 3/2`.

Mechanism: the weight `e^{a‖ξ‖}` is submultiplicative, so it passes through the
convolution; the heat factor absorbs `e^{a‖ξ‖}` when `a² ≤ νt`; and the kernel absorbs
the weight increment `√(νt) - √(ν(t-σ)) ≤ √(νσ)` at the cost of a constant times the
same integrable singularity `σ^{-1/2}` that drives the `L¹` theory.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Convolution

namespace Navier.Analysis.WienerGevrey

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerLocalMild
open Navier.Analysis.WienerMoments

/-! ## Weighted `L¹` functionals -/

/-- The weighted `L¹` functional `∫ w(ξ) |f(ξ)| dξ ∈ [0, ∞]`. -/
def wm (w : ES → ℝ) (f : L1C) : ℝ≥0∞ := ∫⁻ ξ, ENNReal.ofReal (w ξ) * ‖f ξ‖ₑ

/-- Truncated weight `min(w, N)` as a bounded multiplier. -/
def truncWL (w : ES → ℝ) (hw : Continuous w) (hw0 : ∀ ξ, 0 ≤ w ξ) (N : ℕ) : LinfC :=
  linfOfBound (fun ξ => ((min (w ξ) (N : ℝ) : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp (hw.min continuous_const).measurable).aestronglyMeasurable N
    (fun ξ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_min (hw0 ξ) (Nat.cast_nonneg N))]
      exact min_le_right _ _)

theorem ofReal_norm_mulL_truncWL (w : ES → ℝ) (hw : Continuous w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (N : ℕ) (f : L1C) :
    ENNReal.ofReal ‖mulL (truncWL w hw hw0 N) f‖ =
      ∫⁻ ξ, ENNReal.ofReal (min (w ξ) (N : ℝ)) * ‖f ξ‖ₑ := by
  rw [L1.ofReal_norm_eq_lintegral]
  apply lintegral_congr_ae
  filter_upwards [coeFn_mulL (truncWL w hw hw0 N) f, coeFn_linfOfBound _ _ _ _] with ξ h1 h2
  rw [h1, enorm_mul]
  unfold truncWL
  rw [h2, enorm_ofReal_complex (le_min (hw0 ξ) (Nat.cast_nonneg N))]

theorem wm_eq_iSup (w : ES → ℝ) (hw : Continuous w) (hw0 : ∀ ξ, 0 ≤ w ξ) (f : L1C) :
    wm w f = ⨆ N : ℕ, ENNReal.ofReal ‖mulL (truncWL w hw hw0 N) f‖ := by
  simp_rw [ofReal_norm_mulL_truncWL]
  unfold wm
  have hfm : Measurable fun ξ => ‖f ξ‖ₑ := (Lp.stronglyMeasurable f).enorm
  have hmeas : ∀ N : ℕ, Measurable (fun ξ => ENNReal.ofReal (min (w ξ) (N : ℝ)) * ‖f ξ‖ₑ) :=
    fun N => (ENNReal.measurable_ofReal.comp (hw.min continuous_const).measurable).mul hfm
  have hmono : Monotone (fun N : ℕ => fun ξ => ENNReal.ofReal (min (w ξ) (N : ℝ)) * ‖f ξ‖ₑ) := by
    intro N M hNM ξ
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact min_le_min_left _ (by exact_mod_cast hNM)
  rw [← lintegral_iSup hmeas hmono]
  congr 1
  funext ξ
  rw [← ENNReal.iSup_mul]
  congr 1
  exact (iSup_ofReal_min _).symm

theorem lowerSemicontinuous_wm (w : ES → ℝ) (hw : Continuous w) (hw0 : ∀ ξ, 0 ≤ w ξ) :
    LowerSemicontinuous (wm w) := by
  have h : wm w = fun f => ⨆ N : ℕ, ENNReal.ofReal ‖mulL (truncWL w hw hw0 N) f‖ :=
    funext (wm_eq_iSup w hw hw0)
  rw [h]
  exact lowerSemicontinuous_iSup fun N =>
    (ENNReal.continuous_ofReal.comp (continuous_norm.comp (mulL _).continuous)).lowerSemicontinuous

/-- Minkowski's inequality for the weighted functional. -/
theorem wm_integral_le (w : ES → ℝ) (hw : Continuous w) (hw0 : ∀ ξ, 0 ≤ w ξ) {S : Set ℝ}
    (G : ℝ → L1C) (hG : Integrable G (volume.restrict S))
    (b : ℝ → ℝ) (hb : Integrable b (volume.restrict S)) (hb0 : ∀ σ, 0 ≤ b σ)
    (hGb : ∀ᵐ σ ∂(volume.restrict S), wm w (G σ) ≤ ENNReal.ofReal (b σ)) :
    wm w (∫ σ in S, G σ) ≤ ENNReal.ofReal (∫ σ in S, b σ) := by
  rw [wm_eq_iSup w hw hw0]
  refine iSup_le fun N => ?_
  rw [← (mulL (truncWL w hw hw0 N)).integral_comp_comm hG]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_ae ((mulL (truncWL w hw hw0 N)).integrable_comp hG).norm hb ?_)
  filter_upwards [hGb] with σ h
  have h1 : ENNReal.ofReal ‖mulL (truncWL w hw hw0 N) (G σ)‖ ≤ ENNReal.ofReal (b σ) :=
    (le_iSup (fun M : ℕ => ENNReal.ofReal ‖mulL (truncWL w hw hw0 M) (G σ)‖) N).trans
      ((wm_eq_iSup w hw hw0 (G σ)).symm.le.trans h)
  exact (ENNReal.ofReal_le_ofReal_iff (hb0 σ)).mp h1

/-- A multiplier that trades the weight `w` for `w'` at cost `c`. -/
theorem wm_mulL_le (w w' : ES → ℝ) (m : LinfC) {c : ℝ} (hc : 0 ≤ c)
    (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hm : ∀ᵐ ξ ∂(volume : Measure ES), w ξ * ‖m ξ‖ ≤ c * w' ξ) (f : L1C) :
    wm w (mulL m f) ≤ ENNReal.ofReal c * wm w' f := by
  unfold wm
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [coeFn_mulL m f, hm] with ξ h1 h2
  rw [h1, enorm_mul, ← mul_assoc]
  have h3 : ENNReal.ofReal (w ξ) * ‖m ξ‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal (w' ξ) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (hw0 ξ), ← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal h2
  calc ENNReal.ofReal (w ξ) * ‖m ξ‖ₑ * ‖f ξ‖ₑ
      ≤ ENNReal.ofReal c * ENNReal.ofReal (w' ξ) * ‖f ξ‖ₑ := by gcongr
    _ = ENNReal.ofReal c * (ENNReal.ofReal (w' ξ) * ‖f ξ‖ₑ) := by ring

theorem wm_add_le (w : ES → ℝ) (hw : Continuous w) (f g : L1C) :
    wm w (f + g) ≤ wm w f + wm w g := by
  unfold wm
  have hm : Measurable (fun ξ : ES => ENNReal.ofReal (w ξ) * ‖f ξ‖ₑ) :=
    (ENNReal.measurable_ofReal.comp hw.measurable).mul (Lp.stronglyMeasurable f).enorm
  rw [← lintegral_add_left hm]
  apply lintegral_mono_ae
  filter_upwards [Lp.coeFn_add f g] with ξ h
  rw [h, Pi.add_apply, ← mul_add]
  gcongr
  exact enorm_add_le _ _

theorem wm_zero (w : ES → ℝ) : wm w (0 : L1C) = 0 := by
  unfold wm
  have h0 : (fun ξ : ES => ENNReal.ofReal (w ξ) * ‖(0 : L1C) ξ‖ₑ) =ᵐ[volume] 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 1 (volume : Measure ES)] with ξ h
    simp [h]
  rw [lintegral_congr_ae h0]
  simp

theorem wm_sum_le (w : ES → ℝ) (hw : Continuous w) {ι : Type*} (s : Finset ι) (f : ι → L1C) :
    wm w (∑ i ∈ s, f i) ≤ ∑ i ∈ s, wm w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wm_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (wm_add_le w hw _ _).trans (add_le_add le_rfl ih)

/-- A submultiplicative weight passes through the convolution. -/
theorem wm_conv_le (w : ES → ℝ) (hw : Continuous w) (hw0 : ∀ ξ, 0 ≤ w ξ)
    (hsub : ∀ ξ η, w ξ ≤ w η * w (ξ - η)) (f g : L1C) :
    wm w (conv f g) ≤ wm w f * wm w g := by
  have hF : Measurable fun η => ‖f η‖ₑ := (Lp.stronglyMeasurable f).enorm
  have hG : Measurable fun η => ‖g η‖ₑ := (Lp.stronglyMeasurable g).enorm
  have hwm : Measurable fun η : ES => ENNReal.ofReal (w η) :=
    ENNReal.measurable_ofReal.comp hw.measurable
  have hsubm : Measurable fun p : ES × ES => p.1 - p.2 := measurable_fst.sub measurable_snd
  let A : ES → ES → ℝ≥0∞ := fun ξ η =>
    (ENNReal.ofReal (w η) * ‖f η‖ₑ) * (ENNReal.ofReal (w (ξ - η)) * ‖g (ξ - η)‖ₑ)
  have hAm : Measurable (Function.uncurry A) :=
    ((hwm.comp measurable_snd).mul (hF.comp measurable_snd)).mul
      ((hwm.comp hsubm).mul (hG.comp hsubm))
  have h1 : wm w (conv f g) = ∫⁻ ξ, ENNReal.ofReal (w ξ) *
      ‖((⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (⇑g)) ξ‖ₑ := by
    unfold wm
    apply lintegral_congr_ae
    filter_upwards [coeFn_convFun f g] with ξ h
    rw [conv_apply, h]
  have hpt : ∀ ξ, ENNReal.ofReal (w ξ) *
      ‖((⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (⇑g)) ξ‖ₑ ≤ ∫⁻ η, A ξ η := by
    intro ξ
    calc ENNReal.ofReal (w ξ) * ‖((⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (⇑g)) ξ‖ₑ
        ≤ ENNReal.ofReal (w ξ) * ∫⁻ η, ‖f η‖ₑ * ‖g (ξ - η)‖ₑ := by
          gcongr; exact enorm_convolution_le _ _ ξ
      _ = ∫⁻ η, ENNReal.ofReal (w ξ) * (‖f η‖ₑ * ‖g (ξ - η)‖ₑ) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, A ξ η := by
          refine lintegral_mono fun η => ?_
          have hw' : ENNReal.ofReal (w ξ) ≤ ENNReal.ofReal (w η) * ENNReal.ofReal (w (ξ - η)) := by
            rw [← ENNReal.ofReal_mul (hw0 η)]; exact ENNReal.ofReal_le_ofReal (hsub ξ η)
          calc ENNReal.ofReal (w ξ) * (‖f η‖ₑ * ‖g (ξ - η)‖ₑ)
              ≤ ENNReal.ofReal (w η) * ENNReal.ofReal (w (ξ - η)) *
                  (‖f η‖ₑ * ‖g (ξ - η)‖ₑ) := by gcongr
            _ = A ξ η := by simp only [A]; ring
  have hT : ∫⁻ ξ, ∫⁻ η, A ξ η = wm w f * wm w g := by
    rw [lintegral_lintegral_swap hAm.aemeasurable]
    have hin : ∀ η, ∫⁻ ξ, A ξ η = (ENNReal.ofReal (w η) * ‖f η‖ₑ) * wm w g := by
      intro η
      simp only [A]
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)]
      congr 1
      exact lintegral_sub_right_eq_self (fun ξ => ENNReal.ofReal (w ξ) * ‖g ξ‖ₑ) η
    simp_rw [hin]
    have hm : Measurable (fun y : ES => ENNReal.ofReal (w y) * ‖f y‖ₑ) := hwm.mul hF
    rw [lintegral_mul_const _ hm]
    rfl
  rw [h1]
  exact (lintegral_mono hpt).trans hT.le

/-! ## The Gevrey weight -/

/-- The Gevrey weight `e^{a‖ξ‖}`. -/
def gw (a : ℝ) (ξ : ES) : ℝ := Real.exp (a * ‖ξ‖)

theorem continuous_gw (a : ℝ) : Continuous (gw a) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_norm)

theorem gw_nonneg (a : ℝ) (ξ : ES) : 0 ≤ gw a ξ := (Real.exp_pos _).le

theorem gw_sub {a : ℝ} (ha : 0 ≤ a) (ξ η : ES) : gw a ξ ≤ gw a η * gw a (ξ - η) := by
  unfold gw
  rw [← Real.exp_add, Real.exp_le_exp, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ ha
  have := norm_add_le η (ξ - η)
  rwa [add_sub_cancel] at this

theorem wm_gw_zero (f : L1C) : wm (gw 0) f = ENNReal.ofReal ‖f‖ := by
  rw [L1.ofReal_norm_eq_lintegral]
  simp [wm, gw]

theorem exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have hp := Real.exp_pos (1 / 2)
  nlinarith

theorem exp_quarter_le_two : Real.exp (1 / 4) ≤ 2 := by
  have h : Real.exp (1 / 4) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by norm_num)
  exact h.trans exp_half_le_two

/-- The heat factor absorbs `e^{a‖ξ‖}` when `a² ≤ ντ`. -/
theorem gw_mul_heatFactor_le {ν τ a : ℝ} (ha : 0 ≤ a) (haτ : a ^ 2 ≤ ν * τ) (ξ : ES) :
    gw a ξ * heatFactor ν τ ξ ≤ 2 := by
  unfold gw heatFactor
  rw [← Real.exp_add]
  refine le_trans (Real.exp_le_exp.mpr ?_) exp_quarter_le_two
  have hr := norm_nonneg ξ
  have h1 : a ^ 2 * ‖ξ‖ ^ 2 ≤ ν * ‖ξ‖ ^ 2 * τ := by nlinarith [sq_nonneg ‖ξ‖]
  nlinarith [sq_nonneg (a * ‖ξ‖ - 1 / 2)]

/-- The kernel absorbs a weight increment `d` with `d² ≤ νσ`. -/
theorem gw_mul_kernel_le {ν σ d : ℝ} (hν : 0 < ν) (hσ : 0 < σ) (hd : 0 ≤ d)
    (hdσ : d ^ 2 ≤ ν * σ) (ξ : ES) :
    gw d ξ * (heatFactor ν σ ξ * ‖ξ‖) ≤ 4 * singWeight ν σ := by
  set r := ‖ξ‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg ξ
  set B : ℝ := ν * σ with hB
  have hB0 : 0 < B := mul_pos hν hσ
  have hsplit : gw d ξ * (heatFactor ν σ ξ * r) =
      Real.exp (d * r - B / 2 * r ^ 2) * (r * Real.exp (-(B / 2 * r ^ 2))) := by
    have e1 : Real.exp (d * r - B / 2 * r ^ 2) * (r * Real.exp (-(B / 2 * r ^ 2))) =
        r * Real.exp (d * r + -(ν * r ^ 2 * σ)) := by
      rw [mul_left_comm, ← Real.exp_add]; congr 2; rw [hB]; ring
    have e2 : gw d ξ * (heatFactor ν σ ξ * r) = r * Real.exp (d * r + -(ν * r ^ 2 * σ)) := by
      unfold gw heatFactor; rw [← hr, Real.exp_add]; ring
    rw [e2, e1]
  rw [hsplit]
  have h1 : Real.exp (d * r - B / 2 * r ^ 2) ≤ 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_half_le_two
    have : d ^ 2 * r ^ 2 ≤ B * r ^ 2 := by nlinarith [sq_nonneg r]
    nlinarith [sq_nonneg (d * r - 1)]
  have h2 : r * Real.exp (-(B / 2 * r ^ 2)) ≤ (Real.sqrt (B / 2))⁻¹ :=
    mul_exp_neg_sq_le (by positivity) hr0
  have h3 : (Real.sqrt (B / 2))⁻¹ ≤ 2 * singWeight ν σ := by
    rw [← sqrt_mul_inv_eq_singWeight hν hσ, ← hB, Real.sqrt_div hB0.le]
    have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
    have h22 : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [inv_div]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h22 (inv_nonneg.mpr hs.le)
  have hp1 : 0 ≤ r * Real.exp (-(B / 2 * r ^ 2)) := mul_nonneg hr0 (Real.exp_pos _).le
  calc Real.exp (d * r - B / 2 * r ^ 2) * (r * Real.exp (-(B / 2 * r ^ 2)))
      ≤ 2 * (2 * singWeight ν σ) := mul_le_mul h1 (h2.trans h3) hp1 (by norm_num)
    _ = 4 * singWeight ν σ := by ring

theorem sqrt_sub_sqrt_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    Real.sqrt x - Real.sqrt y ≤ Real.sqrt (x - y) := by
  have h : Real.sqrt x ≤ Real.sqrt y + Real.sqrt (x - y) := by
    rw [Real.sqrt_le_left]
    · have h1 := Real.sq_sqrt hy
      have h2 := Real.sq_sqrt (sub_nonneg.mpr hxy)
      nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg (x - y),
        mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg (x - y))]
    · positivity
  linarith

/-! ## Vector Gevrey norms and the invariant set -/

/-- The vector Gevrey functional at weight `e^{a‖ξ‖}`. -/
def gevV (a : ℝ) (v : V1) : ℝ≥0∞ := ∑ i : Fin 3, wm (gw a) (v i)

theorem lowerSemicontinuous_gevV (a : ℝ) : LowerSemicontinuous (gevV a) := by
  unfold gevV
  exact lowerSemicontinuous_sum fun i _ =>
    lsc_comp_continuous (lowerSemicontinuous_wm (gw a) (continuous_gw a) (gw_nonneg a))
      (continuous_apply i)

variable {ν T : ℝ}

/-- Paths with Gevrey radius `√(νt)` at time `t` and Gevrey norm at most `G`. -/
def gevSet (ν G : ℝ) : Set C(Icc (0 : ℝ) T, V1) :=
  {y | ∀ t : Icc (0 : ℝ) T, gevV (Real.sqrt (ν * t)) (y t) ≤ ENNReal.ofReal G}

theorem isClosed_gevSet (ν G : ℝ) : IsClosed (gevSet (T := T) ν G) := by
  have h : gevSet (T := T) ν G = ⋂ t : Icc (0 : ℝ) T,
      (fun y : C(Icc (0 : ℝ) T, V1) => gevV (Real.sqrt (ν * t)) (y t)) ⁻¹'
        Iic (ENNReal.ofReal G) := by
    ext y; simp [gevSet]
  rw [h]
  exact isClosed_iInter fun t =>
    (lsc_comp_continuous (lowerSemicontinuous_gevV _)
      (continuous_eval_const t)).isClosed_preimage _

/-- The heat part. -/
theorem gevV_heatOp_le (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (a₀ : V1) :
    gevV (Real.sqrt (ν * t)) (heatOp ν t a₀) ≤ ENNReal.ofReal (6 * ‖a₀‖) := by
  set a := Real.sqrt (ν * t)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 ≤ ν * max t 0 := by
    rw [Real.sq_sqrt (mul_nonneg hν.le ht), max_eq_left ht]
  have hcoord : ∀ i : Fin 3, wm (gw a) (heatOp ν t a₀ i) ≤ ENNReal.ofReal (2 * ‖a₀‖) := by
    intro i
    rw [heatOp_apply]
    have hb : ∀ᵐ ξ ∂(volume : Measure ES), gw a ξ * ‖heatLinf ν t ξ‖ ≤ 2 * gw 0 ξ := by
      filter_upwards [coeFn_heatLinf hν.le t] with ξ h
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
      have : gw 0 ξ = 1 := by simp [gw]
      rw [this, mul_one]
      exact gw_mul_heatFactor_le ha ha2 ξ
    refine (wm_mulL_le (gw a) (gw 0) _ (by norm_num) (gw_nonneg a) hb _).trans ?_
    rw [wm_gw_zero, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_le_pi_norm a₀ i])
  unfold gevV
  calc ∑ i : Fin 3, wm (gw a) (heatOp ν t a₀ i) ≤ ∑ _i : Fin 3, ENNReal.ofReal (2 * ‖a₀‖) :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = ENNReal.ofReal (6 * ‖a₀‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          show (6 : ℝ) * ‖a₀‖ = 3 * (2 * ‖a₀‖) by ring, ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- One coordinate of the Duhamel kernel, with weight increment `d² ≤ νσ`. -/
theorem wm_kernel_coord_le (hν : 0 < ν) {σ d b : ℝ} (hσ : 0 < σ) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hdσ : d ^ 2 ≤ ν * σ) (u : V1) (i : Fin 3) :
    wm (gw (d + b)) ((kernelOp ν σ (tensorConv u u)) i) ≤
      ENNReal.ofReal (4 * singWeight ν σ) * (gevV b u * gevV b u) := by
  have hs0 : 0 ≤ 4 * singWeight ν σ := mul_nonneg (by norm_num) (singWeight_nonneg ν σ hσ.le)
  have hker : ∀ j k : Fin 3, ∀ᵐ ξ ∂(volume : Measure ES),
      gw (d + b) ξ * ‖kernelLinf ν σ i j k ξ‖ ≤ 4 * singWeight ν σ * gw b ξ := fun j k => by
    filter_upwards [coeFn_kernelLinf hν hσ i j k] with ξ h
    rw [h]
    have hk : ‖kernelSymbol ν σ i j k ξ‖ ≤ heatFactor ν σ ξ * ‖ξ‖ := by
      unfold kernelSymbol
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_left (norm_lerayDerivSymbol_le i j k ξ)
        (heatFactor_nonneg _ _ _)
    have hsplit : gw (d + b) ξ = gw d ξ * gw b ξ := by
      unfold gw; rw [← Real.exp_add]; ring_nf
    calc gw (d + b) ξ * ‖kernelSymbol ν σ i j k ξ‖
        ≤ gw (d + b) ξ * (heatFactor ν σ ξ * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left hk (gw_nonneg _ _)
      _ = (gw d ξ * (heatFactor ν σ ξ * ‖ξ‖)) * gw b ξ := by rw [hsplit]; ring
      _ ≤ 4 * singWeight ν σ * gw b ξ :=
          mul_le_mul_of_nonneg_right (gw_mul_kernel_le hν hσ hd hdσ ξ) (gw_nonneg _ _)
  have hterm : ∀ j k : Fin 3, wm (gw (d + b)) (mulL (kernelLinf ν σ i j k) (conv (u j) (u k))) ≤
      ENNReal.ofReal (4 * singWeight ν σ) * (wm (gw b) (u j) * wm (gw b) (u k)) := by
    intro j k
    refine (wm_mulL_le _ _ _ hs0 (gw_nonneg _) (hker j k) _).trans ?_
    exact mul_le_mul' le_rfl
      (wm_conv_le (gw b) (continuous_gw b) (gw_nonneg b) (gw_sub hb) _ _)
  rw [kernelOp, tensorMulOp_apply]
  simp only [tensorConv_apply]
  refine (wm_sum_le _ (continuous_gw _) _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => (wm_sum_le _ (continuous_gw _) _ _).trans
    (Finset.sum_le_sum fun k _ => hterm j k)).trans (le_of_eq ?_)
  unfold gevV
  simp only [Fin.sum_univ_three]
  ring

/-- The majorant of one Duhamel coordinate. -/
def gevMajorant (ν G t σ : ℝ) : ℝ := (Ioc 0 t).indicator (fun σ => 4 * singWeight ν σ * G ^ 2) σ

theorem gevMajorant_nonneg (ν G t σ : ℝ) : 0 ≤ gevMajorant ν G t σ := by
  unfold gevMajorant
  refine Set.indicator_nonneg (fun σ hσ => ?_) σ
  have := singWeight_nonneg ν σ hσ.1.le
  positivity

theorem integral_gevMajorant (ν G : ℝ) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ σ in Ioc 0 T, gevMajorant ν G t σ = 8 * (Real.sqrt ν)⁻¹ * Real.sqrt t * G ^ 2 := by
  unfold gevMajorant
  rw [setIntegral_indicator measurableSet_Ioc, Ioc_inter_Ioc, max_self, min_eq_right htT,
    integral_mul_const, integral_const_mul, integral_singWeight ν ht]
  ring

theorem integrableOn_gevMajorant (ν G : ℝ) (hT0 : 0 ≤ T) (t : ℝ) :
    IntegrableOn (gevMajorant ν G t) (Ioc 0 T) := by
  have hbase : IntegrableOn (fun σ => 4 * singWeight ν σ * G ^ 2) (Ioc 0 T) :=
    ((integrableOn_singWeight ν hT0).const_mul 4).mul_const _
  refine hbase.mono' ?_ ?_
  · unfold gevMajorant singWeight
    refine (Measurable.indicator ?_ measurableSet_Ioc).aestronglyMeasurable
    exact (measurable_const.mul (measurable_const.mul (measurable_id.pow_const _))).mul
      measurable_const
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
    rw [Real.norm_eq_abs, abs_of_nonneg (gevMajorant_nonneg ν G t σ)]
    unfold gevMajorant
    by_cases hs : σ ∈ Ioc 0 t
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      have := singWeight_nonneg ν σ hσ.1.le
      positivity

/-- **Gevrey bound for one coordinate of the Duhamel term.** -/
theorem gev_duhamel_coord_le (hν : 0 < ν) (hT0 : 0 ≤ T) (y : C(Icc (0 : ℝ) T, V1))
    {G : ℝ} (hG : 0 ≤ G) (hy : y ∈ gevSet ν G) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) :
    wm (gw (Real.sqrt (ν * t))) ((duhamel ν hT0 y y t) i) ≤
      ENNReal.ofReal (∫ σ in Ioc 0 T, gevMajorant ν G t σ) := by
  have hint := integrable_duhIntegrand hν hT0 y y t
  have hcoord : (duhamel ν hT0 y y t) i = ∫ σ in Ioc 0 T, duhIntegrand ν hT0 y y t σ i := by
    unfold duhamel
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => L1C) i).integral_comp_comm
      hint).symm
  rw [hcoord]
  refine wm_integral_le _ (continuous_gw _) (gw_nonneg _) _
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => L1C) i).integrable_comp hint)
    _ (integrableOn_gevMajorant ν G hT0 t) (gevMajorant_nonneg ν G t) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with σ hσ
  by_cases hle : σ ≤ t
  · have hdi : duhIntegrand ν hT0 y y t σ =
        kernelOp ν σ (tensorConv (extend hT0 y (t - σ)) (extend hT0 y (t - σ))) := by
      unfold duhIntegrand
      exact Set.indicator_of_mem (show σ ∈ Iic t from hle) _
    have hmem : t - σ ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hσ.1, ht.2]⟩
    have hext : extend hT0 y (t - σ) = y ⟨t - σ, hmem⟩ := by
      unfold WienerLocalMild.extend; rw [projIcc_of_mem hT0 hmem]
    set b := Real.sqrt (ν * (t - σ)) with hbdef
    set d := Real.sqrt (ν * t) - b with hddef
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hbt : b ≤ Real.sqrt (ν * t) := Real.sqrt_le_sqrt (by nlinarith [hσ.1])
    have hd0 : 0 ≤ d := by rw [hddef]; linarith
    have hdσ : d ^ 2 ≤ ν * σ := by
      have h1 := sqrt_sub_sqrt_le (x := ν * t) (y := ν * (t - σ))
        (mul_nonneg hν.le (by linarith)) (by nlinarith [hσ.1])
      have h2 : ν * t - ν * (t - σ) = ν * σ := by ring
      rw [h2] at h1
      calc d ^ 2 ≤ Real.sqrt (ν * σ) ^ 2 := pow_le_pow_left₀ hd0 h1 2
        _ = ν * σ := Real.sq_sqrt (mul_nonneg hν.le hσ.1.le)
    have hgy : gevV b (extend hT0 y (t - σ)) ≤ ENNReal.ofReal G := by
      rw [hext]; exact hy ⟨t - σ, hmem⟩
    rw [hdi, show Real.sqrt (ν * t) = d + b by rw [hddef]; ring]
    refine (wm_kernel_coord_le hν hσ.1 hd0 hb0 hdσ _ i).trans ?_
    unfold gevMajorant
    rw [Set.indicator_of_mem (show σ ∈ Ioc 0 t from ⟨hσ.1, hle⟩)]
    have hs0 : 0 ≤ 4 * singWeight ν σ := mul_nonneg (by norm_num) (singWeight_nonneg ν σ hσ.1.le)
    rw [ENNReal.ofReal_mul hs0, sq, ENNReal.ofReal_mul hG]
    gcongr
  · have h0 : duhIntegrand ν hT0 y y t σ = 0 := by
      unfold duhIntegrand
      exact Set.indicator_of_notMem (show σ ∉ Iic t from hle) _
    rw [h0, map_zero, wm_zero]
    exact zero_le

/-- **The Gevrey set is invariant under the Picard map.** -/
theorem mapsTo_gevSet (hν : 0 < ν) (hT : 0 < T) (a₀ : V1)
    (hsmall : 1000 * (Real.sqrt T * ‖a₀‖) ≤ Real.sqrt ν) (y : C(Icc (0 : ℝ) T, V1))
    (hy : y ∈ gevSet ν (12 * ‖a₀‖)) :
    heatPath hν a₀ + duhamelPath hν hT.le y y ∈ gevSet ν (12 * ‖a₀‖) := by
  intro t
  have ht : (t : ℝ) ∈ Icc (0 : ℝ) T := t.2
  set G : ℝ := 12 * ‖a₀‖ with hGdef
  have hG0 : 0 ≤ G := by positivity
  have hval : (heatPath hν a₀ + duhamelPath hν hT.le y y : C(Icc (0 : ℝ) T, V1)) t =
      heatOp ν t a₀ + duhamel ν hT.le y y t := rfl
  rw [hval]
  set I : ℝ := ∫ σ in Ioc 0 T, gevMajorant ν G t σ with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioc fun σ _ => gevMajorant_nonneg ν G t σ
  have hD : gevV (Real.sqrt (ν * t)) (duhamel ν hT.le y y t) ≤ 3 * ENNReal.ofReal I := by
    unfold gevV
    simp only [Fin.sum_univ_three]
    have hc := fun i => gev_duhamel_coord_le hν hT.le y hG0 hy ht i
    calc wm (gw (Real.sqrt (ν * t))) (duhamel ν hT.le y y t 0) +
          wm (gw (Real.sqrt (ν * t))) (duhamel ν hT.le y y t 1) +
          wm (gw (Real.sqrt (ν * t))) (duhamel ν hT.le y y t 2)
        ≤ ENNReal.ofReal I + ENNReal.ofReal I + ENNReal.ofReal I := by
          gcongr
          · exact hc 0
          · exact hc 1
          · exact hc 2
      _ = 3 * ENNReal.ofReal I := by ring
  have hIeq : I = 8 * (Real.sqrt ν)⁻¹ * Real.sqrt t * G ^ 2 :=
    integral_gevMajorant ν G ht.1 ht.2
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hst : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
  have h3I : 3 * I ≤ 6 * ‖a₀‖ := by
    rw [hIeq, hGdef]
    have hkey : 3 * (8 * (Real.sqrt ν)⁻¹ * Real.sqrt t * (12 * ‖a₀‖) ^ 2) =
        (3456 * (Real.sqrt t * ‖a₀‖) / Real.sqrt ν) * ‖a₀‖ := by
      field_simp; ring
    rw [hkey]
    have hfrac : 3456 * (Real.sqrt t * ‖a₀‖) / Real.sqrt ν ≤ 6 := by
      rw [div_le_iff₀ hsν]
      have : Real.sqrt t * ‖a₀‖ ≤ Real.sqrt T * ‖a₀‖ :=
        mul_le_mul_of_nonneg_right hst (norm_nonneg _)
      nlinarith [norm_nonneg a₀, Real.sqrt_nonneg t]
    have hn := norm_nonneg a₀
    nlinarith
  calc gevV (Real.sqrt (ν * t)) (heatOp ν t a₀ + duhamel ν hT.le y y t)
      ≤ gevV (Real.sqrt (ν * t)) (heatOp ν t a₀) +
          gevV (Real.sqrt (ν * t)) (duhamel ν hT.le y y t) := by
        unfold gevV
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => wm_add_le _ (continuous_gw _) _ _
    _ ≤ ENNReal.ofReal (6 * ‖a₀‖) + 3 * ENNReal.ofReal I :=
        add_le_add (gevV_heatOp_le hν ht.1 a₀) hD
    _ = ENNReal.ofReal (6 * ‖a₀‖ + 3 * I) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          show ENNReal.ofReal (3 * I) = 3 * ENNReal.ofReal I by
            rw [ENNReal.ofReal_mul (by norm_num)]; norm_num]
    _ ≤ ENNReal.ofReal G := ENNReal.ofReal_le_ofReal (by rw [hGdef]; linarith)

/-! ## The Gevrey fixed point -/

theorem sqrt_small_of {T : ℝ} {c : ℝ} (hT : 0 < T) (hc : 0 < c) (a : ℝ) (ha : 0 ≤ a)
    {ν : ℝ} (h : c ^ 2 * T * a ^ 2 ≤ ν) : c * (Real.sqrt T * a) ≤ Real.sqrt ν := by
  have h1 := Real.sqrt_le_sqrt h
  rwa [show c ^ 2 * T * a ^ 2 = (c * (Real.sqrt T * a)) ^ 2 by
    rw [mul_pow, mul_pow, Real.sq_sqrt hT.le]; ring,
    Real.sqrt_sq (by positivity)] at h1

/-- Uniqueness of a fixed point of `x = y + B(x,x)` in any ball of radius `R` with
`2CR < 1`. -/
theorem picard_unique_R {X : Type*} [NormedAddCommGroup X] {B : X → X → X} {C : ℝ}
    (hC : 0 < C) (hB : ∀ a b : X, ‖B a b‖ ≤ C * (‖a‖ * ‖b‖))
    (hdiff : ∀ a b : X, B a a - B b b = B (a - b) a + B b (a - b))
    {y : X} {R : ℝ} (hR : 2 * C * R < 1) {x z : X} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R)
    (hxe : x = y + B x x) (hze : z = y + B z z) : x = z := by
  have hd : x - z = B (x - z) x + B z (x - z) := by
    rw [← hdiff]
    conv_lhs => rw [hxe, hze]
    abel
  have hab : (0 : ℝ) ≤ ‖x - z‖ := norm_nonneg _
  have hn : ‖x - z‖ ≤ (2 * C * R) * ‖x - z‖ := by
    have h := (norm_add_le (B (x - z) x) (B z (x - z))).trans (add_le_add (hB _ _) (hB _ _))
    rw [← hd] at h
    nlinarith [mul_le_mul_of_nonneg_left hx (mul_nonneg hC.le hab),
      mul_le_mul_of_nonneg_left hz (mul_nonneg hC.le hab)]
  have h0 : ‖x - z‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖x - z‖ := lt_of_le_of_ne hab (Ne.symm hne)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- **Instant Gevrey smoothing of the Wiener mild solution.**  If
`10⁶ T ‖a₀‖² ≤ ν`, every fixed point of the Picard map in the ball of radius
`2‖a₀‖` (in particular the mild solution) satisfies
`∑ᵢ ∫ e^{√(νt)‖ξ‖} |xᵢ(t, ξ)| dξ ≤ 12‖a₀‖` for all `t ∈ [0, T]`. -/
theorem fixedPoint_mem_gevSet (hν : 0 < ν) (hT : 0 < T) (a₀ : V1)
    (hsmall : 10 ^ 6 * T * ‖a₀‖ ^ 2 ≤ ν) (x : C(Icc (0 : ℝ) T, V1))
    (hxle : ‖x‖ ≤ 2 * ‖a₀‖) (hxeq : x = heatPath hν a₀ + duhamelPath hν hT.le x x) :
    x ∈ gevSet ν (12 * ‖a₀‖) := by
  set C : ℝ := 18 * (Real.sqrt ν)⁻¹ * Real.sqrt T with hC
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hC0 : 0 < C := by rw [hC]; positivity
  set y : C(Icc (0 : ℝ) T, V1) := heatPath hν a₀ with hy
  have hyle : ‖y‖ ≤ ‖a₀‖ := norm_heatPath_le hν a₀
  have hroot : 1000 * (Real.sqrt T * ‖a₀‖) ≤ Real.sqrt ν :=
    sqrt_small_of hT (by norm_num) ‖a₀‖ (norm_nonneg _) (by norm_num at hsmall ⊢; linarith)
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
  have hB := norm_duhamelPath_le hν hT.le
  have hdiff := duhamelPath_diff hν hT.le
  have hyS : y ∈ gevSet ν (12 * ‖a₀‖) := by
    intro t
    exact (gevV_heatOp_le hν t.2.1 a₀).trans
      (ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg a₀]))
  obtain ⟨xg, hxgS, hxgle, hxgeq⟩ := picard_small_data_on hC0 hB hdiff y hsmallC
    (gevSet ν (12 * ‖a₀‖)) (isClosed_gevSet ν _) hyS
    (fun z hz _ => mapsTo_gevSet hν hT a₀ hroot z hz)
  have hxx : xg = x := picard_unique_R hC0 hB hdiff (R := 2 * ‖a₀‖)
    (by
      have h1 : 2 * C * (2 * ‖a₀‖) ≤ 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν := by
        rw [hC, div_eq_mul_inv]; nlinarith [norm_nonneg a₀, inv_pos.mpr hsν]
      have h2 : 72 * (Real.sqrt T * ‖a₀‖) / Real.sqrt ν < 1 := by
        rw [div_lt_one hsν]
        have : 0 ≤ Real.sqrt T * ‖a₀‖ := by positivity
        nlinarith
      linarith)
    (hxgle.trans (by linarith)) hxle hxgeq hxeq
  rw [← hxx]
  exact hxgS

/-! ## Moments at positive times -/

theorem pow_le_factorial_mul_gw (n : ℕ) {a : ℝ} (ha : 0 < a) (ξ : ES) :
    ‖ξ‖ ^ n ≤ ((Nat.factorial n : ℝ) / a ^ n) * gw a ξ := by
  have h := Real.pow_div_factorial_le_exp (x := a * ‖ξ‖) (mul_nonneg ha.le (norm_nonneg ξ)) n
  have hf : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have han : 0 < a ^ n := pow_pos ha n
  unfold gw
  rw [div_le_iff₀ hf, mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ han]
  nlinarith

theorem mom_le_wm (n : ℕ) {a : ℝ} (ha : 0 < a) (f : L1C) :
    mom n f ≤ ENNReal.ofReal ((Nat.factorial n : ℝ) / a ^ n) * wm (gw a) f := by
  unfold mom wm
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ξ => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact pow_le_factorial_mul_gw n ha ξ

/-- **Every Fourier moment at a positive time.** -/
theorem momV_le_of_gevSet {G : ℝ} {y : C(Icc (0 : ℝ) T, V1)} (hy : y ∈ gevSet ν G)
    (hν : 0 < ν) (n : ℕ) (t : Icc (0 : ℝ) T) (ht : 0 < (t : ℝ)) :
    momV n (y t) ≤ ENNReal.ofReal ((Nat.factorial n : ℝ) / Real.sqrt (ν * t) ^ n) * ENNReal.ofReal G := by
  have ha : 0 < Real.sqrt (ν * t) := Real.sqrt_pos.mpr (mul_pos hν ht)
  unfold momV
  calc ∑ i : Fin 3, mom n (y t i)
      ≤ ∑ i : Fin 3, ENNReal.ofReal ((Nat.factorial n : ℝ) / Real.sqrt (ν * t) ^ n) *
          wm (gw (Real.sqrt (ν * t))) (y t i) :=
        Finset.sum_le_sum fun i _ => mom_le_wm n ha _
    _ = ENNReal.ofReal ((Nat.factorial n : ℝ) / Real.sqrt (ν * t) ^ n) * gevV (Real.sqrt (ν * t)) (y t) := by
        rw [gevV, Finset.mul_sum]
    _ ≤ _ := by gcongr; exact hy t

end Navier.Analysis.WienerGevrey

set_option pp.fullNames true in
#check @Navier.Analysis.WienerGevrey.fixedPoint_mem_gevSet
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerGevrey.fixedPoint_mem_gevSet
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerGevrey.momV_le_of_gevSet
