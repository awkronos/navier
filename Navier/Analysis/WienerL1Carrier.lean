import Navier.Analysis.ContinuousLeiLinSpace
import Mathlib.MeasureTheory.Function.Holder

/-!
# The Fourier-`L¹` (Wiener) carrier on `ℝ³`: convolution and multipliers

Scalar building blocks of the subcritical short-time contraction for
large Schwartz data on the whole-space Fourier carrier `ES = ℝ³`.

* `conv : L1C →L[ℂ] L1C →L[ℂ] L1C` is the Lebesgue convolution on the Banach
  space `L¹(ℝ³; ℂ)`, with operator norm at most one (`norm_convFun_le`),
  and its representative is the literal convolution of representatives
  (`coeFn_convFun`) — the same `⋆[ContinuousLinearMap.mul ℂ ℂ, volume]` used by
  `ContinuousLeiLinSpace.rawNavierConvection`.
* `mulL : L∞ →L[ℂ] L1C →L[ℂ] L1C` is pointwise multiplication (Hölder), and
  `linfOfBound` packages a bounded measurable symbol with its sup bound.
* `lerayDerivSymbol i j k ξ` is the `(i; j, k)` coefficient of the Fourier
  Navier symbol `W ↦ continuousLeray ξ (I • ∑ⱼ ξⱼ W j ·)`; it is bounded by
  `‖ξ‖` (`norm_lerayDerivSymbol_le`).  Multiplied by the heat factor
  `exp(-ν‖ξ‖²τ)` it is bounded by `(ντ)^{-1/2}` (`norm_kernelSymbol_le`) and is
  Lipschitz in `τ ≥ τ₀ > 0` uniformly in `ξ` (`norm_kernelSymbol_sub_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Convolution ENNReal NNReal

namespace Navier.Analysis.WienerL1Carrier

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.FourierMajorant

/-- Scalar Wiener carrier `L¹(ℝ³; ℂ)` on the Fourier side. -/
abbrev L1C := Lp ℂ 1 (volume : Measure ES)

/-- Bounded measurable Fourier multipliers. -/
abbrev LinfC := Lp ℂ ∞ (volume : Measure ES)

/-! ## Convolution on `L¹` -/

theorem integral_norm_conv_le (f g : ES → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x‖ ≤
      (∫ x, ‖f x‖) * ∫ x, ‖g x‖ := by
  have hnf : Integrable (fun x => ‖f x‖) := hf.norm
  have hng : Integrable (fun x => ‖g x‖) := hg.norm
  calc ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x‖
      ≤ ∫ x, convolution (fun y => ‖f y‖) (fun y => ‖g y‖) x :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hnf.integrable_convolution _ hng)
          (Eventually.of_forall (norm_complex_convolution_le f g))
    _ = (∫ x, ‖f x‖) * ∫ x, ‖g x‖ := by
        simpa [normX0] using normX0_convolution_eq _ _ hnf hng

/-- Convolution of two `L¹` classes, through representatives. -/
def convFun (f g : L1C) : L1C :=
  ((L1.integrable_coeFn f).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (L1.integrable_coeFn g)).toL1 _

theorem coeFn_convFun (f g : L1C) :
    convFun f g =ᵐ[volume] ((⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (⇑g)) :=
  Integrable.coeFn_toL1 _

theorem norm_convFun_le (f g : L1C) : ‖convFun f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm f, L1.norm_eq_integral_norm g,
    integral_congr_ae (by filter_upwards [coeFn_convFun f g] with x hx; rw [hx])]
  exact integral_norm_conv_le _ _ (L1.integrable_coeFn f) (L1.integrable_coeFn g)

theorem convFun_add_left (f f' g : L1C) :
    convFun (f + f') g = convFun f g + convFun f' g := by
  apply Lp.ext
  have hcongr : (⇑(f + f')) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑g =
      (⇑f + ⇑f') ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑g :=
    convolution_congr _ (Lp.coeFn_add f f') (EventuallyEq.refl _ _)
  filter_upwards [coeFn_convFun (f + f') g, Lp.coeFn_add (convFun f g) (convFun f' g),
    coeFn_convFun f g, coeFn_convFun f' g,
    Integrable.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ)
      (L1.integrable_coeFn f) (L1.integrable_coeFn g),
    Integrable.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ)
      (L1.integrable_coeFn f') (L1.integrable_coeFn g)]
    with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.add_apply, h3, h4, hcongr, h5.add_distrib h6]

theorem convFun_add_right (f g g' : L1C) :
    convFun f (g + g') = convFun f g + convFun f g' := by
  apply Lp.ext
  have hcongr : (⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑(g + g') =
      (⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (⇑g + ⇑g') :=
    convolution_congr _ (EventuallyEq.refl _ _) (Lp.coeFn_add g g')
  filter_upwards [coeFn_convFun f (g + g'), Lp.coeFn_add (convFun f g) (convFun f g'),
    coeFn_convFun f g, coeFn_convFun f g',
    Integrable.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ)
      (L1.integrable_coeFn f) (L1.integrable_coeFn g),
    Integrable.ae_convolution_exists (L := ContinuousLinearMap.mul ℂ ℂ)
      (L1.integrable_coeFn f) (L1.integrable_coeFn g')]
    with x h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.add_apply, h3, h4, hcongr, h5.distrib_add h6]

theorem convFun_smul_left (c : ℂ) (f g : L1C) :
    convFun (c • f) g = c • convFun f g := by
  apply Lp.ext
  have hcongr : (⇑(c • f)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑g =
      (c • ⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑g :=
    convolution_congr _ (Lp.coeFn_smul c f) (EventuallyEq.refl _ _)
  filter_upwards [coeFn_convFun (c • f) g, Lp.coeFn_smul c (convFun f g),
    coeFn_convFun f g] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, hcongr, smul_convolution]
  rfl

theorem convFun_smul_right (c : ℂ) (f g : L1C) :
    convFun f (c • g) = c • convFun f g := by
  apply Lp.ext
  have hcongr : (⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑(c • g) =
      (⇑f) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (c • ⇑g) :=
    convolution_congr _ (EventuallyEq.refl _ _) (Lp.coeFn_smul c g)
  filter_upwards [coeFn_convFun f (c • g), Lp.coeFn_smul c (convFun f g),
    coeFn_convFun f g] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, hcongr, convolution_smul]
  rfl

/-- **Convolution on `L¹(ℝ³; ℂ)` as a bounded bilinear map of norm `≤ 1`.** -/
def conv : L1C →L[ℂ] L1C →L[ℂ] L1C :=
  (LinearMap.mk₂ ℂ convFun convFun_add_left convFun_smul_left convFun_add_right
    convFun_smul_right).mkContinuous₂ 1 (fun f g => by
      simpa [one_mul] using norm_convFun_le f g)

theorem conv_apply (f g : L1C) : conv f g = convFun f g := rfl

theorem norm_conv_apply_le (f g : L1C) : ‖conv f g‖ ≤ ‖f‖ * ‖g‖ :=
  norm_convFun_le f g

/-! ## Bounded multipliers -/

/-- Pointwise multiplication `L∞ × L¹ → L¹` (Hölder). -/
def mulL : LinfC →L[ℂ] L1C →L[ℂ] L1C :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 1 1

theorem coeFn_mulL (m : LinfC) (f : L1C) :
    mulL m f =ᵐ[volume] fun ξ => m ξ * f ξ :=
  (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 1) m f

theorem norm_mulL_apply_le (m : LinfC) (f : L1C) : ‖mulL m f‖ ≤ ‖m‖ * ‖f‖ := by
  calc ‖mulL m f‖ ≤ ‖mulL m‖ * ‖f‖ := (mulL m).le_opNorm f
    _ ≤ (‖mulL‖ * ‖m‖) * ‖f‖ := by gcongr; exact mulL.le_opNorm m
    _ ≤ (1 * ‖m‖) * ‖f‖ := by
        gcongr
        exact (ContinuousLinearMap.norm_holderL_le _).trans
          (ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
    _ = ‖m‖ * ‖f‖ := by rw [one_mul]

theorem norm_mulL_le (m : LinfC) : ‖mulL m‖ ≤ ‖m‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_mulL_apply_le m)

/-- An `L∞` class with an a.e. bound `M ≥ 0` has norm at most `M`. -/
theorem linf_norm_le_of_ae_bound (f : LinfC) {M : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ᵐ ξ ∂(volume : Measure ES), ‖f ξ‖ ≤ M) : ‖f‖ ≤ M := by
  rw [Lp.norm_def, eLpNorm_exponent_top]
  exact ENNReal.toReal_le_of_le_ofReal hM0 (eLpNormEssSup_le_of_ae_bound h)

/-- A bounded a.e.-strongly-measurable symbol as an `L∞` class. -/
def linfOfBound (m : ES → ℂ) (hm : AEStronglyMeasurable m (volume : Measure ES))
    (M : ℝ) (hM : ∀ ξ, ‖m ξ‖ ≤ M) : LinfC :=
  (memLp_top_of_bound hm M (Eventually.of_forall hM)).toLp m

theorem coeFn_linfOfBound (m : ES → ℂ) (hm : AEStronglyMeasurable m (volume : Measure ES))
    (M : ℝ) (hM : ∀ ξ, ‖m ξ‖ ≤ M) :
    linfOfBound m hm M hM =ᵐ[volume] m :=
  MemLp.coeFn_toLp _

/-! ## The Navier symbol coefficients -/

/-- The `(i; j, k)` coefficient of the Fourier Navier symbol
`W ↦ continuousLeray ξ (I • ∑ⱼ ξⱼ W j ·)`: the Leray-projected derivative
applied to the elementary tensor with advecting coordinate `j` and
advected coordinate `k`. -/
def lerayDerivSymbol (i j k : Fin 3) (ξ : ES) : ℂ :=
  continuousLeray ξ (Pi.single k (Complex.I * ((ξ j : ℝ) : ℂ))) i

theorem norm_coord_le_complexEuclideanNorm (z : ContinuousLeiLinSpace.ComplexSpace) (i : Fin 3) :
    ‖z i‖ ≤ complexEuclideanNorm z := by
  unfold complexEuclideanNorm
  exact PiLp.norm_apply_le (complexEuclideanPoint z) i

theorem complexEuclideanNorm_single (k : Fin 3) (c : ℂ) :
    complexEuclideanNorm (Pi.single k c) = ‖c‖ := by
  unfold complexEuclideanNorm complexEuclideanPoint
  exact PiLp.norm_single 2 (fun _ : Fin 3 => ℂ) k c

theorem norm_lerayDerivSymbol_le (i j k : Fin 3) (ξ : ES) :
    ‖lerayDerivSymbol i j k ξ‖ ≤ ‖ξ‖ := by
  unfold lerayDerivSymbol
  refine (norm_coord_le_complexEuclideanNorm _ i).trans ?_
  refine (continuousLeray_norm_le ξ _).trans ?_
  rw [complexEuclideanNorm_single, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  exact (Real.norm_eq_abs (ξ j) ▸ PiLp.norm_apply_le ξ j)

theorem lerayDerivSymbol_formula (i j k : Fin 3) (ξ : ES) :
    lerayDerivSymbol i j k ξ =
      (Pi.single k (Complex.I * ((ξ j : ℝ) : ℂ)) : ContinuousLeiLinSpace.ComplexSpace) i -
        ((∑ l, ((spaceProj ξ) l : ℂ) *
            (Pi.single k (Complex.I * ((ξ j : ℝ) : ℂ)) : ContinuousLeiLinSpace.ComplexSpace) l) /
          (((spaceProj ξ) ⬝ᵥ (spaceProj ξ) : ℝ) : ℂ)) * ((spaceProj ξ) i : ℂ) := by
  unfold lerayDerivSymbol continuousLeray
  exact complexLeray_formula _ _ i

theorem measurable_lerayDerivSymbol (i j k : Fin 3) :
    Measurable (lerayDerivSymbol i j k) := by
  have hq : Continuous (fun ξ : ES => spaceProj ξ) := spaceProj.continuous
  have hc : ∀ l : Fin 3, Measurable (fun ξ : ES => ((spaceProj ξ) l : ℂ)) := fun l =>
    (Complex.continuous_ofReal.comp ((continuous_apply l).comp hq)).measurable
  have hs : ∀ l : Fin 3, Measurable (fun ξ : ES =>
      (Pi.single k (Complex.I * ((ξ j : ℝ) : ℂ)) : ContinuousLeiLinSpace.ComplexSpace) l) := by
    intro l
    by_cases hl : l = k
    · subst hl
      simp only [Pi.single_eq_same]
      exact (measurable_const.mul
        (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)).measurable)
    · simp only [Pi.single_eq_of_ne hl]
      exact measurable_const
  have hden : Measurable (fun ξ : ES =>
      (((spaceProj ξ) ⬝ᵥ (spaceProj ξ) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (Continuous.dotProduct hq hq)).measurable
  have hform : lerayDerivSymbol i j k = fun ξ =>
      (Pi.single k (Complex.I * ((ξ j : ℝ) : ℂ)) : ContinuousLeiLinSpace.ComplexSpace) i -
        ((∑ l, ((spaceProj ξ) l : ℂ) *
            (Pi.single k (Complex.I * ((ξ j : ℝ) : ℂ)) : ContinuousLeiLinSpace.ComplexSpace) l) /
          (((spaceProj ξ) ⬝ᵥ (spaceProj ξ) : ℝ) : ℂ)) * ((spaceProj ξ) i : ℂ) := by
    funext ξ
    exact lerayDerivSymbol_formula i j k ξ
  rw [hform]
  exact (hs i).sub (((Finset.measurable_sum _ fun l _ => (hc l).mul (hs l)).div hden).mul
    (hc i))

/-! ## Heat-weighted symbols -/

/-- The heat factor `exp(-ν‖ξ‖²τ)`. -/
def heatFactor (ν τ : ℝ) (ξ : ES) : ℝ := Real.exp (-(ν * ‖ξ‖ ^ 2 * τ))

/-- The Duhamel kernel coefficient `exp(-ν‖ξ‖²τ) · lerayDerivSymbol i j k ξ`. -/
def kernelSymbol (ν τ : ℝ) (i j k : Fin 3) (ξ : ES) : ℂ :=
  (heatFactor ν τ ξ : ℂ) * lerayDerivSymbol i j k ξ

theorem measurable_heatFactor (ν τ : ℝ) : Measurable (heatFactor ν τ) :=
  (Real.continuous_exp.comp ((continuous_const.mul
    (continuous_norm.pow 2)).mul continuous_const).neg).measurable

theorem measurable_kernelSymbol (ν τ : ℝ) (i j k : Fin 3) :
    Measurable (kernelSymbol ν τ i j k) :=
  (Complex.measurable_ofReal.comp (measurable_heatFactor ν τ)).mul
    (measurable_lerayDerivSymbol i j k)

theorem heatFactor_nonneg (ν τ : ℝ) (ξ : ES) : 0 ≤ heatFactor ν τ ξ :=
  (Real.exp_pos _).le

theorem heatFactor_le_one {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (ξ : ES) :
    heatFactor ν τ ξ ≤ 1 := by
  unfold heatFactor
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ν * ‖ξ‖ ^ 2 * τ := by positivity
  linarith

/-- `r·exp(-a r²) ≤ a^{-1/2}`, via `x ≤ 1 + x² ≤ exp(x²)` at `x = √a r`. -/
theorem mul_exp_neg_sq_le {a r : ℝ} (ha : 0 < a) (_hr : 0 ≤ r) :
    r * Real.exp (-(a * r ^ 2)) ≤ (Real.sqrt a)⁻¹ := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set x := Real.sqrt a * r with hx
  have hx2 : x ^ 2 = a * r ^ 2 := by
    rw [hx, mul_pow, Real.sq_sqrt ha.le]
  have hxle : x ≤ Real.exp (x ^ 2) := by
    have h1 : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have h2 : 1 + x ^ 2 ≤ Real.exp (x ^ 2) := by
      have := Real.add_one_le_exp (x ^ 2)
      linarith
    linarith
  have hexp : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  have key : x * Real.exp (-(x ^ 2)) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hexp]
    exact hxle
  have heq : r * Real.exp (-(a * r ^ 2)) = (x * Real.exp (-(x ^ 2))) * (Real.sqrt a)⁻¹ := by
    rw [hx2, hx]
    field_simp
  rw [heq]
  calc (x * Real.exp (-(x ^ 2))) * (Real.sqrt a)⁻¹ ≤ 1 * (Real.sqrt a)⁻¹ :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = (Real.sqrt a)⁻¹ := one_mul _

theorem norm_kernelSymbol_le {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (i j k : Fin 3) (ξ : ES) :
    ‖kernelSymbol ν τ i j k ξ‖ ≤ (Real.sqrt (ν * τ))⁻¹ := by
  unfold kernelSymbol
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
  calc heatFactor ν τ ξ * ‖lerayDerivSymbol i j k ξ‖ ≤ heatFactor ν τ ξ * ‖ξ‖ :=
        mul_le_mul_of_nonneg_left (norm_lerayDerivSymbol_le i j k ξ) (heatFactor_nonneg _ _ _)
    _ = ‖ξ‖ * Real.exp (-((ν * τ) * ‖ξ‖ ^ 2)) := by
        unfold heatFactor; rw [mul_comm]; congr 2; ring
    _ ≤ (Real.sqrt (ν * τ))⁻¹ := mul_exp_neg_sq_le (mul_pos hν hτ) (norm_nonneg ξ)

/-- `|e^{-aτ} - e^{-aτ'}| ≤ a|τ-τ'| e^{-aτ₀}` for `a ≥ 0`, `τ, τ' ≥ τ₀`. -/
theorem abs_exp_sub_exp_le {a τ τ' τ₀ : ℝ} (ha : 0 ≤ a) (hτ : τ₀ ≤ τ) (hτ' : τ₀ ≤ τ') :
    |Real.exp (-(a * τ)) - Real.exp (-(a * τ'))| ≤ a * |τ - τ'| * Real.exp (-(a * τ₀)) := by
  have key : ∀ s s' : ℝ, τ₀ ≤ s → s ≤ s' →
      |Real.exp (-(a * s)) - Real.exp (-(a * s'))| ≤ a * |s - s'| * Real.exp (-(a * τ₀)) := by
    intro s s' hs hss'
    have hmono : Real.exp (-(a * s')) ≤ Real.exp (-(a * s)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hss')]
    have hsplit : Real.exp (-(a * s')) = Real.exp (-(a * s)) * Real.exp (-(a * (s' - s))) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : 1 - a * (s' - s) ≤ Real.exp (-(a * (s' - s))) := by
      have := Real.add_one_le_exp (-(a * (s' - s))); linarith
    have h2 : Real.exp (-(a * s)) ≤ Real.exp (-(a * τ₀)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hpos := Real.exp_pos (-(a * s))
    have hdiff : Real.exp (-(a * s)) - Real.exp (-(a * s')) ≤
        Real.exp (-(a * s)) * (a * (s' - s)) := by
      rw [hsplit]; nlinarith
    calc Real.exp (-(a * s)) - Real.exp (-(a * s')) ≤ Real.exp (-(a * s)) * (a * (s' - s)) := hdiff
      _ ≤ Real.exp (-(a * τ₀)) * (a * (s' - s)) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg ha (by linarith))
      _ = a * -(s - s') * Real.exp (-(a * τ₀)) := by ring
  rcases le_total τ τ' with h | h
  · exact key τ τ' hτ h
  · rw [abs_sub_comm, abs_sub_comm τ τ']
    exact key τ' τ hτ' h

/-- `r²·e^{-b r²} ≤ b⁻¹` for `b > 0`. -/
theorem sq_mul_exp_neg_le {b r : ℝ} (hb : 0 < b) :
    r ^ 2 * Real.exp (-(b * r ^ 2)) ≤ b⁻¹ := by
  have hx : b * r ^ 2 ≤ Real.exp (b * r ^ 2) := by
    have := Real.add_one_le_exp (b * r ^ 2); linarith
  have hexp := Real.exp_pos (b * r ^ 2)
  have key : (b * r ^ 2) * Real.exp (-(b * r ^ 2)) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hexp]; exact hx
  have heq : r ^ 2 * Real.exp (-(b * r ^ 2)) = (b * r ^ 2) * Real.exp (-(b * r ^ 2)) * b⁻¹ := by
    field_simp
  rw [heq]
  calc (b * r ^ 2) * Real.exp (-(b * r ^ 2)) * b⁻¹ ≤ 1 * b⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hb.le)
    _ = b⁻¹ := one_mul _

/-- The τ-Lipschitz constant of the kernel symbol above `τ₀`. -/
def kernelLipConst (ν τ₀ : ℝ) : ℝ :=
  ν * ((Real.sqrt (ν * τ₀ / 2))⁻¹ * (ν * τ₀ / 2)⁻¹)

theorem norm_kernelSymbol_sub_le {ν τ τ' τ₀ : ℝ} (hν : 0 < ν) (hτ₀ : 0 < τ₀)
    (hτ : τ₀ ≤ τ) (hτ' : τ₀ ≤ τ') (i j k : Fin 3) (ξ : ES) :
    ‖kernelSymbol ν τ i j k ξ - kernelSymbol ν τ' i j k ξ‖ ≤
      kernelLipConst ν τ₀ * |τ - τ'| := by
  unfold kernelSymbol
  rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set a := ν * ‖ξ‖ ^ 2 with ha_def
  have ha : 0 ≤ a := by positivity
  have hb : 0 < ν * τ₀ / 2 := by positivity
  have hexp : |heatFactor ν τ ξ - heatFactor ν τ' ξ| ≤ a * |τ - τ'| * Real.exp (-(a * τ₀)) := by
    unfold heatFactor
    rw [show ν * ‖ξ‖ ^ 2 * τ = a * τ by ring, show ν * ‖ξ‖ ^ 2 * τ' = a * τ' by ring]
    exact abs_exp_sub_exp_le ha hτ hτ'
  have hsplit : Real.exp (-(a * τ₀)) =
      Real.exp (-((ν * τ₀ / 2) * ‖ξ‖ ^ 2)) * Real.exp (-((ν * τ₀ / 2) * ‖ξ‖ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; rw [ha_def]; ring
  have hA := mul_exp_neg_sq_le hb (norm_nonneg ξ)
  have hB := sq_mul_exp_neg_le (r := ‖ξ‖) hb
  have hA0 : 0 ≤ ‖ξ‖ * Real.exp (-((ν * τ₀ / 2) * ‖ξ‖ ^ 2)) := by positivity
  have hB0 : 0 ≤ ‖ξ‖ ^ 2 * Real.exp (-((ν * τ₀ / 2) * ‖ξ‖ ^ 2)) := by positivity
  calc |heatFactor ν τ ξ - heatFactor ν τ' ξ| * ‖lerayDerivSymbol i j k ξ‖
      ≤ (a * |τ - τ'| * Real.exp (-(a * τ₀))) * ‖ξ‖ :=
        mul_le_mul hexp (norm_lerayDerivSymbol_le i j k ξ) (norm_nonneg _)
          (by positivity)
    _ = ν * ((‖ξ‖ * Real.exp (-((ν * τ₀ / 2) * ‖ξ‖ ^ 2))) *
          (‖ξ‖ ^ 2 * Real.exp (-((ν * τ₀ / 2) * ‖ξ‖ ^ 2)))) * |τ - τ'| := by
        rw [hsplit, ha_def]; ring
    _ ≤ ν * ((Real.sqrt (ν * τ₀ / 2))⁻¹ * (ν * τ₀ / 2)⁻¹) * |τ - τ'| := by
        gcongr
    _ = kernelLipConst ν τ₀ * |τ - τ'| := rfl

theorem kernelLipConst_nonneg {ν τ₀ : ℝ} (hν : 0 < ν) (hτ₀ : 0 < τ₀) :
    0 ≤ kernelLipConst ν τ₀ := by
  unfold kernelLipConst; positivity

/-! ## Multipliers as `L∞` classes -/

/-- The kernel coefficient as an `L∞` class (zero off `ν, τ > 0`, where it is
never used). -/
def kernelLinf (ν τ : ℝ) (i j k : Fin 3) : LinfC :=
  if h : 0 < ν ∧ 0 < τ then
    linfOfBound (kernelSymbol ν τ i j k) (measurable_kernelSymbol ν τ i j k).aestronglyMeasurable
      (Real.sqrt (ν * τ))⁻¹ (norm_kernelSymbol_le h.1 h.2 i j k)
  else 0

theorem coeFn_kernelLinf {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (i j k : Fin 3) :
    kernelLinf ν τ i j k =ᵐ[volume] kernelSymbol ν τ i j k := by
  unfold kernelLinf
  rw [dif_pos ⟨hν, hτ⟩]
  exact coeFn_linfOfBound _ _ _ _

theorem norm_kernelLinf_le {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (i j k : Fin 3) :
    ‖kernelLinf ν τ i j k‖ ≤ (Real.sqrt (ν * τ))⁻¹ :=
  linf_norm_le_of_ae_bound _ (by positivity) (by
    filter_upwards [coeFn_kernelLinf hν hτ i j k] with ξ h
    rw [h]; exact norm_kernelSymbol_le hν hτ i j k ξ)

theorem norm_kernelLinf_sub_le {ν τ τ' τ₀ : ℝ} (hν : 0 < ν) (hτ₀ : 0 < τ₀)
    (hτ : τ₀ ≤ τ) (hτ' : τ₀ ≤ τ') (i j k : Fin 3) :
    ‖kernelLinf ν τ i j k - kernelLinf ν τ' i j k‖ ≤ kernelLipConst ν τ₀ * |τ - τ'| :=
  linf_norm_le_of_ae_bound _
    (mul_nonneg (kernelLipConst_nonneg hν hτ₀) (abs_nonneg _)) (by
    filter_upwards [Lp.coeFn_sub (kernelLinf ν τ i j k) (kernelLinf ν τ' i j k),
      coeFn_kernelLinf hν (lt_of_lt_of_le hτ₀ hτ) i j k,
      coeFn_kernelLinf hν (lt_of_lt_of_le hτ₀ hτ') i j k] with ξ h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    exact norm_kernelSymbol_sub_le hν hτ₀ hτ hτ' i j k ξ)

/-- The heat factor as an `L∞` class, at time `max t 0`. -/
def heatLinf (ν t : ℝ) : LinfC :=
  if h : 0 ≤ ν then
    linfOfBound (fun ξ => (heatFactor ν (max t 0) ξ : ℂ))
      (Complex.measurable_ofReal.comp (measurable_heatFactor ν _)).aestronglyMeasurable 1
      (fun ξ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
        exact heatFactor_le_one h (le_max_right _ _) ξ)
  else 0

theorem coeFn_heatLinf {ν : ℝ} (hν : 0 ≤ ν) (t : ℝ) :
    heatLinf ν t =ᵐ[volume] fun ξ => (heatFactor ν (max t 0) ξ : ℂ) := by
  unfold heatLinf
  rw [dif_pos hν]
  exact coeFn_linfOfBound _ _ _ _

theorem norm_heatLinf_le (ν t : ℝ) : ‖heatLinf ν t‖ ≤ 1 := by
  by_cases hν : 0 ≤ ν
  · exact linf_norm_le_of_ae_bound _ zero_le_one (by
      filter_upwards [coeFn_heatLinf hν t] with ξ h
      rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
      exact heatFactor_le_one hν (le_max_right _ _) ξ)
  · unfold heatLinf; rw [dif_neg hν, norm_zero]; exact zero_le_one

/-! ## Vector and tensor carriers -/

/-- Velocity Fourier coefficients: three `L¹` coordinates. -/
abbrev V1 := Fin 3 → L1C

/-- Tensor Fourier coefficients: the `(j, k)` coordinate carries
`û_j ⋆ v̂_k`. -/
abbrev W1 := Fin 3 → Fin 3 → L1C

/-- Coordinatewise multiplier operator `(W ↦ ∑ⱼₖ mᵢⱼₖ · W j k)ᵢ`. -/
def tensorMulOp (m : Fin 3 → Fin 3 → Fin 3 → LinfC) : W1 →L[ℂ] V1 :=
  ContinuousLinearMap.pi fun i => ∑ j : Fin 3, ∑ k : Fin 3,
    (mulL (m i j k)).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => L1C) k).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => Fin 3 → L1C) j))

theorem tensorMulOp_apply (m : Fin 3 → Fin 3 → Fin 3 → LinfC) (W : W1) (i : Fin 3) :
    tensorMulOp m W i = ∑ j : Fin 3, ∑ k : Fin 3, mulL (m i j k) (W j k) := by
  simp [tensorMulOp]

theorem norm_tensorMulOp_apply_le (m : Fin 3 → Fin 3 → Fin 3 → LinfC) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i j k, ‖m i j k‖ ≤ M) (W : W1) :
    ‖tensorMulOp m W‖ ≤ 9 * M * ‖W‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [tensorMulOp_apply]
  calc ‖∑ j : Fin 3, ∑ k : Fin 3, mulL (m i j k) (W j k)‖
      ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖mulL (m i j k) (W j k)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j : Fin 3, ∑ k : Fin 3, M * ‖W‖ := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        refine (norm_mulL_apply_le _ _).trans ?_
        exact mul_le_mul (hM i j k) ((norm_le_pi_norm (W j) k).trans (norm_le_pi_norm W j))
          (norm_nonneg _) hM0
    _ = 9 * M * ‖W‖ := by simp; ring

theorem norm_tensorMulOp_le (m : Fin 3 → Fin 3 → Fin 3 → LinfC) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i j k, ‖m i j k‖ ≤ M) : ‖tensorMulOp m‖ ≤ 9 * M :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_tensorMulOp_apply_le m hM0 hM)

theorem tensorMulOp_sub (m m' : Fin 3 → Fin 3 → Fin 3 → LinfC) :
    tensorMulOp m - tensorMulOp m' = tensorMulOp (m - m') := by
  ext W i : 2
  simp [tensorMulOp_apply, map_sub, Finset.sum_sub_distrib]

/-- **The Duhamel kernel operator** `K_τ : W1 → V1`,
`(K_τ W)ᵢ(ξ) = e^{-ν‖ξ‖²τ} ∑ⱼₖ lerayDerivSymbol i j k ξ · W j k (ξ)`. -/
def kernelOp (ν τ : ℝ) : W1 →L[ℂ] V1 := tensorMulOp (kernelLinf ν τ)

theorem norm_kernelOp_le {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) :
    ‖kernelOp ν τ‖ ≤ 9 * (Real.sqrt (ν * τ))⁻¹ :=
  norm_tensorMulOp_le _ (by positivity) (norm_kernelLinf_le hν hτ)

theorem norm_kernelOp_sub_le {ν τ τ' τ₀ : ℝ} (hν : 0 < ν) (hτ₀ : 0 < τ₀)
    (hτ : τ₀ ≤ τ) (hτ' : τ₀ ≤ τ') :
    ‖kernelOp ν τ - kernelOp ν τ'‖ ≤ 9 * (kernelLipConst ν τ₀ * |τ - τ'|) := by
  unfold kernelOp
  rw [tensorMulOp_sub]
  exact norm_tensorMulOp_le _ (mul_nonneg (kernelLipConst_nonneg hν hτ₀) (abs_nonneg _))
    (fun i j k => norm_kernelLinf_sub_le hν hτ₀ hτ hτ' i j k)

/-- The kernel operator is norm-continuous in `τ > 0`. -/
theorem continuousOn_kernelOp {ν : ℝ} (hν : 0 < ν) :
    ContinuousOn (kernelOp ν) (Ioi 0) := by
  intro τ₀ hτ₀
  have hτ₀ : 0 < τ₀ := hτ₀
  refine (Metric.continuousAt_iff.mpr fun ε hε => ?_).continuousWithinAt
  set L := 9 * kernelLipConst ν (τ₀ / 2) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]; exact mul_nonneg (by norm_num) (kernelLipConst_nonneg hν (by positivity))
  refine ⟨min (τ₀ / 2) (ε / (L + 1)), by positivity, fun {τ} hτ => ?_⟩
  rw [Real.dist_eq] at hτ
  have h1 : |τ - τ₀| < τ₀ / 2 := lt_of_lt_of_le hτ (min_le_left _ _)
  have h2 : |τ - τ₀| < ε / (L + 1) := lt_of_lt_of_le hτ (min_le_right _ _)
  have hτge : τ₀ / 2 ≤ τ := by
    have := neg_abs_le (τ - τ₀); linarith
  rw [dist_eq_norm]
  calc ‖kernelOp ν τ - kernelOp ν τ₀‖ ≤ 9 * (kernelLipConst ν (τ₀ / 2) * |τ - τ₀|) :=
        norm_kernelOp_sub_le hν (by positivity) hτge (by linarith)
    _ = L * |τ - τ₀| := by rw [hL]; ring
    _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left h2.le hL0
    _ < ε := by
        rw [mul_div_assoc']
        rw [div_lt_iff₀ (by linarith)]
        nlinarith

/-- The heat semigroup acting coordinatewise on `V1`. -/
def heatOp (ν t : ℝ) : V1 →L[ℂ] V1 :=
  ContinuousLinearMap.pi fun i => (mulL (heatLinf ν t)).comp (ContinuousLinearMap.proj i)

theorem heatOp_apply (ν t : ℝ) (v : V1) (i : Fin 3) :
    heatOp ν t v i = mulL (heatLinf ν t) (v i) := rfl

theorem norm_heatOp_apply_le (ν t : ℝ) (v : V1) : ‖heatOp ν t v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  rw [heatOp_apply]
  calc ‖mulL (heatLinf ν t) (v i)‖ ≤ ‖heatLinf ν t‖ * ‖v i‖ := norm_mulL_apply_le _ _
    _ ≤ 1 * ‖v‖ := mul_le_mul (norm_heatLinf_le ν t) (norm_le_pi_norm v i)
        (norm_nonneg _) zero_le_one
    _ = ‖v‖ := one_mul _

/-! ## The convolution tensor -/

/-- Raw tensor convolution `(û_j ⋆ v̂_k)_{j,k}`. -/
def tensorConvFun (u v : V1) : W1 := fun j k => conv (u j) (v k)

theorem norm_tensorConvFun_le (u v : V1) : ‖tensorConvFun u v‖ ≤ ‖u‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  exact (norm_conv_apply_le _ _).trans
    (mul_le_mul (norm_le_pi_norm u j) (norm_le_pi_norm v k) (norm_nonneg _) (norm_nonneg _))

/-- `(u, v) ↦ (û_j ⋆ v̂_k)_{j,k}` as a bounded bilinear map. -/
def tensorConv : V1 →L[ℂ] V1 →L[ℂ] W1 :=
  (LinearMap.mk₂ ℂ tensorConvFun
    (fun u u' v => by
      funext j k; simp only [tensorConvFun, Pi.add_apply, map_add, ContinuousLinearMap.add_apply])
    (fun c u v => by
      funext j k
      simp only [tensorConvFun, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_apply])
    (fun u v v' => by
      funext j k; simp only [tensorConvFun, Pi.add_apply, map_add])
    (fun c u v => by
      funext j k; simp only [tensorConvFun, Pi.smul_apply, map_smul])).mkContinuous₂ 1
    (fun u v => by
      rw [LinearMap.mk₂_apply, one_mul]
      exact norm_tensorConvFun_le u v)

theorem tensorConv_apply (u v : V1) (j k : Fin 3) :
    tensorConv u v j k = conv (u j) (v k) := rfl

theorem norm_tensorConv_apply_le (u v : V1) : ‖tensorConv u v‖ ≤ ‖u‖ * ‖v‖ :=
  norm_tensorConvFun_le u v

/-! ## Strong continuity of the heat semigroup -/

theorem continuous_heat_mulL {ν : ℝ} (hν : 0 ≤ ν) (f : L1C) :
    Continuous fun t : ℝ => mulL (heatLinf ν t) f := by
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ t : ℝ, ‖mulL (heatLinf ν t) f - mulL (heatLinf ν t₀) f‖ =
      ∫ ξ, ‖(((heatFactor ν (max t 0) ξ : ℂ)) - (heatFactor ν (max t₀ 0) ξ : ℂ)) * f ξ‖ := by
    intro t
    have hsub : mulL (heatLinf ν t) f - mulL (heatLinf ν t₀) f =
        mulL (heatLinf ν t - heatLinf ν t₀) f := by
      rw [map_sub, ContinuousLinearMap.sub_apply]
    rw [hsub, L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [coeFn_mulL (heatLinf ν t - heatLinf ν t₀) f,
      Lp.coeFn_sub (heatLinf ν t) (heatLinf ν t₀), coeFn_heatLinf hν t,
      coeFn_heatLinf hν t₀] with ξ h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, h3, h4]
  simp_rw [hnorm]
  rw [show (nhds (0 : ℝ)) = nhds (∫ _ξ : ES, (0 : ℝ)) by simp]
  have hcontξ : ∀ ξ : ES, Continuous fun t : ℝ => (heatFactor ν (max t 0) ξ : ℂ) := by
    intro ξ
    unfold heatFactor
    fun_prop
  refine tendsto_integral_filter_of_dominated_convergence (fun ξ => 2 * ‖f ξ‖) ?_ ?_
    ((L1.integrable_coeFn f).norm.const_mul 2) ?_
  · exact Eventually.of_forall fun t =>
      ((((Complex.measurable_ofReal.comp (measurable_heatFactor ν _)).sub
        (Complex.measurable_ofReal.comp (measurable_heatFactor ν _))).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable f)).norm
  · refine Eventually.of_forall fun t => Eventually.of_forall fun ξ => ?_
    rw [norm_norm, norm_mul]
    have hb : ∀ s : ℝ, ‖((heatFactor ν (max s 0) ξ : ℝ) : ℂ)‖ ≤ 1 := fun s => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heatFactor_nonneg _ _ _)]
      exact heatFactor_le_one hν (le_max_right _ _) ξ
    have := norm_sub_le ((heatFactor ν (max t 0) ξ : ℂ)) ((heatFactor ν (max t₀ 0) ξ : ℂ))
    have h2 : ‖((heatFactor ν (max t 0) ξ : ℂ)) - (heatFactor ν (max t₀ 0) ξ : ℂ)‖ ≤ 2 := by
      linarith [hb t, hb t₀]
    nlinarith [norm_nonneg (f ξ), norm_nonneg
      (((heatFactor ν (max t 0) ξ : ℂ)) - (heatFactor ν (max t₀ 0) ξ : ℂ))]
  · refine Eventually.of_forall fun ξ => ?_
    have hc : Continuous fun t : ℝ =>
        ‖(((heatFactor ν (max t 0) ξ : ℂ)) - (heatFactor ν (max t₀ 0) ξ : ℂ)) * f ξ‖ :=
      (((hcontξ ξ).sub continuous_const).mul continuous_const).norm
    have := hc.tendsto t₀
    simpa using this

theorem continuous_heatOp_apply {ν : ℝ} (hν : 0 ≤ ν) (v : V1) :
    Continuous fun t : ℝ => heatOp ν t v :=
  continuous_pi fun i => by
    simpa only [heatOp_apply] using continuous_heat_mulL hν (v i)

/-! ## Faithfulness of the coefficient decomposition -/

/-- The `(i; j, k)` coefficients reassemble the repository's Fourier Navier
symbol: `∑ⱼₖ lerayDerivSymbol i j k ξ · w j k` is the `i`-th coordinate of
`continuousLeray ξ (I • ∑ⱼ ξⱼ w j ·)`, the operator inside
`ContinuousLeiLinSpace.continuousNavierBilinear`
(with `w j k = (û_j ⋆ v̂_k)(ξ)`). -/
theorem sum_lerayDerivSymbol (ξ : ES) (w : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    ∑ j : Fin 3, ∑ k : Fin 3, lerayDerivSymbol i j k ξ * w j k =
      continuousLeray ξ (Complex.I • fun k => ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * w j k) i := by
  have harg : (Complex.I • fun k => ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * w j k :
        ContinuousLeiLinSpace.ComplexSpace) =
      ∑ j : Fin 3, ∑ k : Fin 3,
        w j k • (Pi.single k (Complex.I * ((ξ j : ℝ) : ℂ)) :
          ContinuousLeiLinSpace.ComplexSpace) := by
    funext k'
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.single_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single k']
    · simp; ring
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  unfold lerayDerivSymbol continuousLeray
  rw [harg, map_sum]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end Navier.Analysis.WienerL1Carrier

set_option pp.fullNames true in
#check @Navier.Analysis.WienerL1Carrier.norm_kernelOp_le
set_option pp.fullNames true in
#check @Navier.Analysis.WienerL1Carrier.sum_lerayDerivSymbol
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerL1Carrier.conv
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerL1Carrier.norm_conv_apply_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerL1Carrier.norm_kernelOp_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerL1Carrier.continuousOn_kernelOp
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerL1Carrier.continuous_heatOp_apply
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerL1Carrier.sum_lerayDerivSymbol
