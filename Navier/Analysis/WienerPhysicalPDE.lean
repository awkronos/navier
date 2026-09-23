import Navier.Analysis.WienerReality
import Mathlib.Analysis.Fourier.Convolution

/-!
# Towards the pointwise physical Navier–Stokes identity

First objects:

* `fourierInv_convolution`: on `L¹(ℝ³)` the inverse Fourier transform turns the
  convolution used by the repository's Navier symbol into the pointwise
  product (`Real.fourier_mul_convolution_eq` plus `𝓕⁻ f x = 𝓕 f (-x)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

namespace Navier.Analysis.WienerPhysicalPDE

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerL1Carrier
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPointwiseODE

/-- **Convolution theorem for the inverse Fourier transform on `L¹`.** -/
theorem fourierInv_convolution {f g : ES → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ES) :
    𝓕⁻ (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x = 𝓕⁻ f x * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg,
    Real.fourierInv_eq_fourier_neg]
  exact Real.fourier_mul_convolution_eq hf hg (-x)

/-! ## Spatial derivatives of inverse Fourier transforms with explicit moments -/

/-- `∂ₗ 𝓕⁻ f = 2πi 𝓕⁻(ξₗ f)`, as a Fréchet derivative. -/
theorem hasFDerivAt_fourierInv' {f : ES → ℂ} (hf : Integrable f)
    (h1 : ∀ j : Fin 3, Integrable (fun ξ : ES => ((ξ j : ℝ) : ℂ) * f ξ)) (y : ES) :
    HasFDerivAt (𝓕⁻ f) (∑ j : Fin 3, (EuclideanSpace.proj j : ES →L[ℝ] ℝ).smulRight
      ((2 * Real.pi : ℂ) * Complex.I * 𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * f ξ) y)) y :=
  hasFDerivAt_fourierInv hf (fun j ξ => ((ξ j : ℝ) : ℂ) * f ξ)
    (fun j => EventuallyEq.refl _ _) h1 y

theorem fderiv_fourierInv_single {f : ES → ℂ} (hf : Integrable f)
    (h1 : ∀ j : Fin 3, Integrable (fun ξ : ES => ((ξ j : ℝ) : ℂ) * f ξ)) (y : ES) (l : Fin 3) :
    fderiv ℝ (𝓕⁻ f) y (EuclideanSpace.single l 1) =
      (2 * Real.pi : ℂ) * Complex.I * 𝓕⁻ (fun ξ : ES => ((ξ l : ℝ) : ℂ) * f ξ) y := by
  rw [(hasFDerivAt_fourierInv' hf h1 y).fderiv]
  simp [ContinuousLinearMap.sum_apply, Pi.single_apply, Finset.sum_ite_eq']

/-- The evaluation of the inverse Fourier transform at a point, as a continuous
linear functional on `L¹`. -/
def evalInv (y : ES) : L1C →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => 𝓕⁻ (⇑f) y
      map_add' := fun f g => by
        rw [show f + g = f - (-g) by abel, fourierInv_sub, show -g = (-1 : ℝ) • g by simp,
          fourierInv_smul]
        simp
      map_smul' := fun c f => by
        rw [Real.fourierInv_eq, Real.fourierInv_eq, ← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c f] with v h
        rw [h, Pi.smul_apply, smul_comm]
        rfl } 1
    (fun f => by simpa using norm_fourierInv_le f y)

theorem evalInv_apply (y : ES) (f : L1C) : evalInv y f = 𝓕⁻ (⇑f) y := rfl

/-! ## Linearity of `𝓕⁻` on integrable functions -/

theorem fourierInv_const_mul (c : ℂ) (f : ES → ℂ) (y : ES) :
    𝓕⁻ (fun ξ => c * f ξ) y = c * 𝓕⁻ f y := by
  rw [fourierInv_eq_exp, fourierInv_eq_exp, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  ring

theorem integrable_exp_mul {f : ES → ℂ} (hf : Integrable f) (y : ES) :
    Integrable (fun ξ => Complex.exp (phaseCLM ξ y) * f ξ) := by
  refine hf.norm.mono' ?_ (Eventually.of_forall fun ξ => by
    rw [norm_mul, norm_exp_phase, one_mul])
  exact ((Complex.continuous_exp.comp
    (phaseL.continuous.clm_apply continuous_const)).aestronglyMeasurable).mul hf.1

theorem fourierInv_add {f g : ES → ℂ} (hf : Integrable f) (hg : Integrable g) (y : ES) :
    𝓕⁻ (fun ξ => f ξ + g ξ) y = 𝓕⁻ f y + 𝓕⁻ g y := by
  rw [fourierInv_eq_exp, fourierInv_eq_exp, fourierInv_eq_exp,
    ← integral_add (integrable_exp_mul hf y) (integrable_exp_mul hg y)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  ring

theorem fourierInv_sum {ι : Type*} (s : Finset ι) {f : ι → ES → ℂ}
    (hf : ∀ i ∈ s, Integrable (f i)) (y : ES) :
    𝓕⁻ (fun ξ => ∑ i ∈ s, f i ξ) y = ∑ i ∈ s, 𝓕⁻ (f i) y := by
  rw [fourierInv_eq_exp]
  simp_rw [fourierInv_eq_exp, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_exp_mul (hf i hi) y

/-! ## The Laplacian of an inverse Fourier transform -/

theorem mono_zero (ξ : ES) : mono 0 ξ = 1 := by simp [mono]

theorem mono_ej (j : Fin 3) (ξ : ES) : mono (ej j) ξ = ((ξ j : ℝ) : ℂ) := by
  have h := mono_add_ej 0 j ξ
  simp only [zero_add] at h
  rw [h]; simp [mono]

theorem mono_ej_ej (j l : Fin 3) (ξ : ES) :
    mono (ej l + ej j) ξ = ((ξ j : ℝ) : ℂ) * ((ξ l : ℝ) : ℂ) := by
  rw [mono_add_ej, mono_ej]

theorem integrable_coord_mul {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) (j : Fin 3) :
    Integrable (fun ξ : ES => ((ξ j : ℝ) : ℂ) * f ξ) :=
  (hmom (ej j)).congr (Eventually.of_forall fun ξ => by dsimp only; rw [mono_ej])

theorem moments_coord_mul {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) (l : Fin 3) :
    ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * (((ξ l : ℝ) : ℂ) * f ξ)) := by
  intro α
  refine (hmom (α + ej l)).congr (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [mono_add_ej]; ring

/-- `∂ₗ 𝓕⁻ f = 2πi 𝓕⁻(ξₗ f)` at every point, as a function identity. -/
theorem fderiv_fourierInv_single_fun {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) (l : Fin 3) :
    (fun z => fderiv ℝ (𝓕⁻ f) z (EuclideanSpace.single l 1)) =
      fun z => (2 * Real.pi : ℂ) * Complex.I * 𝓕⁻ (fun ξ : ES => ((ξ l : ℝ) : ℂ) * f ξ) z := by
  funext z
  have hf : Integrable f := (hmom 0).congr (Eventually.of_forall fun ξ => by simp [mono_zero])
  exact fderiv_fourierInv_single hf (integrable_coord_mul hmom) z l

/-- Second directional derivative. -/
theorem fderiv_fderiv_fourierInv_single {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) (j l : Fin 3) (y : ES) :
    fderiv ℝ (fun z => fderiv ℝ (𝓕⁻ f) z (EuclideanSpace.single l 1)) y
        (EuclideanSpace.single j 1) =
      (2 * Real.pi : ℂ) * Complex.I * ((2 * Real.pi : ℂ) * Complex.I *
        𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * (((ξ l : ℝ) : ℂ) * f ξ)) y) := by
  rw [fderiv_fourierInv_single_fun hmom l]
  have hg := moments_coord_mul hmom l
  have hgi : Integrable (fun ξ : ES => ((ξ l : ℝ) : ℂ) * f ξ) :=
    (hg 0).congr (Eventually.of_forall fun ξ => by simp [mono_zero])
  have hd := (hasFDerivAt_fourierInv' hgi (integrable_coord_mul hg) y).const_mul
    ((2 * Real.pi : ℂ) * Complex.I)
  rw [hd.fderiv]
  simp [ContinuousLinearMap.sum_apply, Pi.single_apply, Finset.sum_ite_eq', smul_eq_mul]

/-- **The Laplacian of an inverse Fourier transform**:
`∑ₗ ∂ₗ∂ₗ 𝓕⁻ f = -4π² 𝓕⁻(‖ξ‖² f)`. -/
theorem laplacian_fourierInv {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) (y : ES) :
    ∑ l : Fin 3, fderiv ℝ (fun z => fderiv ℝ (𝓕⁻ f) z (EuclideanSpace.single l 1)) y
        (EuclideanSpace.single l 1) =
      -(4 * (Real.pi : ℂ) ^ 2) * 𝓕⁻ (fun ξ : ES => ((‖ξ‖ ^ 2 : ℝ) : ℂ) * f ξ) y := by
  simp_rw [fderiv_fderiv_fourierInv_single hmom]
  have hint : ∀ l ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun ξ : ES => ((ξ l : ℝ) : ℂ) * (((ξ l : ℝ) : ℂ) * f ξ)) := fun l _ =>
    (hmom (ej l + ej l)).congr (Eventually.of_forall fun ξ => by dsimp only; rw [mono_ej_ej]; ring)
  have hsq : (fun ξ : ES => ((‖ξ‖ ^ 2 : ℝ) : ℂ) * f ξ) =
      fun ξ => ∑ l : Fin 3, ((ξ l : ℝ) : ℂ) * (((ξ l : ℝ) : ℂ) * f ξ) := by
    funext ξ
    rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Real.norm_eq_abs, sq_abs]; push_cast; ring
  rw [hsq, fourierInv_sum _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (4 * (Real.pi : ℂ) ^ 2 *
    𝓕⁻ (fun ξ : ES => ((ξ l : ℝ) : ℂ) * (((ξ l : ℝ) : ℂ) * f ξ)) y) * hI

/-! ## Moments of convolutions of majorized profiles -/

theorem integrable_moment_conv {u v : ES → ComplexSpace} (hu : StronglyMeasurable u)
    (hv : StronglyMeasurable v) {Mu Mv : ES → ℝ≥0∞} (hMu : Measurable Mu) (hMv : Measurable Mv)
    (hub : ∀ᵐ η ∂(volume : Measure ES), ‖u η‖ₑ ≤ Mu η)
    (hvb : ∀ᵐ η ∂(volume : Measure ES), ‖v η‖ₑ ≤ Mv η)
    (hMum : ∀ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * Mu ξ ≠ ⊤)
    (hMvm : ∀ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * Mv ξ ≠ ⊤) (j k : Fin 3)
    (α : Fin 3 → ℕ) :
    Integrable (fun ξ => mono α ξ *
      ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η k)) ξ) := by
  refine ⟨((by unfold mono; fun_prop : Continuous (mono α)).aestronglyMeasurable).mul
    (stronglyMeasurable_conv_coord hu hv j k).aestronglyMeasurable, ?_⟩
  have h := lintegral_weight_convE_le (deg α) Mu Mv hMu hMv
  have hfin : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ deg α) * ∫⁻ η, Mu η * Mv (ξ - η) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ h
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp)
      (ENNReal.mul_ne_top (hMum _) (lintegral_ne_top_of_mom hMvm)),
      ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (lintegral_ne_top_of_mom hMum)
        (hMvm _))⟩
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hfin.lt_top
  rw [enorm_mul]
  refine mul_le_mul' ?_ ((enorm_conv_coord_le u v j k ξ).trans ?_)
  · rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_mono_le α ξ)
  · unfold convE
    refine lintegral_mono_ae ?_
    filter_upwards [hub, ae_sub_left hvb ξ] with η h1 h2
    exact mul_le_mul' h1 h2

/-! ## The abstract local solution -/

section Local

open Navier.Analysis.ContinuousLeiLinSelfMap

variable {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν) (a : ES → ComplexSpace)
  {w : ℝ → ES → ComplexSpace}
  (hfix : ∀ t ∈ Icc (0 : ℝ) T, ∀ ξ, w t ξ = continuousMildImage ν hν a w t ξ)
  (hG : Good T w)

theorem towerSym_mem (k : ℕ) (α : Fin 3 → ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3)
    (ξ : ES) : towerSym hT (W ν w) i k α t ξ = mono α ξ * W ν w k t ξ i := by
  unfold towerSym
  rw [projIcc_of_mem hT.le ht]

include hT hν hG in
theorem integrable_moment (k : ℕ) (α : Fin 3 → ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (i : Fin 3) : Integrable (fun ξ => mono α ξ * W ν w k t ξ i) := by
  have h := integrable_towerSym hT (W ν w) (good_W hν.le hG) i k α t
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  exact towerSym_mem hT k α ht i ξ

include hT hν hfix hG in
/-- **Time derivative of the physical coordinates**: within `[0,T)`,
`∂ₜ 𝓕⁻(wᵢ)(y) = 𝓕⁻((W 1)ᵢ)(y)`. -/
theorem hasDerivWithinAt_physTime (i : Fin 3) (y : ES) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun s => 𝓕⁻ (fun ξ => w s ξ i) y)
      (𝓕⁻ (fun ξ => W ν w 1 t ξ i) y) (Ico (0 : ℝ) T) t := by
  have hGW := good_W hν.le hG
  have hdW := hasTimeDeriv_W hν.le hG (hasTimeDeriv_W_zero hν a hfix hG)
  have hD := towerD_deriv hT (W ν w) hGW i hdW 0 0 ht
  have hc := ((evalInv y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hD
  have hval : ∀ (k : ℕ) (s : ℝ), s ∈ Icc (0 : ℝ) T →
      evalInv y (towerD hT (W ν w) hGW i k 0 s) = 𝓕⁻ (fun ξ => W ν w k s ξ i) y := by
    intro k s hs
    rw [evalInv_apply, fourierInv_congr (coeFn_towerD hT (W ν w) hGW i k 0 s) y]
    have hfun : towerSym hT (W ν w) i k 0 s = fun ξ => W ν w k s ξ i := by
      funext ξ
      rw [towerSym_mem hT k 0 hs i ξ, mono_zero, one_mul]
    rw [hfun]
  have hI : ∀ s ∈ Ico (0 : ℝ) T, s ∈ Icc (0 : ℝ) T := fun s hs => Ico_subset_Icc_self hs
  refine (hc.congr (fun s hs => ?_) ?_).congr_deriv ?_
  · show 𝓕⁻ (fun ξ => w s ξ i) y = evalInv y (towerD hT (W ν w) hGW i 0 0 s)
    rw [hval 0 s (hI s hs), W_zero]
  · show 𝓕⁻ (fun ξ => w t ξ i) y = evalInv y (towerD hT (W ν w) hGW i 0 0 t)
    rw [hval 0 t (hI t ht), W_zero]
  · show evalInv y (towerD hT (W ν w) hGW i (0 + 1) 0 t) = _
    exact hval 1 t (hI t ht)

/-- The convolution coefficient `(wⱼ ⋆ wₖ)(ξ)` at time `t`. -/
def cc (w : ℝ → ES → ComplexSpace) (t : ℝ) (j k : Fin 3) (ξ : ES) : ℂ :=
  ((fun η => w t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => w t η k)) ξ

/-- The Fourier pressure coefficient `∑ⱼₖ ξⱼξₖ (wⱼ ⋆ wₖ)(ξ) / ‖ξ‖²`. -/
def Qhat (w : ℝ → ES → ComplexSpace) (t : ℝ) (ξ : ES) : ℂ :=
  (∑ j : Fin 3, ∑ k : Fin 3, ((ξ j : ℝ) : ℂ) * ((ξ k : ℝ) : ℂ) * cc w t j k ξ) /
    ((‖ξ‖ ^ 2 : ℝ) : ℂ)

include hT hν hG in
theorem hmom_w {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (i : Fin 3) (α : Fin 3 → ℕ) :
    Integrable (fun ξ => mono α ξ * w t ξ i) := by
  have h := integrable_moment hT hν hG 0 α ht i
  simpa [W_zero] using h

include hG in
theorem hmom_cc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (j k : Fin 3) (α : Fin 3 → ℕ) :
    Integrable (fun ξ => mono α ξ * cc w t j k ξ) := by
  obtain ⟨hm, M, hM, hb, hmom, -⟩ := hG
  have hbt : ∀ᵐ η ∂(volume : Measure ES), ‖w t η‖ₑ ≤ M η := by
    filter_upwards [hb] with η h using h t ht
  exact integrable_moment_conv (hm t) (hm t) hM hM hbt hbt hmom hmom j k α

theorem norm_coord_mul_le (ξ : ES) (j k : Fin 3) : |ξ j * ξ k| ≤ ‖ξ‖ ^ 2 := by
  rw [abs_mul, sq]
  exact mul_le_mul (PiLp.norm_apply_le ξ j) (PiLp.norm_apply_le ξ k) (abs_nonneg _)
    (norm_nonneg _)

theorem norm_Qhat_le (t : ℝ) (ξ : ES) :
    ‖Qhat w t ξ‖ ≤ ∑ j : Fin 3, ∑ k : Fin 3, ‖cc w t j k ξ‖ := by
  unfold Qhat
  by_cases hξ : ξ = 0
  · subst hξ; simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Complex.ofReal_zero, div_zero, norm_zero]
    positivity
  have hpos : 0 < ‖ξ‖ ^ 2 := by positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, div_le_iff₀ hpos]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, ← abs_mul, mul_comm (‖cc w t j k ξ‖)]
  exact mul_le_mul_of_nonneg_right (norm_coord_mul_le ξ j k) (norm_nonneg _)

include hG in
theorem hmom_Qhat {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (α : Fin 3 → ℕ) :
    Integrable (fun ξ => mono α ξ * Qhat w t ξ) := by
  have hsum : Integrable (fun ξ => ∑ j : Fin 3, ∑ k : Fin 3, ‖mono α ξ * cc w t j k ξ‖) :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      (hmom_cc hG ht j k α).norm
  obtain ⟨hm, -, -, -, -, -⟩ := hG
  refine hsum.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · have hcc : ∀ j k, StronglyMeasurable (cc w t j k) := fun j k =>
      stronglyMeasurable_conv_coord (hm t) (hm t) j k
    unfold Qhat
    refine ((by unfold mono; fun_prop : Continuous (mono α)).aestronglyMeasurable).mul ?_
    have hnum : Measurable (fun ξ : ES => ∑ j : Fin 3, ∑ k : Fin 3,
        ((ξ j : ℝ) : ℂ) * ((ξ k : ℝ) : ℂ) * cc w t j k ξ) :=
      Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun k _ =>
        ((Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j)).measurable.mul
          (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ k)).measurable).mul
          (hcc j k).measurable
    have hden : Measurable (fun ξ : ES => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_norm.pow 2)).measurable
    exact (hnum.div hden).aestronglyMeasurable
  · simp only [norm_mul]
    calc ‖mono α ξ‖ * ‖Qhat w t ξ‖ ≤ ‖mono α ξ‖ * ∑ j : Fin 3, ∑ k : Fin 3, ‖cc w t j k ξ‖ :=
          mul_le_mul_of_nonneg_left (norm_Qhat_le t ξ) (norm_nonneg _)
      _ = _ := by simp only [Finset.mul_sum]

/-! ### The Navier bilinear symbol in divergence-plus-pressure form -/

theorem spaceProj_apply' (ξ : ES) (l : Fin 3) :
    (Navier.Analysis.FourierMajorant.spaceProj ξ) l = ξ l := rfl

theorem spaceProj_dot (ξ : ES) :
    (Navier.Analysis.FourierMajorant.spaceProj ξ) ⬝ᵥ (Navier.Analysis.FourierMajorant.spaceProj ξ)
      = ‖ξ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, spaceProj_apply', Real.norm_eq_abs, sq, abs_mul_abs_self]

/-- `Bil(w,w)ᵢ(ξ) = i ∑ⱼ ξⱼ (wⱼ⋆wᵢ)(ξ) - i ξᵢ Q̂(ξ)`. -/
theorem bil_formula (t : ℝ) (ξ : ES) (i : Fin 3) :
    continuousNavierBilinear (w t) (w t) ξ i =
      ∑ j : Fin 3, Complex.I * (((ξ j : ℝ) : ℂ) * cc w t j i ξ) +
        (-Complex.I) * (((ξ i : ℝ) : ℂ) * Qhat w t ξ) := by
  unfold continuousNavierBilinear continuousLeray
  rw [Navier.Analysis.ComplexLerayNorm.complexLeray_formula]
  simp only [spaceProj_apply', spaceProj_dot, Pi.smul_apply, smul_eq_mul, rawNavierConvection]
  unfold Qhat cc
  have hn : ∑ l : Fin 3, ((ξ l : ℝ) : ℂ) * (Complex.I * ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) *
        ((fun η => w t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => w t η l)) ξ) =
      Complex.I * ∑ j : Fin 3, ∑ k : Fin 3, ((ξ j : ℝ) : ℂ) * ((ξ k : ℝ) : ℂ) *
        ((fun η => w t η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => w t η k)) ξ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hn, Finset.mul_sum]
  ring

theorem W_one (t : ℝ) (ξ : ES) (i : Fin 3) :
    W ν w 1 t ξ i = heatSym2 ν ξ * w t ξ i + continuousNavierBilinear (w t) (w t) ξ i := by
  rw [W_succ]
  simp [W_zero]

theorem integrable_of_hmom {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) : Integrable f :=
  (hmom 0).congr (Eventually.of_forall fun ξ => by simp [mono_zero])

theorem integrable_normsq_mul {f : ES → ℂ}
    (hmom : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * f ξ)) :
    Integrable (fun ξ : ES => ((‖ξ‖ ^ 2 : ℝ) : ℂ) * f ξ) := by
  have hsq : (fun ξ : ES => ((‖ξ‖ ^ 2 : ℝ) : ℂ) * f ξ) =
      fun ξ => ∑ l : Fin 3, ((ξ l : ℝ) : ℂ) * (((ξ l : ℝ) : ℂ) * f ξ) := by
    funext ξ
    rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Real.norm_eq_abs, sq_abs]; push_cast; ring
  rw [hsq]
  exact integrable_finsetSum _ fun l _ =>
    (hmom (ej l + ej l)).congr (Eventually.of_forall fun ξ => by dsimp only; rw [mono_ej_ej]; ring)

include hT hν hfix hG in
/-- **The complex physical identity.** With `Uᵢ = 𝓕⁻(wᵢ)` and `Π = 𝓕⁻ Q̂`, on `[0,T)`:
`∂ₜUᵢ = (ν/4π²) ΔUᵢ + (1/2π) ∑ⱼ ∂ⱼ(UⱼUᵢ) - (1/2π) ∂ᵢΠ`. -/
theorem hasDerivWithinAt_physical_identity (i : Fin 3) (y : ES) {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun s => 𝓕⁻ (fun ξ => w s ξ i) y)
      ((ν : ℂ) / (4 * (Real.pi : ℂ) ^ 2) *
          ∑ l : Fin 3, fderiv ℝ (fun z => fderiv ℝ (𝓕⁻ (fun ξ => w t ξ i)) z
            (EuclideanSpace.single l 1)) y (EuclideanSpace.single l 1) +
        1 / (2 * (Real.pi : ℂ)) * ∑ j : Fin 3, fderiv ℝ (fun z =>
          𝓕⁻ (fun ξ => w t ξ j) z * 𝓕⁻ (fun ξ => w t ξ i) z) y (EuclideanSpace.single j 1) -
        1 / (2 * (Real.pi : ℂ)) * fderiv ℝ (𝓕⁻ (Qhat w t)) y (EuclideanSpace.single i 1))
      (Ico (0 : ℝ) T) t := by
  refine (hasDerivWithinAt_physTime hT hν a hfix hG i y ht).congr_deriv ?_
  have htI : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
  have hw : ∀ k, ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * w t ξ k) :=
    fun k α => hmom_w hT hν hG htI k α
  have hc : ∀ j k, ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * cc w t j k ξ) :=
    fun j k α => hmom_cc hG htI j k α
  have hQ : ∀ α : Fin 3 → ℕ, Integrable (fun ξ => mono α ξ * Qhat w t ξ) :=
    fun α => hmom_Qhat hG htI α
  -- the Fourier side
  have hW : (fun ξ => W ν w 1 t ξ i) = fun ξ =>
      (-(ν : ℂ)) * (((‖ξ‖ ^ 2 : ℝ) : ℂ) * w t ξ i) +
        (∑ j : Fin 3, Complex.I * (((ξ j : ℝ) : ℂ) * cc w t j i ξ) +
          (-Complex.I) * (((ξ i : ℝ) : ℂ) * Qhat w t ξ)) := by
    funext ξ
    rw [W_one, bil_formula]
    unfold heatSym2
    push_cast; ring
  have i1 : Integrable (fun ξ : ES => (-(ν : ℂ)) * (((‖ξ‖ ^ 2 : ℝ) : ℂ) * w t ξ i)) :=
    (integrable_normsq_mul (hw i)).const_mul _
  have i2 : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun ξ : ES => Complex.I * (((ξ j : ℝ) : ℂ) * cc w t j i ξ)) :=
    fun j _ => (integrable_coord_mul (hc j i) j).const_mul _
  have i3 : Integrable (fun ξ : ES => (-Complex.I) * (((ξ i : ℝ) : ℂ) * Qhat w t ξ)) :=
    (integrable_coord_mul hQ i).const_mul _
  rw [hW, fourierInv_add (g := fun ξ : ES => ∑ j : Fin 3, Complex.I *
      (((ξ j : ℝ) : ℂ) * cc w t j i ξ) + (-Complex.I) * (((ξ i : ℝ) : ℂ) * Qhat w t ξ))
      i1 ((integrable_finsetSum _ i2).add i3),
    fourierInv_add (integrable_finsetSum _ i2) i3, fourierInv_sum _ i2,
    fourierInv_const_mul, fourierInv_const_mul]
  simp_rw [fourierInv_const_mul]
  -- the physical side
  rw [laplacian_fourierInv (hw i) y]
  have hprod : ∀ j : Fin 3, (fun z => 𝓕⁻ (fun ξ => w t ξ j) z * 𝓕⁻ (fun ξ => w t ξ i) z) =
      𝓕⁻ (cc w t j i) := by
    intro j
    funext z
    unfold cc
    exact (fourierInv_convolution (integrable_of_hmom (hw j)) (integrable_of_hmom (hw i)) z).symm
  simp_rw [hprod]
  simp_rw [fderiv_fourierInv_single (integrable_of_hmom (hc _ i)) (integrable_coord_mul (hc _ i)) y]
  rw [fderiv_fourierInv_single (integrable_of_hmom hQ) (integrable_coord_mul hQ) y i]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Finset.mul_sum]
  have hsum : ∀ j : Fin 3, 1 / (2 * (Real.pi : ℂ)) * ((2 * Real.pi : ℂ) * Complex.I *
      𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * cc w t j i ξ) y) =
      Complex.I * 𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * cc w t j i ξ) y := by
    intro j; field_simp
  simp_rw [hsum]
  field_simp
  ring

end Local

end Navier.Analysis.WienerPhysicalPDE

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPhysicalPDE.fourierInv_convolution
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPhysicalPDE.hasDerivWithinAt_physical_identity
