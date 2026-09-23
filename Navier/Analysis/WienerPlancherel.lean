import Navier.Analysis.WienerPhysicalPDE
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Plancherel inequality on `L¹ ∩ L²`

For `f ∈ L¹(ℝ³)` with `∫ |f|² < ∞`:

`∫⁻ |𝓕⁻ f|² ≤ ∫⁻ |f|²`.

Proof by Gaussian regularisation: for `b > 0`,
`∫ e^{-b|y|²} |𝓕⁻ f(y)|² dy = ∬ f(ξ) conj f(η) K_b(ξ - η)` with the Gaussian
kernel `K_b(z) = ∫ e^{-b|y|² + 2πi⟨z,y⟩} dy ≥ 0` of total mass one; the
arithmetic–geometric bound `|f(ξ)||f(η)| ≤ (|f(ξ)|² + |f(η)|²)/2` bounds the
right side by `∫|f|²`, and monotone convergence `b ↓ 0` concludes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal NNReal FourierTransform ComplexConjugate RealInnerProductSpace Topology

namespace Navier.Analysis.WienerPlancherel

open Navier.Analysis.ContinuousLeiLinSpace (ES)
open Navier.Analysis.WienerSmoothPath
open GaussianFourier

/-! ## The Gaussian kernel -/

/-- `K_b(w) = ∫ e^{-b|y|² + 2πi⟨w,y⟩} dy`, in Mathlib's closed form. -/
def gK (b : ℝ) (w : ES) : ℂ :=
  ((Real.pi : ℂ) / (b : ℂ)) ^ ((Module.finrank ℝ ES : ℂ) / 2) *
    Complex.exp ((2 * Real.pi * Complex.I) ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * (b : ℂ)))

theorem integral_gauss_phase {b : ℝ} (hb : 0 < b) (w : ES) :
    ∫ y : ES, Complex.exp (-(b : ℂ) * (‖y‖ : ℂ) ^ 2 + (2 * Real.pi * Complex.I) * (⟪w, y⟫ : ℂ)) =
      gK b w := by
  have h := integral_cexp_neg_mul_sq_norm_add (V := ES) (b := (b : ℂ)) (by simpa using hb)
    (2 * Real.pi * Complex.I) w
  rw [h]
  rfl

theorem finrank_ES : Module.finrank ℝ ES = 3 := finrank_euclideanSpace_fin

/-- The kernel's modulus. -/
theorem norm_gK {b : ℝ} (hb : 0 < b) (w : ES) :
    ‖gK b w‖ = (Real.pi / b) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / b) * ‖w‖ ^ 2) := by
  unfold gK
  rw [norm_mul, finrank_ES, Complex.norm_exp]
  have h1 : ((Real.pi : ℂ) / (b : ℂ)) = ((Real.pi / b : ℝ) : ℂ) := by push_cast; ring
  rw [h1, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  congr 1
  · congr 1; simp
  · congr 1
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
    have : (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * (b : ℂ)) =
        ((-(Real.pi ^ 2 / b) * ‖w‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      field_simp
      rw [Complex.I_sq]
      ring
    rw [this, Complex.ofReal_re]

theorem lintegral_enorm_gK {b : ℝ} (hb : 0 < b) : ∫⁻ w : ES, ‖gK b w‖ₑ = 1 := by
  have ha : 0 < Real.pi ^ 2 / b := by positivity
  have hint : Integrable (fun w : ES => Real.exp (-(Real.pi ^ 2 / b) * ‖w‖ ^ 2)) := by
    have h := (integrable_cexp_neg_mul_sq_norm_add (V := ES) (b := ((Real.pi ^ 2 / b : ℝ) : ℂ))
      (by rw [Complex.ofReal_re]; exact ha) 0 0).norm
    refine h.congr (Eventually.of_forall fun w => ?_)
    simp only [zero_mul, add_zero]
    rw [Complex.norm_exp]
    congr 1
    push_cast
    simp [← Complex.ofReal_pow, Complex.ofReal_re]
  have hI := integral_rexp_neg_mul_sq_norm (V := ES) ha
  rw [finrank_ES, show ((3 : ℕ) : ℝ) / 2 = (3 : ℝ) / 2 by norm_num] at hI
  simp_rw [← ofReal_norm, norm_gK hb]
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Eventually.of_forall fun w => by positivity), integral_const_mul, hI]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  have : Real.pi / b * (Real.pi / (Real.pi ^ 2 / b)) = 1 := by
    field_simp
  rw [this, Real.one_rpow, ENNReal.ofReal_one]

theorem measurable_gK (b : ℝ) : Measurable (gK b) := by
  unfold gK
  exact measurable_const.mul (Complex.continuous_exp.comp (continuous_const.mul
    ((Complex.continuous_ofReal.comp continuous_norm).pow 2) |>.div_const _)).measurable

/-! ## The Gaussian-weighted identity -/

/-- The phase product: `e^{2πi⟨ξ,y⟩} conj(e^{2πi⟨η,y⟩}) = e^{2πi⟨ξ-η,y⟩}`. -/
theorem exp_phase_mul_conj (ξ η y : ES) :
    Complex.exp (phaseCLM ξ y) * conj (Complex.exp (phaseCLM η y)) =
      Complex.exp ((2 * Real.pi * Complex.I) * (⟪ξ - η, y⟫ : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, phaseCLM_apply, phaseCLM_apply, inner_sub_left]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

theorem continuous_phase : Continuous (fun q : ES × ES => phaseCLM q.1 q.2) :=
  (phaseL.continuous.comp continuous_fst).clm_apply continuous_snd

variable {f : ES → ℂ}

/-- **The Gaussian-weighted identity.** -/
theorem integral_gauss_weight (hfm : StronglyMeasurable f) (hf : Integrable f) {b : ℝ}
    (hb : 0 < b) :
    ∫ y : ES, Complex.exp (-(b : ℂ) * (‖y‖ : ℂ) ^ 2) * (𝓕⁻ f y * conj (𝓕⁻ f y)) =
      ∫ p : ES × ES, f p.1 * conj (f p.2) * gK b (p.1 - p.2) := by
  set A : ES → ES → ℂ := fun y ξ => Complex.exp (phaseCLM ξ y) * f ξ with hA
  have hFy : ∀ y, 𝓕⁻ f y * conj (𝓕⁻ f y) =
      ∫ p : ES × ES, A y p.1 * conj (A y p.2) := by
    intro y
    rw [Measure.volume_eq_prod, integral_prod_mul (fun ξ => A y ξ) (fun η => conj (A y η)),
      integral_conj, fourierInv_eq_exp]
  set H : ES → ES × ES → ℂ := fun y p =>
    Complex.exp (-(b : ℂ) * (‖y‖ : ℂ) ^ 2) * (A y p.1 * conj (A y p.2)) with hH
  have hLHS : ∫ y : ES, Complex.exp (-(b : ℂ) * (‖y‖ : ℂ) ^ 2) * (𝓕⁻ f y * conj (𝓕⁻ f y)) =
      ∫ y : ES, ∫ p : ES × ES, H y p := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hH]
    rw [hFy y, integral_const_mul]
  have hgauss : Integrable (fun y : ES => Real.exp (-b * ‖y‖ ^ 2)) := by
    have h := (integrable_cexp_neg_mul_sq_norm_add (V := ES) (b := (b : ℂ))
      (by rw [Complex.ofReal_re]; exact hb) 0 0).norm
    refine h.congr (Eventually.of_forall fun w => ?_)
    simp only [zero_mul, add_zero]
    rw [Complex.norm_exp]
    congr 1
    simp [← Complex.ofReal_pow, Complex.ofReal_re]
  have hff : Integrable (fun p : ES × ES => ‖f p.1‖ * ‖f p.2‖) (volume : Measure (ES × ES)) := by
    rw [Measure.volume_eq_prod]; exact hf.norm.mul_prod hf.norm
  have hc1 : Continuous (fun q : ES × (ES × ES) =>
      Complex.exp (-(b : ℂ) * (‖q.1‖ : ℂ) ^ 2)) :=
    (continuous_const.mul ((Complex.continuous_ofReal.comp
      (continuous_norm.comp continuous_fst)).pow 2)).cexp
  have hp2 : Continuous (fun q : ES × (ES × ES) => phaseCLM q.2.1 q.1) := by
    simp only [phaseCLM]
    exact (phaseL.continuous.comp (continuous_fst.comp continuous_snd)).clm_apply continuous_fst
  have hp3 : Continuous (fun q : ES × (ES × ES) => phaseCLM q.2.2 q.1) := by
    simp only [phaseCLM]
    exact (phaseL.continuous.comp (continuous_snd.comp continuous_snd)).clm_apply continuous_fst
  have hm1 : StronglyMeasurable (fun q : ES × (ES × ES) => f q.2.1) :=
    hfm.comp_measurable (measurable_fst.comp measurable_snd)
  have hm2 : StronglyMeasurable (fun q : ES × (ES × ES) => f q.2.2) :=
    hfm.comp_measurable (measurable_snd.comp measurable_snd)
  have hHm : StronglyMeasurable (Function.uncurry H) :=
    hc1.stronglyMeasurable.mul ((hp2.cexp.stronglyMeasurable.mul hm1).mul
      (Complex.continuous_conj.comp_stronglyMeasurable (hp3.cexp.stronglyMeasurable.mul hm2)))
  have hnorm : ∀ q : ES × (ES × ES), ‖Function.uncurry H q‖ =
      Real.exp (-b * ‖q.1‖ ^ 2) * (‖f q.2.1‖ * ‖f q.2.2‖) := by
    intro q
    show ‖Complex.exp (-(b : ℂ) * (‖q.1‖ : ℂ) ^ 2) *
      (Complex.exp (phaseCLM q.2.1 q.1) * f q.2.1 *
        conj (Complex.exp (phaseCLM q.2.2 q.1) * f q.2.2))‖ = _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, norm_mul, norm_exp_phase,
      norm_exp_phase, one_mul, one_mul, Complex.norm_exp]
    congr 2
    simp [← Complex.ofReal_pow, Complex.ofReal_re]
  have hHint : Integrable (Function.uncurry H) (volume.prod volume) :=
    (hgauss.mul_prod hff).mono' hHm.aestronglyMeasurable
      (Eventually.of_forall fun q => (hnorm q).le)
  rw [hLHS, integral_integral_swap hHint]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  show ∫ y, H y p = _
  have hpt : ∀ y, H y p = f p.1 * conj (f p.2) *
      Complex.exp (-(b : ℂ) * (‖y‖ : ℂ) ^ 2 +
        (2 * Real.pi * Complex.I) * (⟪p.1 - p.2, y⟫ : ℂ)) := by
    intro y
    simp only [hH, hA, map_mul]
    rw [Complex.exp_add, ← exp_phase_mul_conj]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_gauss_phase hb]

/-! ## The bound -/

theorem lintegral_sq_kernel_le (hfm : StronglyMeasurable f) {b : ℝ} (hb : 0 < b) :
    ∫⁻ p : ES × ES, ‖f p.1‖ₑ * ‖f p.2‖ₑ * ‖gK b (p.1 - p.2)‖ₑ ≤ ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 := by
  have hmf : Measurable (fun ξ => ‖f ξ‖ₑ) := hfm.measurable.enorm
  have hmK : Measurable (fun p : ES × ES => ‖gK b (p.1 - p.2)‖ₑ) :=
    ((measurable_gK b).comp (measurable_fst.sub measurable_snd)).enorm
  -- AM-GM
  have hamgm : ∀ p : ES × ES, ‖f p.1‖ₑ * ‖f p.2‖ₑ * ‖gK b (p.1 - p.2)‖ₑ +
      ‖f p.1‖ₑ * ‖f p.2‖ₑ * ‖gK b (p.1 - p.2)‖ₑ ≤
      ‖f p.1‖ₑ ^ 2 * ‖gK b (p.1 - p.2)‖ₑ + ‖f p.2‖ₑ ^ 2 * ‖gK b (p.1 - p.2)‖ₑ := by
    intro p
    simp only [← ofReal_norm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hk := norm_nonneg (gK b (p.1 - p.2))
    nlinarith [mul_nonneg hk (sq_nonneg (‖f p.1‖ - ‖f p.2‖))]
  have hm1 : Measurable (fun p : ES × ES => ‖f p.1‖ₑ ^ 2 * ‖gK b (p.1 - p.2)‖ₑ) :=
    ((hmf.comp measurable_fst).pow_const 2).mul hmK
  have hm2 : Measurable (fun p : ES × ES => ‖f p.2‖ₑ ^ 2 * ‖gK b (p.1 - p.2)‖ₑ) :=
    ((hmf.comp measurable_snd).pow_const 2).mul hmK
  have h1 : ∫⁻ p : ES × ES, ‖f p.1‖ₑ ^ 2 * ‖gK b (p.1 - p.2)‖ₑ = ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hm1.aemeasurable]
    refine lintegral_congr fun ξ => ?_
    have hk : Measurable (fun y : ES => ‖gK b (ξ - y)‖ₑ) :=
      ((measurable_gK b).comp (measurable_const.sub measurable_id)).enorm
    show ∫⁻ y : ES, ‖f ξ‖ₑ ^ 2 * ‖gK b (ξ - y)‖ₑ = _
    rw [lintegral_const_mul _ hk]
    have := lintegral_sub_left_eq_self (μ := (volume : Measure ES)) (fun z => ‖gK b z‖ₑ) ξ
    rw [this, lintegral_enorm_gK hb, mul_one]
  have h2 : ∫⁻ p : ES × ES, ‖f p.2‖ₑ ^ 2 * ‖gK b (p.1 - p.2)‖ₑ = ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 := by
    rw [Measure.volume_eq_prod, lintegral_prod_symm _ hm2.aemeasurable]
    refine lintegral_congr fun η => ?_
    have hk : Measurable (fun x : ES => ‖gK b (x - η)‖ₑ) :=
      ((measurable_gK b).comp (measurable_id.sub measurable_const)).enorm
    show ∫⁻ x : ES, ‖f η‖ₑ ^ 2 * ‖gK b (x - η)‖ₑ = _
    rw [lintegral_const_mul _ hk]
    have := lintegral_sub_right_eq_self (μ := (volume : Measure ES)) (fun z => ‖gK b z‖ₑ) η
    rw [this, lintegral_enorm_gK hb, mul_one]
  have hX : Measurable (fun p : ES × ES => ‖f p.1‖ₑ * ‖f p.2‖ₑ * ‖gK b (p.1 - p.2)‖ₑ) :=
    ((hmf.comp measurable_fst).mul (hmf.comp measurable_snd)).mul hmK
  have hsum : ∫⁻ p : ES × ES, (‖f p.1‖ₑ * ‖f p.2‖ₑ * ‖gK b (p.1 - p.2)‖ₑ +
      ‖f p.1‖ₑ * ‖f p.2‖ₑ * ‖gK b (p.1 - p.2)‖ₑ) ≤
      ∫⁻ p : ES × ES, (‖f p.1‖ₑ ^ 2 * ‖gK b (p.1 - p.2)‖ₑ +
        ‖f p.2‖ₑ ^ 2 * ‖gK b (p.1 - p.2)‖ₑ) := lintegral_mono hamgm
  rw [lintegral_add_left hX, lintegral_add_left hm1, h1, h2, ← two_mul, ← two_mul] at hsum
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hsum

theorem norm_fourierInv_le_integral (f : ES → ℂ) (y : ES) : ‖𝓕⁻ f y‖ ≤ ∫ ξ, ‖f ξ‖ := by
  rw [fourierInv_eq_exp]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [norm_mul, norm_exp_phase, one_mul]

theorem gauss_weight_le (hfm : StronglyMeasurable f) (hf : Integrable f) {b : ℝ} (hb : 0 < b) :
    ∫⁻ y : ES, ENNReal.ofReal (Real.exp (-b * ‖y‖ ^ 2)) * ‖𝓕⁻ f y‖ₑ ^ 2 ≤
      ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 := by
  set g : ES → ℝ := fun y => Real.exp (-b * ‖y‖ ^ 2) * ‖𝓕⁻ f y‖ ^ 2 with hg
  have hgauss : Integrable (fun y : ES => Real.exp (-b * ‖y‖ ^ 2)) := by
    have h := (integrable_cexp_neg_mul_sq_norm_add (V := ES) (b := (b : ℂ))
      (by rw [Complex.ofReal_re]; exact hb) 0 0).norm
    refine h.congr (Eventually.of_forall fun w => ?_)
    simp only [zero_mul, add_zero]
    rw [Complex.norm_exp]
    congr 1
    simp [← Complex.ofReal_pow, Complex.ofReal_re]
  have hFc : Continuous (𝓕⁻ f) := continuous_fourierInv hf
  set C : ℝ := ∫ ξ, ‖f ξ‖
  have hgint : Integrable g := by
    refine (hgauss.mul_const (C ^ 2)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2))).mul
        ((continuous_norm.comp hFc).pow 2)).aestronglyMeasurable
    · simp only [hg, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_pow,
        abs_norm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (norm_fourierInv_le_integral f y) 2) (Real.exp_pos _).le
  have hg0 : ∀ y, 0 ≤ g y := fun y => by positivity
  have hL : ∫⁻ y : ES, ENNReal.ofReal (Real.exp (-b * ‖y‖ ^ 2)) * ‖𝓕⁻ f y‖ₑ ^ 2 =
      ENNReal.ofReal (∫ y, g y) := by
    rw [ofReal_integral_eq_lintegral_ofReal hgint (Eventually.of_forall hg0)]
    refine lintegral_congr fun y => ?_
    rw [hg, ENNReal.ofReal_mul (Real.exp_pos _).le, ← ofReal_norm,
      ENNReal.ofReal_pow (norm_nonneg _)]
  have hcx : ∀ y : ES, Complex.exp (-(b : ℂ) * (‖y‖ : ℂ) ^ 2) * (𝓕⁻ f y * conj (𝓕⁻ f y)) =
      ((g y : ℝ) : ℂ) := by
    intro y
    rw [Complex.mul_conj, hg, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hI := integral_gauss_weight hfm hf hb
  simp_rw [hcx] at hI
  rw [integral_complex_ofReal] at hI
  have hR : ENNReal.ofReal (∫ y, g y) = ‖((∫ y, g y : ℝ) : ℂ)‖ₑ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg hg0)]
  rw [hL, hR, hI]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans (le_of_eq ?_) (lintegral_sq_kernel_le hfm hb)
  refine lintegral_congr fun p => ?_
  rw [enorm_mul, enorm_mul, ← ofReal_norm ((starRingEnd ℂ) (f p.2)), Complex.norm_conj, ofReal_norm]

/-- **The Plancherel inequality on `L¹ ∩ L²`**: `∫⁻ |𝓕⁻ f|² ≤ ∫⁻ |f|²`. -/
theorem lintegral_sq_fourierInv_le (hfm : StronglyMeasurable f) (hf : Integrable f) :
    ∫⁻ y : ES, ‖𝓕⁻ f y‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 := by
  set F : ℕ → ES → ℝ≥0∞ := fun n y =>
    ENNReal.ofReal (Real.exp (-(1 / ((n : ℝ) + 1)) * ‖y‖ ^ 2)) * ‖𝓕⁻ f y‖ₑ ^ 2 with hF
  have hFc : Continuous (𝓕⁻ f) := continuous_fourierInv hf
  have hmeas : ∀ n, AEMeasurable (F n) := fun n =>
    ((ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_norm.pow 2)))).measurable.mul
      ((continuous_enorm.comp hFc).measurable.pow_const 2)).aemeasurable
  have hmono : ∀ᵐ y ∂(volume : Measure ES), Monotone fun n => F n y := by
    refine Eventually.of_forall fun y n m hnm => ?_
    refine mul_le_mul_left ?_ _
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have h1 : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    nlinarith [sq_nonneg ‖y‖]
  have hlim : ∀ᵐ y ∂(volume : Measure ES),
      Tendsto (fun n => F n y) atTop (𝓝 (‖𝓕⁻ f y‖ₑ ^ 2)) := by
    refine Eventually.of_forall fun y => ?_
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(1 / ((n : ℝ) + 1)) * ‖y‖ ^ 2)))
        atTop (𝓝 1) := by
      have hc : Continuous (fun s : ℝ => ENNReal.ofReal (Real.exp (-s * ‖y‖ ^ 2))) :=
        ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
          (continuous_neg.mul continuous_const))
      have := (hc.tendsto 0).comp h0
      simpa [Function.comp_def] using this
    have := ENNReal.Tendsto.mul_const h1 (Or.inr (ENNReal.pow_ne_top (n := 2) (enorm_ne_top (x := 𝓕⁻ f y))))
    simpa only [one_mul] using this
  have ht := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim
  refine le_of_tendsto' ht fun n => ?_
  have hb : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact gauss_weight_le hfm hf hb

end Navier.Analysis.WienerPlancherel

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPlancherel.lintegral_sq_fourierInv_le
