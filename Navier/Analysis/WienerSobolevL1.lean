import Navier.Analysis.WienerSmoothPath
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The Fourier `H³` weight controls the Wiener (`L¹`) norm

`∫ |f| ≤ C_W^{1/2} · (∫ (1 + |ξ|)⁶ |f|²)^{1/2}` on `ℝ³`, with the universal constant
`C_W = ∫ (1 + |ξ|)^{-6} dξ < ∞` (`lintegral_enorm_le_h3F`, `CW_ne_top`).

This is the quantitative link the piece-restart chain uses: the step length of a Wiener
piece is `ν / (10⁶ (‖ŵ‖²_{L¹} + 1))`, so a uniform bound on the `H³` weight of the
restart profiles gives a uniform step.  The constant depends on nothing but the
dimension; the `H³` bound itself must come from the `T`-uniform damped estimate, not from
per-piece qualitative bounds (ledger/brief requirement, 2026-09-23).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Navier.Analysis.WienerSobolevL1

open Navier.Analysis.ContinuousLeiLinSpace (ES)

/-- The Fourier `H³` weight `∫ (1 + |ξ|)⁶ |f(ξ)|²`. -/
def h3F (f : ES → ℂ) : ℝ≥0∞ := ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ 6) * ‖f ξ‖ₑ ^ 2

/-- The universal constant `∫ (1 + |ξ|)^{-6}`. -/
def CW : ℝ≥0∞ := ∫⁻ ξ : ES, ENNReal.ofReal ((1 + ‖ξ‖) ^ (-(6 : ℝ)))

theorem CW_ne_top : CW ≠ ⊤ := by
  have h : Integrable (fun ξ : ES => (1 + ‖ξ‖) ^ (-(6 : ℝ))) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  have h2 := h.2
  unfold HasFiniteIntegral at h2
  unfold CW
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun ξ => ?_)) h2)
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- **The Wiener norm is bounded by the Fourier `H³` weight.** -/
theorem lintegral_enorm_le_h3F {f : ES → ℂ} (hf : AEMeasurable f) :
    ∫⁻ ξ, ‖f ξ‖ₑ ≤ CW ^ (1 / (2 : ℝ)) * h3F f ^ (1 / (2 : ℝ)) := by
  set F : ES → ℝ≥0∞ := fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ (-(3 : ℝ))) with hF
  set G : ES → ℝ≥0∞ := fun ξ => ENNReal.ofReal ((1 + ‖ξ‖) ^ (3 : ℕ)) * ‖f ξ‖ₑ with hG
  have hFm : AEMeasurable F := by
    refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    exact (measurable_const.add measurable_norm).pow_const _
  have hGm : AEMeasurable G :=
    (ENNReal.measurable_ofReal.comp ((measurable_const.add measurable_norm).pow_const _)
      ).aemeasurable.mul hf.enorm
  have hpt : ∀ ξ, ‖f ξ‖ₑ = (F * G) ξ := by
    intro ξ
    have hpos : 0 < 1 + ‖ξ‖ := by positivity
    simp only [Pi.mul_apply, hF, hG, ← mul_assoc]
    rw [← ENNReal.ofReal_mul (by positivity)]
    have : (1 + ‖ξ‖) ^ (-(3 : ℝ)) * (1 + ‖ξ‖) ^ (3 : ℕ) = 1 := by
      rw [Real.rpow_neg hpos.le, ← Real.rpow_natCast]
      push_cast
      field_simp
    rw [this, ENNReal.ofReal_one, one_mul]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hFm hGm
  have hF2 : ∫⁻ ξ, F ξ ^ (2 : ℝ) = CW := by
    unfold CW
    refine lintegral_congr fun ξ => ?_
    have hpos : 0 < 1 + ‖ξ‖ := by positivity
    simp only [hF]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul hpos.le]
    norm_num
  have hG2 : ∫⁻ ξ, G ξ ^ (2 : ℝ) = h3F f := by
    unfold h3F
    refine lintegral_congr fun ξ => ?_
    simp only [hG]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.rpow_two, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (by positivity), ← pow_mul]
  calc ∫⁻ ξ, ‖f ξ‖ₑ = ∫⁻ ξ, (F * G) ξ := lintegral_congr hpt
    _ ≤ (∫⁻ ξ, F ξ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ ξ, G ξ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        hHolder
    _ = CW ^ (1 / (2 : ℝ)) * h3F f ^ (1 / (2 : ℝ)) := by rw [hF2, hG2]

/-- The real-valued form: `‖f‖_{L¹}² ≤ C_W · H₃(f)`. -/
theorem lintegral_enorm_sq_le {f : ES → ℂ} (hf : AEMeasurable f) :
    (∫⁻ ξ, ‖f ξ‖ₑ) ^ 2 ≤ CW * h3F f := by
  have h := lintegral_enorm_le_h3F hf
  have h2 := pow_le_pow_left₀ zero_le h 2
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

end Navier.Analysis.WienerSobolevL1

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerSobolevL1.lintegral_enorm_sq_le
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerSobolevL1.CW_ne_top
