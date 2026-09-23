import Mathlib

/-!
# The interpolation inequality behind the dissipation threshold

Frequency-side form of `‖Λˢu‖ ≤ ‖u‖^{1/(s+1)} ‖Λ^{s+1}u‖^{s/(s+1)}`: for a weight
`W ≥ 0` (on the Fourier side `W(ξ) = ‖ξ‖²`) and a density `g ≥ 0` (`g = |û|²`),

`∫ W^s g ≤ (∫ g)^{1/(s+1)} (∫ W^{s+1} g)^{s/(s+1)}`,

by Hölder with exponents `s+1` and `(s+1)/s`.  Equivalently
`∫ W^{s+1} g ≥ (∫ W^s g)^{(s+1)/s} (∫ g)^{-1/s}`, the dissipation lower bound
`‖Λ^{s+1}u‖² ≥ ‖Λˢu‖^{2+2/s} E^{-2/s}` used by
`DampedThresholdGronwall.damped_rate_reduction`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace Navier.Analysis.SobolevInterpolation

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Frequency-side interpolation.** -/
theorem lintegral_interpolation {s : ℝ} (hs : 0 < s) {W g : α → ℝ≥0∞}
    (hW : AEMeasurable W μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, W a ^ s * g a ∂μ ≤
      (∫⁻ a, g a ∂μ) ^ (1 / (s + 1)) * (∫⁻ a, W a ^ (s + 1) * g a ∂μ) ^ (s / (s + 1)) := by
  have hp : 1 < s + 1 := by linarith
  have hpq : (s + 1).HolderConjugate ((s + 1) / s) := by
    rw [Real.holderConjugate_iff_eq_conjExponent hp]
    congr 1; ring
  have hs1 : 0 < s + 1 := by linarith
  set f : α → ℝ≥0∞ := fun a => g a ^ (1 / (s + 1)) with hf
  set h : α → ℝ≥0∞ := fun a => (W a ^ (s + 1) * g a) ^ (s / (s + 1)) with hh
  have hfm : AEMeasurable f μ := hg.pow_const _
  have hhm : AEMeasurable h μ := ((hW.pow_const _).mul hg).pow_const _
  have hpt : ∀ a, W a ^ s * g a = (f * h) a := by
    intro a
    simp only [hf, hh, Pi.mul_apply]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
    rw [show (s + 1) * (s / (s + 1)) = s by field_simp]
    calc W a ^ s * g a = W a ^ s * (g a ^ (1 / (s + 1)) * g a ^ (s / (s + 1))) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
            show 1 / (s + 1) + s / (s + 1) = 1 by field_simp; ring, ENNReal.rpow_one]
      _ = g a ^ (1 / (s + 1)) * (W a ^ s * g a ^ (s / (s + 1))) := by ring
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hfm hhm
  have e1 : ∀ a, f a ^ (s + 1) = g a := fun a => by
    simp only [hf]
    rw [← ENNReal.rpow_mul, show 1 / (s + 1) * (s + 1) = 1 by field_simp, ENNReal.rpow_one]
  have e2 : ∀ a, h a ^ ((s + 1) / s) = W a ^ (s + 1) * g a := fun a => by
    simp only [hh]
    rw [← ENNReal.rpow_mul, show s / (s + 1) * ((s + 1) / s) = 1 by field_simp,
      ENNReal.rpow_one]
  simp_rw [e1, e2] at hH
  rw [show 1 / ((s + 1) / s) = s / (s + 1) by field_simp] at hH
  calc ∫⁻ a, W a ^ s * g a ∂μ = ∫⁻ a, (f * h) a ∂μ := lintegral_congr hpt
    _ ≤ _ := hH

end Navier.Analysis.SobolevInterpolation

set_option pp.fullNames true in
#print axioms Navier.Analysis.SobolevInterpolation.lintegral_interpolation
