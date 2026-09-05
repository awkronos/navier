import Navier.Analysis.GalerkinLocalizedBessel
import Navier.Analysis.FourierTransverseProjection

/-!
# Localized Bessel bounds for transverse Fourier vectors

The input may have a longitudinal component. Pairing with transverse vectors
removes it, so the localized coefficient bound involves only the actual
transverse part. This is the estimate required by the all-input Galerkin
stability statement.
-/

noncomputable section
open MeasureTheory

namespace Navier.Analysis.GalerkinTransverseBessel

open FourierTransverseProjection GalerkinLocalizedBessel

local instance : InnerProductSpace ℝ CS := InnerProductSpace.rclikeToReal ℂ CS
attribute [local instance 2000] MeasureTheory.L2.innerProductSpace

theorem continuous_frequencyVector : Continuous frequencyVector := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
  exact continuous_pi fun i => Complex.continuous_ofReal.comp (by fun_prop)

/-- The projection multiplier is measurable, including at the origin. -/
theorem measurable_transverseProjection (f : ES → CS) (hf : Measurable f) :
    Measurable (fun ξ => transverseProjection ξ (f ξ)) := by
  simp_rw [transverseProjection_eq]
  have hξ := continuous_frequencyVector.measurable
  exact hf.sub (((hξ.inner hf).div
    (Complex.measurable_ofReal.comp (hξ.norm.pow_const 2))).smul hξ)

/-- The actual pointwise projection preserves square integrability. -/
theorem memLp_transverseProjection (f : ES → CS)
    (hf : MemLp f 2 (volume : Measure ES)) :
    MemLp (fun ξ => transverseProjection ξ (f ξ)) 2 (volume : Measure ES) := by
  have hξ : AEStronglyMeasurable frequencyVector (volume : Measure ES) :=
    continuous_frequencyVector.aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun ξ => transverseProjection ξ (f ξ)) volume := by
    simp_rw [transverseProjection_eq]
    exact hf.1.sub (((hξ.inner hf.1).div₀
      (Complex.continuous_ofReal.comp_aestronglyMeasurable (hξ.norm.pow 2))).smul hξ)
  exact hf.mono hm (Filter.Eventually.of_forall fun ξ =>
    transverseProjection_norm_le ξ (f ξ))

/-- Coefficients of a transverse orthonormal family supported in a band are
bounded by the transverse input mass in that band, for every `L²` input. -/
theorem sum_inner_sq_le_transverse_integralOn
    {ι : Type*} [Fintype ι] (w : ι → ES → CS)
    (hw : ∀ i, MemLp (w i) 2 (volume : Measure ES))
    (horth : Orthonormal ℝ (fun i => (hw i).toLp (w i)))
    (f : ES → CS) (hf : MemLp f 2 (volume : Measure ES))
    {B : Set ES} (hB : MeasurableSet B)
    (hsupport : ∀ i, ∀ᵐ ξ, ξ ∉ B → w i ξ = 0)
    (htransverse : ∀ i, ∀ᵐ ξ, inner ℂ (frequencyVector ξ) (w i ξ) = 0) :
    (∑ i, ‖inner ℝ ((hw i).toLp (w i)) (hf.toLp f)‖ ^ 2) ≤
      ∫ ξ in B, ‖transverseProjection ξ (f ξ)‖ ^ 2 := by
  let g := fun ξ => transverseProjection ξ (f ξ)
  have hg := memLp_transverseProjection f hf
  have hinner : ∀ i, inner ℝ ((hw i).toLp (w i)) (hf.toLp f) =
      inner ℝ ((hw i).toLp (w i)) (hg.toLp g) := by
    intro i
    rw [L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hw i).coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
      htransverse i] with ξ hξw hξf hξg hξt
    rw [hξw, hξf, hξg]
    change (inner ℂ (w i ξ) (f ξ)).re =
      (inner ℂ (w i ξ) (transverseProjection ξ (f ξ))).re
    rw [inner_transverseProjection_right ξ (w i ξ) (f ξ) hξt]
  simp_rw [hinner]
  exact sum_inner_sq_le_integralOn w hw horth g hg hB hsupport

/-- In a bounded annulus, the lower radius times the coefficient mass is
controlled by the input's curl-symbol energy in that same annulus. The input
is arbitrary, and both integrals exist as Bochner integrals. -/
theorem lowerRadius_sq_mul_sum_inner_sq_le_curlSymbolIntegral
    {ι : Type*} [Fintype ι] (w : ι → ES → CS)
    (hw : ∀ i, MemLp (w i) 2 (volume : Measure ES))
    (horth : Orthonormal ℝ (fun i => (hw i).toLp (w i)))
    (f : ES → CS) (hf : MemLp f 2 (volume : Measure ES))
    {B : Set ES} (hB : MeasurableSet B) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hband : ∀ ξ ∈ B, a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b)
    (hsupport : ∀ i, ∀ᵐ ξ, ξ ∉ B → w i ξ = 0)
    (htransverse : ∀ i, ∀ᵐ ξ, inner ℂ (frequencyVector ξ) (w i ξ) = 0) :
    a ^ 2 * (∑ i, ‖inner ℝ ((hw i).toLp (w i)) (hf.toLp f)‖ ^ 2) ≤
      ∫ ξ in B, curlSymbolEnergy ξ (f ξ) := by
  let g := fun ξ => transverseProjection ξ (f ξ)
  have hg := memLp_transverseProjection f hf
  have hgint : Integrable (fun ξ => ‖g ξ‖ ^ 2) (volume : Measure ES) :=
    (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  have hm : AEStronglyMeasurable (fun ξ => ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2)
      (volume : Measure ES) :=
    (continuous_id.norm.pow 2).aestronglyMeasurable.mul (hg.1.norm.pow 2)
  have hweighted : IntegrableOn (fun ξ => ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) B := by
    refine (hgint.restrict.const_mul (b ^ 2)).mono' hm.restrict ?_
    filter_upwards [ae_restrict_mem hB] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg ξ) (hband ξ hξ).2 2) (sq_nonneg _)
  have hcompare : a ^ 2 * (∫ ξ in B, ‖g ξ‖ ^ 2) ≤
      ∫ ξ in B, ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hgint.restrict.const_mul (a ^ 2)) hweighted
    filter_upwards [ae_restrict_mem hB] with ξ hξ
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ ha (hband ξ hξ).1 2) (sq_nonneg _)
  have hbessel := sum_inner_sq_le_transverse_integralOn
    w hw horth f hf hB hsupport htransverse
  refine (mul_le_mul_of_nonneg_left hbessel (sq_nonneg a)).trans
    (hcompare.trans_eq ?_)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => transverseProjection_weighted_norm_sq ξ (f ξ)

end Navier.Analysis.GalerkinTransverseBessel
