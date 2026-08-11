import Navier.Analysis.FourierMajorant
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Continuous Lei--Lin critical norm on `R³`

The continuous critical Fourier norm is the literal Lebesgue integral
`∫ |ξ|⁻¹ |f̂(ξ)|`.  This file begins with the singular-weight integrability
lemma needed to put Fourier transforms of Schwartz data into that space.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinSpace

open MeasureTheory Set
open scoped FourierTransform SchwartzMap
open Navier.Analysis.FourierWeightedPlancherel

abbrev ES := EuclideanSpace ℝ (Fin 3)

/-- The continuous homogeneous `X^{-1}` quantity. -/
def normXm1 (f : ES → ℂ) : ℝ :=
  ∫ ξ : ES, ‖ξ‖⁻¹ * ‖f ξ‖

/-- Fourier-side heat evolution on the continuous carrier. -/
def heatMode (ν t : ℝ) (f : ES → ℂ) (ξ : ES) : ℂ :=
  (Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) • f ξ

/-- A Schwartz function on three-dimensional Euclidean space is integrable
against the critical singular Fourier weight.  The proof splits at the unit
ball: `|ξ|⁻¹` is locally integrable in dimension three, while outside that
ball it is dominated by `|ξ|`, whose Schwartz-weighted integral is finite. -/
theorem schwartz_integrable_norm_inv_mul (g : SchwartzMap ES ℂ) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖) := by
  obtain ⟨C, hC0, hC⟩ := g.decay 0 0
  have hbound : ∀ ξ : ES, ‖g ξ‖ ≤ C := by
    intro ξ
    simpa using hC ξ
  have hlocal : LocallyIntegrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖) volume := by
    refine locallyIntegrable_of_norm_le_rpow (μ := volume) (E := ES)
      (F := ℝ) (by norm_num) (C := C) (α := (1 : ℝ)) (by norm_num) ?_ ?_
    · filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
        (norm_nonneg _)), Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left (hbound ξ) (inv_nonneg.mpr (norm_nonneg _))
    · exact ((continuous_norm.aestronglyMeasurable.inv₀).mul
        (g.continuous.norm.aestronglyMeasurable))
  have hnear : IntegrableOn (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖)
      (Metric.closedBall 0 1) volume :=
    hlocal.integrableOn_isCompact (isCompact_closedBall _ _)
  have hfar : IntegrableOn (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖)
      (Metric.closedBall 0 1)ᶜ volume := by
    have hbase : Integrable (fun ξ : ES => ‖ξ‖ ^ 1 * ‖g ξ‖)
        (volume.restrict (Metric.closedBall 0 1)ᶜ) :=
      (g.integrable_pow_mul volume 1).integrableOn
    refine hbase.mono' ?_ ?_
    · exact ((continuous_norm.aestronglyMeasurable.inv₀).mul
        (g.continuous.norm.aestronglyMeasurable))
    · filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with ξ hξ
      have h1 : 1 ≤ ‖ξ‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hξ
      have hi : ‖ξ‖⁻¹ ≤ ‖ξ‖ := by
        rw [inv_le_iff₀ (lt_of_lt_of_le zero_lt_one h1)]
        nlinarith [sq_nonneg (‖ξ‖ - 1)]
      simpa using mul_le_mul_of_nonneg_right hi (norm_nonneg (g ξ))
  rw [← integrableOn_univ, ← compl_union_self (Metric.closedBall (0 : ES) 1),
    integrableOn_union]
  exact ⟨hfar, hnear⟩

/-- The Fourier transform of a Schwartz function belongs to continuous
`X^{-1}`. -/
theorem fourier_schwartz_integrable_Xm1 (f : SchwartzMap ES ℂ) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(𝓕 f) ξ‖) :=
  schwartz_integrable_norm_inv_mul (𝓕 f)

/-- The continuous heat semigroup contracts the literal homogeneous
`X^{-1}(R³)` norm. -/
theorem heat_contracts_Xm1 {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f : ES → ℂ) (hf : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖)) :
    normXm1 (heatMode ν t f) ≤ normXm1 f := by
  have hpoint : ∀ ξ : ES,
      ‖ξ‖⁻¹ * ‖heatMode ν t f ξ‖ ≤ ‖ξ‖⁻¹ * ‖f ξ‖ := by
    intro ξ
    have harg : 0 ≤ ν * ‖ξ‖ ^ 2 * t := by positivity
    have hexp : Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    rw [heatMode, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
      (inv_nonneg.mpr (norm_nonneg _))
  have hheat : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖heatMode ν t f ξ‖) := by
    refine hf.mono' ?_ (Filter.Eventually.of_forall hpoint)
    exact ((Real.continuous_exp.comp
      ((continuous_const.mul (continuous_norm.pow 2)).mul continuous_const).neg).aestronglyMeasurable
      .mul hf.aestronglyMeasurable)
  exact integral_mono hheat hf (Filter.Eventually.of_forall hpoint)

end Navier.Analysis.ContinuousLeiLinSpace

#print axioms Navier.Analysis.ContinuousLeiLinSpace.schwartz_integrable_norm_inv_mul
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_Xm1
#print axioms Navier.Analysis.ContinuousLeiLinSpace.heat_contracts_Xm1
