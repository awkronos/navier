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
open scoped FourierTransform SchwartzMap Convolution
open Navier.Analysis.FourierWeightedPlancherel

abbrev ES := EuclideanSpace ℝ (Fin 3)

/-- The continuous homogeneous `X^{-1}` quantity. -/
def normXm1 (f : ES → ℂ) : ℝ :=
  ∫ ξ : ES, ‖ξ‖⁻¹ * ‖f ξ‖

/-- The continuous homogeneous `X¹` quantity. -/
def normX1 (f : ES → ℂ) : ℝ :=
  ∫ ξ : ES, ‖ξ‖ * ‖f ξ‖

/-- Fourier-side heat evolution on the continuous carrier. -/
def heatMode (ν t : ℝ) (f : ES → ℂ) (ξ : ES) : ℂ :=
  ((Real.exp (-(ν * ((‖ξ‖ : ℝ) ^ 2) * t)) : ℝ) : ℂ) * f ξ

/-- Scalar continuous Fourier convolution, with Lebesgue measure on `R³`. -/
def convolution (f g : ES → ℝ) : ES → ℝ :=
  f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g

/-- The continuous `X⁰` (Wiener) mass for a nonnegative Fourier density. -/
def normX0 (f : ES → ℝ) : ℝ := ∫ ξ : ES, f ξ

/-- Fubini/Tonelli's exact convolution mass identity on the actual continuous
carrier.  This is the continuous replacement for the lattice `tsum` identity
used by the discrete Lei--Lin prototype. -/
theorem normX0_convolution_eq (f g : ES → ℝ) (hf : Integrable f) (hg : Integrable g) :
    normX0 (convolution f g) = normX0 f * normX0 g := by
  exact integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hf hg

/-- The actual complex Fourier convolution of two Schwartz Fourier profiles
is an `L¹(R³)` function.  This is the measure-theoretic carrier on which the
Leray-projected Navier bilinear operator must next be bounded. -/
theorem fourier_schwartz_convolution_integrable (f g : SchwartzMap ES ℂ) :
    Integrable (((𝓕 f : SchwartzMap ES ℂ) : ES → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      ((𝓕 g : SchwartzMap ES ℂ) : ES → ℂ)) :=
  (𝓕 f : SchwartzMap ES ℂ).integrable.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (𝓕 g : SchwartzMap ES ℂ).integrable

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
      have hle := mul_le_mul_of_nonneg_left (hbound ξ)
        (inv_nonneg.mpr (norm_nonneg ξ))
      simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg (g ξ))),
        Real.rpow_neg_one, mul_comm] using hle
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
      have h1' : 1 < ‖ξ‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hξ
      have h1 : 1 ≤ ‖ξ‖ := h1'.le
      have hi : ‖ξ‖⁻¹ ≤ ‖ξ‖ := by
        rw [inv_le_iff_one_le_mul₀ (lt_of_lt_of_le zero_lt_one h1)]
        nlinarith
      simpa using mul_le_mul_of_nonneg_right hi (norm_nonneg (g ξ))
  rw [← integrableOn_univ, ← compl_union_self (Metric.closedBall (0 : ES) 1),
    integrableOn_union]
  exact ⟨hfar, hnear⟩

/-- The Fourier transform of a Schwartz function belongs to continuous
`X^{-1}`. -/
theorem fourier_schwartz_integrable_Xm1 (f : SchwartzMap ES ℂ) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(𝓕 f) ξ‖) :=
  schwartz_integrable_norm_inv_mul (𝓕 f)

/-- Schwartz functions have finite continuous `X¹` mass. -/
theorem schwartz_integrable_X1 (g : SchwartzMap ES ℂ) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖g ξ‖) := by
  simpa using g.integrable_pow_mul volume 1

/-- Fourier transforms of Schwartz functions have finite continuous `X¹`
mass.  Together with `fourier_schwartz_integrable_Xm1`, this puts the free
Schwartz Fourier carrier in both endpoint norms needed by Lei--Lin. -/
theorem fourier_schwartz_integrable_X1 (f : SchwartzMap ES ℂ) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖(𝓕 f) ξ‖) :=
  schwartz_integrable_X1 (𝓕 f)

/-- The continuous heat semigroup contracts the literal homogeneous
`X^{-1}(R³)` norm. -/
theorem heat_contracts_Xm1 {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (f : ES → ℂ) (hf : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖)) :
    normXm1 (heatMode ν t f) ≤ normXm1 f := by
  have heat_norm : ∀ ξ : ES,
      ‖heatMode ν t f ξ‖ = Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖f ξ‖ := by
    intro ξ
    rw [heatMode, norm_mul, Complex.norm_real]
    simp [abs_of_nonneg (Real.exp_nonneg _)]
  have hpoint : ∀ ξ : ES,
      ‖ξ‖⁻¹ * ‖heatMode ν t f ξ‖ ≤ ‖ξ‖⁻¹ * ‖f ξ‖ := by
    intro ξ
    have harg : 0 ≤ ν * ‖ξ‖ ^ 2 * t := by positivity
    have hexp : Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hprod : Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖f ξ‖ ≤ ‖f ξ‖ := by
      simpa using mul_le_mul_of_nonneg_right hexp (norm_nonneg (f ξ))
    rw [heat_norm]
    exact mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (norm_nonneg _))
  have hheat : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖heatMode ν t f ξ‖) := by
    have heq : (fun ξ : ES => ‖ξ‖⁻¹ * ‖heatMode ν t f ξ‖) =
        fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖f ξ‖) := by
      funext ξ
      rw [heat_norm]
      ring
    rw [heq]
    refine hf.mono' ?_ ?_
    · have hmeas : AEStronglyMeasurable
          (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) :=
        (Real.continuous_exp.comp
          ((continuous_const.mul (continuous_norm.pow 2)).mul continuous_const).neg).aestronglyMeasurable
      exact hmeas.mul hf.aestronglyMeasurable
    · filter_upwards with ξ
      have h := hpoint ξ
      rw [heat_norm] at h
      simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg (f ξ))),
        mul_assoc, mul_left_comm, mul_comm] using h
  exact integral_mono hheat hf hpoint

end Navier.Analysis.ContinuousLeiLinSpace

#print axioms Navier.Analysis.ContinuousLeiLinSpace.schwartz_integrable_norm_inv_mul
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_Xm1
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_X1
#print axioms Navier.Analysis.ContinuousLeiLinSpace.heat_contracts_Xm1
#print axioms Navier.Analysis.ContinuousLeiLinSpace.normX0_convolution_eq
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_convolution_integrable
