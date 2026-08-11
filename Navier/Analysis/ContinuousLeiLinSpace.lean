import Navier.Analysis.FourierMajorant
import Navier.Analysis.ComplexLerayNorm
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
open Navier.Analysis.FourierMajorant
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm

abbrev ES := EuclideanSpace ℝ (Fin 3)
abbrev ComplexSpace := Fin 3 → ℂ
abbrev ComplexE3 := EuclideanSpace ℂ (Fin 3)

/-- The continuous homogeneous `X^{-1}` quantity. -/
def normXm1 (f : ES → ℂ) : ℝ :=
  ∫ ξ : ES, ‖ξ‖⁻¹ * ‖f ξ‖

/-- The continuous homogeneous `X¹` quantity. -/
def normX1 (f : ES → ℂ) : ℝ :=
  ∫ ξ : ES, ‖ξ‖ * ‖f ξ‖

/-- Fourier-side heat evolution on the continuous carrier. -/
def heatMode (ν t : ℝ) (f : ES → ℂ) (ξ : ES) : ℂ :=
  ((Real.exp (-(ν * ((‖ξ‖ : ℝ) ^ 2) * t)) : ℝ) : ℂ) * f ξ

/-- The continuous Fourier Leray multiplier.  The frequency is transported
from Euclidean `R³` to the coordinate carrier, and the underlying canonical
projection is total at `ξ = 0` (where it is the identity). -/
def continuousLeray (ξ : ES) (z : ComplexSpace) : ComplexSpace :=
  complexLeray (spaceProj ξ) z

/-- The same continuous-frequency multiplier on the Hermitian Euclidean
carrier, which is the normed carrier used for Bochner integrability. -/
def continuousLerayE (ξ : ES) (z : ComplexE3) : ComplexE3 :=
  complexEuclideanLeray (spaceProj ξ) z

/-- The real-to-complex frequency embedding is continuous. -/
theorem continuous_complexFrequency : Continuous (complexFrequency : Space → ComplexE3) := by
  unfold complexFrequency complexEuclideanPoint complexOfReal complexOfParts
  apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℂ)).comp
  apply continuous_pi
  intro i
  apply Continuous.add
  · exact Complex.continuous_ofReal.comp (continuous_apply i)
  · exact continuous_const.mul (Complex.continuous_ofReal.comp continuous_const)

/-- The continuous multiplier is exactly identity at zero frequency. -/
@[simp] theorem continuousLeray_zero (z : ComplexSpace) :
    continuousLeray 0 z = z := by
  simp [continuousLeray, spaceProj]

/-- Pointwise Hermitian norm contraction of the continuous Leray multiplier. -/
theorem continuousLeray_norm_le (ξ : ES) (z : ComplexSpace) :
    complexEuclideanNorm (continuousLeray ξ z) ≤ complexEuclideanNorm z := by
  exact complexEuclideanNorm_complexLeray_le (spaceProj ξ) z

/-- The Hermitian-carrier multiplier contracts pointwise. -/
theorem continuousLerayE_norm_le (ξ : ES) (z : ComplexE3) :
    ‖continuousLerayE ξ z‖ ≤ ‖z‖ :=
  complexEuclideanLeray_norm_le (spaceProj ξ) z

/-- Once the (a.e.) measurability of a projected Fourier profile is supplied,
the Leray contraction promotes integrability of its Hermitian norm.  This is
the exact Bochner consumer used by the future convolution estimate; no
discrete carrier is involved. -/
theorem integrable_continuousLerayE_of_aestronglyMeasurable
    (v : ES → ComplexE3)
    (hv_meas : AEStronglyMeasurable (fun ξ => continuousLerayE ξ (v ξ)))
    (hv : Integrable (fun ξ => ‖v ξ‖)) :
    Integrable (fun ξ => continuousLerayE ξ (v ξ)) := by
  refine hv.mono' hv_meas ?_
  filter_upwards with ξ
  exact continuousLerayE_norm_le ξ (v ξ)

/-- The totalized continuous Leray multiplier is a.e. strongly measurable on
measurable Hermitian Fourier profiles.  Its exceptional directional
discontinuity at the single frequency `0` is absorbed by measurability of the
explicit algebraic formula. -/
theorem continuousLerayE_aestronglyMeasurable (v : ES → ComplexE3)
    (hv : AEStronglyMeasurable v) :
    AEStronglyMeasurable (fun ξ => continuousLerayE ξ (v ξ)) := by
  have hformula : (fun ξ : ES => continuousLerayE ξ (v ξ)) =
      fun ξ : ES => v ξ -
        (inner ℂ (complexFrequency (spaceProj ξ)) (v ξ) /
          ((‖complexFrequency (spaceProj ξ)‖ ^ 2 : ℝ) : ℂ)) •
          complexFrequency (spaceProj ξ) := by
    funext ξ
    exact complexEuclideanLeray_formula (spaceProj ξ) (v ξ)
  rw [hformula]
  simp only [div_eq_mul_inv]
  have hq : Continuous (fun ξ : ES => complexFrequency (spaceProj ξ)) :=
    continuous_complexFrequency.comp spaceProj.continuous
  have hqM : AEStronglyMeasurable (fun ξ : ES => complexFrequency (spaceProj ξ)) :=
    hq.aestronglyMeasurable
  have hden : AEStronglyMeasurable
      (fun ξ : ES => ((‖complexFrequency (spaceProj ξ)‖ ^ 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp (hq.norm.pow 2)).aestronglyMeasurable
  exact hv.sub ((hqM.inner hv).mul hden.inv₀ |>.smul hqM)

/-- The continuous Leray multiplier preserves Bochner integrability of
Hermitian Fourier profiles. -/
theorem integrable_continuousLerayE (v : ES → ComplexE3) (hv : Integrable v) :
    Integrable (fun ξ => continuousLerayE ξ (v ξ)) :=
  integrable_continuousLerayE_of_aestronglyMeasurable v
    (continuousLerayE_aestronglyMeasurable v hv.aestronglyMeasurable) hv.norm

/-- Every nonnegative Fourier weight is preserved under the continuous Leray
multiplier pointwise.  This is the projection half of the future weighted
convolution estimate; its analytic measurability/convolution half remains
separate. -/
theorem continuousLeray_weighted_norm_le (w : ES → ℝ) (ξ : ES) (z : ComplexSpace)
    (hw : 0 ≤ w ξ) :
    w ξ * complexEuclideanNorm (continuousLeray ξ z) ≤
      w ξ * complexEuclideanNorm z :=
  mul_le_mul_of_nonneg_left (continuousLeray_norm_le ξ z) hw

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

/-- The frequency triangle inequality in the form used to distribute one
derivative across a Fourier convolution. -/
theorem frequency_triangle (ξ η : ES) :
    ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
  calc
    ‖ξ‖ = ‖η + (ξ - η)‖ := by
      congr 1
      abel
    _ ≤ ‖η‖ + ‖ξ - η‖ := norm_add_le _ _

/-- Pointwise derivative allocation for nonnegative convolution profiles.
This is the algebraic kernel of the continuous Lei--Lin bilinear estimate:
the output frequency weight is assigned to either input frequency. -/
theorem frequency_weighted_product_split (ξ η : ES) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖ξ‖ * (a * b) ≤ (‖η‖ * a) * b + a * (‖ξ - η‖ * b) := by
  have hfreq := frequency_triangle ξ η
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  calc
    ‖ξ‖ * (a * b) ≤ (‖η‖ + ‖ξ - η‖) * (a * b) :=
      mul_le_mul_of_nonneg_right hfreq hab
    _ = (‖η‖ * a) * b + a * (‖ξ - η‖ * b) := by ring

/-- The preceding derivative allocation specialized to complex Fourier
profiles.  It is ready for Tonelli and the convolution change of variables. -/
theorem frequency_weighted_norm_product_split (f g : ES → ℂ) (ξ η : ES) :
    ‖ξ‖ * (‖f η‖ * ‖g (ξ - η)‖) ≤
      (‖η‖ * ‖f η‖) * ‖g (ξ - η)‖ +
        ‖f η‖ * (‖ξ - η‖ * ‖g (ξ - η)‖) :=
  frequency_weighted_product_split ξ η (norm_nonneg _) (norm_nonneg _)

/-- A pointwise weighted convolution estimate.  The hypotheses expose exactly
the three integrability obligations which Tonelli supplies for Schwartz
profiles; no discrete-frequency replacement is used. -/
theorem frequency_weighted_convolution_pointwise (f g : ES → ℝ)
    (hf : ∀ η, 0 ≤ f η) (hg : ∀ η, 0 ≤ g η) (ξ : ES)
    (hfg : Integrable (fun η : ES => f η * g (ξ - η)))
    (hl : Integrable (fun η : ES => (‖η‖ * f η) * g (ξ - η)))
    (hr : Integrable (fun η : ES => f η * (‖ξ - η‖ * g (ξ - η)))) :
    ‖ξ‖ * convolution f g ξ ≤
      convolution (fun η => ‖η‖ * f η) g ξ +
        convolution f (fun η => ‖η‖ * g η) ξ := by
  change ‖ξ‖ * (∫ η : ES, f η * g (ξ - η)) ≤
    (∫ η : ES, (‖η‖ * f η) * g (ξ - η)) +
      ∫ η : ES, f η * (‖ξ - η‖ * g (ξ - η))
  rw [← integral_const_mul,
    ← integral_add hl hr]
  apply integral_mono (hfg.const_mul ‖ξ‖) (hl.add hr)
  intro η
  exact frequency_weighted_product_split ξ η (hf η) (hg (ξ - η))

/-- The first derivative-allocation kernel is integrable on frequency space
times frequency space.  This is the Tonelli input for the `X¹(f) X⁰(g)`
term. -/
theorem integrable_left_frequency_kernel (f g : ES → ℝ)
    (hf : Integrable (fun η => ‖η‖ * f η)) (hg : Integrable g) :
    Integrable (fun p : ES × ES => (‖p.2‖ * f p.2) * g (p.1 - p.2))
      (volume.prod volume) := by
  simpa using hf.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg

/-- The second derivative-allocation kernel is integrable on the product
frequency space. -/
theorem integrable_right_frequency_kernel (f g : ES → ℝ)
    (hf : Integrable f) (hg : Integrable (fun η => ‖η‖ * g η)) :
    Integrable (fun p : ES × ES => f p.2 * (‖p.1 - p.2‖ * g (p.1 - p.2)))
      (volume.prod volume) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hf.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg

/-- Tonelli and the continuous convolution identity factor the first product
kernel into its two Fourier masses. -/
theorem integral_left_frequency_kernel (f g : ES → ℝ)
    (hf : Integrable (fun η => ‖η‖ * f η)) (hg : Integrable g) :
    (∫ p : ES × ES, (‖p.2‖ * f p.2) * g (p.1 - p.2) ∂(volume.prod volume)) =
      (∫ η : ES, ‖η‖ * f η) * normX0 g := by
  rw [integral_prod _ (integrable_left_frequency_kernel f g hf hg)]
  exact normX0_convolution_eq (fun η => ‖η‖ * f η) g hf hg

/-- Tonelli and translation invariance factor the second product kernel. -/
theorem integral_right_frequency_kernel (f g : ES → ℝ)
    (hf : Integrable f) (hg : Integrable (fun η => ‖η‖ * g η)) :
    (∫ p : ES × ES, f p.2 * (‖p.1 - p.2‖ * g (p.1 - p.2)) ∂(volume.prod volume)) =
      normX0 f * (∫ η : ES, ‖η‖ * g η) := by
  rw [integral_prod _ (integrable_right_frequency_kernel f g hf hg)]
  exact normX0_convolution_eq f (fun η => ‖η‖ * g η) hf hg

/-- For Fourier transforms of Schwartz data, the first Tonelli kernel is
integrable on the actual continuous product frequency space. -/
theorem fourier_schwartz_integrable_left_frequency_kernel (f g : SchwartzMap ES ℂ) :
    Integrable
      (fun p : ES × ES =>
        (‖p.2‖ * ‖(𝓕 f) p.2‖) * ‖(𝓕 g) (p.1 - p.2)‖)
      (volume.prod volume) :=
  integrable_left_frequency_kernel _ _ (fourier_schwartz_integrable_X1 f)
    (𝓕 g).integrable.norm

/-- The symmetric Schwartz Fourier kernel is likewise Tonelli-integrable. -/
theorem fourier_schwartz_integrable_right_frequency_kernel (f g : SchwartzMap ES ℂ) :
    Integrable
      (fun p : ES × ES => ‖(𝓕 f) p.2‖ *
        (‖p.1 - p.2‖ * ‖(𝓕 g) (p.1 - p.2)‖))
      (volume.prod volume) :=
  integrable_right_frequency_kernel _ _ (𝓕 f).integrable.norm
    (fourier_schwartz_integrable_X1 g)

/-- Product-space Fubini supplies an integrable (hence a.e. measurable)
continuous convolution representative for scalar `L¹` profiles. -/
theorem integrable_scalar_convolution (f g : ES → ℝ)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (convolution f g) := by
  change Integrable (fun ξ : ES => ∫ η : ES, f η * g (ξ - η))
  simpa using
    (hf.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg).integral_prod_left

/-- The weighted convolution inequality holds almost everywhere under the
four `L¹` profile hypotheses.  This is the form appropriate for Bochner
integration; demanding an everywhere representative is unnecessary. -/
theorem ae_frequency_weighted_convolution_pointwise (f g : ES → ℝ)
    (hf0 : Integrable f) (hg0 : Integrable g)
    (hf1 : Integrable (fun η => ‖η‖ * f η))
    (hg1 : Integrable (fun η => ‖η‖ * g η))
    (hfn : ∀ η, 0 ≤ f η) (hgn : ∀ η, 0 ≤ g η) :
    ∀ᵐ ξ : ES,
      ‖ξ‖ * convolution f g ξ ≤
        convolution (fun η => ‖η‖ * f η) g ξ +
          convolution f (fun η => ‖η‖ * g η) ξ := by
  have h0 := hf0.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hg0
  have hl := integrable_left_frequency_kernel f g hf1 hg0
  have hr := integrable_right_frequency_kernel f g hf0 hg1
  have h0ae : ∀ᵐ ξ : ES, Integrable (fun η : ES => f η * g (ξ - η)) :=
    (integrable_prod_iff h0.aestronglyMeasurable).mp h0 |>.1
  have hlae : ∀ᵐ ξ : ES, Integrable (fun η : ES => (‖η‖ * f η) * g (ξ - η)) :=
    (integrable_prod_iff hl.aestronglyMeasurable).mp hl |>.1
  have hrae : ∀ᵐ ξ : ES,
      Integrable (fun η : ES => f η * (‖ξ - η‖ * g (ξ - η))) :=
    (integrable_prod_iff hr.aestronglyMeasurable).mp hr |>.1
  filter_upwards [h0ae, hlae, hrae] with ξ h0ξ hlξ hrξ
  exact frequency_weighted_convolution_pointwise f g hfn hgn ξ h0ξ hlξ hrξ

/-- Global continuous weighted convolution bound obtained by integrating the
a.e. frequency allocation and using the two Tonelli factorizations. -/
theorem weighted_convolution_mass_le (f g : ES → ℝ)
    (hf0 : Integrable f) (hg0 : Integrable g)
    (hf1 : Integrable (fun η => ‖η‖ * f η))
    (hg1 : Integrable (fun η => ‖η‖ * g η))
    (hfn : ∀ η, 0 ≤ f η) (hgn : ∀ η, 0 ≤ g η) :
    (∫ ξ : ES, ‖ξ‖ * convolution f g ξ) ≤
      (∫ η : ES, ‖η‖ * f η) * (∫ η : ES, g η) +
        (∫ η : ES, f η) * (∫ η : ES, ‖η‖ * g η) := by
  have hconv := integrable_scalar_convolution f g hf0 hg0
  have hlconv := integrable_scalar_convolution (fun η => ‖η‖ * f η) g hf1 hg0
  have hrconv := integrable_scalar_convolution f (fun η => ‖η‖ * g η) hf0 hg1
  have hrhs : Integrable (fun ξ : ES =>
      convolution (fun η => ‖η‖ * f η) g ξ +
        convolution f (fun η => ‖η‖ * g η) ξ) := hlconv.add hrconv
  have hae := ae_frequency_weighted_convolution_pointwise f g hf0 hg0 hf1 hg1 hfn hgn
  have hconv_nonneg : ∀ ξ : ES, 0 ≤ convolution f g ξ := by
    intro ξ
    change 0 ≤ ∫ η : ES, f η * g (ξ - η)
    apply integral_nonneg_of_ae
    filter_upwards with η
    exact mul_nonneg (hfn η) (hgn (ξ - η))
  have hnorm : ∀ᵐ ξ : ES,
      ‖‖ξ‖ * convolution f g ξ‖ ≤
        convolution (fun η => ‖η‖ * f η) g ξ +
          convolution f (fun η => ‖η‖ * g η) ξ := by
    filter_upwards [hae] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg ξ) (hconv_nonneg ξ))]
    exact hξ
  have hlhs : Integrable (fun ξ : ES => ‖ξ‖ * convolution f g ξ) :=
    hrhs.mono' (continuous_norm.aestronglyMeasurable.mul hconv.aestronglyMeasurable) hnorm
  calc
    (∫ ξ : ES, ‖ξ‖ * convolution f g ξ) ≤
        ∫ ξ : ES, convolution (fun η => ‖η‖ * f η) g ξ +
          convolution f (fun η => ‖η‖ * g η) ξ := integral_mono_ae hlhs hrhs hae
    _ = (∫ η : ES, ‖η‖ * f η) * (∫ η : ES, g η) +
          (∫ η : ES, f η) * (∫ η : ES, ‖η‖ * g η) := by
      rw [integral_add hlconv hrconv]
      change normX0 (convolution (fun η => ‖η‖ * f η) g) +
          normX0 (convolution f (fun η => ‖η‖ * g η)) = _
      rw [normX0_convolution_eq (fun η => ‖η‖ * f η) g hf1 hg0,
        normX0_convolution_eq f (fun η => ‖η‖ * g η) hf0 hg1]
      rfl

/-- The continuous Leray multiplier contracts the weighted `L¹` mass of any
a.e. strongly measurable vector frequency profile. -/
theorem integrable_weighted_continuousLerayE (v : ES → ComplexE3)
    (hv : AEStronglyMeasurable v)
    (hw : Integrable (fun ξ : ES => ‖ξ‖ * ‖v ξ‖)) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖continuousLerayE ξ (v ξ)‖) := by
  refine hw.mono' ?_ ?_
  · exact continuous_norm.aestronglyMeasurable.mul
      (continuousLerayE_aestronglyMeasurable v hv).norm
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg ξ)
      (norm_nonneg (continuousLerayE ξ (v ξ))))]
    exact mul_le_mul_of_nonneg_left (continuousLerayE_norm_le ξ (v ξ)) (norm_nonneg ξ)

/-- Integral form of the continuous weighted Leray contraction. -/
theorem weighted_continuousLerayE_mass_le (v : ES → ComplexE3)
    (hv : AEStronglyMeasurable v)
    (hw : Integrable (fun ξ : ES => ‖ξ‖ * ‖v ξ‖)) :
    (∫ ξ : ES, ‖ξ‖ * ‖continuousLerayE ξ (v ξ)‖) ≤
      ∫ ξ : ES, ‖ξ‖ * ‖v ξ‖ :=
  integral_mono (integrable_weighted_continuousLerayE v hv hw) hw
    (fun ξ => mul_le_mul_of_nonneg_left (continuousLerayE_norm_le ξ (v ξ)) (norm_nonneg ξ))

/-- The norm of the literal complex Fourier convolution is bounded pointwise
by convolution of its scalar norm profiles. -/
theorem norm_complex_convolution_le (f g : ES → ℂ) (ξ : ES) :
    ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) ξ‖ ≤
      convolution (fun η => ‖f η‖) (fun η => ‖g η‖) ξ := by
  change ‖∫ η : ES, f η * g (ξ - η)‖ ≤
    ∫ η : ES, ‖f η‖ * ‖g (ξ - η)‖
  simpa only [norm_mul] using
    (norm_integral_le_integral_norm (fun η : ES => f η * g (ξ - η)))

/-- The literal continuous Fourier convection tensor: at output coordinate
`i`, sum the three advecting coordinates `u_j` against `v_i` and apply the
output-frequency derivative. -/
def rawNavierConvection (u v : ES → ComplexSpace) (ξ : ES) : ComplexSpace := fun i =>
  ∑ j : Fin 3, (ξ j : ℂ) *
    ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ

/-- The continuous Fourier Navier bilinear symbol, including the Fourier
derivative phase and the frequencywise Leray projection. -/
def continuousNavierBilinear (u v : ES → ComplexSpace) (ξ : ES) : ComplexSpace :=
  continuousLeray ξ (Complex.I • rawNavierConvection u v ξ)

/-- The PiLp/WithLp Borel structure on the Hermitian three-coordinate carrier.
It is named explicitly because the finite-dimensional inner-product volume
construction can otherwise expose the same Borel structure through a distinct
instance path. -/
@[reducible] def complexE3PiMeasurableSpace : MeasurableSpace ComplexE3 :=
  WithLp.measurableSpace 2 (Fin 3 → ℂ)

/-- The measurable-space path selected by the finite-dimensional Hermitian
volume construction. -/
@[reducible] def complexE3EuclideanMeasurableSpace : MeasurableSpace ComplexE3 :=
  measureSpaceOfInnerProductSpace.toMeasurableSpace

/-- The PiLp measurable structure is exactly the Borel σ-algebra. -/
theorem complexE3PiMeasurableSpace_eq_borel :
    complexE3PiMeasurableSpace = borel ComplexE3 := by
  exact @BorelSpace.measurable_eq ComplexE3 _ complexE3PiMeasurableSpace
    (PiLp.borelSpace 2)

/-- The inner-product volume measurable structure is also exactly Borel. -/
theorem complexE3EuclideanMeasurableSpace_eq_borel :
    complexE3EuclideanMeasurableSpace = borel ComplexE3 := by
  exact @BorelSpace.measurable_eq ComplexE3 _ complexE3EuclideanMeasurableSpace _

/-- The two instance paths for the finite-dimensional complex Euclidean carrier
are measurably coherent. -/
theorem complexE3_measurableSpace_coherent :
    complexE3PiMeasurableSpace = complexE3EuclideanMeasurableSpace := by
  rw [complexE3PiMeasurableSpace_eq_borel]
  exact complexE3EuclideanMeasurableSpace_eq_borel.symm

/-- An `ℓ²` coordinate vector is bounded by its finite `ℓ¹` coordinate mass. -/
theorem euclidean_norm_le_coordinate_sum (z : ComplexSpace) :
    complexEuclideanNorm z ≤ ∑ i : Fin 3, ‖z i‖ := by
  unfold complexEuclideanNorm complexEuclideanPoint
  have hz : z = ∑ i : Fin 3, Pi.single i (z i) := by
    ext i
    simp
  conv_lhs => rw [hz, WithLp.toLp_sum]
  refine le_trans (norm_sum_le (Finset.univ)
    (fun i => WithLp.toLp 2 (Pi.single i (z i)))) ?_
  simp

/-- A coordinate of the output frequency is bounded by its Euclidean norm. -/
theorem navier_frequency_factor_le (ξ : ES) (a : ℂ) (j : Fin 3) :
    ‖(ξ j : ℂ) * a‖ ≤ ‖ξ‖ * ‖a‖ := by
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le ξ j) (norm_nonneg _)

/-- Componentwise scalar-convolution majorant for the actual vector-valued
continuous Fourier Navier symbol. -/
theorem continuousNavierBilinear_majorant (u v : ES → ComplexSpace) (ξ : ES) :
    complexEuclideanNorm (continuousNavierBilinear u v ξ) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ‖ξ‖ *
        convolution (fun η => ‖u η j‖) (fun η => ‖v η i‖) ξ := by
  refine le_trans (continuousLeray_norm_le ξ (Complex.I • rawNavierConvection u v ξ)) ?_
  have hphase : complexEuclideanNorm (Complex.I • rawNavierConvection u v ξ) =
      complexEuclideanNorm (rawNavierConvection u v ξ) := by
    unfold complexEuclideanNorm complexEuclideanPoint
    rw [WithLp.toLp_smul, norm_smul]
    simp
  rw [hphase]
  refine le_trans (euclidean_norm_le_coordinate_sum (rawNavierConvection u v ξ)) ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [rawNavierConvection]
  refine le_trans (norm_sum_le Finset.univ (fun j => (ξ j : ℂ) *
    ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ)) ?_
  apply Finset.sum_le_sum
  intro j hj
  refine le_trans (navier_frequency_factor_le ξ
    (((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun η => v η i)) ξ) j) ?_
  exact mul_le_mul_of_nonneg_left
    (norm_complex_convolution_le (fun η => u η j) (fun η => v η i) ξ) (norm_nonneg _)

/-- The `X⁻¹` output weight cancels one Fourier derivative, including at zero
frequency where Lean's total inverse is zero. -/
theorem inv_mul_derivative_le (r a : ℝ) (_hr : 0 ≤ r) (ha : 0 ≤ a) :
    r⁻¹ * (r * a) ≤ a := by
  by_cases hz : r = 0
  · simp [hz, ha]
  · calc
      r⁻¹ * (r * a) = (r⁻¹ * r) * a := by ring
      _ ≤ a := by rw [inv_mul_cancel₀ hz, one_mul]

/-- Pointwise `X⁻¹` majorant for the literal continuous Navier symbol. -/
theorem normXm1_continuousNavierBilinear_pointwise (u v : ES → ComplexSpace) (ξ : ES) :
    ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierBilinear u v ξ) ≤
      ∑ i : Fin 3, ∑ j : Fin 3,
        convolution (fun η => ‖u η j‖) (fun η => ‖v η i‖) ξ := by
  have h := mul_le_mul_of_nonneg_left
    (continuousNavierBilinear_majorant u v ξ)
    (inv_nonneg.mpr (norm_nonneg ξ))
  simp_rw [Finset.mul_sum] at h
  refine le_trans h ?_
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply inv_mul_derivative_le ‖ξ‖
  · exact norm_nonneg ξ
  apply integral_nonneg_of_ae
  filter_upwards with η
  exact mul_nonneg (norm_nonneg (u η j)) (norm_nonneg (v (ξ - η) i))

/-- The integrated continuous vector bilinear estimate.  `hout` is stated
explicitly because this module proves the symbol estimate; constructing the
time-dependent Bochner representative is the next Duhamel leaf. -/
theorem normXm1_continuousNavierBilinear_mass_le
    (u v : ES → ComplexSpace)
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖))
    (hv0 : ∀ i : Fin 3, Integrable (fun η : ES => ‖v η i‖))
    (hout : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * complexEuclideanNorm
      (continuousNavierBilinear u v ξ))) :
    (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierBilinear u v ξ)) ≤
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∫ η : ES, ‖u η j‖) * (∫ η : ES, ‖v η i‖) := by
  have hsum : Integrable (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
      convolution (fun η => ‖u η j‖) (fun η => ‖v η i‖) ξ) := by
    refine integrable_finsetSum Finset.univ ?_
    intro i hi
    refine integrable_finsetSum Finset.univ ?_
    intro j hj
    exact integrable_scalar_convolution _ _ (hu0 j) (hv0 i)
  calc
    (∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierBilinear u v ξ)) ≤
        ∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3,
          convolution (fun η => ‖u η j‖) (fun η => ‖v η i‖) ξ :=
      integral_mono hout hsum (normXm1_continuousNavierBilinear_pointwise u v)
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        (∫ η : ES, ‖u η j‖) * (∫ η : ES, ‖v η i‖) := by
      have hinner : ∀ i : Fin 3, Integrable (fun ξ : ES => ∑ j : Fin 3,
          convolution (fun η => ‖u η j‖) (fun η => ‖v η i‖) ξ) := by
        intro i
        refine integrable_finsetSum Finset.univ ?_
        intro j hj
        exact integrable_scalar_convolution _ _ (hu0 j) (hv0 i)
      rw [integral_finsetSum Finset.univ (fun i _ => hinner i)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum Finset.univ (fun j _ =>
        integrable_scalar_convolution _ _ (hu0 j) (hv0 i))]
      apply Finset.sum_congr rfl
      intro j hj
      exact normX0_convolution_eq _ _ (hu0 j) (hv0 i)

end Navier.Analysis.ContinuousLeiLinSpace

#print axioms Navier.Analysis.ContinuousLeiLinSpace.schwartz_integrable_norm_inv_mul
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_Xm1
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_X1
#print axioms Navier.Analysis.ContinuousLeiLinSpace.heat_contracts_Xm1
#print axioms Navier.Analysis.ContinuousLeiLinSpace.normX0_convolution_eq
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_convolution_integrable
#print axioms Navier.Analysis.ContinuousLeiLinSpace.continuousLeray_norm_le
#print axioms Navier.Analysis.ContinuousLeiLinSpace.continuousLeray_weighted_norm_le
#print axioms Navier.Analysis.ContinuousLeiLinSpace.continuousLerayE_aestronglyMeasurable
#print axioms Navier.Analysis.ContinuousLeiLinSpace.integrable_continuousLerayE
#print axioms Navier.Analysis.ContinuousLeiLinSpace.frequency_triangle
#print axioms Navier.Analysis.ContinuousLeiLinSpace.frequency_weighted_product_split
#print axioms Navier.Analysis.ContinuousLeiLinSpace.frequency_weighted_norm_product_split
#print axioms Navier.Analysis.ContinuousLeiLinSpace.frequency_weighted_convolution_pointwise
#print axioms Navier.Analysis.ContinuousLeiLinSpace.integrable_left_frequency_kernel
#print axioms Navier.Analysis.ContinuousLeiLinSpace.integrable_right_frequency_kernel
#print axioms Navier.Analysis.ContinuousLeiLinSpace.integral_left_frequency_kernel
#print axioms Navier.Analysis.ContinuousLeiLinSpace.integral_right_frequency_kernel
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_left_frequency_kernel
#print axioms Navier.Analysis.ContinuousLeiLinSpace.fourier_schwartz_integrable_right_frequency_kernel
#print axioms Navier.Analysis.ContinuousLeiLinSpace.integrable_scalar_convolution
#print axioms Navier.Analysis.ContinuousLeiLinSpace.ae_frequency_weighted_convolution_pointwise
#print axioms Navier.Analysis.ContinuousLeiLinSpace.weighted_convolution_mass_le
#print axioms Navier.Analysis.ContinuousLeiLinSpace.integrable_weighted_continuousLerayE
#print axioms Navier.Analysis.ContinuousLeiLinSpace.weighted_continuousLerayE_mass_le
#print axioms Navier.Analysis.ContinuousLeiLinSpace.norm_complex_convolution_le
#print axioms Navier.Analysis.ContinuousLeiLinSpace.complexE3_measurableSpace_coherent
#print axioms Navier.Analysis.ContinuousLeiLinSpace.continuousNavierBilinear_majorant
#print axioms Navier.Analysis.ContinuousLeiLinSpace.normXm1_continuousNavierBilinear_pointwise
#print axioms Navier.Analysis.ContinuousLeiLinSpace.normXm1_continuousNavierBilinear_mass_le
