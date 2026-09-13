import Navier.Analysis.ContinuousLeiLinPhysicalReality

/-!
# Physical Fourier integrability from the two Lei--Lin endpoint weights

The continuous carrier already interpolates the numerical `X⁰` integral
between `X⁻¹` and `X¹`, but a Bochner integral is totalized to zero off its
integrable domain.  The physical inversion and reality consumer instead need
the genuine proposition `Integrable f`.

This module supplies that missing producer.  It factors `‖f ξ‖` almost
everywhere as the product of the square roots of the two weighted densities,
uses Hölder at exponents `2,2`, and then combines norm integrability with
strong measurability.  The final theorem immediately consumes the result in
`physicalCoord_im_eq_zero`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter

namespace Navier.Analysis.ContinuousLeiLinPhysicalIntegrability

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinReality
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinPhysicalReality

/-- The two homogeneous endpoint densities force the unweighted scalar norm
to be genuinely integrable. -/
theorem integrable_norm_of_integrable_Xm1_X1 (f : ES → ℂ)
    (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖))
    (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖f ξ‖)) :
    Integrable (fun ξ : ES => ‖f ξ‖) := by
  let a : ES → ℝ := fun ξ => Real.sqrt (‖ξ‖⁻¹ * ‖f ξ‖)
  let b : ES → ℝ := fun ξ => Real.sqrt (‖ξ‖ * ‖f ξ‖)
  have ha_meas : AEStronglyMeasurable a :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hxm1.aestronglyMeasurable
  have hb_meas : AEStronglyMeasurable b :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hx1.aestronglyMeasurable
  have ha_sq : Integrable (fun ξ => a ξ ^ 2) := by
    convert hxm1 using 1
    ext ξ
    dsimp [a]
    rw [Real.sq_sqrt]
    positivity
  have hb_sq : Integrable (fun ξ => b ξ ^ 2) := by
    convert hx1 using 1
    ext ξ
    dsimp [b]
    rw [Real.sq_sqrt]
    positivity
  have ha : MemLp a 2 volume := (memLp_two_iff_integrable_sq ha_meas).mpr ha_sq
  have hb : MemLp b 2 volume := (memLp_two_iff_integrable_sq hb_meas).mpr hb_sq
  have hprod : Integrable (a * b) := ha.integrable_mul hb
  have hz : ∀ᵐ ξ : ES, ξ ≠ 0 := by simp [ae_iff, measure_singleton]
  refine hprod.congr (hz.mono fun ξ hξ => ?_)
  dsimp [a, b]
  rw [← Real.sqrt_mul (by positivity)]
  have hnorm : 0 ≤ ‖f ξ‖ := norm_nonneg _
  have hξnorm : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  field_simp
  simp [pow_two, Real.sqrt_mul_self hnorm]

/-- Strong measurability upgrades the integrable scalar norm to Bochner
integrability of the complex Fourier coordinate itself. -/
theorem integrable_of_integrable_Xm1_X1 (f : ES → ℂ)
    (hf : AEStronglyMeasurable f)
    (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖))
    (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖f ξ‖)) :
    Integrable f := by
  exact (integrable_norm_iff hf).mp
    (integrable_norm_of_integrable_Xm1_X1 f hxm1 hx1)

/-- A Hermitian profile satisfying the actual two endpoint integrability
conditions has a real-valued inverse Fourier coordinate. -/
theorem physicalCoord_im_eq_zero_of_Xm1_X1
    (w : ES → ComplexSpace) (hw : ProfileHermitian w) (i : Fin 3)
    (hmeas : AEStronglyMeasurable (fun ξ : ES => w ξ i))
    (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖w ξ i‖))
    (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖w ξ i‖)) (x : ES) :
    (physicalCoord w i x).im = 0 := by
  exact physicalCoord_im_eq_zero w hw i
    (integrable_of_integrable_Xm1_X1 (fun ξ : ES => w ξ i) hmeas hxm1 hx1) x

end Navier.Analysis.ContinuousLeiLinPhysicalIntegrability

#check Navier.Analysis.ContinuousLeiLinPhysicalIntegrability.integrable_norm_of_integrable_Xm1_X1
#check Navier.Analysis.ContinuousLeiLinPhysicalIntegrability.integrable_of_integrable_Xm1_X1
#check Navier.Analysis.ContinuousLeiLinPhysicalIntegrability.physicalCoord_im_eq_zero_of_Xm1_X1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalIntegrability.integrable_norm_of_integrable_Xm1_X1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalIntegrability.integrable_of_integrable_Xm1_X1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalIntegrability.physicalCoord_im_eq_zero_of_Xm1_X1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalReality.physicalCoord_im_eq_zero
