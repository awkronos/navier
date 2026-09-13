import Navier.Analysis.ContinuousLeiLinPhysicalIntegrability
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Scale-sensitive physical regularity from the Lei--Lin first moment

The preceding `X⁻¹ ∩ X¹ ⇒ L¹` result makes Fourier inversion
genuine.  This module uses the `X¹` moment a second time: differentiation
under the inverse Fourier integral gives an everywhere Fréchet derivative,
whose operator norm is bounded explicitly by `2π` times the `X¹` mass.

Unlike kinetic energy, this estimate is scale-sensitive.  It is the first
physical-space slice bound capable of feeding a classical local lifespan;
higher moments remain necessary for the full smooth restart interface.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace Navier.Analysis.ContinuousLeiLinPhysicalRegularity

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinPhysicalIntegrability

/-- The inverse Fourier transform is everywhere differentiable when the two
Lei--Lin endpoint densities are integrable. -/
theorem differentiable_fourierInv_of_integrable_Xm1_X1 (f : ES → ℂ)
    (hf : AEStronglyMeasurable f)
    (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖))
    (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖f ξ‖)) :
    Differentiable ℝ (FourierTransform.fourierInv f) := by
  let L : ES →L[ℝ] ES →L[ℝ] ℝ :=
    -(innerSL ℝ : ES →L[ℝ] ES →L[ℝ] ℝ)
  have hL : L.toLinearMap₁₂ = -innerₗ ES := rfl
  have hfint : Integrable f := integrable_of_integrable_Xm1_X1 f hf hxm1 hx1
  simpa only [FourierTransform.fourierInv, hL] using
    (VectorFourier.differentiable_fourierIntegral L hfint hx1)

/-- Quantitative first-moment estimate for the full Fréchet derivative of
the inverse Fourier transform. -/
theorem norm_fderiv_fourierInv_le_X1 (f : ES → ℂ)
    (hf : AEStronglyMeasurable f)
    (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖))
    (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖f ξ‖)) (x : ES) :
    ‖fderiv ℝ (FourierTransform.fourierInv f) x‖ ≤ 2 * Real.pi * normX1 f := by
  let L : ES →L[ℝ] ES →L[ℝ] ℝ :=
    -(innerSL ℝ : ES →L[ℝ] ES →L[ℝ] ℝ)
  have hL : L.toLinearMap₁₂ = -innerₗ ES := rfl
  have hfint : Integrable f := integrable_of_integrable_Xm1_X1 f hf hxm1 hx1
  have hR : Integrable (VectorFourier.fourierSMulRight L f) := by
    refine (hx1.const_mul (2 * Real.pi * ‖L‖)).mono'
      hfint.aestronglyMeasurable.fourierSMulRight ?_
    filter_upwards with ξ
    exact (VectorFourier.norm_fourierSMulRight_le L f ξ).trans_eq (by ring)
  have hderiv : fderiv ℝ (FourierTransform.fourierInv f) x =
      VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
        (VectorFourier.fourierSMulRight L f) x := by
    simpa only [FourierTransform.fourierInv, hL] using
      (VectorFourier.hasFDerivAt_fourierIntegral L hfint hx1 x).fderiv
  rw [hderiv]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume L.toLinearMap₁₂ (VectorFourier.fourierSMulRight L f) x).trans ?_
  have hLnorm : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ξ
    rw [one_mul]
    change ‖-(innerSL ℝ ξ)‖ ≤ ‖ξ‖
    rw [norm_neg, innerSL_apply_norm]
  have hpoint : ∀ ξ : ES,
      ‖VectorFourier.fourierSMulRight L f ξ‖ ≤
        2 * Real.pi * (‖ξ‖ * ‖f ξ‖) := by
    intro ξ
    calc
      ‖VectorFourier.fourierSMulRight L f ξ‖ ≤
          2 * Real.pi * ‖L‖ * ‖ξ‖ * ‖f ξ‖ :=
        VectorFourier.norm_fourierSMulRight_le L f ξ
      _ ≤ 2 * Real.pi * 1 * ‖ξ‖ * ‖f ξ‖ := by gcongr
      _ = 2 * Real.pi * (‖ξ‖ * ‖f ξ‖) := by ring
  have hmajorant : Integrable (fun ξ : ES => 2 * Real.pi * (‖ξ‖ * ‖f ξ‖)) :=
    hx1.const_mul (2 * Real.pi)
  calc
    (∫ ξ : ES, ‖VectorFourier.fourierSMulRight L f ξ‖) ≤
        ∫ ξ : ES, 2 * Real.pi * (‖ξ‖ * ‖f ξ‖) :=
      integral_mono_ae hR.norm hmajorant (ae_of_all volume hpoint)
    _ = 2 * Real.pi * normX1 f := by
      rw [integral_const_mul]
      rfl

/-- Each physical coordinate inherits everywhere differentiability from its
two endpoint Fourier densities. -/
theorem differentiable_physicalCoord_of_Xm1_X1
    (w : ES → ComplexSpace) (i : Fin 3)
    (hmeas : AEStronglyMeasurable (fun ξ : ES => w ξ i))
    (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖w ξ i‖))
    (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖w ξ i‖)) :
    Differentiable ℝ (physicalCoord w i) := by
  exact differentiable_fourierInv_of_integrable_Xm1_X1 (fun ξ => w ξ i) hmeas hxm1 hx1

/-- The physical coordinate gradient is controlled pointwise by its actual
`X¹` Fourier moment. -/
theorem norm_fderiv_physicalCoord_le_X1
    (w : ES → ComplexSpace) (i : Fin 3)
    (hmeas : AEStronglyMeasurable (fun ξ : ES => w ξ i))
    (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖w ξ i‖))
    (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖w ξ i‖)) (x : ES) :
    ‖fderiv ℝ (physicalCoord w i) x‖ ≤
      2 * Real.pi * normX1 (fun ξ => w ξ i) := by
  exact norm_fderiv_fourierInv_le_X1 (fun ξ => w ξ i) hmeas hxm1 hx1 x

/-- The same first-moment control integrated along a spatial line segment:
every physical coordinate is globally Lipschitz with the scale-sensitive
`X¹` constant. -/
theorem norm_physicalCoord_sub_le_X1_mul_norm
    (w : ES → ComplexSpace) (i : Fin 3)
    (hmeas : AEStronglyMeasurable (fun ξ : ES => w ξ i))
    (hxm1 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖w ξ i‖))
    (hx1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖w ξ i‖)) (x y : ES) :
    ‖physicalCoord w i y - physicalCoord w i x‖ ≤
      (2 * Real.pi * normX1 (fun ξ => w ξ i)) * ‖y - x‖ := by
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (f := physicalCoord w i)
    (C := 2 * Real.pi * normX1 (fun ξ => w ξ i))
    (fun z _ => (differentiable_physicalCoord_of_Xm1_X1 w i hmeas hxm1 hx1) z)
    (fun z _ => norm_fderiv_physicalCoord_le_X1 w i hmeas hxm1 hx1 z)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)

/-- Summing the coordinate bounds gives the vector carrier's scale-sensitive
physical gradient estimate. -/
theorem sum_norm_fderiv_physicalCoord_le_coordinateX1Mass
    (w : ES → ComplexSpace)
    (hmeas : ∀ i : Fin 3, AEStronglyMeasurable (fun ξ : ES => w ξ i))
    (hxm1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖w ξ i‖))
    (hx1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖w ξ i‖))
    (x : ES) :
    ∑ i : Fin 3, ‖fderiv ℝ (physicalCoord w i) x‖ ≤
      2 * Real.pi * coordinateX1Mass w := by
  calc
    ∑ i : Fin 3, ‖fderiv ℝ (physicalCoord w i) x‖ ≤
        ∑ i : Fin 3, 2 * Real.pi * normX1 (fun ξ => w ξ i) :=
      Finset.sum_le_sum fun i _ =>
        norm_fderiv_physicalCoord_le_X1 w i (hmeas i) (hxm1 i) (hx1 i) x
    _ = 2 * Real.pi * coordinateX1Mass w := by
      simp [coordinateX1Mass, Finset.mul_sum]

end Navier.Analysis.ContinuousLeiLinPhysicalRegularity

#check Navier.Analysis.ContinuousLeiLinPhysicalRegularity.differentiable_fourierInv_of_integrable_Xm1_X1
#check Navier.Analysis.ContinuousLeiLinPhysicalRegularity.norm_fderiv_fourierInv_le_X1
#check Navier.Analysis.ContinuousLeiLinPhysicalRegularity.differentiable_physicalCoord_of_Xm1_X1
#check Navier.Analysis.ContinuousLeiLinPhysicalRegularity.norm_fderiv_physicalCoord_le_X1
#check Navier.Analysis.ContinuousLeiLinPhysicalRegularity.norm_physicalCoord_sub_le_X1_mul_norm
#check Navier.Analysis.ContinuousLeiLinPhysicalRegularity.sum_norm_fderiv_physicalCoord_le_coordinateX1Mass

#print axioms Navier.Analysis.ContinuousLeiLinPhysicalRegularity.differentiable_fourierInv_of_integrable_Xm1_X1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalRegularity.norm_fderiv_fourierInv_le_X1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalRegularity.differentiable_physicalCoord_of_Xm1_X1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalRegularity.norm_fderiv_physicalCoord_le_X1
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalRegularity.norm_physicalCoord_sub_le_X1_mul_norm
#print axioms Navier.Analysis.ContinuousLeiLinPhysicalRegularity.sum_norm_fderiv_physicalCoord_le_coordinateX1Mass
