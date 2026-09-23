import Navier.Analysis.WienerSchwartzSmooth
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

/-- **Convolution theorem for the inverse Fourier transform on `L¹`.** -/
theorem fourierInv_convolution {f g : ES → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ES) :
    𝓕⁻ (f ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] g) x = 𝓕⁻ f x * 𝓕⁻ g x := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg,
    Real.fourierInv_eq_fourier_neg]
  exact Real.fourier_mul_convolution_eq hf hg (-x)

end Navier.Analysis.WienerPhysicalPDE

set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerPhysicalPDE.fourierInv_convolution
