import Navier.Analysis.ContinuousLeiLinSpace

/-!
# Fourier convention bridge: the repository symbol versus physical Navier–Stokes

Mathlib's Fourier transform `𝓕 f(ξ) = ∫ e^{-2πi⟨x,ξ⟩} f(x) dx` turns `∂ⱼ` into
`2πi ξⱼ` and `Δ` into `-4π²‖ξ‖²`.  For a divergence-free velocity with
`û = 𝓕 u`, the unforced Navier–Stokes equation at viscosity `ν` reads

`∂ₜ û = -4π²ν‖ξ‖² û - 2πi · P(ξ) (∑ⱼ ξⱼ (ûⱼ ⋆ û)).`         (`physicalFourierRHS`)

The repository's continuous carrier uses the normalized symbol

`∂ₜ â = -ν'‖ξ‖² â + P(ξ)(i ∑ⱼ ξⱼ (âⱼ ⋆ â))`                 (`repoFourierRHS`)

(`ContinuousLeiLinSpace.continuousNavierBilinear`).  `rescale_rhs` proves the
exact bridge: with `ν' = 4π²ν` and `û = -(2π)⁻¹ â`, the repository right-hand
side, rescaled, IS the physical one.  In particular a repository solution with
`ν' = 4π²` yields a physical solution at viscosity one after multiplying by
`-(2π)⁻¹`, and the physical datum `𝓕 u₀` corresponds to the repository datum
`-2π · 𝓕 u₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Convolution

namespace Navier.Analysis.WienerConvention

open Navier.Analysis.ContinuousLeiLinSpace

/-- The repository's normalized Fourier right-hand side. -/
def repoFourierRHS (ν' : ℝ) (a : ES → ComplexSpace) (ξ : ES) : ComplexSpace :=
  (((-(ν' * ‖ξ‖ ^ 2)) : ℝ) : ℂ) • a ξ + continuousNavierBilinear a a ξ

/-- The Fourier right-hand side of physical Navier–Stokes at viscosity `ν`
under Mathlib's `2π` convention. -/
def physicalFourierRHS (ν : ℝ) (u : ES → ComplexSpace) (ξ : ES) : ComplexSpace :=
  (((-(4 * Real.pi ^ 2 * ν * ‖ξ‖ ^ 2)) : ℝ) : ℂ) • u ξ -
    ((2 * Real.pi : ℂ) * Complex.I) • continuousLeray ξ (rawNavierConvection u u ξ)

theorem rawNavierConvection_smul (c : ℂ) (u : ES → ComplexSpace) (ξ : ES) :
    rawNavierConvection (fun η => c • u η) (fun η => c • u η) ξ =
      (c * c) • rawNavierConvection u u ξ := by
  funext i
  simp only [rawNavierConvection, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ((fun η => c * u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      (fun η => c * u η i)) = (c * c) • ((fun η => u η j) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η => u η i)) := by
    rw [show (fun η => c * u η j) = c • (fun η => u η j) from rfl,
      show (fun η => c * u η i) = c • (fun η => u η i) from rfl,
      smul_convolution, convolution_smul, smul_smul]
  rw [h, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuousLeray_smul (ξ : ES) (c : ℂ) (z : ComplexSpace) :
    continuousLeray ξ (c • z) = c • continuousLeray ξ z := by
  unfold continuousLeray
  exact map_smul _ c z

/-- **The convention bridge.**  With `ν' = 4π²ν` and `c = -(2π)⁻¹`,
`c • repoFourierRHS ν' a = physicalFourierRHS ν (c • a)`. -/
theorem rescale_rhs (ν : ℝ) (a : ES → ComplexSpace) (ξ : ES) :
    (-(2 * Real.pi : ℂ)⁻¹) • repoFourierRHS (4 * Real.pi ^ 2 * ν) a ξ =
      physicalFourierRHS ν (fun η => (-(2 * Real.pi : ℂ)⁻¹) • a η) ξ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold repoFourierRHS physicalFourierRHS continuousNavierBilinear
  rw [rawNavierConvection_smul, continuousLeray_smul, continuousLeray_smul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  field_simp
  ring

end Navier.Analysis.WienerConvention

set_option pp.fullNames true in
#check @Navier.Analysis.WienerConvention.rescale_rhs
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerConvention.rescale_rhs
