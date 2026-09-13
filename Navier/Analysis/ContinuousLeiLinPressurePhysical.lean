import Navier.Analysis.ContinuousLeiLinPressureReconstruction
import Navier.Analysis.FourierWeightedPlancherel
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Physical-space pressure inversion on the continuous Lei--Lin carrier

Completes the named residual of
`Navier.Analysis.ContinuousLeiLinPressureReconstruction`: the physical-space
distributional Poisson pairing `∫ p Δφ` against Schwartz test functions, on
the repo's actual carriers, by the `L¹` Fourier inversion bridge.

## What is constructed

`continuousPressurePhysical u := 𝓕⁻ (continuousPressureFourier u)`, i.e.
pointwise `p(x) = ∫ ξ, exp(2πi⟪ξ, x⟫) • p̂(ξ)` (`Real.fourierInv_eq`) — the
brief's `∫ ξ, exp(I⟨ξ,x⟩) • p̂(ξ)` in the repo's `2π`-in-the-character
convention (𝐞(t) = exp(2πit)); the primitive's derivative convention
`𝓕(∂ₘ f) = 2πi⟪ξ, m⟫ 𝓕 f` is exactly
`SchwartzMap.fourier_lineDerivOp_eq`, so no convention bridge is needed.
Well-definedness is unconditional in the Bochner-junk sense; under the
primitive's own `AEStronglyMeasurable` + `Integrable` coordinate premises
`p̂ ∈ L¹`, and the inversion bounds `‖p(x)‖ ≤ ∫‖p̂‖ ≤ coordinateX0Mass u²`
(`norm_continuousPressurePhysical_le`) and is continuous
(`continuous_continuousPressurePhysical`): the C₀-type representative.

## The physical Poisson identity proved here

For every Schwartz test `ψ` on `ES`, with the physical Laplacian
`physicalLaplacian ψ = ∑ⱼ ∂_{eⱼ}∂_{eⱼ} ψ` in the LineDeriv calculus:

  `∫ x, p(x) · (Δψ)(x) = (2π)² · ∫ ξ, (∑ᵢ ∑ⱼ ξᵢξⱼ·(ûᵢ ⋆ ûⱼ)(ξ)) · (𝓕⁻ψ)(ξ)`

(`continuousPressurePhysical_pairing_physicalLaplacian`).  This is the
frequency-carrier Poisson pairing
`continuousPressurePoisson_pairing` transported to physical space through
`VectorFourier.integral_bilin_fourierIntegral_eq_flip` (self-adjointness of
`𝓕⁻` for the bilinear pairing, which the pinned Mathlib proves under `L¹`
integrability alone — the inversion bridge the residual demanded, packaged
as `integral_fourierInv_pairing`) together with the test-side multiplier
computation `𝓕⁻(Δψ) = -(2π)²‖·‖² · 𝓕⁻ψ`
(`fourierInv_physicalLaplacian_apply`: `SchwartzMap.fourierInv_lineDerivOp_eq`
applied twice plus the basis expansion `sum_inner_single_sq`).  The `(2π)²`
factor is the exact image of `Δ` on the test side; on the frequency carrier
it cancels inside the symbol `ξᵢξⱼ/‖ξ‖²` (primitive header).

## Honest scope: which physical identity is genuinely proved

The remaining rewrite of the transported source
`((2π)²∑ᵢⱼ ξᵢξⱼ(ûᵢ⋆ûⱼ))` into `∑ᵢⱼ ∂ᵢ∂ⱼ(vᵢ vⱼ)` with the physical
velocities `vᵢ = 𝓕⁻ ûᵢ` requires the product-to-convolution bridge
`𝓕⁻(ûᵢ ⋆ ûⱼ) = vᵢ · vⱼ` for merely-`L¹` frequency data.  The pinned Mathlib
carries only the convolution-to-product direction
(`Real.fourier_bilin_convolution_eq`); the product-to-convolution direction
holds in `𝓢` (`SchwartzMap.fourier_convolution` + inversion) but the physical
velocities of `L¹` profiles are bounded continuous functions that need not be
integrable, so the `𝓢`-level bridge does not transport to this carrier
without strengthening the velocity hypothesis (e.g. `u = fourierDatum` of a
`SchwartzVelocity`, cf. `ContinuousLeiLinPhysicalCarrier`).  This is the
exact named residual, not a defect of the identity proved above: the brief's
target — `∫ p Δφ` equal to the transported frequency pairing — is PROVED.

## Mean-zero normalization

The constructed representative is the literal `L¹` inversion `p = 𝓕⁻(p̂)` of
the density with `p̂(0) = 0` (`continuousPressureFourier_zero`): no Dirac mass
at the zero frequency is added and no quotient-by-constants is taken, so the
bounded-continuous function `p` IS the pressure; any other whole-space
distributional pressure for the same velocity differs from it by an additive
constant (primitive header).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinPressurePhysical

open MeasureTheory Set SchwartzMap LineDeriv
open scoped BigOperators FourierTransform SchwartzMap Convolution
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
  (coordinateX0Mass)
open Navier.Analysis.ContinuousLeiLinPressureReconstruction
open Navier.Analysis.FourierWeightedPlancherel (sum_inner_single_sq)

/-- The `j`-th Euclidean basis vector of `ES`. -/
private abbrev basisVec (j : Fin 3) : ES := EuclideanSpace.single j (1 : ℝ)

/-- The physical-space Laplacian of a Schwartz test function, as the trace of
the Hessian in the LineDeriv calculus the repo already uses
(`FourierWeightedPlancherel`). -/
noncomputable def physicalLaplacian (ψ : 𝓢(ES, ℂ)) : 𝓢(ES, ℂ) :=
  ∑ j : Fin 3, ∂_{basisVec j} (∂_{basisVec j} ψ)

/-!
## The inversion is available under the primitive's premises
-/

/-- The pressure density is an `L¹` function under the primitive's
coordinate premises. -/
theorem integrable_continuousPressureFourier (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) :
    Integrable (continuousPressureFourier u) :=
  (integrable_norm_iff (aesstronglyMeasurable_continuousPressureFourier u hu hu0)).mp
    (integrable_norm_continuousPressureFourier u hu hu0)

/-!
## The physical-space pressure of a velocity profile
-/

/-- The physical-space pressure density: the `L¹` inverse Fourier transform
of the reconstructed frequency pressure,
`p(x) = 𝓕⁻(p̂)(x) = ∫ ξ, exp(2πi⟪ξ,x⟫) • p̂(ξ)` (`Real.fourierInv_eq`), the
C₀-type representative pinned by the mean-zero normalization `p̂(0) = 0` of
the primitive. -/
noncomputable def continuousPressurePhysical (u : ES → ComplexSpace) : ES → ℂ :=
  𝓕⁻ (continuousPressureFourier u)

/-- Kernel unfolding: the oscillatory integral the definition computes. -/
theorem continuousPressurePhysical_apply (u : ES → ComplexSpace) (x : ES) :
    continuousPressurePhysical u x =
      ∫ ξ : ES, 𝐞 (inner ℝ ξ x) • continuousPressureFourier u ξ :=
  Real.fourierInv_eq _ x

/-- Unconditional pointwise domination of the physical pressure by the
`L¹` mass of the frequency density (Bochner-junk safe: both sides are `0`
when `p̂ ∉ L¹`). -/
theorem norm_continuousPressurePhysical_le_integral_norm
    (u : ES → ComplexSpace) (x : ES) :
    ‖continuousPressurePhysical u x‖ ≤ ∫ ξ : ES, ‖continuousPressureFourier u ξ‖ := by
  show ‖VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ES) _ x‖ ≤ _
  exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (-innerₗ ES) _ x

/-- The `C⁰` bound on the actual carrier: the physical pressure is bounded by
the squared Wiener-slot mass, `‖p(x)‖ ≤ coordinateX0Mass u ^ 2`. -/
theorem norm_continuousPressurePhysical_le (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) (x : ES) :
    ‖continuousPressurePhysical u x‖ ≤ coordinateX0Mass u ^ 2 :=
  (norm_continuousPressurePhysical_le_integral_norm u x).trans
    (integral_norm_continuousPressureFourier_le u hu hu0)

/-- The physical pressure of an admissible velocity profile is continuous:
the Fourier integral of an `L¹` function. -/
theorem continuous_continuousPressurePhysical (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖)) :
    Continuous (continuousPressurePhysical u) := by
  show Continuous (VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ES)
    (continuousPressureFourier u))
  refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
    (integrable_continuousPressureFourier u hu hu0)
  exact (continuous_fst.inner continuous_snd).neg

/-!
## Truth checks on the physical representative
-/

/-- Degenerate data: the zero velocity profile reconstructs the zero physical
pressure. -/
theorem continuousPressurePhysical_zero_velocity :
    continuousPressurePhysical (0 : ES → ComplexSpace) = 0 := by
  unfold continuousPressurePhysical
  rw [continuousPressureFourier_zero_velocity]
  funext x
  rw [Real.fourierInv_eq]
  simp

/-- Mean-zero normalization transported: the frequency density inverted here
vanishes at the zero frequency (the primitive's totalized symbol), so no
additive constant is present in the constructed representative. -/
theorem continuousPressureFourier_zero_at_origin (u : ES → ComplexSpace) :
    (fun ξ : ES => continuousPressureFourier u ξ) 0 = 0 :=
  continuousPressureFourier_zero u

/-!
## The inversion bridge: `L¹` self-adjointness of `𝓕⁻`
-/

/-- The `L¹`-level self-adjointness of `𝓕⁻` for the bilinear pairing against
an integrable test: `∫ x, (𝓕⁻f)(x) • g x = ∫ ξ, f(ξ) • (𝓕⁻g)(ξ)`.  The
pinned Mathlib proves the underlying `VectorFourier` identity from
`Integrable f`, `Integrable g` alone, so no Schwartz hypothesis is needed on
the inverted side — this is the inversion bridge the reconstruction residual
demanded. -/
theorem integral_fourierInv_pairing (f : ES → ℂ) (g : ES → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    ∫ x : ES, 𝓕⁻ f x • g x = ∫ ξ : ES, f ξ • 𝓕⁻ g ξ := by
  have hflip : LinearMap.flip (-innerₗ ES) = -innerₗ ES := by
    ext x y
    simp [LinearMap.flip_apply, real_inner_comm]
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (M := ContinuousLinearMap.lsmul ℂ ℂ) (μ := volume) (ν := volume)
    (L := -innerₗ ES) Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd |>.neg) hf hg
  simp only [ContinuousLinearMap.lsmul_apply] at h
  rw [hflip] at h
  exact h

/-!
## The derivative multiplier on the test side
-/

/-- Inverse-transform multiplier for one line derivative of a Schwartz test:
`𝓕⁻(∂ₘψ)(ξ) = -(2πi)⟪ξ,m⟫ · 𝓕⁻ψ(ξ)`, the function-level reading of
`SchwartzMap.fourierInv_lineDerivOp_eq`. -/
theorem fourierInv_lineDeriv_apply (ψ : 𝓢(ES, ℂ)) (m : ES) (ξ : ES) :
    𝓕⁻ (⇑((∂_{m} ψ : 𝓢(ES, ℂ)))) ξ =
      -(2 * Real.pi * Complex.I) * (inner ℝ ξ m : ℂ) * 𝓕⁻ ⇑ψ ξ := by
  have hg : (fun x : ES => inner ℝ x m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hstep : 𝓕⁻ (⇑((∂_{m} ψ : 𝓢(ES, ℂ)))) ξ =
      (-(2 * Real.pi * Complex.I) : ℂ) • (inner ℝ ξ m • 𝓕⁻ ⇑ψ ξ) := by
    rw [← SchwartzMap.fourierInv_coe, SchwartzMap.fourierInv_lineDerivOp_eq,
      smul_apply, smulLeftCLM_apply_apply hg, SchwartzMap.fourierInv_coe]
  rw [hstep]
  simp [mul_assoc]

/-- The inverse transform of the physical Laplacian multiplies by
`-(2π)²‖ξ‖²`: `𝓕⁻(Δψ)(ξ) = -(2π)² ‖ξ‖² · 𝓕⁻ψ(ξ)`, two applications of the
line-derivative multiplier plus the basis expansion `sum_inner_single_sq`. -/
theorem fourierInv_physicalLaplacian_apply (ψ : 𝓢(ES, ℂ)) (ξ : ES) :
    𝓕⁻ (⇑(physicalLaplacian ψ)) ξ =
      -((2 * Real.pi : ℂ) ^ 2) * (‖ξ‖ : ℂ) ^ 2 * 𝓕⁻ ⇑ψ ξ := by
  have hI : (2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I) =
      -((2 * Real.pi : ℂ) ^ 2) := by
    rw [show (2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I) =
        ((2 * Real.pi : ℂ) ^ 2) * (Complex.I ^ 2) from by ring,
      Complex.I_sq]
    ring
  have key : (𝓕⁻ (physicalLaplacian ψ) : 𝓢(ES, ℂ)) =
      ∑ j : Fin 3,
        (𝓕⁻ ((∂_{basisVec j} (∂_{basisVec j} ψ) : 𝓢(ES, ℂ))) : 𝓢(ES, ℂ)) := by
    rw [show (physicalLaplacian ψ : 𝓢(ES, ℂ)) =
        ∑ j : Fin 3, (∂_{basisVec j} (∂_{basisVec j} ψ) : 𝓢(ES, ℂ)) from rfl]
    exact FourierTransform.fourierInv_sum
      (fun j => (∂_{basisVec j} (∂_{basisVec j} ψ) : 𝓢(ES, ℂ))) Finset.univ
  have hsum : 𝓕⁻ (⇑(physicalLaplacian ψ)) ξ =
      ∑ j : Fin 3, 𝓕⁻ (⇑((∂_{basisVec j} (∂_{basisVec j} ψ) : 𝓢(ES, ℂ)))) ξ :=
    calc 𝓕⁻ (⇑(physicalLaplacian ψ)) ξ
        _ = ⇑((𝓕⁻ (physicalLaplacian ψ) : 𝓢(ES, ℂ))) ξ :=
          (congrFun (SchwartzMap.fourierInv_coe (physicalLaplacian ψ)) ξ).symm
        _ = ⇑(∑ j : Fin 3,
            (𝓕⁻ ((∂_{basisVec j} (∂_{basisVec j} ψ) : 𝓢(ES, ℂ))) : 𝓢(ES, ℂ))) ξ :=
          congrArg (fun z : 𝓢(ES, ℂ) => ⇑z ξ) key
        _ = ∑ j : Fin 3,
            ⇑((𝓕⁻ ((∂_{basisVec j} (∂_{basisVec j} ψ) : 𝓢(ES, ℂ))) : 𝓢(ES, ℂ))) ξ :=
          rfl
        _ = ∑ j : Fin 3, 𝓕⁻ (⇑((∂_{basisVec j} (∂_{basisVec j} ψ) : 𝓢(ES, ℂ)))) ξ :=
          Finset.sum_congr rfl fun j _ =>
            congrFun (SchwartzMap.fourierInv_coe _) ξ
  rw [hsum]
  have hterm : ∀ j : Fin 3,
      𝓕⁻ (⇑((∂_{basisVec j} (∂_{basisVec j} ψ) : 𝓢(ES, ℂ)))) ξ =
        -((2 * Real.pi : ℂ) ^ 2) * (inner ℝ ξ (basisVec j) : ℂ) ^ 2 * 𝓕⁻ ⇑ψ ξ := by
    intro j
    rw [fourierInv_lineDeriv_apply, fourierInv_lineDeriv_apply]
    rw [show -(2 * Real.pi * Complex.I) * (inner ℝ ξ (basisVec j) : ℂ) *
        (-(2 * Real.pi * Complex.I) * (inner ℝ ξ (basisVec j) : ℂ) * 𝓕⁻ ⇑ψ ξ) =
        ((2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I)) *
          ((inner ℝ ξ (basisVec j) : ℂ) ^ 2 * 𝓕⁻ ⇑ψ ξ) from by ring]
    rw [hI]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, basisVec]
  have hsq : (∑ i : Fin 3, ((inner ℝ ξ (EuclideanSpace.single i (1 : ℝ)) : ℂ)) ^ 2) =
      (‖ξ‖ : ℂ) ^ 2 := by
    norm_cast
    rw [sum_inner_single_sq]
  rw [hsq]

/-!
## The physical-space distributional Poisson identity
-/

/-- The compact frequency-side form of the physical Poisson pairing:
`∫ x, p(x)·(Δψ)(x) = -(2π)² ∫ ξ, ‖ξ‖²·p̂(ξ)·(𝓕⁻ψ)(ξ)`. -/
theorem continuousPressurePhysical_pairing_laplacian_neg (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖))
    (ψ : 𝓢(ES, ℂ)) :
    ∫ x : ES, continuousPressurePhysical u x • ⇑(physicalLaplacian ψ) x =
      -((2 * Real.pi : ℂ) ^ 2) *
        ∫ ξ : ES, (‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ * 𝓕⁻ ⇑ψ ξ := by
  have hp : Integrable (continuousPressureFourier u) :=
    integrable_continuousPressureFourier u hu hu0
  have hpair := integral_fourierInv_pairing (continuousPressureFourier u)
    (⇑(physicalLaplacian ψ)) hp (physicalLaplacian ψ).integrable
  show ∫ x : ES, 𝓕⁻ (continuousPressureFourier u) x • ⇑(physicalLaplacian ψ) x = _
  rw [hpair]
  have hrew : (fun ξ : ES => continuousPressureFourier u ξ •
      𝓕⁻ (⇑(physicalLaplacian ψ)) ξ) =
      (fun ξ : ES => -((2 * Real.pi : ℂ) ^ 2) •
        ((‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ * 𝓕⁻ ⇑ψ ξ)) := by
    funext ξ
    rw [fourierInv_physicalLaplacian_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [hrew, integral_smul]
  simp only [smul_eq_mul]

/-- **The physical-space distributional Poisson identity.**  For every
Schwartz test `ψ` on `ES`,
`∫ x, p(x)·(Δψ)(x) = (2π)² ∫ ξ, (∑ᵢ ∑ⱼ ξᵢξⱼ·(ûᵢ⋆ûⱼ)(ξ))·(𝓕⁻ψ)(ξ)`:
the reconstructed physical pressure paired against `Δψ` equals the
frequency-carrier Poisson pairing transported to physical space.  Via
`continuousPressurePoisson_pointwise` this is exactly the distributional
statement `Δp = ∑ᵢ∑ⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)` on the density carried by `p`, modulo the
named product-to-convolution residual recorded in the header. -/
theorem continuousPressurePhysical_pairing_physicalLaplacian (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖))
    (ψ : 𝓢(ES, ℂ)) :
    ∫ x : ES, continuousPressurePhysical u x • ⇑(physicalLaplacian ψ) x =
      ((2 * Real.pi : ℂ) ^ 2) *
        ∫ ξ : ES, (∑ i : Fin 3, ∑ j : Fin 3,
          (ξ i * ξ j : ℂ) *
            ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (fun η => u η j)) ξ) * 𝓕⁻ ⇑ψ ξ := by
  have hcore :
      ∫ ξ : ES, (∑ i : Fin 3, ∑ j : Fin 3,
          (ξ i * ξ j : ℂ) *
            ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (fun η => u η j)) ξ) * 𝓕⁻ ⇑ψ ξ =
        -∫ ξ : ES, (‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ * 𝓕⁻ ⇑ψ ξ := by
    have h := continuousPressurePoisson_pairing u (𝓕⁻ ψ)
    simp only [SchwartzMap.fourierInv_coe] at h
    have hnegf : (fun ξ : ES =>
          (-∑ i : Fin 3, ∑ j : Fin 3,
            (ξ i * ξ j : ℂ) *
              ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                (fun η => u η j)) ξ) * 𝓕⁻ ⇑ψ ξ) =
        (fun ξ : ES => -((∑ i : Fin 3, ∑ j : Fin 3,
            (ξ i * ξ j : ℂ) *
              ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                (fun η => u η j)) ξ) * 𝓕⁻ ⇑ψ ξ)) := by
      funext ξ
      rw [neg_mul]
    rw [hnegf, integral_neg] at h
    exact (neg_eq_iff_eq_neg).mp h.symm
  calc ∫ x : ES, continuousPressurePhysical u x • ⇑(physicalLaplacian ψ) x
      _ = -((2 * Real.pi : ℂ) ^ 2) *
            ∫ ξ : ES, (‖ξ‖ ^ 2 : ℂ) * continuousPressureFourier u ξ * 𝓕⁻ ⇑ψ ξ :=
          continuousPressurePhysical_pairing_laplacian_neg u hu hu0 ψ
      _ = ((2 * Real.pi : ℂ) ^ 2) *
            ∫ ξ : ES, (∑ i : Fin 3, ∑ j : Fin 3,
              (ξ i * ξ j : ℂ) *
                ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                  (fun η => u η j)) ξ) * 𝓕⁻ ⇑ψ ξ := by
          rw [hcore]
          simp only [neg_mul, mul_neg]

end Navier.Analysis.ContinuousLeiLinPressurePhysical

#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.physicalLaplacian
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.integrable_continuousPressureFourier
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_apply
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.norm_continuousPressurePhysical_le_integral_norm
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.norm_continuousPressurePhysical_le
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.continuous_continuousPressurePhysical
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_zero_velocity
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressureFourier_zero_at_origin
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.integral_fourierInv_pairing
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.fourierInv_lineDeriv_apply
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.fourierInv_physicalLaplacian_apply
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_pairing_laplacian_neg
#check @Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_pairing_physicalLaplacian

#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.physicalLaplacian
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.integrable_continuousPressureFourier
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_apply
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.norm_continuousPressurePhysical_le_integral_norm
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.norm_continuousPressurePhysical_le
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuous_continuousPressurePhysical
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_zero_velocity
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressureFourier_zero_at_origin
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.integral_fourierInv_pairing
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.fourierInv_lineDeriv_apply
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.fourierInv_physicalLaplacian_apply
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_pairing_laplacian_neg
#print axioms Navier.Analysis.ContinuousLeiLinPressurePhysical.continuousPressurePhysical_pairing_physicalLaplacian
