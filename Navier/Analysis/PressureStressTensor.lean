import Navier.Analysis.ContinuousLeiLinPressurePhysical
import Navier.Analysis.ContinuousLeiLinPhysicalCarrier
import Mathlib.Analysis.Fourier.Convolution

/-!
# The stress-tensor bridge for the reconstructed pressure

Addresses the named residual of `ContinuousLeiLinPressurePhysical` (header
"Honest scope"): the pointwise product-to-convolution bridge
`𝓕⁻(ûᵢ ⋆ ûⱼ) = vᵢ · vⱼ` for `L¹` frequency data, and the fully-physical
stress-tensor rewrite of the Poisson pairing under the Schwartz specialization
`u = fourierDatum u₀` of `ContinuousLeiLinPhysicalCarrier`.

## What is proved here

1. **The bridge for merely-`L¹` data — unconditionally, no specialization.**
   `fourierInv_bilin_convolution`: for integrable `a b : ES → ℂ` and every `x`,
   `𝓕⁻ (a ⋆ b) x = 𝓕⁻ a x * 𝓕⁻ b x`.  The pinned Mathlib carries only the
   `𝓕`-side convolution-to-product direction
   (`Real.fourier_mul_convolution_eq`); the bridge is its exact image under
   the reflection identity `𝓕⁻ f = 𝓕 (f ∘ neg)`
   (`Real.fourierInv_eq_fourier_comp_neg`) plus the (here-proved) fact that
   reflecting the argument commutes with the bilinear convolution
   (`bilin_convolution_comp_neg`, the volume change of variables `t ↦ -t`).
   No Schwartz, no density, no extra integrability: the hypothesis is
   literally `a, b ∈ L¹`.  Specialized to the carrier:
   `pressureStress_bridge_pointwise` states
   `𝓕⁻(ûᵢ ⋆ ûⱼ) = physicalCoord u i · physicalCoord u j` under the
   primitive's own `AEStronglyMeasurable` + `Integrable` coordinate premises,
   and `pressureStress_bridge_fourierDatum` under its `SchwartzVelocity`
   specialization.

2. **The forward bridge on `𝓢`.**  `fourier_mul_bilin_convolution`: for
   Schwartz `F G`, `𝓕 (⇑F · ⇑G) = 𝓕⇑F ⋆ 𝓕⇑G` pointwise — the exact inverse
   direction, consumed by the stress pairing below.

3. **The stress-tensor Poisson identity for Schwartz data.**
   `continuousPressurePhysical_pairing_stressTensor`: for `u₀ :
   SchwartzVelocity` and every Schwartz test `ψ`,
   `∫ x, p x • (Δψ) x = -∑ᵢ ∑ⱼ ∫ x, ∂ᵢ∂ⱼ(vᵢ vⱼ) x • ψ x`
   with `p = continuousPressurePhysical (fourierDatum u₀)` and
   `vᵢ = 𝓕⁻(fourierDatum u₀)·ᵢ = ⇑(euclidComponent u₀ i)`
   (`physicalCoord_fourierDatum`): distributionally `Δp = -∑ᵢⱼ ∂ᵢ∂ⱼ(vᵢ vⱼ)`,
   the physical stress-tensor form of the Poisson relation the primitive
   reconstructs from.  The proof consumes the landed physical pairing
   `continuousPressurePhysical_pairing_physicalLaplacian` and rewrites its
   frequency source termwise by (2), the derivative multiplier
   `𝓕(∂ₘ w) = (2πi⟪·,m⟫)·𝓕 w` (`SchwartzMap.fourier_lineDerivOp_eq`, landed
   function-level here as `fourier_lineDeriv_apply`), and the bilinear
   self-adjointness `SchwartzMap.integral_bilin_fourier_eq`.

## Honest gap for general box elements (residual disposition)

The pointwise bridge (1) holds for every `L¹` coordinate pair, so the record
does NOT need a Schwartz-dense specialization hypothesis for the bridge
itself; a density-and-continuity closure argument would prove strictly less
than what is available unconditionally.  The `X⁰`-quotient continuity moduli
such an argument would have needed are established directly in section 4
(`norm_fourierInv_le_integral_norm`, `norm_fourierInv_mul_sub_le`: the
inverse transform is an `L¹ → C_b` contraction, and the product side is
jointly stable in the `L¹` quotients, uniformly in `x`; the corresponding
pressure bounds `‖p(x)‖ ≤ ∫‖p̂‖ ≤ coordinateX0Mass u²` and
`normX1 p̂ ≤ 2 · coordinateX0Mass · coordinateX1Mass` are already landed in
`ContinuousLeiLinPressurePhysical` / `ContinuousLeiLinPressureReconstruction`).

What remains genuinely open for general (box-represented) `u` is the
STRESS-PAIRING transport, not the bridge: for merely-`L¹` `ûᵢ` the physical
velocities `vᵢ` are bounded continuous but need not be integrable, so the
termwise identity `𝓕(∂ᵢ∂ⱼ(vᵢ vⱼ)) = -(2π)² ξᵢξⱼ (ûᵢ ⋆ ûⱼ)` asks the
Fourier transform of a non-`L¹` function; no function-level rewrite is
available and the `X⁰`/`X¹` quotients do not control second-moment-weighted
convergence of derivative terms, so no approximation closure exists inside
these quotients.  Closing the stress pairing on the general carrier changes
the carrier: the pinned Mathlib `Analysis.Distribution.TemperedDistribution`
API (which carries the derivative multiplier and the bilinear pairing
without any integrability hypothesis) is the named replacement route.  This
module does not launder that gap behind an approximation hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Navier.Analysis.PressureStressTensor

open MeasureTheory Set SchwartzMap LineDeriv
open scoped BigOperators FourierTransform SchwartzMap Convolution RealInnerProductSpace
open Navier
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.FourierMajorant
open Navier.Analysis.ContinuousLeiLinPressureReconstruction
open Navier.Analysis.ContinuousLeiLinPressurePhysical

/-- The `j`-th Euclidean basis vector of `ES` (mirrors the `private` one in
`ContinuousLeiLinPressurePhysical`, whose `physicalLaplacian` is consumed
here unchanged). -/
private abbrev basisVec (j : Fin 3) : ES := EuclideanSpace.single j (1 : ℝ)

/-- The volume-preserving reflection of `ES`. -/
private abbrev negEquiv : ES ≃ₗᵢ[ℝ] ES := LinearIsometryEquiv.neg ℝ

private theorem negEquiv_apply (x : ES) : ⇑negEquiv x = -x := rfl

private theorem integrable_comp_neg {f : ES → ℂ} (hf : Integrable f) :
    Integrable (fun x : ES => f (-x)) := by
  have hmap : Measure.map (fun x : ES => -x) volume = volume := by
    rw [← funext negEquiv_apply]
    exact negEquiv.measurePreserving.map_eq
  have hg : Integrable f (Measure.map (fun x : ES => -x) volume) := by
    rwa [hmap]
  exact hg.comp_measurable measurable_id.neg

/-!
## 1. The bridge for merely-`L¹` frequency data
-/

/-- Reflecting the argument of a bilinear convolution equals convolving the
reflected factors: `(a ⋆ b)(-x) = (a ∘ neg ⋆ b ∘ neg)(x)`, pointwise on `ES`
with scalar multiplication as the bilinear map.  The proof is the volume
change of variables `t ↦ -t` in the defining integral
`(a ⋆ b)(x) = ∫ t, a t * b (x - t)` (`convolution_def`). -/
theorem bilin_convolution_comp_neg (a b : ES → ℂ) (x : ES) :
    (a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] b) (-x) =
      ((fun y => a (-y)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun y => b (-y))) x := by
  show (∫ t : ES, a t * b (-x - t)) =
    ∫ t : ES, a (-t) * b (-(x - t))
  have hflip : (∫ t : ES, a t * b (-x - t)) = ∫ t : ES, a (-t) * b (-x + t) := by
    rw [← MeasurePreserving.integral_comp negEquiv.measurePreserving
      negEquiv.toHomeomorph.measurableEmbedding
      (g := fun t : ES => a t * b (-x - t))]
    refine integral_congr_ae (ae_of_all volume fun t => ?_)
    show a (-t) * b (-x - -t) = a (-t) * b (-x + t)
    rw [sub_neg_eq_add]
  rw [hflip]
  refine integral_congr_ae (ae_of_all volume fun t =>
    congrArg (fun s : ES => a (-t) * b s) ?_)
  rw [neg_sub]
  abel

/-- **The product-to-convolution bridge for merely-`L¹` frequency data.**
For integrable `a b : ES → ℂ` and every `x : ES`,
`𝓕⁻ (a ⋆ b) x = 𝓕⁻ a x * 𝓕⁻ b x`: the inverse Fourier transform converts the
`L¹` convolution into the pointwise product of the inverse transforms.  This
is the exact form of the named residual
`𝓕⁻(ûᵢ ⋆ ûⱼ) = vᵢ · vⱼ`; no Schwartz or density hypothesis is used — the
reflection identity `𝓕⁻ = 𝓕 ∘ neg` converts the pinned
`Real.fourier_mul_convolution_eq` (convolution-to-product for `𝓕`) into this
statement. -/
theorem fourierInv_bilin_convolution (a b : ES → ℂ)
    (ha : Integrable a) (hb : Integrable b) (x : ES) :
    𝓕⁻ (a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] b) x =
      𝓕⁻ a x * 𝓕⁻ b x := by
  have hflip : (fun y : ES => (a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] b) (-y)) =
      (fun y : ES => a (-y)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun y : ES => b (-y)) := by
    funext y
    exact bilin_convolution_comp_neg a b y
  calc 𝓕⁻ (a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] b) x
      _ = 𝓕 (fun y : ES => (a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] b) (-y)) x := by
        rw [Real.fourierInv_eq_fourier_comp_neg]
      _ = 𝓕 ((fun y : ES => a (-y)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun y : ES => b (-y))) x := by
        rw [hflip]
      _ = 𝓕 (fun y : ES => a (-y)) x * 𝓕 (fun y : ES => b (-y)) x :=
        Real.fourier_mul_convolution_eq
          (integrable_comp_neg ha) (integrable_comp_neg hb) x
      _ = 𝓕⁻ a x * 𝓕⁻ b x := by
        rw [← Real.fourierInv_eq_fourier_comp_neg, ← Real.fourierInv_eq_fourier_comp_neg]

/-- **The named residual, specialized to the continuous carrier.**  For every
velocity profile `u : ES → ComplexSpace` carrying the primitive's own
measurability and integrability premises (the hypotheses consumed by
`ContinuousLeiLinPressureReconstruction` and
`ContinuousLeiLinPressurePhysical`), the pointwise bridge
`𝓕⁻(ûᵢ ⋆ ûⱼ) = vᵢ · vⱼ` holds at every `x` with `vᵢ = physicalCoord u i`:
the stress product `vᵢ vⱼ` is the inverse transform of the frequency
convolution `ûᵢ ⋆ ûⱼ`, for `L¹` (box) data — no specialization needed. -/
theorem pressureStress_bridge_pointwise (u : ES → ComplexSpace)
    (hu : ∀ j : Fin 3, AEStronglyMeasurable (fun η : ES => u η j))
    (hu0 : ∀ j : Fin 3, Integrable (fun η : ES => ‖u η j‖))
    (i j : Fin 3) (x : ES) :
    𝓕⁻ ((fun η => u η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η => u η j)) x =
      physicalCoord u i x * physicalCoord u j x :=
  fourierInv_bilin_convolution (fun η => u η i) (fun η => u η j)
    ((integrable_norm_iff (hu i)).mp (hu0 i)) ((integrable_norm_iff (hu j)).mp (hu0 j)) x

/-- The coordinate premise helper for the `fourierDatum` carrier: measurability. -/
private theorem fourierDatum_aesm (u₀ : SchwartzVelocity) (k : Fin 3) :
    AEStronglyMeasurable (fun η : ES => fourierDatum u₀ η k) := by
  have heq : (fun η : ES => fourierDatum u₀ η k) = 𝓕 ⇑(euclidComponent u₀ k) := rfl
  rw [heq, ← SchwartzMap.fourier_coe]
  exact ((𝓕 (euclidComponent u₀ k) : 𝓢(ES, ℂ)).continuous).aestronglyMeasurable

/-- The coordinate premise helper for the `fourierDatum` carrier: integrability. -/
private theorem fourierDatum_integrable (u₀ : SchwartzVelocity) (k : Fin 3) :
    Integrable (fun η : ES => ‖fourierDatum u₀ η k‖) := by
  have h := fourierDatum_aesm u₀ k
  refine (integrable_norm_iff h).mpr ?_
  have heq : (fun η : ES => fourierDatum u₀ η k) = 𝓕 ⇑(euclidComponent u₀ k) := rfl
  rw [heq, ← SchwartzMap.fourier_coe]
  exact (𝓕 (euclidComponent u₀ k) : 𝓢(ES, ℂ)).integrable

/-- **The named bridge on the Schwartz datum carrier.**  For
`u₀ : SchwartzVelocity` the frequency convolution of the datum coordinates
inverts pointwise to the product of the physical velocities
`x ↦ (u₀ (spaceProj x) i)`, by `physicalCoord_fourierDatum`. -/
theorem pressureStress_bridge_fourierDatum (u₀ : SchwartzVelocity)
    (i j : Fin 3) (x : ES) :
    𝓕⁻ ((fun η => fourierDatum u₀ η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η => fourierDatum u₀ η j)) x =
      ((u₀ (spaceProj x) i : ℝ) : ℂ) * ((u₀ (spaceProj x) j : ℝ) : ℂ) := by
  have h := fourierInv_bilin_convolution (fun η => fourierDatum u₀ η i)
    (fun η => fourierDatum u₀ η j)
    ((integrable_norm_iff (fourierDatum_aesm u₀ i)).mp (fourierDatum_integrable u₀ i))
    ((integrable_norm_iff (fourierDatum_aesm u₀ j)).mp (fourierDatum_integrable u₀ j)) x
  rw [h]
  congr 1
  · exact physicalCoord_fourierDatum u₀ i x
  · exact physicalCoord_fourierDatum u₀ j x

/-!
## 2. The forward bridge on Schwartz data
-/

/-- The coe of the Schwartz-space convolution of the transforms equals the
function convolution of the transformed coes:
`⇑(convolution B (𝓕 F) (𝓕 G)) = 𝓕⇑F ⋆[B, volume] 𝓕⇑G`, via
`SchwartzMap.convolution_apply`. -/
theorem schConv_coe (B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (F G : 𝓢(ES, ℂ)) :
    ⇑(SchwartzMap.convolution B (𝓕 F) (𝓕 G)) =
      (𝓕 ⇑F ⋆[B, volume] 𝓕 ⇑G) := by
  funext y
  simp only [← SchwartzMap.fourier_coe]
  rw [← SchwartzMap.convolution_apply B (𝓕 F) (𝓕 G)]

/-- The Fourier transform converts the pointwise product of Schwartz
functions into the `L¹` convolution of their transforms:
`𝓕 (⇑F · ⇑G) = 𝓕⇑F ⋆ 𝓕⇑G`, pointwise.  Proof: with `k` the Schwartz-space
convolution `convolution B (𝓕F) (𝓕G)`, section 1 (applied to the
integrable `𝓕⇑F`, `𝓕⇑G`) inverts `⇑k` back to `⇑F · ⇑G`, and the
map-level inversion `𝓕 ∘ 𝓕⁻ = id` on `⇑k` then reads
`𝓕 (⇑F · ⇑G) = ⇑k`, whose coe is the function convolution by
`schConv_coe`. -/
theorem fourier_mul_bilin_convolution (F G : 𝓢(ES, ℂ)) (x : ES) :
    𝓕 (⇑F * ⇑G) x =
      (𝓕 ⇑F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] 𝓕 ⇑G) x := by
  set k : 𝓢(ES, ℂ) :=
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕 F) (𝓕 G) with hk
  have hcoe : ⇑k = 𝓕 ⇑F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] 𝓕 ⇑G :=
    schConv_coe (ContinuousLinearMap.mul ℂ ℂ) F G
  have hfa : 𝓕⁻ (𝓕 ⇑F) = ⇑F := by
    rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe,
      FourierTransform.fourierInv_fourier_eq]
  have hfb : 𝓕⁻ (𝓕 ⇑G) = ⇑G := by
    rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe,
      FourierTransform.fourierInv_fourier_eq]
  have hinv : 𝓕⁻ ⇑k = ⇑F * ⇑G := by
    funext y
    rw [hcoe, fourierInv_bilin_convolution (𝓕 ⇑F) (𝓕 ⇑G)
      (𝓕 F).integrable (𝓕 G).integrable y]
    rw [hfa, hfb]
    rfl
  calc 𝓕 (⇑F * ⇑G) x
      _ = 𝓕 (𝓕⁻ ⇑k) x := by rw [← hinv]
      _ = ⇑k x := by
        rw [← SchwartzMap.fourierInv_coe, ← SchwartzMap.fourier_coe,
          FourierTransform.fourier_fourierInv_eq]
      _ = (𝓕 ⇑F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] 𝓕 ⇑G) x := by rw [hcoe]

/-!
## 3. The stress-tensor Poisson identity for Schwartz data
-/

/-- Inverse-transform-side function reading of the derivative multiplier:
`𝓕(∂ₘψ)(ξ) = (2πi)⟪ξ,m⟫ · 𝓕ψ(ξ)`, the forward twin of
`ContinuousLeiLinPressurePhysical.fourierInv_lineDeriv_apply`. -/
theorem fourier_lineDeriv_apply (ψ : 𝓢(ES, ℂ)) (m : ES) (ξ : ES) :
    𝓕 (⇑((∂_{m} ψ : 𝓢(ES, ℂ)))) ξ =
      (2 * Real.pi * Complex.I) * (inner ℝ ξ m : ℂ) * 𝓕 ⇑ψ ξ := by
  have hg : (fun x : ES => inner ℝ x m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hstep : 𝓕 (⇑((∂_{m} ψ : 𝓢(ES, ℂ)))) ξ =
      ((2 * Real.pi * Complex.I) : ℂ) • (inner ℝ ξ m • 𝓕 ⇑ψ ξ) := by
    rw [← SchwartzMap.fourier_coe, SchwartzMap.fourier_lineDerivOp_eq,
      smul_apply, smulLeftCLM_apply_apply hg, SchwartzMap.fourier_coe]
  rw [hstep]
  simp [mul_assoc]

/-- Twice the derivative multiplier:
`𝓕(∂ₘ∂ₙ w) = -(2π)²⟪ξ,m⟫⟪ξ,n⟫ · 𝓕 w`. -/
theorem fourier_iteratedLineDeriv_apply (w : 𝓢(ES, ℂ)) (m n : ES) (ξ : ES) :
    𝓕 (⇑((∂_{m} (∂_{n} w) : 𝓢(ES, ℂ)))) ξ =
      -((2 * Real.pi : ℂ) ^ 2) * (inner ℝ ξ m : ℂ) * (inner ℝ ξ n : ℂ) * 𝓕 ⇑w ξ := by
  have hI : (2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I) =
      -((2 * Real.pi : ℂ) ^ 2) := by
    rw [show (2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I) =
        ((2 * Real.pi : ℂ) ^ 2) * (Complex.I ^ 2) from by ring,
      Complex.I_sq]
    ring
  have hc : (2 * Real.pi * Complex.I) * (inner ℝ ξ m : ℂ) *
      ((2 * Real.pi * Complex.I) * (inner ℝ ξ n : ℂ) * 𝓕 ⇑w ξ) =
      ((2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I)) *
        ((inner ℝ ξ m : ℂ) * (inner ℝ ξ n : ℂ) * 𝓕 ⇑w ξ) := by ring
  rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply, hc, hI]
  ring

/-- The datum coordinate is the transform of its Euclidean component. -/
private theorem coord_fourier (u₀ : SchwartzVelocity) (k : Fin 3) :
    (fun η : ES => fourierDatum u₀ η k) = 𝓕 ⇑(euclidComponent u₀ k) := by
  funext η
  simp [fourierDatum, SchwartzMap.fourier_coe]

private theorem basisVec_inner (ξ : ES) (j : Fin 3) :
    (inner ℝ ξ (basisVec j) : ℂ) = (ξ j : ℂ) := by
  rw [basisVec, EuclideanSpace.inner_single_right]
  simp

/-- The pointwise product of two datum coordinate maps.  The pinned Mathlib
has no `Mul` instance on `𝓢`; `SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)`
is the pointwise-product transport (its `pairing_apply` is definitionally
`⇑(f ⋅ g) = ⇑f * ⇑g` at the function level). -/
private def coordProd (u₀ : SchwartzVelocity) (i j : Fin 3) : 𝓢(ES, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
    (euclidComponent u₀ i) (euclidComponent u₀ j)

private theorem coordProd_apply (u₀ : SchwartzVelocity) (i j : Fin 3) :
    ⇑(coordProd u₀ i j) = ⇑(euclidComponent u₀ i) * ⇑(euclidComponent u₀ j) :=
  SchwartzMap.pairing_apply (ContinuousLinearMap.mul ℂ ℂ)
    (euclidComponent u₀ i) (euclidComponent u₀ j)

/-- The one-term stress rewrite: for the datum velocity coordinates,
`(2π)² ξᵢξⱼ · (v̂ᵢ ⋆ v̂ⱼ)(ξ) = -𝓕(∂ᵢ∂ⱼ(vᵢ vⱼ))(ξ)`, the frequency source of
the landed physical pairing matched to the Fourier image of the physical
stress term (derivative multiplier twice + forward bridge).  The minus is
`(2πi)² = -(2π)²`. -/
theorem stressTerm_fourier (u₀ : SchwartzVelocity) (i j : Fin 3) (ξ : ES) :
    ((2 * Real.pi : ℂ) ^ 2) * (ξ i * ξ j : ℂ) *
      ((fun η : ES => fourierDatum u₀ η i) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        (fun η : ES => fourierDatum u₀ η j)) ξ =
    -𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
        (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
        𝓢(ES, ℂ)))) ξ := by
  have hfw := fourier_mul_bilin_convolution
    (euclidComponent u₀ i) (euclidComponent u₀ j) ξ
  have hder := fourier_iteratedLineDeriv_apply
    (coordProd u₀ i j) (basisVec i) (basisVec j) ξ
  have hcoe : (⇑(euclidComponent u₀ i) * ⇑(euclidComponent u₀ j)) =
      ⇑(coordProd u₀ i j) := (coordProd_apply u₀ i j).symm
  rw [coord_fourier u₀ i, coord_fourier u₀ j, ← hfw, hder,
    basisVec_inner ξ i, basisVec_inner ξ j, hcoe]
  ring

/-- One-term pairing transfer: the frequency pairing of the stress term's
Fourier image against `𝓕⁻ψ` equals the physical pairing of the stress term
against `ψ` — bilinear self-adjointness of `𝓕` on `𝓢`
(`SchwartzMap.integral_bilin_fourier_eq`). -/
theorem stressTerm_pairing (u₀ : SchwartzVelocity) (i j : Fin 3)
    (ψ : 𝓢(ES, ℂ)) :
    ∫ ξ : ES, 𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
        (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
        𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ =
      ∫ x : ES, ⇑((∂_{basisVec i} (∂_{basisVec j}
        (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
        𝓢(ES, ℂ))) x * ⇑ψ x := by
  set w : 𝓢(ES, ℂ) := ∂_{basisVec i} (∂_{basisVec j}
    (coordProd u₀ i j)) with hw
  have hbb := integral_bilin_fourier_eq w (𝓕⁻ ψ) (ContinuousLinearMap.mul ℂ ℂ)
  convert hbb using 1
  · congr
    ext ξ
    simp only [SchwartzMap.fourier_coe, SchwartzMap.fourierInv_coe,
      ContinuousLinearMap.mul_apply']
  · congr
    ext x
    rw [ContinuousLinearMap.mul_apply', FourierTransform.fourier_fourierInv_eq]

/-- The summand of the stress pairing is integrable in the frequency slot —
the side condition for swapping the double sum and the integral. -/
private theorem integrable_stressTerm_pairing (u₀ : SchwartzVelocity)
    (i j : Fin 3) (ψ : 𝓢(ES, ℂ)) :
    Integrable (fun ξ : ES =>
      𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
        (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
        𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ) := by
  set w : 𝓢(ES, ℂ) := ∂_{basisVec i} (∂_{basisVec j}
    (coordProd u₀ i j)) with hw
  have heq : (fun ξ : ES => 𝓕 ⇑w ξ * 𝓕⁻ ⇑ψ ξ) =
      ⇑(SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 w) (𝓕⁻ ψ)) := by
    funext ξ
    simp only [SchwartzMap.pairing_apply_apply, SchwartzMap.fourier_coe,
      SchwartzMap.fourierInv_coe, ContinuousLinearMap.mul_apply']
  rw [heq]
  exact (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 w) (𝓕⁻ ψ)).integrable

/-- **The stress-tensor form of the physical Poisson identity, for Schwartz
data.**  For `u₀ : SchwartzVelocity` (hence `u = fourierDatum u₀` carries the
primitive's premises) and every Schwartz test `ψ`:

  `∫ x, p x • (Δψ) x = -∑ᵢ ∑ⱼ ∫ x, ∂ᵢ∂ⱼ(vᵢ vⱼ) x • ψ x`,

with `p = continuousPressurePhysical (fourierDatum u₀)` and
`vᵢ = 𝓕⁻(fourierDatum u₀)·ᵢ = ⇑(euclidComponent u₀ i)` the physical velocity
(`physicalCoord_fourierDatum`).  Distributionally this reads
`Δp = -∑ᵢⱼ ∂ᵢ∂ⱼ(vᵢ vⱼ)`: the fully-physical stress-tensor rewrite of the
frequency side that the `ContinuousLeiLinPressurePhysical` header names as
its residual, delivered under the Schwartz specialization. -/
theorem continuousPressurePhysical_pairing_stressTensor
    (u₀ : SchwartzVelocity) (ψ : 𝓢(ES, ℂ)) :
    ∫ x : ES, continuousPressurePhysical (fourierDatum u₀) x •
        ⇑(physicalLaplacian ψ) x =
      -(∑ i : Fin 3, ∑ j : Fin 3,
        ∫ x : ES, ⇑((∂_{basisVec i} (∂_{basisVec j}
          (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
          𝓢(ES, ℂ))) x • ⇑ψ x) := by
  have hprem0 : ∀ k : Fin 3, AEStronglyMeasurable
      (fun η : ES => fourierDatum u₀ η k) := fourierDatum_aesm u₀
  have hprem1 : ∀ k : Fin 3, Integrable (fun η : ES => ‖fourierDatum u₀ η k‖) :=
    fourierDatum_integrable u₀
  have hbase := continuousPressurePhysical_pairing_physicalLaplacian
    (fourierDatum u₀) hprem0 hprem1 ψ
  -- push the (2π)² prefactor inside the frequency integral
  have hpush : ((2 * Real.pi : ℂ) ^ 2) *
      (∫ ξ : ES, (∑ i : Fin 3, ∑ j : Fin 3,
          (ξ i * ξ j : ℂ) *
            ((fun η => fourierDatum u₀ η i)
                ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (fun η => fourierDatum u₀ η j)) ξ) * 𝓕⁻ ⇑ψ ξ) =
      ∫ ξ : ES, ((2 * Real.pi : ℂ) ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
          (ξ i * ξ j : ℂ) *
            ((fun η => fourierDatum u₀ η i)
                ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (fun η => fourierDatum u₀ η j)) ξ)) * 𝓕⁻ ⇑ψ ξ := by
    calc ((2 * Real.pi : ℂ) ^ 2) * (∫ ξ : ES, (∑ i : Fin 3, ∑ j : Fin 3,
          (ξ i * ξ j : ℂ) *
            ((fun η => fourierDatum u₀ η i)
                ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
              (fun η => fourierDatum u₀ η j)) ξ) * 𝓕⁻ ⇑ψ ξ)
        _ = ((2 * Real.pi : ℂ) ^ 2) •
              ∫ ξ : ES, (∑ i : Fin 3, ∑ j : Fin 3,
                  (ξ i * ξ j : ℂ) *
                    ((fun η => fourierDatum u₀ η i)
                        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                      (fun η => fourierDatum u₀ η j)) ξ) * 𝓕⁻ ⇑ψ ξ :=
          (smul_eq_mul _ _).symm
        _ = ∫ ξ : ES, ((2 * Real.pi : ℂ) ^ 2) •
              ((∑ i : Fin 3, ∑ j : Fin 3,
                  (ξ i * ξ j : ℂ) *
                    ((fun η => fourierDatum u₀ η i)
                        ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                      (fun η => fourierDatum u₀ η j)) ξ) * 𝓕⁻ ⇑ψ ξ) :=
          (integral_smul _ _).symm
        _ = ∫ ξ : ES, ((2 * Real.pi : ℂ) ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
              (ξ i * ξ j : ℂ) *
                ((fun η => fourierDatum u₀ η i)
                    ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
                  (fun η => fourierDatum u₀ η j)) ξ)) * 𝓕⁻ ⇑ψ ξ := by
          refine integral_congr_ae (ae_of_all volume fun ξ => ?_)
          simp only [smul_eq_mul, mul_assoc]
  rw [hpush] at hbase
  -- per-term stress rewrite of the frequency source
  have hterm : (fun ξ : ES => ((2 * Real.pi : ℂ) ^ 2 * (∑ i : Fin 3, ∑ j : Fin 3,
        (ξ i * ξ j : ℂ) *
          ((fun η => fourierDatum u₀ η i)
              ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
            (fun η => fourierDatum u₀ η j)) ξ)) * 𝓕⁻ ⇑ψ ξ) =
      (fun ξ : ES => ∑ i : Fin 3, ∑ j : Fin 3,
        -(𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
            (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
            𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ)) := by
    funext ξ
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, stressTerm_fourier u₀ i j ξ]
    ring
  rw [hterm] at hbase
  rw [hbase]
  simp only [smul_eq_mul]
  -- swap sum and integral termwise (all summands integrable: Schwartz coes)
  have hswap : (∫ ξ : ES, ∑ i : Fin 3, ∑ j : Fin 3,
        -(𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
            (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
            𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ)) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES,
        -(𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
            (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
            𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ) := by
    refine (integral_finsetSum Finset.univ
        (f := fun i : Fin 3 => fun ξ => ∑ j : Fin 3,
          -(𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
              (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
              𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ)) ?_).trans
      (Finset.sum_congr rfl fun i _ =>
        integral_finsetSum Finset.univ
          (f := fun j : Fin 3 => fun ξ =>
            -(𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
                (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
                𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ)) ?_)
    · exact fun i _ => integrable_finsetSum Finset.univ
        (fun j _ => (integrable_stressTerm_pairing u₀ i j ψ).neg)
    · exact fun j _ => (integrable_stressTerm_pairing u₀ i j ψ).neg
  rw [hswap]
  have hneg : (∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES,
        -(𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
            (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
            𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ)) =
      -(∑ i : Fin 3, ∑ j : Fin 3, ∫ ξ : ES,
        𝓕 (⇑((∂_{basisVec i} (∂_{basisVec j}
            (coordProd u₀ i j) : 𝓢(ES, ℂ)) :
            𝓢(ES, ℂ)))) ξ * 𝓕⁻ ⇑ψ ξ) := by
    simp only [integral_neg, Finset.sum_neg_distrib]
  rw [hneg, neg_inj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [stressTerm_pairing u₀ i j ψ]

/-!
## 4. Continuity moduli (the `X⁰`-quotient estimates)
-/

/-- The Fourier kernel is a unit multiplier on `ℂ` (circle action). -/
private theorem norm_smul_fourierChar (t : ℝ) (z : ℂ) : ‖𝐞 t • z‖ = ‖z‖ := by
  simp

private theorem integrable_fourierChar_smul {f : ES → ℂ} (hf : Integrable f)
    (y : ES) : Integrable (fun z : ES => 𝐞 ⟪z, y⟫ • f z) := by
  have hmeas : AEStronglyMeasurable (fun z : ES => 𝐞 ⟪z, y⟫) volume :=
    (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const)).aestronglyMeasurable
  have hfn : (fun z : ES => 𝐞 ⟪z, y⟫ • f z) = (fun z : ES => 𝐞 ⟪z, y⟫) • f := rfl
  rw [hfn]
  refine (integrable_norm_iff (hmeas.smul hf.aestronglyMeasurable)).mp ?_
  have hnorm : (fun a : ES => ‖((fun z : ES => 𝐞 ⟪z, y⟫) • f) a‖) =
      fun a : ES => ‖f a‖ := by
    funext a
    show ‖𝐞 ⟪a, y⟫ • f a‖ = ‖f a‖
    exact norm_smul_fourierChar ⟪a, y⟫ (f a)
  rw [hnorm]
  exact hf.norm

/-- Inversion is a contraction `L¹ → C_b`: `|𝓕⁻ f x| ≤ ∫ ‖f‖` at every
point, unconditionally. -/
theorem norm_fourierInv_le_integral_norm (f : ES → ℂ) (x : ES) :
    ‖𝓕⁻ f x‖ ≤ ∫ ξ : ES, ‖f ξ‖ := by
  rw [Real.fourierInv_eq]
  refine (norm_integral_le_integral_norm (fun v : ES => 𝐞 ⟪v, x⟫ • f v)).trans ?_
  exact (integral_congr_ae
    (ae_of_all volume fun v => norm_smul_fourierChar ⟪v, x⟫ (f v))).le

private theorem fourierInv_sub (f g : ES → ℂ) (hf : Integrable f) (hg : Integrable g) :
    𝓕⁻ (f - g) = 𝓕⁻ f - 𝓕⁻ g := by
  funext x
  show 𝓕⁻ (f - g) x = 𝓕⁻ f x - 𝓕⁻ g x
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq]
  rw [integral_congr_ae (ae_of_all volume fun v => by
      rw [Pi.sub_apply, smul_sub]),
    integral_sub (integrable_fourierChar_smul hf x) (integrable_fourierChar_smul hg x)]

/-- Pointwise stability of the product side of the bridge:
`|𝓕⁻a x · 𝓕⁻b x − 𝓕⁻c x · 𝓕⁻d x| ≤ ‖a−c‖₁·∫‖b‖ + ∫‖c‖·‖b−d‖₁` — the
joint-continuity modulus of the bridge's right side, uniformly in `x`. -/
theorem norm_fourierInv_mul_sub_le (a b c d : ES → ℂ) (x : ES)
    (ha : Integrable a) (hb : Integrable b) (hc : Integrable c) (hd : Integrable d) :
    ‖𝓕⁻ a x * 𝓕⁻ b x - 𝓕⁻ c x * 𝓕⁻ d x‖ ≤
      (∫ ξ : ES, ‖(a - c) ξ‖) * (∫ η : ES, ‖b η‖) +
        (∫ ξ : ES, ‖c ξ‖) * (∫ η : ES, ‖(b - d) η‖) := by
  have hA : ‖𝓕⁻ (a - c) x‖ ≤ ∫ ξ : ES, ‖(a - c) ξ‖ :=
    norm_fourierInv_le_integral_norm _ x
  have hA' : 𝓕⁻ (a - c) x = 𝓕⁻ a x - 𝓕⁻ c x :=
    congrFun (fourierInv_sub a c ha hc) x
  have hB : ‖𝓕⁻ b x‖ ≤ ∫ η : ES, ‖b η‖ := norm_fourierInv_le_integral_norm _ x
  have hC : ‖𝓕⁻ c x‖ ≤ ∫ ξ : ES, ‖c ξ‖ := norm_fourierInv_le_integral_norm _ x
  have hD : ‖𝓕⁻ (b - d) x‖ ≤ ∫ η : ES, ‖(b - d) η‖ :=
    norm_fourierInv_le_integral_norm _ x
  have hD' : 𝓕⁻ (b - d) x = 𝓕⁻ b x - 𝓕⁻ d x :=
    congrFun (fourierInv_sub b d hb hd) x
  have hAnonneg : 0 ≤ ∫ ξ : ES, ‖(a - c) ξ‖ := by positivity
  have hCnonneg : 0 ≤ ∫ ξ : ES, ‖c ξ‖ := by positivity
  have hAC : ‖𝓕⁻ a x - 𝓕⁻ c x‖ * ‖𝓕⁻ b x‖ ≤
      (∫ ξ : ES, ‖(a - c) ξ‖) * (∫ η : ES, ‖b η‖) :=
    mul_le_mul (by rw [← hA']; exact hA) hB (norm_nonneg _) hAnonneg
  have hBD : ‖𝓕⁻ c x‖ * ‖𝓕⁻ b x - 𝓕⁻ d x‖ ≤
      (∫ ξ : ES, ‖c ξ‖) * (∫ η : ES, ‖(b - d) η‖) :=
    mul_le_mul hC (by rw [← hD']; exact hD) (norm_nonneg _) hCnonneg
  have hsum : ‖𝓕⁻ a x - 𝓕⁻ c x‖ * ‖𝓕⁻ b x‖ + ‖𝓕⁻ c x‖ * ‖𝓕⁻ b x - 𝓕⁻ d x‖ ≤
      (∫ ξ : ES, ‖(a - c) ξ‖) * (∫ η : ES, ‖b η‖) +
        (∫ ξ : ES, ‖c ξ‖) * (∫ η : ES, ‖(b - d) η‖) :=
      add_le_add hAC hBD
  calc ‖𝓕⁻ a x * 𝓕⁻ b x - 𝓕⁻ c x * 𝓕⁻ d x‖
      _ = ‖(𝓕⁻ a x - 𝓕⁻ c x) * 𝓕⁻ b x + 𝓕⁻ c x * (𝓕⁻ b x - 𝓕⁻ d x)‖ := by ring
      _ ≤ ‖(𝓕⁻ a x - 𝓕⁻ c x) * 𝓕⁻ b x‖ + ‖𝓕⁻ c x * (𝓕⁻ b x - 𝓕⁻ d x)‖ :=
        norm_add_le _ _
      _ = ‖𝓕⁻ a x - 𝓕⁻ c x‖ * ‖𝓕⁻ b x‖ + ‖𝓕⁻ c x‖ * ‖𝓕⁻ b x - 𝓕⁻ d x‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ (∫ ξ : ES, ‖(a - c) ξ‖) * (∫ η : ES, ‖b η‖) +
            (∫ ξ : ES, ‖c ξ‖) * (∫ η : ES, ‖(b - d) η‖) := hsum

end Navier.Analysis.PressureStressTensor

#check @Navier.Analysis.PressureStressTensor.bilin_convolution_comp_neg
#check @Navier.Analysis.PressureStressTensor.fourierInv_bilin_convolution
#check @Navier.Analysis.PressureStressTensor.pressureStress_bridge_pointwise
#check @Navier.Analysis.PressureStressTensor.pressureStress_bridge_fourierDatum
#check @Navier.Analysis.PressureStressTensor.schConv_coe
#check @Navier.Analysis.PressureStressTensor.fourier_mul_bilin_convolution
#check @Navier.Analysis.PressureStressTensor.fourier_lineDeriv_apply
#check @Navier.Analysis.PressureStressTensor.fourier_iteratedLineDeriv_apply
#check @Navier.Analysis.PressureStressTensor.stressTerm_fourier
#check @Navier.Analysis.PressureStressTensor.stressTerm_pairing
#check @Navier.Analysis.PressureStressTensor.continuousPressurePhysical_pairing_stressTensor
#check @Navier.Analysis.PressureStressTensor.norm_fourierInv_le_integral_norm
#check @Navier.Analysis.PressureStressTensor.norm_fourierInv_mul_sub_le

#print axioms Navier.Analysis.PressureStressTensor.bilin_convolution_comp_neg
#print axioms Navier.Analysis.PressureStressTensor.fourierInv_bilin_convolution
#print axioms Navier.Analysis.PressureStressTensor.pressureStress_bridge_pointwise
#print axioms Navier.Analysis.PressureStressTensor.pressureStress_bridge_fourierDatum
#print axioms Navier.Analysis.PressureStressTensor.schConv_coe
#print axioms Navier.Analysis.PressureStressTensor.fourier_mul_bilin_convolution
#print axioms Navier.Analysis.PressureStressTensor.fourier_lineDeriv_apply
#print axioms Navier.Analysis.PressureStressTensor.fourier_iteratedLineDeriv_apply
#print axioms Navier.Analysis.PressureStressTensor.stressTerm_fourier
#print axioms Navier.Analysis.PressureStressTensor.stressTerm_pairing
#print axioms Navier.Analysis.PressureStressTensor.continuousPressurePhysical_pairing_stressTensor
#print axioms Navier.Analysis.PressureStressTensor.norm_fourierInv_le_integral_norm
#print axioms Navier.Analysis.PressureStressTensor.norm_fourierInv_mul_sub_le
