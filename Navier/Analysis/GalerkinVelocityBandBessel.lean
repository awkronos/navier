import Navier.Analysis.GalerkinTransverseBessel
import Navier.Analysis.GalerkinSpectralBandAssembly
import Navier.Analysis.GalerkinBasis

/-!
# Localized Fourier estimates in the original velocity Hilbert space

The Fourier model preserves the real `L²` inner product exactly. Thus the
transverse band estimate controls coefficients of the original orthonormal
velocity family for arbitrary input velocities.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Navier.Analysis.GalerkinVelocityBandBessel

open Navier Navier.Analysis.GalerkinBasis
open DivFreeGradientEnstrophy GalerkinSpectralBands GalerkinSpectralBandAssembly
open FourierTransverseProjection GalerkinTransverseBessel

local instance : InnerProductSpace ℝ CS := InnerProductSpace.rclikeToReal ℂ CS
attribute [local instance 2000] MeasureTheory.L2.innerProductSpace

def fourierL2Velocity (u : SchwartzVelocity) : Lp CS 2 (volume : Measure EuclSpace) :=
  schwartzL2 (𝓕 (euclModel u))

theorem fourierL2Velocity_norm_sq (u : SchwartzVelocity) :
    ‖fourierL2Velocity u‖ ^ 2 = ‖toL2 u‖ ^ 2 := by
  rw [fourierL2Velocity, schwartzL2_norm_sq,
    SchwartzMap.integral_norm_sq_fourier, ← velocityMass_eq_modelMass,
    norm_toL2_sq, schwartzL2Inner]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (Enstrophy.officialInner_self (u x)).symm

theorem fourierL2Velocity_add (u v : SchwartzVelocity) :
    fourierL2Velocity (u + v) = fourierL2Velocity u + fourierL2Velocity v := by
  have hm : euclModel (u + v) = euclModel u + euclModel v := by
    simp [euclModel]
  unfold fourierL2Velocity
  rw [hm, ← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℝ), map_add, map_add]
  rfl

/-- The original real velocity pairing is unchanged by the actual Fourier
and complexification maps. -/
theorem fourierL2Velocity_inner (u v : SchwartzVelocity) :
    inner ℝ (fourierL2Velocity u) (fourierL2Velocity v) =
      inner ℝ (toL2 u) (toL2 v) := by
  have hadd := fourierL2Velocity_norm_sq (u + v)
  rw [fourierL2Velocity_add, toL2_add,
    norm_add_sq_real, norm_add_sq_real,
    fourierL2Velocity_norm_sq, fourierL2Velocity_norm_sq] at hadd
  linarith

/-- Fourier images of the original real orthonormal velocity family remain
orthonormal in the real Hilbert structure of complex `L²`. -/
theorem fourierL2Velocity_orthonormal {ι : Type*}
    (w : ι → SchwartzVelocity) (hw : Orthonormal ℝ (fun i => toL2 (w i))) :
    Orthonormal ℝ (fun i => fourierL2Velocity (w i)) := by
  classical
  rw [orthonormal_iff_ite] at hw ⊢
  intro i j
  rw [fourierL2Velocity_inner]
  exact hw i j

set_option maxHeartbeats 800000 in
/-- Annulus localization for the coefficients used by the original Galerkin
projection. Only the basis fields are divergence-free; the input velocity is
arbitrary. The right side retains localization for later disjoint-band sums.
-/
theorem velocityBand_coefficient_curlSymbol_bound
    {ι : Type*} [Fintype ι] (w : ι → SchwartzVelocity)
    (hw : Orthonormal ℝ (fun i => toL2 (w i)))
    (hdiv : ∀ i, DivergenceFreeInitial (w i))
    (u : SchwartzVelocity) {B : Set EuclSpace} (hB : MeasurableSet B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hband : ∀ ξ ∈ B, a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ b)
    (hsupport : ∀ i ξ, ξ ∉ B → (𝓕 (euclModel (w i))) ξ = 0) :
    a ^ 2 * (∑ i, ‖inner ℝ (toL2 (w i)) (toL2 u)‖ ^ 2) ≤
      ∫ ξ in B, curlSymbolEnergy ξ ((𝓕 (euclModel u)) ξ) := by
  have hwmem (i : ι) : MemLp (fun ξ => (𝓕 (euclModel (w i))) ξ) 2
      (volume : Measure EuclSpace) := (𝓕 (euclModel (w i))).memLp 2 volume
  have humem : MemLp (fun ξ => (𝓕 (euclModel u)) ξ) 2
      (volume : Measure EuclSpace) := (𝓕 (euclModel u)).memLp 2 volume
  have hworth : Orthonormal ℝ (fun i => (hwmem i).toLp
      (fun ξ => (𝓕 (euclModel (w i))) ξ)) :=
    fourierL2Velocity_orthonormal w hw
  have ht (i : ι) : ∀ᵐ ξ : EuclSpace,
      inner ℂ (frequencyVector ξ) ((𝓕 (euclModel (w i))) ξ) = 0 := by
    filter_upwards [] with ξ
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      frequencyVector, mul_comm] using
      fourier_dot_eq_zero_of_divFree (w i) (hdiv i) ξ
  have hpre := lowerRadius_sq_mul_sum_inner_sq_le_curlSymbolIntegral
    (ι := ι) (B := B) (a := a) (b := b)
    (fun i ξ => (𝓕 (euclModel (w i))) ξ) hwmem
  have hpre2 := hpre hworth
  have h := hpre2
    (fun ξ => (𝓕 (euclModel u)) ξ) humem hB ha hb hband
    (fun i => Filter.Eventually.of_forall (hsupport i)) ht
  change a ^ 2 * (∑ i, ‖inner ℝ (fourierL2Velocity (w i))
      (fourierL2Velocity u)‖ ^ 2) ≤ _ at h
  simpa only [fourierL2Velocity_inner] using h

end Navier.Analysis.GalerkinVelocityBandBessel
