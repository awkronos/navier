import Navier.Analysis.GalerkinVelocityBandBessel

/-!
# Uniform curl control for a finite projection inside one Fourier band

The projection is a finite sum of actual divergence-free Schwartz velocities.
Its curl energy is bounded by the input curl-symbol energy in the same band,
with a constant independent of the band's radius and of the number of modes.
-/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Navier.Analysis.GalerkinBandProjection

open Navier GalerkinBasis DivFreeGradientEnstrophy
open GalerkinSpectralBands GalerkinSpectralBandAssembly
open FourierTransverseProjection GalerkinVelocityBandBessel

theorem toL2_finset_sum {ι : Type*} (s : Finset ι)
    (v : ι → SchwartzVelocity) : toL2 (∑ i ∈ s, v i) = ∑ i ∈ s, toL2 (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change (SchwartzMap.toLpCLM ℝ (EuclideanSpace ℝ (Fin 3)) 2 volume)
        ((SchwartzMap.postcompCLM esCLM) 0) = 0
      simp only [map_zero]
  | @insert i s hi ih => simp [Finset.sum_insert hi, toL2_add, ih]

def velocityProjection {ι : Type*} [Fintype ι]
    (w : ι → SchwartzVelocity) (u : SchwartzVelocity) : SchwartzVelocity :=
  ∑ i, (inner ℝ (toL2 (w i)) (toL2 u)) • w i

theorem velocityProjection_divFree {ι : Type*} [Fintype ι]
    (w : ι → SchwartzVelocity) (hdiv : ∀ i, DivergenceFreeInitial (w i))
    (u : SchwartzVelocity) : DivergenceFreeInitial (velocityProjection w u) := by
  classical
  exact divergenceFreeInitial_sum_smul Finset.univ _ w hdiv

theorem velocityProjection_norm_sq {ι : Type*} [Fintype ι]
    (w : ι → SchwartzVelocity) (hw : Orthonormal ℝ (fun i => toL2 (w i)))
    (u : SchwartzVelocity) :
    ‖toL2 (velocityProjection w u)‖ ^ 2 =
      ∑ i, ‖inner ℝ (toL2 (w i)) (toL2 u)‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [velocityProjection, toL2_finset_sum, toL2_smul]
  rw [hw.inner_sum _ _ Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  simp [pow_two]

theorem velocityProjection_fourier_support {ι : Type*} [Fintype ι]
    (w : ι → SchwartzVelocity) (u : SchwartzVelocity) {B : Set EuclSpace}
    (hsupport : ∀ i ξ, ξ ∉ B → (𝓕 (euclModel (w i))) ξ = 0) :
    ∀ ξ, ξ ∉ B → (𝓕 (euclModel (velocityProjection w u))) ξ = 0 := by
  classical
  intro ξ hξ
  have hm : euclModel (velocityProjection w u) =
      ∑ i, (inner ℝ (toL2 (w i)) (toL2 u)) • euclModel (w i) := by
    simp [velocityProjection, euclModel]
  rw [hm, ← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℝ)]
  simp only [map_sum, map_smul]
  simp [hsupport _ ξ hξ]

theorem modelMass_eq_toL2_norm_sq (u : SchwartzVelocity) :
    (∫ ξ : EuclSpace, ‖euclModel u ξ‖ ^ 2) = ‖toL2 u‖ ^ 2 := by
  rw [← velocityMass_eq_modelMass, norm_toL2_sq, schwartzL2Inner]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (Enstrophy.officialInner_self (u x)).symm

theorem velocityProjection_dyadicBand_curl_energy
    {ι : Type*} [Fintype ι] (w : ι → SchwartzVelocity)
    (hw : Orthonormal ℝ (fun i => toL2 (w i)))
    (hdiv : ∀ i, DivergenceFreeInitial (w i)) (u : SchwartzVelocity)
    {B : Set EuclSpace} (hB : MeasurableSet B) {a : ℝ} (ha : 0 < a)
    (hband : ∀ ξ ∈ B, a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a)
    (hsupport : ∀ i ξ, ξ ∉ B → (𝓕 (euclModel (w i))) ξ = 0) :
    (∫ x : Space, OfficialABEncoding.officialEuclideanNorm
        (Vorticity.staticCurl (velocityProjection w u) x) ^ 2) ≤
      (16 * Real.pi ^ 2) *
        ∫ ξ in B, curlSymbolEnergy ξ ((𝓕 (euclModel u)) ξ) := by
  have hprojSupport := velocityProjection_fourier_support w u hsupport
  have hprojBand : ∀ ξ, (𝓕 (euclModel (velocityProjection w u))) ξ ≠ 0 →
      a ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a := by
    intro ξ hξ
    apply hband ξ
    by_contra hnot
    exact hξ (hprojSupport ξ hnot)
  have hupper := (fourierBand_dirichlet_bounds
    (euclModel (velocityProjection w u)) ha.le (by positivity) hprojBand).2
  rw [modelMass_eq_toL2_norm_sq, velocityProjection_norm_sq w hw] at hupper
  have hcoeff := velocityBand_coefficient_curlSymbol_bound w hw hdiv u
    hB ha.le (by positivity) hband hsupport
  rw [curl_sq_eq_fourierWeight_of_divFree _ (velocityProjection_divFree w hdiv u)]
  have hupper' := mul_le_mul_of_nonneg_left hupper
    (by positivity : 0 ≤ 4 * Real.pi ^ 2)
  have hcoeff' := mul_le_mul_of_nonneg_left hcoeff
    (by positivity : 0 ≤ 16 * Real.pi ^ 2)
  nlinarith

end Navier.Analysis.GalerkinBandProjection
