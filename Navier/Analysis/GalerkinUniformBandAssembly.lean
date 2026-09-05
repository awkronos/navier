import Navier.Analysis.GalerkinDisjointBands

/-! Uniform physical curl control for projections assembled across disjoint bands. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Navier.Analysis.GalerkinUniformBandAssembly

open Navier GalerkinBasis DivFreeGradientEnstrophy
open FourierTransverseProjection GalerkinBandProjection GalerkinDisjointBands

theorem integrable_curlSymbolEnergy (g : 𝓢(EuclSpace, CS)) :
    Integrable (fun ξ => curlSymbolEnergy ξ (g ξ)) := by
  refine (integrable_weighted_normSq g 2).mono'
    (by unfold curlSymbolEnergy; fun_prop) ?_
  filter_upwards [] with ξ
  have hn : 0 ≤ curlSymbolEnergy ξ (g ξ) := by
    unfold curlSymbolEnergy
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hn, curlSymbolEnergy_lagrange]
  exact sub_le_self _ (sq_nonneg _)

theorem sum_band_curlSymbolIntegral_le {ι : Type*} [Fintype ι]
    (g : 𝓢(EuclSpace, CS)) (B : ι → Set EuclSpace)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (∑ i, ∫ ξ in B i, curlSymbolEnergy ξ (g ξ)) ≤
      ∫ ξ, curlSymbolEnergy ξ (g ξ) := by
  classical
  have hu := integral_biUnion_finset Finset.univ (fun i _ => hB i)
    (fun i _ j _ hij => hdisj hij)
    (fun _ _ => (integrable_curlSymbolEnergy g).integrableOn)
  rw [← hu]
  apply setIntegral_le_integral (integrable_curlSymbolEnergy g)
  filter_upwards [] with ξ
  unfold curlSymbolEnergy
  positivity

set_option maxHeartbeats 800000 in
/-- The physical curl energy of the sum of finite orthogonal band projections
is at most four times the input curl energy. The input need not be divergence
free, and the constant does not depend on the number or radii of the bands. -/
theorem finite_band_projections_curl_energy_le_four
    {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (w : (i : ι) → κ i → SchwartzVelocity)
    (hw : ∀ i, Orthonormal ℝ (fun j => toL2 (w i j)))
    (hdiv : ∀ i j, DivergenceFreeInitial (w i j))
    (u : SchwartzVelocity) (B : ι → Set EuclSpace)
    (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (a : ι → ℝ) (ha : ∀ i, 0 < a i)
    (hband : ∀ i ξ, ξ ∈ B i → a i ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * a i)
    (hsupport : ∀ i j ξ, ξ ∉ B i → (𝓕 (euclModel (w i j))) ξ = 0) :
    (∫ x : Space, OfficialABEncoding.officialEuclideanNorm
        (Vorticity.staticCurl
          (∑ i, velocityProjection (w i) u : SchwartzVelocity) x) ^ 2) ≤
      4 * ∫ x : Space, OfficialABEncoding.officialEuclideanNorm
        (Vorticity.staticCurl u x) ^ 2 := by
  classical
  have hadd := curl_energy_sum_of_disjoint_fourier_bands (ι := ι)
    (fun i => velocityProjection (w i) u)
    (fun i => velocityProjection_divFree (w i) (hdiv i) u)
    B hdisj (fun i => velocityProjection_fourier_support (w i) u (hsupport i))
  rw [hadd]
  have hpoint (i : ι) := velocityProjection_dyadicBand_curl_energy (ι := κ i)
    (w i) (hw i) (hdiv i) u (B := B i) (hB i) (a := a i) (ha i) (hband i) (hsupport i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hsum
  have hwhole := mul_le_mul_of_nonneg_left
    (sum_band_curlSymbolIntegral_le (𝓕 (euclModel u)) B hB hdisj)
    (by positivity : 0 ≤ 16 * Real.pi ^ 2)
  have hcurl : (∫ x : Space, OfficialABEncoding.officialEuclideanNorm
    (Vorticity.staticCurl u x) ^ 2) =
      4 * Real.pi ^ 2 * ∫ ξ, curlSymbolEnergy ξ ((𝓕 (euclModel u)) ξ) := by
    simpa only [curlSymbolEnergy] using curl_sq_eq_fourierCrossEnergy u
  rw [hcurl]
  nlinarith [hsum.trans hwhole]

end Navier.Analysis.GalerkinUniformBandAssembly
