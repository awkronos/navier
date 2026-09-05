import Navier.Analysis.GalerkinBandProjection

/-! # Additivity of actual curl energy across disjoint Fourier bands -/

noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Navier.Analysis.GalerkinDisjointBands

open Navier GalerkinBasis DivFreeGradientEnstrophy
open GalerkinSpectralBands GalerkinSpectralBandAssembly
open FourierTransverseProjection GalerkinBandProjection

theorem integrable_weighted_normSq {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (g : 𝓢(EuclSpace, H)) (k : ℕ) :
    Integrable (fun x : EuclSpace => ‖x‖ ^ k * ‖g x‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := g.decay 0 0
  have hbound : ∀ x, ‖g x‖ ≤ C := by
    intro x
    simpa using hC x
  refine ((g.integrable_pow_mul volume k).const_mul C).mono'
    (by fun_prop) ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖x‖ ^ k * ‖g x‖ ^ 2 = ‖g x‖ * (‖x‖ ^ k * ‖g x‖) := by ring
    _ ≤ C * (‖x‖ ^ k * ‖g x‖) :=
      mul_le_mul_of_nonneg_right (hbound x) (by positivity)

theorem norm_sum_sq_of_pairwise_zero {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] (z : ι → H)
    (hz : ∀ i j, i ≠ j → z i = 0 ∨ z j = 0) :
    ‖∑ i, z i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  classical
  by_cases h : ∃ i, z i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hzero (j : ι) (hji : j ≠ i) : z j = 0 :=
      (hz i j hji.symm).resolve_left hi
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · intro j _ hji
      simp [hzero j hji]
    · simp
    · intro j _ hji
      exact hzero j hji
    · simp
  · push Not at h
    simp [h]

theorem fourier_euclModel_sum {ι : Type*} [Fintype ι]
    (v : ι → SchwartzVelocity) :
    𝓕 (euclModel (∑ i, v i)) = ∑ i, 𝓕 (euclModel (v i)) := by
  have hm : euclModel (∑ i, v i) = ∑ i, euclModel (v i) := by
    simp [euclModel]
  rw [hm, ← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℝ), map_sum]
  rfl

/-- Exact energy additivity; disjointness is on actual Fourier supports, and
the displayed whole-space integrals are finite by Schwartz decay. -/
theorem curl_energy_sum_of_disjoint_fourier_bands
    {ι : Type*} [Fintype ι] (v : ι → SchwartzVelocity)
    (hdiv : ∀ i, DivergenceFreeInitial (v i)) (B : ι → Set EuclSpace)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hsupport : ∀ i ξ, ξ ∉ B i → (𝓕 (euclModel (v i))) ξ = 0) :
    (∫ x : Space, OfficialABEncoding.officialEuclideanNorm
        (Vorticity.staticCurl (∑ i, v i : SchwartzVelocity) x) ^ 2) =
      ∑ i, ∫ x : Space, OfficialABEncoding.officialEuclideanNorm
        (Vorticity.staticCurl (v i) x) ^ 2 := by
  classical
  have hsumdiv : DivergenceFreeInitial (∑ i, v i) := by
    simpa using divergenceFreeInitial_sum_smul Finset.univ (fun _ => 1) v hdiv
  rw [curl_sq_eq_fourierWeight_of_divFree _ hsumdiv]
  simp_rw [curl_sq_eq_fourierWeight_of_divFree _ (hdiv _)]
  rw [← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_weighted_normSq (𝓕 (euclModel (v i))) 2)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hz : ∀ i j, i ≠ j →
      (𝓕 (euclModel (v i))) ξ = 0 ∨ (𝓕 (euclModel (v j))) ξ = 0 := by
    intro i j hij
    by_cases hi : ξ ∈ B i
    · right
      apply hsupport j ξ
      exact fun hj => Set.disjoint_left.mp (hdisj hij) hi hj
    · exact Or.inl (hsupport i ξ hi)
  rw [fourier_euclModel_sum]
  have hsum : (∑ i, 𝓕 (euclModel (v i))) ξ =
      ∑ i, (𝓕 (euclModel (v i))) ξ := by simp
  rw [hsum]
  rw [norm_sum_sq_of_pairwise_zero _ hz, Finset.mul_sum]

end Navier.Analysis.GalerkinDisjointBands
