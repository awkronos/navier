import Navier.Analysis.GalerkinFourierReality
import Navier.Analysis.GalerkinSpectralBandAssembly

/-!
# Physical curl-graph convergence of Fourier-band approximants

For real divergence-free Schwartz velocities, Plancherel identifies the
physical `L² × curl-L²` graph error with a Fourier integral carrying the
weight `1 + 4π²|ξ|²`.  The weighted approximation already constructed in
`GalerkinFourierReality` therefore converges in the actual physical graph
topology whenever the datum is supported in the prescribed dyadic band.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped FourierTransform SchwartzMap Topology

namespace Navier.Analysis.GalerkinCurlGraphDensity

open Navier
open Navier.Analysis.DivFreeGradientEnstrophy
open Navier.Analysis.Enstrophy
open Navier.Analysis.GalerkinAnnularApproximation
open Navier.Analysis.GalerkinBandDenseFamily
open Navier.Analysis.GalerkinBasis
open Navier.Analysis.GalerkinDisjointBands
open Navier.Analysis.GalerkinFourierReality
open Navier.Analysis.GalerkinSpectralBandAssembly
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

/-- The squared physical graph error: velocity `L²` plus vorticity `L²`.
Both factors are the repository's actual physical `Lp` realizations. -/
def physicalVelocityCurlErrorSq (v u : SchwartzVelocity) : ℝ :=
  ‖toL2 v - toL2 u‖ ^ 2 +
    ‖toL2 (curlSchwartzCLM v) - toL2 (curlSchwartzCLM u)‖ ^ 2

private theorem divergenceFreeInitial_sub (v u : SchwartzVelocity)
    (hv : DivergenceFreeInitial v) (hu : DivergenceFreeInitial u) :
    DivergenceFreeInitial (v - u) := by
  simpa [sub_eq_add_neg] using
    divergenceFreeInitial_add_smul v u (-1) hv hu

private theorem fourier_euclModel_sub (v u : SchwartzVelocity) :
    𝓕 (euclModel (v - u)) = 𝓕 (euclModel v) - 𝓕 (euclModel u) := by
  have hm : euclModel (v - u) = euclModel v - euclModel u := by
    simp [euclModel]
  rw [hm, ← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℝ), map_sub]
  rfl

private theorem norm_toL2_sq_eq_fourier_normSq (u : SchwartzVelocity) :
    ‖toL2 u‖ ^ 2 = ∫ ξ : EuclSpace, ‖(𝓕 (euclModel u)) ξ‖ ^ 2 := by
  rw [norm_toL2_sq, schwartzL2Inner]
  have hinner : (∫ x : Space, officialInner (u x) (u x)) =
      ∫ x : Space, officialEuclideanNorm (u x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    exact officialInner_self (u x)
  rw [hinner, velocityMass_eq_modelMass]
  rw [SchwartzMap.integral_norm_sq_fourier]

private theorem norm_toL2_curl_sq_eq_fourierWeight (u : SchwartzVelocity)
    (hu : DivergenceFreeInitial u) :
    ‖toL2 (curlSchwartzCLM u)‖ ^ 2 =
      4 * Real.pi ^ 2 * ∫ ξ : EuclSpace,
        ‖ξ‖ ^ 2 * ‖(𝓕 (euclModel u)) ξ‖ ^ 2 := by
  rw [norm_toL2_sq, schwartzL2Inner]
  have hinner : (∫ x : Space,
      officialInner ((curlSchwartzCLM u) x) ((curlSchwartzCLM u) x)) =
      ∫ x : Space, officialEuclideanNorm (staticCurl (⇑u) x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [curlSchwartzCLM_apply, officialInner_self]
  rw [hinner, curl_sq_eq_fourierWeight_of_divFree u hu]

private theorem integrable_fourierDifference_weighted
    (v u : SchwartzVelocity) (m : ℕ) :
    Integrable (fun ξ : EuclSpace => ‖ξ‖ ^ m *
      ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) := by
  have h := integrable_weighted_normSq (𝓕 (euclModel (v - u))) m
  rw [fourier_euclModel_sub v u] at h
  exact h

/-- Exact Plancherel comparison between the physical velocity-curl graph
error and its Fourier multiplier expression. -/
theorem physicalVelocityCurlErrorSq_eq_fourierWeighted
    (v u : SchwartzVelocity)
    (hv : DivergenceFreeInitial v) (hu : DivergenceFreeInitial u) :
    physicalVelocityCurlErrorSq v u =
      ∫ ξ : EuclSpace,
        (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 := by
  have hdiv := divergenceFreeInitial_sub v u hv hu
  have hcurlSub :
      curlSchwartzCLM (v - u) = curlSchwartzCLM v - curlSchwartzCLM u :=
    map_sub curlSchwartzCLM v u
  rw [physicalVelocityCurlErrorSq, ← toL2_sub v u,
    ← toL2_sub (curlSchwartzCLM v) (curlSchwartzCLM u), ← hcurlSub,
    norm_toL2_sq_eq_fourier_normSq,
    norm_toL2_curl_sq_eq_fourierWeight (v - u) hdiv,
    fourier_euclModel_sub v u]
  have h0raw := integrable_fourierDifference_weighted v u 0
  have h0 : Integrable (fun ξ : EuclSpace =>
      ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) := by
    simpa using h0raw
  have h2 := integrable_fourierDifference_weighted v u 2
  calc
    (∫ ξ : EuclSpace,
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) +
        4 * Real.pi ^ 2 * ∫ ξ : EuclSpace,
          ‖ξ‖ ^ 2 *
            ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 =
        (∫ ξ : EuclSpace,
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) +
          ∫ ξ : EuclSpace, 4 * Real.pi ^ 2 *
            (‖ξ‖ ^ 2 *
              ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) := by
          rw [integral_const_mul]
    _ = ∫ ξ : EuclSpace,
        (‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 +
          4 * Real.pi ^ 2 * (‖ξ‖ ^ 2 *
            ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2)) :=
      (integral_add h0 (h2.const_mul (4 * Real.pi ^ 2))).symm
    _ = ∫ ξ : EuclSpace,
        (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      ring

private theorem physicalVelocityCurlErrorSq_le_fourierWeighted
    (v u : SchwartzVelocity)
    (hv : DivergenceFreeInitial v) (hu : DivergenceFreeInitial u) :
    physicalVelocityCurlErrorSq v u ≤
      (1 + 4 * Real.pi ^ 2) *
        ∫ ξ : EuclSpace, (1 + ‖ξ‖ ^ 2) *
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 := by
  rw [physicalVelocityCurlErrorSq_eq_fourierWeighted v u hv hu,
    ← integral_const_mul]
  have h0raw := integrable_fourierDifference_weighted v u 0
  have h0 : Integrable (fun ξ : EuclSpace =>
      ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) := by
    simpa using h0raw
  have h2 := integrable_fourierDifference_weighted v u 2
  have hnew : Integrable (fun ξ : EuclSpace =>
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
        ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) := by
    have heq : (fun ξ : EuclSpace =>
        (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) =
        (fun ξ : EuclSpace =>
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 +
            4 * Real.pi ^ 2 * (‖ξ‖ ^ 2 *
              ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2)) := by
      funext ξ
      ring
    rw [heq]
    exact h0.add (h2.const_mul (4 * Real.pi ^ 2))
  have hold : Integrable (fun ξ : EuclSpace =>
      (1 + ‖ξ‖ ^ 2) *
        ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) := by
    have heq : (fun ξ : EuclSpace =>
        (1 + ‖ξ‖ ^ 2) *
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) =
        (fun ξ : EuclSpace =>
          ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 +
            ‖ξ‖ ^ 2 *
              ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) := by
      funext ξ
      ring
    rw [heq]
    exact h0.add h2
  apply integral_mono hnew (hold.const_mul (1 + 4 * Real.pi ^ 2))
  intro ξ
  change (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
      ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 ≤
    (1 + 4 * Real.pi ^ 2) * ((1 + ‖ξ‖ ^ 2) *
      ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2)
  have hweight : 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ≤
      (1 + 4 * Real.pi ^ 2) * (1 + ‖ξ‖ ^ 2) := by
    nlinarith [sq_nonneg ‖ξ‖, sq_nonneg Real.pi]
  calc
    (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) *
        ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 ≤
      ((1 + 4 * Real.pi ^ 2) * (1 + ‖ξ‖ ^ 2)) *
        ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    _ = (1 + 4 * Real.pi ^ 2) * ((1 + ‖ξ‖ ^ 2) *
        ‖(𝓕 (euclModel v)) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2) := by
      ring

/-- Weighted Fourier convergence of divergence-free Schwartz fields implies
convergence in the actual physical `velocityCurlGraph` topology. -/
theorem tendsto_velocityCurlGraph_of_tendsto_fourierWeighted
    (v : ℕ → SchwartzVelocity) (u : SchwartzVelocity)
    (hv : ∀ n, DivergenceFreeInitial (v n)) (hu : DivergenceFreeInitial u)
    (hfourier : Tendsto (fun n => ∫ ξ : EuclSpace,
      (1 + ‖ξ‖ ^ 2) *
        ‖(𝓕 (euclModel (v n))) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2)
      atTop (nhds 0)) :
    Tendsto (fun n => velocityCurlGraph (v n)) atTop
      (nhds (velocityCurlGraph u)) := by
  have herr : Tendsto (fun n => physicalVelocityCurlErrorSq (v n) u)
      atTop (nhds 0) := by
    have hscale : Tendsto (fun n => (1 + 4 * Real.pi ^ 2) *
        ∫ ξ : EuclSpace, (1 + ‖ξ‖ ^ 2) *
          ‖(𝓕 (euclModel (v n))) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2)
        atTop (nhds 0) := by
      have hc : Tendsto (fun _ : ℕ => (1 + 4 * Real.pi ^ 2 : ℝ)) atTop
          (nhds (1 + 4 * Real.pi ^ 2)) := tendsto_const_nhds
      have h := hc.mul hfourier
      simpa only [mul_zero] using h
    apply squeeze_zero
    · intro n
      unfold physicalVelocityCurlErrorSq
      positivity
    · intro n
      exact physicalVelocityCurlErrorSq_le_fourierWeighted (v n) u (hv n) hu
    · exact hscale
  rw [Metric.tendsto_atTop] at herr ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := herr (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have herror : physicalVelocityCurlErrorSq (v n) u < ε ^ 2 := by
    have hnonneg : 0 ≤ physicalVelocityCurlErrorSq (v n) u := by
      unfold physicalVelocityCurlErrorSq
      positivity
    simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hN n hn
  have hvel : ‖toL2 (v n) - toL2 u‖ < ε := by
    have hsq : ‖toL2 (v n) - toL2 u‖ ^ 2 < ε ^ 2 := by
      unfold physicalVelocityCurlErrorSq at herror
      nlinarith [sq_nonneg
        ‖toL2 (curlSchwartzCLM (v n)) - toL2 (curlSchwartzCLM u)‖]
    nlinarith [norm_nonneg (toL2 (v n) - toL2 u)]
  have hcurl :
      ‖toL2 (curlSchwartzCLM (v n)) - toL2 (curlSchwartzCLM u)‖ < ε := by
    have hsq :
        ‖toL2 (curlSchwartzCLM (v n)) - toL2 (curlSchwartzCLM u)‖ ^ 2 <
          ε ^ 2 := by
      unfold physicalVelocityCurlErrorSq at herror
      nlinarith [sq_nonneg ‖toL2 (v n) - toL2 u‖]
    nlinarith [norm_nonneg
      (toL2 (curlSchwartzCLM (v n)) - toL2 (curlSchwartzCLM u))]
  change max (dist (toL2 (v n)) (toL2 u))
    (dist (toL2 (curlSchwartzCLM (v n)))
      (toL2 (curlSchwartzCLM u))) < ε
  simpa only [dist_eq_norm, max_lt_iff] using ⟨hvel, hcurl⟩

/-- A divergence-free datum already carried by one dyadic band has actual
divergence-free Schwartz approximants in that same band converging in the
physical velocity-curl graph norm. -/
theorem exists_dyadic_band_velocityCurlGraph_approximation
    (k : ℤ) (u : SchwartzVelocity)
    (hu : u ∈ bandFields (dyadicAnnulus k)) :
    ∃ v : ℕ → SchwartzVelocity,
      (∀ n, v n ∈ bandFields (dyadicAnnulus k)) ∧
      Tendsto (fun n => velocityCurlGraph (v n)) atTop
        (nhds (velocityCurlGraph u)) := by
  obtain ⟨v, hv, happ⟩ :=
    exists_dyadic_divFree_schwartz_band_approximation k u hu.1
  have hindicator (ξ : EuclSpace) :
      (dyadicAnnulus k).indicator
          (fun η => (𝓕 (euclModel u)) η) ξ =
        (𝓕 (euclModel u)) ξ := by
    by_cases hξ : ξ ∈ dyadicAnnulus k
    · simp [hξ]
    · simp [hξ, hu.2 ξ hξ]
  have happ' : Tendsto (fun n => ∫ ξ : EuclSpace,
      (1 + ‖ξ‖ ^ 2) *
        ‖(𝓕 (euclModel (v n))) ξ - (𝓕 (euclModel u)) ξ‖ ^ 2)
      atTop (nhds 0) := by
    simpa only [hindicator] using happ
  exact ⟨v, hv,
    tendsto_velocityCurlGraph_of_tendsto_fourierWeighted v u
      (fun n => (hv n).1) hu.1 happ'⟩

end Navier.Analysis.GalerkinCurlGraphDensity
