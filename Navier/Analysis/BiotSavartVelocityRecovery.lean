import Navier.Analysis.BiotSavartConvolution

/-!
# Recovery of a divergence-free Schwartz velocity from its curl

The trace of the distributional Biot--Savart gradient identity first gives
the scalar Newton identity.  Symmetry of the same principal-value tensor then
annihilates the longitudinal part of a divergence-free vector field.  These
two facts recover the velocity from its actual Schwartz curl.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Matrix LineDeriv

namespace Navier.Analysis.BiotSavartVelocityRecovery

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartPuncture
open Navier.Analysis.BiotSavartTruncationComparison
open Navier.Analysis.BiotSavartPrincipalValue
open Navier.Analysis.BiotSavartConvolution
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

/-- The off-origin Calderón--Zygmund tensor is trace free, including at the
assigned origin value. -/
theorem bsGradKernel_trace (z : Space) :
    (∑ i : Fin 3, bsGradKernel i i z) = 0 := by
  by_cases hz : z = 0
  · subst z
    simp [bsGradKernel]
  · simp only [Fin.sum_univ_three]
    rw [bsGradKernel_apply_of_ne_zero hz,
      bsGradKernel_apply_of_ne_zero hz,
      bsGradKernel_apply_of_ne_zero hz]
    simp only [ite_true]
    have hr : officialEuclideanNorm z ≠ 0 :=
      (officialEuclideanNorm_eq_zero_iff z).not.mpr hz
    have hsq : officialEuclideanNorm z ^ 2 =
        z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      rw [officialEuclideanNorm_eq_sqrt_sum_sq,
        Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg |z k|)]
      simp only [Fin.sum_univ_three, sq_abs]
    field_simp
    nlinarith

theorem bsGradKernel_symm (i j : Fin 3) (z : Space) :
    bsGradKernel i j z = bsGradKernel j i z := by
  by_cases hz : z = 0
  · subst z
    simp [bsGradKernel]
  · rw [bsGradKernel_apply_of_ne_zero hz,
      bsGradKernel_apply_of_ne_zero hz]
    by_cases hij : i = j
    · subst j
      rfl
    · simp only [if_neg hij, if_neg (Ne.symm hij), zero_div, zero_sub]
      ring

private theorem puncturedGradientIntegral_symm
    (ε : ℝ) (i j : Fin 3) (φ : Space → ℝ) :
    puncturedGradientIntegral ε i j φ =
      puncturedGradientIntegral ε j i φ := by
  rw [puncturedGradientIntegral, puncturedGradientIntegral]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : ε < officialEuclideanNorm z
  · simp [hz, bsGradKernel_symm]
  · simp [hz]

theorem principalValueConvolution_symm
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    principalValueConvolution i j φ x =
      principalValueConvolution j i φ x := by
  have hij := hasBiotSavartPrincipalValue_reflectedTranslate i j φ x
  have hji := hasBiotSavartPrincipalValue_reflectedTranslate j i φ x
  have heq : (fun ε : ℝ => puncturedGradientIntegral ε i j
      (reflectedTranslate φ x)) =
      fun ε => puncturedGradientIntegral ε j i (reflectedTranslate φ x) := by
    funext ε
    exact puncturedGradientIntegral_symm ε i j _
  change Tendsto (fun ε : ℝ => puncturedGradientIntegral ε i j
      (reflectedTranslate φ x)) (nhdsWithin 0 (Ioi 0))
      (nhds (principalValueConvolution i j φ x)) at hij
  change Tendsto (fun ε : ℝ => puncturedGradientIntegral ε j i
      (reflectedTranslate φ x)) (nhdsWithin 0 (Ioi 0))
      (nhds (principalValueConvolution j i φ x)) at hji
  rw [heq] at hij
  exact tendsto_nhds_unique hij hji

private theorem puncturedGradientIntegral_trace
    {ε : ℝ} (hε : 0 < ε) (φ : SchwartzMap Space ℝ) :
    (∑ i : Fin 3, puncturedGradientIntegral ε i i φ) = 0 := by
  simp only [puncturedGradientIntegral, exteriorIntegral]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    integrable_sharpPuncturedGradient_schwartz hε i i φ)]
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  by_cases hz : ε < officialEuclideanNorm z
  · have hind (i : Fin 3) :
        Set.indicator {x : Space | ε < officialEuclideanNorm x}
          (fun x => (1 / (4 * Real.pi)) * bsGradKernel i i x * φ x) z =
        (1 / (4 * Real.pi)) * bsGradKernel i i z * φ z :=
      by
        apply Set.indicator_of_mem
        exact hz
    simp_rw [hind]
    rw [← Finset.sum_mul, ← Finset.mul_sum, bsGradKernel_trace,
      mul_zero, zero_mul]
    rfl
  · simp [hz]

theorem principalValueConvolution_trace
    (φ : SchwartzMap Space ℝ) (x : Space) :
    (∑ i : Fin 3, principalValueConvolution i i φ x) = 0 := by
  have h0 := hasBiotSavartPrincipalValue_reflectedTranslate 0 0 φ x
  have h1 := hasBiotSavartPrincipalValue_reflectedTranslate 1 1 φ x
  have h2 := hasBiotSavartPrincipalValue_reflectedTranslate 2 2 φ x
  have hsum := (h0.add h1).add h2
  have hzero : Tendsto (fun _ : ℝ => (0 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℝ)) := tendsto_const_nhds
  have heq : (fun ε : ℝ =>
      puncturedGradientIntegral ε 0 0 (reflectedTranslate φ x) +
        puncturedGradientIntegral ε 1 1 (reflectedTranslate φ x) +
          puncturedGradientIntegral ε 2 2 (reflectedTranslate φ x))
      =ᶠ[nhdsWithin 0 (Ioi 0)] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [Fin.sum_univ_three] using
      puncturedGradientIntegral_trace hε (reflectedTranslate φ x)
  have hz := hzero.congr' heq.symm
  have hvalue :
      principalValueConvolution 0 0 φ x +
          principalValueConvolution 1 1 φ x +
            principalValueConvolution 2 2 φ x = 0 :=
    tendsto_nhds_unique hsum hz
  simpa only [Fin.sum_univ_three] using hvalue

private theorem integrable_derivativeConvolution
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    Integrable (fun z : Space =>
      fderiv ℝ φ (x - z) (basisVector i) * bsVectorKernel z j) := by
  have h := integrable_fderiv_mul_bsVectorKernel i j (reflectedTranslate φ x)
  have hn := h.neg
  exact hn.congr (ae_of_all _ fun z => by
    change -(fderiv ℝ (reflectedTranslate φ x) z (basisVector i) *
      bsVectorKernel z j) = _
    rw [fderiv_reflectedTranslate_basis]
    ring)

/-- Scalar Newton recovery, derived from the trace-free principal-value
tensor and its three one-third local coefficients. -/
theorem sum_integral_bsVectorKernel_mul_fderiv (φ : SchwartzMap Space ℝ)
    (x : Space) :
    (∑ j : Fin 3, ∫ z : Space,
      fderiv ℝ φ (x - z) (basisVector j) * bsVectorKernel z j) = φ x := by
  have htrace := principalValueConvolution_trace φ x
  simp only [principalValueConvolution] at htrace
  have hlocal : (∑ j : Fin 3,
      (1 / 3 : ℝ) * basisVector j j * φ x) = φ x := by
    simp [basisVector]
  rw [Finset.sum_sub_distrib, hlocal] at htrace
  linarith

/-- A scalar component of a Schwartz velocity. -/
def velocityComponentSchwartz (u : SchwartzVelocity) (j : Fin 3) :
    SchwartzMap Space ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.proj j) u

@[simp] theorem velocityComponentSchwartz_apply
    (u : SchwartzVelocity) (j : Fin 3) (x : Space) :
    velocityComponentSchwartz u j x = u x j := rfl

theorem fderiv_velocityComponentSchwartz
    (u : SchwartzVelocity) (j : Fin 3) (x v : Space) :
    fderiv ℝ (velocityComponentSchwartz u j) x v =
      fderiv ℝ u x v j := by
  let proj : Space →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hcomp := proj.hasFDerivAt.comp x u.differentiableAt.hasFDerivAt
  have hfun : (⇑(velocityComponentSchwartz u j) : Space → ℝ) =
      proj ∘ (⇑u) := rfl
  rw [hfun, hcomp.fderiv]
  rfl

private theorem localRow_sum (u : SchwartzVelocity) (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, (1 / 3 : ℝ) * basisVector i j *
      velocityComponentSchwartz u j x) = (1 / 3 : ℝ) * u x i := by
  fin_cases i <;> simp [basisVector, Fin.sum_univ_three]

private theorem localColumn_sum (u : SchwartzVelocity) (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, (1 / 3 : ℝ) * basisVector j i *
      velocityComponentSchwartz u j x) = (1 / 3 : ℝ) * u x i := by
  fin_cases i <;> simp [basisVector, Fin.sum_univ_three]

/-- The longitudinal kernel contraction vanishes for a divergence-free
Schwartz velocity.  This is obtained from symmetry of the sharp PV tensor;
no Fourier or Newton-potential premise is introduced. -/
theorem sum_integral_velocityDerivative_mul_bsVectorKernel_eq_zero
    (u : SchwartzVelocity) (hdiv : DivergenceFreeInitial u)
    (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, ∫ z : Space,
      fderiv ℝ (velocityComponentSchwartz u j) (x - z) (basisVector i) *
        bsVectorKernel z j) = 0 := by
  let P : Fin 3 → Fin 3 → ℝ := fun a b =>
    principalValueConvolution a b (velocityComponentSchwartz u b) x
  have hsymm : (∑ j : Fin 3, P i j) =
      ∑ j : Fin 3,
        principalValueConvolution j i (velocityComponentSchwartz u j) x := by
    apply Finset.sum_congr rfl
    intro j _
    exact principalValueConvolution_symm i j
      (velocityComponentSchwartz u j) x
  have hright : (∑ j : Fin 3,
      principalValueConvolution j i (velocityComponentSchwartz u j) x) =
      -(1 / 3 : ℝ) * u x i := by
    simp only [principalValueConvolution]
    rw [Finset.sum_sub_distrib, localColumn_sum]
    have hInt : ∀ j : Fin 3, Integrable (fun z : Space =>
        fderiv ℝ (velocityComponentSchwartz u j) (x - z)
          (basisVector j) * bsVectorKernel z i) := fun j =>
      integrable_derivativeConvolution j i (velocityComponentSchwartz u j) x
    have hIntegral : (∑ j : Fin 3, ∫ z : Space,
        fderiv ℝ (velocityComponentSchwartz u j) (x - z)
          (basisVector j) * bsVectorKernel z i) = 0 := by
      rw [← integral_finsetSum Finset.univ (fun j _ => hInt j)]
      apply integral_eq_zero_of_ae
      filter_upwards [] with z
      rw [← Finset.sum_mul]
      have hzdiv : (∑ j : Fin 3,
          fderiv ℝ (velocityComponentSchwartz u j) (x - z)
            (basisVector j)) = 0 := by
        simp_rw [fderiv_velocityComponentSchwartz]
        exact hdiv (x - z)
      rw [hzdiv, zero_mul]
      rfl
    rw [hIntegral]
    ring
  have hleft : (∑ j : Fin 3, P i j) =
      (∑ j : Fin 3, ∫ z : Space,
        fderiv ℝ (velocityComponentSchwartz u j) (x - z) (basisVector i) *
          bsVectorKernel z j) - (1 / 3 : ℝ) * u x i := by
    simp only [P, principalValueConvolution]
    rw [Finset.sum_sub_distrib, localRow_sum]
  rw [hleft, hright] at hsymm
  linarith

private theorem curl_cross_kernel_pointwise
    (u : SchwartzVelocity) (x z : Space) (i : Fin 3) :
    (staticCurl (⇑u) (x - z) ⨯₃ bsVectorKernel z) i =
      (∑ j : Fin 3,
        fderiv ℝ (velocityComponentSchwartz u i) (x - z)
            (basisVector j) * bsVectorKernel z j) -
      ∑ j : Fin 3,
        fderiv ℝ (velocityComponentSchwartz u j) (x - z)
            (basisVector i) * bsVectorKernel z j := by
  simp_rw [fderiv_velocityComponentSchwartz]
  fin_cases i
  all_goals simp only [staticCurl, Fin.sum_univ_three]
  all_goals simp [basisVector, cross_apply]
  all_goals ring

private theorem integrable_curl_cross_kernel_coord
    (u : SchwartzVelocity) (x : Space) (i : Fin 3) :
    Integrable (fun z : Space =>
      (staticCurl (⇑u) (x - z) ⨯₃ bsVectorKernel z) i) := by
  have hA : ∀ j : Fin 3, Integrable (fun z : Space =>
      fderiv ℝ (velocityComponentSchwartz u i) (x - z)
        (basisVector j) * bsVectorKernel z j) := fun j =>
    integrable_derivativeConvolution j j (velocityComponentSchwartz u i) x
  have hB : ∀ j : Fin 3, Integrable (fun z : Space =>
      fderiv ℝ (velocityComponentSchwartz u j) (x - z)
        (basisVector i) * bsVectorKernel z j) := fun j =>
    integrable_derivativeConvolution i j (velocityComponentSchwartz u j) x
  have hsumA := integrable_finsetSum Finset.univ (fun j _ => hA j)
  have hsumB := integrable_finsetSum Finset.univ (fun j _ => hB j)
  exact (hsumA.sub hsumB).congr (ae_of_all _ fun z =>
    (curl_cross_kernel_pointwise u x z i).symm)

/-- Coordinate form of the Biot--Savart velocity recovery. -/
theorem integral_staticCurl_cross_bsVectorKernel_coord
    (u : SchwartzVelocity) (hdiv : DivergenceFreeInitial u)
    (x : Space) (i : Fin 3) :
    (∫ z : Space,
      (staticCurl (⇑u) (x - z) ⨯₃ bsVectorKernel z) i) = u x i := by
  have hA : ∀ j : Fin 3, Integrable (fun z : Space =>
      fderiv ℝ (velocityComponentSchwartz u i) (x - z)
        (basisVector j) * bsVectorKernel z j) := fun j =>
    integrable_derivativeConvolution j j (velocityComponentSchwartz u i) x
  have hB : ∀ j : Fin 3, Integrable (fun z : Space =>
      fderiv ℝ (velocityComponentSchwartz u j) (x - z)
        (basisVector i) * bsVectorKernel z j) := fun j =>
    integrable_derivativeConvolution i j (velocityComponentSchwartz u j) x
  have hsumA := integrable_finsetSum Finset.univ (fun j _ => hA j)
  have hsumB := integrable_finsetSum Finset.univ (fun j _ => hB j)
  rw [integral_congr_ae (ae_of_all _ fun z =>
    curl_cross_kernel_pointwise u x z i)]
  rw [integral_sub hsumA hsumB,
    integral_finsetSum Finset.univ (fun j _ => hA j),
    integral_finsetSum Finset.univ (fun j _ => hB j),
    sum_integral_bsVectorKernel_mul_fderiv
      (velocityComponentSchwartz u i) x,
    sum_integral_velocityDerivative_mul_bsVectorKernel_eq_zero u hdiv x i]
  simp

/-- **Biot--Savart recovery.**  Every divergence-free Schwartz velocity is
the convolution of its actual curl with the vector kernel, in the orientation
`curl u × K`. -/
theorem integral_staticCurl_cross_bsVectorKernel
    (u : SchwartzVelocity) (hdiv : DivergenceFreeInitial u) (x : Space) :
    (∫ z : Space, staticCurl (⇑u) (x - z) ⨯₃ bsVectorKernel z) = u x := by
  have hint : Integrable (fun z : Space =>
      staticCurl (⇑u) (x - z) ⨯₃ bsVectorKernel z) :=
    integrable_pi_iff.mpr fun i => integrable_curl_cross_kernel_coord u x i
  ext i
  have hproj := (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ).integral_comp_comm hint
  change (ContinuousLinearMap.proj i : Space →L[ℝ] ℝ)
      (∫ z : Space, staticCurl (⇑u) (x - z) ⨯₃ bsVectorKernel z) = u x i
  rw [← hproj]
  exact integral_staticCurl_cross_bsVectorKernel_coord u hdiv x i

end Navier.Analysis.BiotSavartVelocityRecovery
