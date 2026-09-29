import Navier.Analysis.GalerkinBasis
import Navier.Analysis.DivFreeGradientEnstrophy
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Data.Complex.BigOperators
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# No divergence-free Schwartz field is a `curl` eigenfield (`Analysis.GalerkinBasis`)

**Kernel refutation of the exact curl–projection commutation route** (registry
row NAVIER-01; ledger entry F-029).  The docstring conjectures attached to
`curl_proj_sq_le_of_commutes` and `curl_proj_converges_of_commutes` claimed, on
Fourier grounds, that the hypothesis

```
∀ m u, curl (P_m u) = P_m (curl u)
```

is unsatisfiable by any `GalerkinBasisFamily`; until now that argument lived
only in prose ("not mechanized").  This file mechanizes it.

## Route

1. Commutation at `m = 1` fixes the first mode (`proj_basis`), so
   `curl w₀ = P₁(curl w₀) = ⟪curl w₀, w₀⟫ • w₀`: the first mode is an
   eigenfield of `curl` with eigenvalue `λ := ⟪curl w₀, w₀⟫`.
2. Two curls and divergence-freeness (`curlCurlSchwartz_eq_neg_laplacian`)
   give `Δ w₀ = −λ² w₀` — an eigenfield of `−Δ` with eigenvalue `μ = λ² ≥ 0`.
3. Transport to the complexified Euclidean model (`euclModel`) and take the
   Schwartz-space Fourier transform: the symbol of `∂_{eᵢ}` is
   `2πi · ⟪ξ, eᵢ⟫` (`SchwartzMap.fourier_lineDerivOp_eq`), so the model
   Laplacian's symbol is `−4π²‖ξ‖²` and the eigen-equation becomes, pointwise,
   `(λ² − 4π²‖ξ‖²) • 𝓕(euclModel w₀) ξ = 0`.
4. The coefficient vanishes only on the sphere `‖ξ‖ = |λ|/(2π)`; its
   complement is **dense** (`mem_closure_norm_ne`, a `Metric.mem_closure_iff`
   perturbation argument — no sphere-interior API needed), and
   `𝓕(euclModel w₀)` is continuous, so it vanishes everywhere
   (`eq_zero_of_modelLaplacian_eq_neg_smul`).  Inverting (`𝓕⁻𝓕 = id`) and
   using injectivity of `euclModel` forces `w₀ = 0`.  This covers `λ = 0`
   uniformly: the sphere of radius `0` is still nowhere dense in `ℝ³`.
5. Orthonormality contradicts the conclusion: `1 = ⟪w₀, w₀⟫ = 0`.

## What this changes downstream

* `first_mode_not_curl_eigenfield` supplies, unconditionally, the hypothesis
  `not_curl_proj_commutes_of_first_mode_not_eigenfield` (in
  `GalerkinModeData.lean`) previously took as a free parameter — the algebraic
  half was already banked there; this file discharges the analytic half.
* The live route for `curl_proj_converges` remains the structural
  `GraphDense ∧ CurlStable` ordering (stability, **not** commutation).
-/

open scoped FourierTransform LineDeriv
open Navier Navier.Analysis.DivFreeGradientEnstrophy

namespace Navier.Analysis.GalerkinBasis

/-! ## The real Euclidean model basis -/

/-- The `i`-th unit of `EuclSpace`, the counterpart of `Navier.basisVector i`
under `euclCoords` (a public copy of `DivFreeGradientEnstrophy`'s private `e3`). -/
noncomputable def euclBasisVector (i : Fin 3) : EuclSpace := EuclideanSpace.single i (1 : ℝ)

@[simp] theorem norm_euclBasisVector (i : Fin 3) : ‖euclBasisVector i‖ = 1 := by
  simp [euclBasisVector]

@[simp] theorem inner_euclBasisVector (ξ : EuclSpace) (i : Fin 3) :
    (inner ℝ ξ (euclBasisVector i) : ℝ) = ξ i := by
  simp [euclBasisVector, EuclideanSpace.inner_single_right]

/-- Parseval-type identity: the coordinates recover the squared norm. -/
theorem sum_inner_euclBasisVector_sq (ξ : EuclSpace) :
    ∑ i : Fin 3, (inner ℝ ξ (euclBasisVector i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
  simp only [inner_euclBasisVector]
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [sq_abs]

/-- Re-derivation of `DivFreeGradientEnstrophy.euclid_norm_sq` (private there). -/
private theorem eucl_norm_sq (ξ : EuclSpace) : ‖ξ‖ ^ 2 = ∑ i : Fin 3, (ξ i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ => by simp [sq_abs]

theorem euclCoords_euclBasisVector (i : Fin 3) :
    euclCoords (euclBasisVector i) = basisVector i := by
  ext j
  show (euclBasisVector i : Fin 3 → ℝ) j = basisVector i j
  simp [euclBasisVector, basisVector, Pi.single, Function.update]

/-! ## `euclModel` is an `ℝ`-linear intertwiner -/

/-- Pointwise model line derivative, re-derived with the public basis
(`DivFreeGradientEnstrophy.euclModel_lineDeriv_apply` mentions the private `e3`
and cannot be matched from outside). -/
theorem model_lineDeriv_apply (u : SchwartzVelocity) (i : Fin 3) (y : EuclSpace) :
    (∂_{euclBasisVector i} (euclModel u)) y =
      realToCx (fderiv ℝ u (euclCoords y) (basisVector i)) := by
  have hu : Differentiable ℝ (⇑u) := (u.smooth 1).differentiable (by norm_num)
  have hfun : (⇑(euclModel u) : EuclSpace → CxSpace) =
      fun z => realToCx (u (euclCoords z)) := funext fun z => euclModel_apply u z
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hfun]
  have h1 : HasFDerivAt (fun z => u (euclCoords z))
      ((fderiv ℝ u (euclCoords y)).comp
        ((euclCoords : EuclSpace ≃L[ℝ] Space) : EuclSpace →L[ℝ] Space)) y :=
    (hu (euclCoords y)).hasFDerivAt.comp y euclCoords.hasFDerivAt
  have h2 : HasFDerivAt (fun z => realToCx (u (euclCoords z)))
      (realToCx.comp ((fderiv ℝ u (euclCoords y)).comp
        ((euclCoords : EuclSpace ≃L[ℝ] Space) : EuclSpace →L[ℝ] Space))) y :=
    realToCx.hasFDerivAt.comp y h1
  rw [h2.fderiv]
  simp [euclCoords_euclBasisVector]

/-- The model transport intertwines line derivatives:
`euclModel (∂_{basisVector i} u) = ∂_{euclBasisVector i} (euclModel u)`. -/
theorem euclModel_lineDeriv (u : SchwartzVelocity) (i : Fin 3) :
    euclModel (∂_{basisVector i} u) = ∂_{euclBasisVector i} (euclModel u) := by
  ext y
  rw [euclModel_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    ← model_lineDeriv_apply]

/-- The model transport commutes with finite sums. -/
private theorem sum_euclModel (f : Fin 3 → SchwartzVelocity) :
    euclModel (∑ i, f i) = ∑ i, euclModel (f i) := by
  unfold euclModel
  simp only [map_sum]

/-- The model transport commutes with real scalars (complexified). -/
theorem euclModel_smul_real (a : ℝ) (u : SchwartzVelocity) :
    euclModel (a • u) = (a : ℂ) • euclModel u := by
  have hc (v : SchwartzMap EuclSpace CxSpace) : (a : ℝ) • v = (a : ℂ) • v := by
    ext y i
    simp
  unfold euclModel
  simp only [map_smul]
  exact hc _

/-- `euclModel` is injective: coordinate evaluations recover the field. -/
theorem euclModel_injective : Function.Injective euclModel := by
  intro u1 u2 h
  have h1 : ∀ (y : EuclSpace) (k : Fin 3),
      (u1 (euclCoords y) k : ℂ) = (u2 (euclCoords y) k : ℂ) := by
    intro y k
    have := congrArg (fun f : SchwartzMap EuclSpace CxSpace => f y k) h
    simp only [euclModel_apply, realToCx_apply] at this
    exact this
  ext x i
  have h2 := h1 (euclCoords.symm x) i
  rw [ContinuousLinearEquiv.apply_symm_apply] at h2
  exact Complex.ofReal_inj.mp h2

/-- `euclModel` reflects zero. -/
theorem euclModel_eq_zero_iff (u : SchwartzVelocity) : euclModel u = 0 ↔ u = 0 := by
  have hz : euclModel (0 : SchwartzVelocity) = 0 := by
    ext y
    simp only [euclModel_apply, SchwartzMap.coe_zero, Pi.zero_apply, map_zero]
  constructor
  · intro h
    exact euclModel_injective (h.trans hz.symm)
  · intro h
    rw [h, hz]

/-! ## Model Laplacian and its Fourier symbol -/

/-- The Laplacian on the complexified model: `∑ i, ∂_{eᵢ} ∂_{eᵢ}`. -/
noncomputable def modelLaplacian (v : SchwartzMap EuclSpace CxSpace) :
    SchwartzMap EuclSpace CxSpace :=
  ∑ i : Fin 3, ∂_{euclBasisVector i} (∂_{euclBasisVector i} v)

/-- `euclModel` intertwines `laplacianSchwartz` with `modelLaplacian`. -/
theorem euclModel_laplacianSchwartz (u : SchwartzVelocity) :
    euclModel (laplacianSchwartz u) = modelLaplacian (euclModel u) := by
  unfold laplacianSchwartz modelLaplacian
  rw [sum_euclModel]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [euclModel_lineDeriv, euclModel_lineDeriv]

/-- The Fourier symbol of one model line derivative, evaluated at `ξ`. -/
theorem fourier_lineDeriv_apply (v : SchwartzMap EuclSpace CxSpace)
    (m ξ : EuclSpace) :
    (𝓕 (∂_{m} v)) ξ =
      (2 * (Real.pi : ℂ) * Complex.I * (inner ℝ ξ m : ℂ)) • 𝓕 v ξ := by
  have htemp : (inner ℝ · m : EuclSpace → ℝ).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [SchwartzMap.smulLeftCLM_apply_apply htemp, smul_apply]
  show (2 * (Real.pi : ℂ) * Complex.I) • ((inner ℝ ξ m : ℂ) • 𝓕 v ξ) = _
  rw [← mul_smul]

/-- `(2πi)² = −4π²`. -/
private theorem two_pi_I_sq :
    (2 * (Real.pi : ℂ) * Complex.I) ^ 2 = -((4 : ℂ) * (Real.pi : ℂ) ^ 2) := by
  rw [mul_pow, mul_pow, Complex.I_sq]
  ring

/-- `(2πi·t)·(2πi·t) = −4π²·t²`. -/
private theorem hsq_fuse (t : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I * t) * (2 * (Real.pi : ℂ) * Complex.I * t) =
      -((4 : ℂ) * (Real.pi : ℂ) ^ 2) * t ^ 2 := by
  rw [← pow_two, mul_pow, two_pi_I_sq]

/-- The Fourier symbol of the model Laplacian: `𝓕(Δ_model v) ξ = −4π²‖ξ‖² · 𝓕v ξ`. -/
theorem fourier_modelLaplacian_apply (v : SchwartzMap EuclSpace CxSpace)
    (ξ : EuclSpace) :
    (𝓕 (modelLaplacian v)) ξ =
      -((4 : ℂ) * (Real.pi : ℂ) ^ 2 * (‖ξ‖ ^ 2 : ℂ)) • 𝓕 v ξ := by
  unfold modelLaplacian
  have hsum : (𝓕 (∑ i : Fin 3, ∂_{euclBasisVector i} (∂_{euclBasisVector i} v))) ξ =
      ∑ i : Fin 3, (𝓕 (∂_{euclBasisVector i} (∂_{euclBasisVector i} v))) ξ := by
    rw [← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ), map_sum, sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ)]
  rw [hsum]
  have hterm (i : Fin 3) :
      (𝓕 (∂_{euclBasisVector i} (∂_{euclBasisVector i} v))) ξ =
        (-((4 : ℂ) * (Real.pi : ℂ) ^ 2) * (ξ i : ℂ) ^ 2) • 𝓕 v ξ := by
    rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply, inner_euclBasisVector,
      ← mul_smul, hsq_fuse]
  simp only [hterm]
  rw [← Finset.sum_smul, ← Finset.mul_sum]
  refine congrArg (fun s : ℂ => s • (𝓕 v) ξ) ?_
  have hnorm : (∑ i : Fin 3, (ξ i : ℂ) ^ 2) = (‖ξ‖ : ℂ) ^ 2 := by
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum, eucl_norm_sq]
  rw [hnorm]
  ring

/-! ## Vanishing: no `ℝ³` Schwartz field satisfies `Δv = −μv`, `μ ≥ 0` -/

/-- Every point lies in the closure of the complement of any sphere:
`{ξ | ‖ξ‖ ≠ r}` is dense in `EuclSpace`. -/
private theorem mem_closure_norm_ne (r : ℝ) (x₀ : EuclSpace) :
    x₀ ∈ closure {ξ : EuclSpace | ‖ξ‖ ≠ r} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases hx : x₀ = 0
  · subst hx
    by_cases h : (ε / 2 : ℝ) = r
    · have hε4 : (0 : ℝ) < ε / 4 := by linarith
      refine ⟨(ε / 4) • euclBasisVector 0, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hε4.le, norm_euclBasisVector, mul_one]
        rw [← h]
        linarith
      · rw [dist_eq_norm', sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hε4.le, norm_euclBasisVector, mul_one]
        linarith
    · have hε2 : (0 : ℝ) < ε / 2 := by linarith
      refine ⟨(ε / 2) • euclBasisVector 0, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hε2.le, norm_euclBasisVector, mul_one]
        exact h
      · rw [dist_eq_norm', sub_zero, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hε2.le, norm_euclBasisVector, mul_one]
        linarith
  · have hn : 0 < ‖x₀‖ := norm_pos_iff.mpr hx
    by_cases h : ‖x₀‖ + ε / 2 = r
    · -- perturb outward by ε/4 (stays inside the ε-ball, misses the sphere)
      refine ⟨(1 + (ε / 4) / ‖x₀‖) • x₀, ?_, ?_⟩
      · have hp : (0 : ℝ) ≤ 1 + (ε / 4) / ‖x₀‖ := by positivity
        have hnorm' : ‖(1 + (ε / 4) / ‖x₀‖) • x₀‖ = ‖x₀‖ + ε / 4 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
          field_simp [ne_of_gt hn]
        rw [Set.mem_setOf_eq, hnorm', ← h]
        linarith
      · have ht : (0 : ℝ) ≤ (ε / 4) / ‖x₀‖ := by positivity
        have hsub : (1 + (ε / 4) / ‖x₀‖) • x₀ - x₀ = ((ε / 4) / ‖x₀‖) • x₀ := by
          rw [add_smul, one_smul, add_sub_cancel_left]
        have hdist : ‖(1 + (ε / 4) / ‖x₀‖) • x₀ - x₀‖ = ε / 4 := by
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
          field_simp [ne_of_gt hn]
        rw [dist_eq_norm', hdist]
        linarith
    · -- perturb outward by ε/2 (the sphere radius is not `‖x₀‖ + ε/2`)
      refine ⟨(1 + (ε / 2) / ‖x₀‖) • x₀, ?_, ?_⟩
      · have hp : (0 : ℝ) ≤ 1 + (ε / 2) / ‖x₀‖ := by positivity
        have hnorm' : ‖(1 + (ε / 2) / ‖x₀‖) • x₀‖ = ‖x₀‖ + ε / 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
          field_simp [ne_of_gt hn]
        rw [Set.mem_setOf_eq, hnorm']
        exact h
      · have ht : (0 : ℝ) ≤ (ε / 2) / ‖x₀‖ := by positivity
        have hsub : (1 + (ε / 2) / ‖x₀‖) • x₀ - x₀ = ((ε / 2) / ‖x₀‖) • x₀ := by
          rw [add_smul, one_smul, add_sub_cancel_left]
        have hdist : ‖(1 + (ε / 2) / ‖x₀‖) • x₀ - x₀‖ = ε / 2 := by
          rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
          field_simp [ne_of_gt hn]
        rw [dist_eq_norm', hdist]
        linarith

/-- **The vanishing theorem.**  A Schwartz `CxSpace`-valued field on `ℝ³` whose
model Laplacian is `−μ` times itself, with `μ ≥ 0` — i.e. an eigenfield of `−Δ`
with a nonnegative eigenvalue — is identically zero.  (There is no discrete
spectrum on the whole space.) -/
theorem eq_zero_of_modelLaplacian_eq_neg_smul {μ : ℝ} (hμ : 0 ≤ μ)
    (v : SchwartzMap EuclSpace CxSpace)
    (hv : modelLaplacian v = -((μ : ℂ)) • v) : v = 0 := by
  have h1 : ∀ ξ : EuclSpace,
      -((4 : ℂ) * (Real.pi : ℂ) ^ 2 * (‖ξ‖ ^ 2 : ℂ)) • 𝓕 v ξ =
        -((μ : ℂ)) • 𝓕 v ξ := by
    intro ξ
    have h2 : (𝓕 (modelLaplacian v)) ξ = (𝓕 (-((μ : ℂ)) • v)) ξ := by rw [hv]
    have h3 : (𝓕 (-((μ : ℂ)) • v)) ξ = -((μ : ℂ)) • 𝓕 v ξ := by
      rw [← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ), map_smul,
        SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ)]
      simp
    rw [fourier_modelLaplacian_apply] at h2
    rw [h3] at h2
    exact h2
  have hkey : ∀ ξ : EuclSpace,
      ((μ : ℂ) - (4 * (Real.pi : ℂ) ^ 2 * (‖ξ‖ ^ 2 : ℂ))) • 𝓕 v ξ = 0 := by
    intro ξ
    have h5 : ((-((4 : ℂ) * (Real.pi : ℂ) ^ 2 * (‖ξ‖ ^ 2 : ℂ))) - (-(μ : ℂ))) •
        𝓕 v ξ = 0 := by
      rw [sub_smul, h1 ξ, sub_self]
    have hce : ((-((4 : ℂ) * (Real.pi : ℂ) ^ 2 * (‖ξ‖ ^ 2 : ℂ))) - (-(μ : ℂ))) =
        ((μ : ℂ) - (4 * (Real.pi : ℂ) ^ 2 * (‖ξ‖ ^ 2 : ℂ))) := by ring
    rw [hce] at h5
    exact h5
  have hzero : ∀ ξ : EuclSpace, ‖ξ‖ ≠ Real.sqrt μ / (2 * Real.pi) →
      𝓕 v ξ = 0 := by
    intro ξ hξ
    rcases smul_eq_zero.mp (hkey ξ) with hcoef | hz
    · exfalso
      apply hξ
      norm_cast at hcoef
      -- hcoef : μ = 4 * π ^ 2 * ‖ξ‖ ^ 2
      have hs : (Real.sqrt μ / (2 * Real.pi)) ^ 2 = μ / (4 * Real.pi ^ 2) := by
        rw [div_pow, Real.sq_sqrt hμ]
        congr 1
        ring
      have h2' : μ = 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by linarith
      have hsq : ‖ξ‖ ^ 2 = μ / (4 * Real.pi ^ 2) := by
        rw [h2']
        field_simp [Real.pi_ne_zero]
      have hnn : (0 : ℝ) ≤ Real.sqrt μ / (2 * Real.pi) :=
        div_nonneg (Real.sqrt_nonneg μ) (by positivity)
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hnn, hsq, ← hs]
    · exact hz
  have hclosed : IsClosed {ξ : EuclSpace | 𝓕 v ξ = 0} := by
    have hz0 : IsClosed {z : CxSpace | z = 0} := isClosed_eq continuous_id continuous_const
    have heq : {ξ : EuclSpace | 𝓕 v ξ = 0} =
        (fun ξ : EuclSpace => 𝓕 v ξ) ⁻¹' {z : CxSpace | z = 0} := rfl
    rw [heq]
    exact IsClosed.preimage ((𝓕 v).continuous) hz0
  have hsub : {ξ : EuclSpace | ‖ξ‖ ≠ Real.sqrt μ / (2 * Real.pi)} ⊆
      {ξ : EuclSpace | 𝓕 v ξ = 0} := hzero
  have hdense : closure {ξ : EuclSpace | ‖ξ‖ ≠ Real.sqrt μ / (2 * Real.pi)} =
      Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro ξ
    exact mem_closure_norm_ne _ ξ
  have hcl : closure {ξ : EuclSpace | ‖ξ‖ ≠ Real.sqrt μ / (2 * Real.pi)} ⊆
      {ξ : EuclSpace | 𝓕 v ξ = 0} := closure_minimal hsub hclosed
  have hw : 𝓕 v = 0 := by
    ext ξ i
    have hmem : ξ ∈ closure {ξ : EuclSpace | ‖ξ‖ ≠ Real.sqrt μ / (2 * Real.pi)} := by
      rw [hdense]
      exact Set.mem_univ ξ
    have heq : 𝓕 v ξ = (0 : CxSpace) := hcl hmem
    rw [heq]
    simp
  have hinv : (𝓕⁻ (𝓕 v) : SchwartzMap EuclSpace CxSpace) = v :=
    FourierPair.fourierInv_fourier_eq v
  rw [← hinv, hw]
  exact map_zero _

/-! ## The eigenfield obstruction and the refutation -/

/-- **No nonzero divergence-free Schwartz field on `ℝ³` is an eigenfield of
`curl`.**  If `curl u = a • u` and `div u = 0`, then `u = 0`.  (Equivalently:
`−Δ` has no eigenfields on the whole space; the Beltrami family `μ = a²` and
the harmonic family `μ = 0` are both covered.) -/
theorem eq_zero_of_curl_eq_smul {a : ℝ} {u : SchwartzVelocity}
    (hu : DivergenceFreeInitial u) (h : curlSchwartzCLM u = a • u) : u = 0 := by
  have h2 : curlSchwartzCLM (curlSchwartzCLM u) = (a ^ 2 : ℝ) • u := by
    rw [h, ContinuousLinearMap.map_smul, h, smul_smul, pow_two]
  have h3 : -laplacianSchwartz u = (a ^ 2 : ℝ) • u :=
    (curlCurlSchwartz_eq_neg_laplacian u hu).symm.trans h2
  have h4 : laplacianSchwartz u = (-(a ^ 2) : ℝ) • u := by
    have := congrArg (fun t : SchwartzVelocity => -t) h3
    rwa [neg_neg, ← neg_smul] at this
  have h5 : modelLaplacian (euclModel u) = -((a ^ 2 : ℝ) : ℂ) • euclModel u := by
    rw [← euclModel_laplacianSchwartz, h4, euclModel_smul_real, Complex.ofReal_neg]
  have h6 : euclModel u = 0 :=
    eq_zero_of_modelLaplacian_eq_neg_smul (sq_nonneg a) (euclModel u) h5
  exact (euclModel_eq_zero_iff u).mp h6

/-- The first mode of any Galerkin basis is **not** a `curl` eigenfield:
`curl (w 0) ≠ a • w 0` for every real `a`.  (Discharges the hypothesis
`not_curl_proj_commutes_of_first_mode_not_eigenfield` takes for free.) -/
theorem first_mode_not_curl_eigenfield (W : GalerkinBasisFamily) (a : ℝ) :
    curlSchwartzCLM (W.w 0) ≠ a • W.w 0 := by
  intro h
  have h0 : W.w 0 = 0 := eq_zero_of_curl_eq_smul (W.divergence_free 0) h
  have h1 : schwartzL2Inner (W.w 0) (W.w 0) = (0 : ℝ) := by
    rw [h0, schwartzL2Inner_zero_left]
  have h2 : schwartzL2Inner (W.w 0) (W.w 0) = (1 : ℝ) := by
    simpa using W.orthonormal 0 0
  linarith

/-- **Kernel refutation of the curl–projection commutation route** (ledger
F-029, mechanizing the docstring conjecture at `curl_proj_sq_le_of_commutes`,
registry row NAVIER-01): *no* `GalerkinBasisFamily` satisfies
`∀ m u, curl (P_m u) = P_m (curl u)`.  Commutation at `m = 1` forces the first
mode to be a `curl` eigenfield; there are no nonzero ones. -/
theorem not_forall_curl_commutes (W : GalerkinBasisFamily) :
    ¬ ∀ (m : ℕ) (u : SchwartzVelocity),
      curlSchwartzCLM (W.proj m u) = W.proj m (curlSchwartzCLM u) := by
  intro hcomm
  refine first_mode_not_curl_eigenfield W
    (schwartzL2Inner (curlSchwartzCLM (W.w 0)) (W.w 0)) ?_
  calc curlSchwartzCLM (W.w 0)
      = curlSchwartzCLM (W.proj 1 (W.w 0)) := by rw [proj_basis W (by omega)]
    _ = W.proj 1 (curlSchwartzCLM (W.w 0)) := hcomm 1 (W.w 0)
    _ = schwartzL2Inner (curlSchwartzCLM (W.w 0)) (W.w 0) • W.w 0 := by
        simp [GalerkinBasisFamily.proj, GalerkinBasisFamily.coeff]

-- Registry footer: axiom probes are run externally via proof-loop.py.

end Navier.Analysis.GalerkinBasis
