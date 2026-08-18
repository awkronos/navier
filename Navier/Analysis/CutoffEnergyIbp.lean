import Navier.Analysis.ParabolicCaccioppoli
import Navier.Analysis.CutoffIntegrationByParts

/-!
# Cutoff IBP for the kinetic energy density |u|²

This file builds the integrated-by-parts form of the local energy balance (the
`|u|²` analogue of `CutoffIntegrationByParts.cutoffEnstrophy_hasDerivAt_ibp`),
applying the same directional / transport / Laplacian integration-by-parts
lemmas to the integrand of the parabolic Caccioppoli inequality:

* `integral_cutoff_energy_transport_ibp` — ∫ χ (u·∇)|u|² = − ∫ (u·∇χ)|u|²
* `integral_cutoff_energy_laplacian_ibp` — ∫ χ Δ|u|² = ∫ (Δχ)|u|²
* `cutoffEnergy_ibp_eq` — the capstone equality for zero-force solutions:

  `∫ χ²⟨u,∂ₜu⟩ + ν∫ χ²|∇u|² = ∫ χ(u·∇χ)|u|² + (ν/2)∫ (Δχ²)|u|² − ∫ χ²(u·∇)p`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open MeasureTheory Set

namespace Navier.Analysis.CutoffEnergyIbp

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.ParabolicCaccioppoli
open Navier.Analysis.CutoffIntegrationByParts

/-! ### Smoothness and support plumbing -/

/-- The square of a `C^∞` scalar is `C^∞`. -/
theorem contDiff_sq {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (χ ^ 2) :=
  hχ.pow 2

/-- The square of a compactly supported scalar is compactly supported. -/
theorem hasCompactSupport_sq {χ : Space → ℝ}
    (hχsupp : HasCompactSupport χ) : HasCompactSupport (χ ^ 2) :=
  hχsupp.pow 2

/── Pointwise `(u·∇)(χ²) = 2χ(u·∇χ)`. -/
theorem fderiv_sq_apply {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (x v : Space) :
    fderiv ℝ (χ ^ 2) x v = 2 * χ x * fderiv ℝ χ x v := by
  have hdiff : DifferentiableAt ℝ χ x :=
    (hχ.differentiable (by norm_num)).differentiableAt
  calc
    fderiv ℝ (χ ^ 2) x v = fderiv ℝ (fun y : Space => χ y * χ y) x v := by
      simp [sq]
    _ = fderiv ℝ χ x v * χ x + χ x * fderiv ℝ χ x v := by
      rw [fderiv_fun_mul hdiff hdiff]
      simp
    _ = 2 * χ x * fderiv ℝ χ x v := by ring

/-! ### The two integration-by-parts identities for |u|² -/

/── **Transport IBP for |u|²**: ∫ χ (u·∇)|u|² = − ∫ (u·∇χ)|u|².
Follows directly from `integral_cutoff_transport_ibp` with `F = |u|²`. -/
theorem integral_cutoff_energy_transport_ibp
    {χ : Space → ℝ} {u : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, staticDivergence u x = 0) :
    ∫ x : Space, χ x * fderiv ℝ (fun y => officialEuclideanNorm (u y) ^ 2) x (u x) =
      - ∫ x : Space, fderiv ℝ χ x (u x) * officialEuclideanNorm (u x) ^ 2 :=
  integral_cutoff_transport_ibp hχ hχsupp (contDiff_officialNormSq_comp hu) hu hdiv

/── **Laplacian IBP for |u|²**: ∫ χ Δ|u|² = ∫ (Δχ)|u|².
Follows directly from `integral_cutoff_laplacian_ibp` with `F = |u|²`. -/
theorem integral_cutoff_energy_laplacian_ibp
    {χ : Space → ℝ} {u : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ u) :
    ∫ x : Space, χ x * (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun y => officialEuclideanNorm (u y) ^ 2) z
          (basisVector i)) x (basisVector i)) =
      ∫ x : Space, (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i))
        * officialEuclideanNorm (u x) ^ 2 :=
  integral_cutoff_laplacian_ibp hχ hχsupp (contDiff_officialNormSq_comp hu)

/-! ### The capstone equality (zero force) -/

/── **Cutoff energy balance, integrated by parts (zero force).**  Along a zero-force
partial classical solution, for every smooth compactly supported cutoff `χ` and
time `t ∈ (0,T)`,

  `∫ χ²⟨u,∂ₜu⟩ + ν∫ χ²|∇u|²
   = ∫ χ(u·∇χ)|u|² + (ν/2)∫ (Δχ²)|u|² − ∫ χ²(u·∇)p`.

The proof: integrate `local_energy_balance × χ²`, cancel the matched dissipation,
then apply transport and Laplacian IBP.
-/
theorem cutoffEnergy_ibp_eq
    {ν : ℝ} {u₀ : VelocityField} {T : ℝ}
    (sol : PartialClassicalSolution ν zeroForce u₀ T)
    {χ : Space → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t < T) :
    (∫ x : Space, χ x ^ 2 * officialInner (sol.velocity t x)
        (timeDerivative sol.velocity t x))
      + ν * (∫ x : Space, χ x ^ 2 * (∑ i : Fin 3,
          officialEuclideanNorm (fderiv ℝ (sol.velocity t) x (basisVector i)) ^ 2))
    = (∫ x : Space, χ x * fderiv ℝ χ x (sol.velocity t x) *
        officialEuclideanNorm (sol.velocity t x) ^ 2)
      - (∫ x : Space, χ x ^ 2 * fderiv ℝ (sol.pressure t) x (sol.velocity t x))
      + (ν / 2) * (∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x
          (basisVector i)) * officialEuclideanNorm (sol.velocity t x) ^ 2) := by
  set u := sol.velocity with hu_def
  set p := sol.pressure with hp_def
  have huC : ContDiff ℝ ∞ (u t) := velocity_slice_contDiff sol ht0 htT
  have hpC : ContDiff ℝ ∞ (p t) := pressure_slice_contDiff sol ht0 htT
  have hdivfree : ∀ x, staticDivergence (u t) x = 0 := by
    intro x
    have hi : IncompressibleBefore T u := sol.incompressible
    simpa [staticDivergence, divergence, spatialDerivative] using hi t ht0 htT x
  have hχ_sq : ContDiff ℝ ∞ (χ ^ 2) := contDiff_sq hχ
  have hχ_sq_supp : HasCompactSupport (χ ^ 2) := hasCompactSupport_sq hχsupp
  -- pointwise energy balance for zero force
  have hbalance : ∀ x : Space,
      2 * officialInner (u t x) (timeDerivative u t x) =
      - fderiv ℝ (fun y => officialEuclideanNorm (u t y) ^ 2) x (u t x)
      + ν * (∑ i : Fin 3,
          fderiv ℝ (fun z =>
            fderiv ℝ (fun y => officialEuclideanNorm (u t y) ^ 2) z (basisVector i)) x
            (basisVector i))
      - 2 * ν * (∑ i : Fin 3,
          officialEuclideanNorm (fderiv ℝ (u t) x (basisVector i)) ^ 2)
      - 2 * fderiv ℝ (p t) x (u t x) := by
    intro x
    have h := local_energy_balance sol ht0 htT x
    have hzero : zeroForce t x = (0 : Space) := rfl
    -- zeroForce t x = 0, so the force term drops
    simpa [hzero, officialInner_zero_right] using h
  -- continuous representatives for the five slots
  let A : Space → ℝ := fun x =>
    fderiv ℝ (fun y => officialEuclideanNorm (u t y) ^ 2) x (u t x)
  let B : Space → ℝ := fun x => ∑ i : Fin 3,
    fderiv ℝ (fun z =>
      fderiv ℝ (fun y => officialEuclideanNorm (u t y) ^ 2) z (basisVector i)) x
      (basisVector i)
  let C : Space → ℝ := fun x => ∑ i : Fin 3,
    officialEuclideanNorm (fderiv ℝ (u t) x (basisVector i)) ^ 2
  let D : Space → ℝ := fun x => fderiv ℝ (p t) x (u t x)
  have h_cont_A : Continuous A :=
    ((contDiff_officialNormSq_comp huC).continuous_fderiv (by norm_num)).clm_apply
      huC.continuous
  have h_cont_B : Continuous B :=
    continuous_finsetSum _ fun i _ =>
      (contDiff_fderiv_apply (contDiff_fderiv_apply
        (contDiff_officialNormSq_comp huC) (basisVector i)) (basisVector i)
      ).continuous
  have h_cont_C : Continuous C :=
    continuous_finsetSum _ fun i _ =>
      continuous_officialNormSq_comp
        (((huC.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const).continuous)
  have h_cont_D : Continuous D :=
    (hpC.continuous_fderiv (by norm_num)).clm_apply huC.continuous
  -- integrability of χ²·A, χ²·B, χ²·C, χ²·D
  have h_int_A : Integrable (fun x : Space => χ x ^ 2 * A x) :=
    (hχ_sq.continuous.mul h_cont_A).integrable_of_hasCompactSupport hχ_sq_supp.mul_right
  have h_int_B : Integrable (fun x : Space => χ x ^ 2 * B x) :=
    (hχ_sq.continuous.mul h_cont_B).integrable_of_hasCompactSupport hχ_sq_supp.mul_right
  have h_int_C : Integrable (fun x : Space => χ x ^ 2 * C x) :=
    (hχ_sq.continuous.mul h_cont_C).integrable_of_hasCompactSupport hχ_sq_supp.mul_right
  have h_int_D : Integrable (fun x : Space => χ x ^ 2 * D x) :=
    (hχ_sq.continuous.mul h_cont_D).integrable_of_hasCompactSupport hχ_sq_supp.mul_right
  have h_int_time : Integrable (fun x : Space =>
      χ x ^ 2 * officialInner (u t x) (timeDerivative u t x)) :=
    (hχ_sq.continuous.mul (continuous_officialInner_comp huC.continuous
      ((huC.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    )).integrable_of_hasCompactSupport hχ_sq_supp.mul_right
  -- pointwise equality: multiply hbalance by χ²/2, add ν·χ²·C, rearrange
  have hpointwise : ∀ x : Space,
      χ x ^ 2 * officialInner (u t x) (timeDerivative u t x)
        + ν * (χ x ^ 2 * C x) =
      -(1/2 : ℝ) * (χ x ^ 2 * A x)
        + (ν/2 : ℝ) * (χ x ^ 2 * B x)
        - χ x ^ 2 * D x := by
    intro x
    have hx := hbalance x
    nlinarith
  -- integrate the pointwise equality
  have hLHS : (∫ x : Space, χ x ^ 2 * officialInner (u t x) (timeDerivative u t x))
      + ν * (∫ x : Space, χ x ^ 2 * C x) =
      -(1/2 : ℝ) * (∫ x : Space, χ x ^ 2 * A x)
        + (ν/2 : ℝ) * (∫ x : Space, χ x ^ 2 * B x)
        - (∫ x : Space, χ x ^ 2 * D x) := by
    calc
      (∫ x : Space, χ x ^ 2 * officialInner (u t x) (timeDerivative u t x))
          + ν * (∫ x : Space, χ x ^ 2 * C x)
        = ∫ x : Space, (χ x ^ 2 * officialInner (u t x) (timeDerivative u t x)
            + ν * (χ x ^ 2 * C x)) := by
          rw [integral_add h_int_time (h_int_C.const_smul ν), smul_eq_mul]
      _ = ∫ x : Space, (-(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x)
            - χ x ^ 2 * D x) := by
          refine integral_congr_ae ?_
          filter_upwards with x; exact hpointwise x
      _ = (∫ x : Space, (-(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x)))
            - (∫ x : Space, χ x ^ 2 * D x) := by
          rw [integral_sub ?_ h_int_D]
          · exact (h_int_A.const_smul (-(1/2 : ℝ))).add (h_int_B.const_smul (ν/2 : ℝ))
      _ = (-(1/2 : ℝ) * (∫ x : Space, χ x ^ 2 * A x)
            + (ν/2 : ℝ) * (∫ x : Space, χ x ^ 2 * B x))
          - (∫ x : Space, χ x ^ 2 * D x) := by
        simp [integral_add (h_int_A.const_smul (-(1/2 : ℝ))) (h_int_B.const_smul (ν/2 : ℝ)),
          integral_const_mul]
      _ = -(1/2 : ℝ) * (∫ x : Space, χ x ^ 2 * A x)
          + (ν/2 : ℝ) * (∫ x : Space, χ x ^ 2 * B x)
          - (∫ x : Space, χ x ^ 2 * D x) := by ring
  -- apply transport IBP to ∫ χ²·A  (cutoff = χ², field = u t)
  have hIBP_A : ∫ x : Space, χ x ^ 2 * A x =
      - ∫ x : Space, 2 * χ x * fderiv ℝ χ x (u t x) *
        officialEuclideanNorm (u t x) ^ 2 := by
    have h_transport : ∫ x : Space, χ x ^ 2 * A x =
        - ∫ x : Space, fderiv ℝ (fun y => χ y ^ 2) x (u t x) *
          officialEuclideanNorm (u t x) ^ 2 :=
      integral_cutoff_energy_transport_ibp hχ_sq hχ_sq_supp huC hdivfree
    have h_sq_apply : ∀ x : Space,
        fderiv ℝ (fun y => χ y ^ 2) x (u t x) = 2 * χ x * fderiv ℝ χ x (u t x) :=
      fderiv_sq_apply hχ (x := ·) (v := u t ·)
    rw [h_transport]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [h_sq_apply x]
  have hIBP_B : ∫ x : Space, χ x ^ 2 * B x =
      ∫ x : Space, (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x
        (basisVector i)) * officialEuclideanNorm (u t x) ^ 2 :=
    integral_cutoff_energy_laplacian_ibp hχ_sq hχ_sq_supp huC
  -- substitute the IBP results into hLHS
  calc
    (∫ x : Space, χ x ^ 2 * officialInner (u t x) (timeDerivative u t x))
        + ν * (∫ x : Space, χ x ^ 2 * C x)
      = -(1/2 : ℝ) * (∫ x : Space, χ x ^ 2 * A x)
          + (ν/2 : ℝ) * (∫ x : Space, χ x ^ 2 * B x)
          - (∫ x : Space, χ x ^ 2 * D x) := hLHS
    _ = -(1/2 : ℝ) * (- ∫ x : Space, 2 * χ x * fderiv ℝ χ x (u t x) *
          officialEuclideanNorm (u t x) ^ 2)
        + (ν/2 : ℝ) * (∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x
          (basisVector i)) * officialEuclideanNorm (u t x) ^ 2)
        - (∫ x : Space, χ x ^ 2 * D x) := by
      rw [hIBP_A, hIBP_B]
    _ = (∫ x : Space, χ x * fderiv ℝ χ x (u t x) *
          officialEuclideanNorm (u t x) ^ 2)
        + (ν / 2) * (∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x
          (basisVector i)) * officialEuclideanNorm (u t x) ^ 2)
        - (∫ x : Space, χ x ^ 2 * D x) := by
      ring_nf
      simp [integral_const_mul]
    _ = (∫ x : Space, χ x * fderiv ℝ χ x (u t x) *
          officialEuclideanNorm (u t x) ^ 2)
        - (∫ x : Space, χ x ^ 2 * D x)
        + (ν / 2) * (∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x
          (basisVector i)) * officialEuclideanNorm (u t x) ^ 2) := by ring
    _ = (∫ x : Space, χ x * fderiv ℝ χ x (sol.velocity t x) *
          officialEuclideanNorm (sol.velocity t x) ^ 2)
        - (∫ x : Space, χ x ^ 2 * fderiv ℝ (sol.pressure t) x (sol.velocity t x))
        + (ν / 2) * (∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x
          (basisVector i)) * officialEuclideanNorm (sol.velocity t x) ^ 2) := by
      simp [u, p, D]

end Navier.Analysis.CutoffEnergyIbp
