import Navier.Analysis.ParabolicCaccioppoli
import Navier.Analysis.CutoffIntegrationByParts
import Navier.Breakdown.MaximalNonextension

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
set_option maxHeartbeats 0

noncomputable section

open scoped ContDiff Topology
open MeasureTheory Set

namespace Navier.Analysis.CutoffEnergyIbp

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Enstrophy
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.CutoffEnstrophy
open Navier.Analysis.ParabolicCaccioppoli
open Navier.Analysis.CutoffIntegrationByParts
open Navier.Breakdown

/-! ### Smoothness and support plumbing -/

/-- The square of a `C^∞` scalar is `C^∞`. -/
theorem contDiff_sq {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (χ ^ 2) :=
  hχ.pow 2

/-- The square of a compactly supported scalar is compactly supported. -/
theorem hasCompactSupport_sq {χ : Space → ℝ}
    (hχsupp : HasCompactSupport χ) : HasCompactSupport (χ ^ 2) := by
  simpa [sq] using hχsupp.mul_right (f' := χ)

/-- Pointwise `(u·∇)(χ²) = 2χ(u·∇χ)`. -/
theorem fderiv_sq_apply {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (x v : Space) :
    fderiv ℝ (χ ^ 2) x v = 2 * χ x * fderiv ℝ χ x v := by
  have hdiff : DifferentiableAt ℝ χ x :=
    (hχ.differentiable (by norm_num)).differentiableAt
  calc
    fderiv ℝ (χ ^ 2) x v = fderiv ℝ (χ * χ) x v := by simp [sq]
    _ = (χ x • fderiv ℝ χ x + χ x • fderiv ℝ χ x) v := by
      rw [fderiv_mul hdiff hdiff]
    _ = χ x * fderiv ℝ χ x v + χ x * fderiv ℝ χ x v := by simp
    _ = 2 * χ x * fderiv ℝ χ x v := by ring

/-! ### The two integration-by-parts identities for |u|² -/

/-- **Transport IBP for |u|²**: ∫ χ (u·∇)|u|² = − ∫ (u·∇χ)|u|².
Follows directly from `integral_cutoff_transport_ibp` with `F = |u|²`. -/
theorem integral_cutoff_energy_transport_ibp
    {χ : Space → ℝ} {u : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ u) (hdiv : ∀ x, staticDivergence u x = 0) :
    ∫ x : Space, χ x * fderiv ℝ (fun y => officialEuclideanNorm (u y) ^ 2) x (u x) =
      - ∫ x : Space, fderiv ℝ χ x (u x) * officialEuclideanNorm (u x) ^ 2 :=
  integral_cutoff_transport_ibp hχ hχsupp (contDiff_officialNormSq_comp hu) hu hdiv

/-- **Laplacian IBP for |u|²**: ∫ χ Δ|u|² = ∫ (Δχ)|u|².
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

/-- Laplacian of `chi^2` (second fderiv sum). Irreducible to avoid `whnf` blowup. -/
@[irreducible] noncomputable def laplacianChiSq (χ : Space → ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3,
    fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x (basisVector i)

/-- Squared Frobenius norm of `grad u`. Irreducible to avoid `whnf` blowup. -/
@[irreducible] noncomputable def gradNormSq (u : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2

lemma laplacianChiSq_eq (χ : Space → ℝ) (x : Space) : laplacianChiSq χ x =
    ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x (basisVector i) := by
  unfold laplacianChiSq; rfl

lemma gradNormSq_eq (u : Space → Space) (x : Space) : gradNormSq u x =
    ∑ i : Fin 3, officialEuclideanNorm (fderiv ℝ u x (basisVector i)) ^ 2 := by
  unfold gradNormSq; rfl

/-- **Cutoff energy balance, integrated by parts (zero force).**  Along a zero-force
partial classical solution, for every smooth compactly supported cutoff `chi` and
time `t in (0,T)`,

  `∫ chi^2 <u, d_t u> + nu ∫ chi^2 |grad u|^2
   = ∫ chi (u · grad chi) |u|^2 + (nu/2) ∫ (Δ chi^2) |u|^2
     - ∫ chi^2 (u · grad) p`.

The proof: integrate `local_energy_balance * chi^2`, cancel the matched dissipation,
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
      + ν * (∫ x : Space, χ x ^ 2 * gradNormSq (sol.velocity t) x)
    = (∫ x : Space, χ x * fderiv ℝ χ x (sol.velocity t x) *
        officialEuclideanNorm (sol.velocity t x) ^ 2)
      - (∫ x : Space, χ x ^ 2 * fderiv ℝ (sol.pressure t) x (sol.velocity t x))
      + (ν / 2) * (∫ x : Space, laplacianChiSq χ x * officialEuclideanNorm (sol.velocity t x) ^ 2) := by
  set_option maxHeartbeats 0 in
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
    have hzero_inner : officialInner (sol.velocity t x) (0 : Space) = 0 := by
      simp [officialInner_eq_sum]
    -- zeroForce t x = 0, so the force term drops
    simpa [u, p, hzero, hzero_inner] using h
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
  -- helper: convert Integrable.smul (c • f) to Integrable (fun x => c * f x)
  have h_int_smul (c : ℝ) (f : Space → ℝ) (hf : Integrable f volume) :
      Integrable (fun x : Space => c * f x) volume := by
    have h_eq : c • f = (fun x : Space => c * f x) := by
      ext x; simp
    simpa [h_eq] using hf.smul c
  have h_int_time : Integrable (fun x : Space =>
      χ x ^ 2 * officialInner (u t x) (timeDerivative u t x)) := by
    -- Use the pointwise equality from hbalance to rewrite as linear combination of
    -- already-integrable terms, avoiding continuity of timeDerivative at t = 0.
    have h_expr_pointwise (x : Space) : χ x ^ 2 * officialInner (u t x) (timeDerivative u t x) =
        -(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x)
        - ν * (χ x ^ 2 * C x) - χ x ^ 2 * D x := by
      have hx := hbalance x
      -- hx: 2·⟨u,∂u⟩ = -A + ν·B - 2ν·C - 2·D
      have h_inner : officialInner (u t x) (timeDerivative u t x) =
          -(1/2 : ℝ) * A x + (ν/2 : ℝ) * B x - ν * C x - D x := by
        linarith
      calc
        χ x ^ 2 * officialInner (u t x) (timeDerivative u t x)
            = χ x ^ 2 * (-(1/2 : ℝ) * A x + (ν/2 : ℝ) * B x - ν * C x - D x) := by rw [h_inner]
        _ = -(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x)
            - ν * (χ x ^ 2 * C x) - χ x ^ 2 * D x := by ring
    have h_expr : (fun x : Space => χ x ^ 2 * officialInner (u t x) (timeDerivative u t x)) =
        (fun x : Space => -(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x)
          - ν * (χ x ^ 2 * C x) - χ x ^ 2 * D x) := by
      funext x; exact h_expr_pointwise x
    rw [h_expr]
    have hsumAB : Integrable (fun x : Space =>
        (-(1/2 : ℝ)) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x)) :=
      (h_int_smul (-(1/2 : ℝ)) (fun x => χ x ^ 2 * A x) h_int_A).add
        (h_int_smul (ν/2 : ℝ) (fun x => χ x ^ 2 * B x) h_int_B)
    have hsumC : Integrable (fun x : Space => ν * (χ x ^ 2 * C x)) :=
      h_int_smul ν (fun x => χ x ^ 2 * C x) h_int_C
    exact ((hsumAB.sub hsumC).sub h_int_D)
  -- pointwise equality: multiply hbalance by χ²/2, add ν·χ²·C, rearrange
  have hpointwise : ∀ x : Space,
      χ x ^ 2 * officialInner (u t x) (timeDerivative u t x)
        + ν * (χ x ^ 2 * C x) =
      -(1/2 : ℝ) * (χ x ^ 2 * A x)
        + (ν/2 : ℝ) * (χ x ^ 2 * B x)
        - χ x ^ 2 * D x := by
    intro x
    have hx := hbalance x
    -- hx: 2·⟨u,∂u⟩ = -A + ν·B - 2ν·C - 2·D
    have hx_simp : officialInner (u t x) (timeDerivative u t x) + ν * C x =
        -(1/2 : ℝ) * A x + (ν/2 : ℝ) * B x - D x := by
      linarith
    calc
      χ x ^ 2 * officialInner (u t x) (timeDerivative u t x) + ν * (χ x ^ 2 * C x) =
          χ x ^ 2 * (officialInner (u t x) (timeDerivative u t x) + ν * C x) := by ring
      _ = χ x ^ 2 * (-(1/2 : ℝ) * A x + (ν/2 : ℝ) * B x - D x) := by rw [hx_simp]
      _ = -(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x) - χ x ^ 2 * D x := by ring
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
          have h_nuC : Integrable (fun x : Space => ν * (χ x ^ 2 * C x)) :=
            h_int_smul ν (fun x => χ x ^ 2 * C x) h_int_C
          rw [← integral_const_mul, ← integral_add h_int_time h_nuC]
    _ = ∫ x : Space, (-(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x)
          - χ x ^ 2 * D x) := by
        refine integral_congr_ae ?_
        filter_upwards with x; exact hpointwise x
    _ = (∫ x : Space, (-(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x)))
          - (∫ x : Space, χ x ^ 2 * D x) := by
        have h_AB : Integrable (fun x : Space =>
            (-(1/2 : ℝ) * (χ x ^ 2 * A x) + (ν/2 : ℝ) * (χ x ^ 2 * B x))) :=
          (h_int_smul (-(1/2 : ℝ)) (fun x => χ x ^ 2 * A x) h_int_A).add
            (h_int_smul (ν/2 : ℝ) (fun x => χ x ^ 2 * B x) h_int_B)
        rw [integral_sub h_AB h_int_D]
    _ = (-(1/2 : ℝ) * (∫ x : Space, χ x ^ 2 * A x)
          + (ν/2 : ℝ) * (∫ x : Space, χ x ^ 2 * B x))
        - (∫ x : Space, χ x ^ 2 * D x) := by
      have hA_s : Integrable (fun x : Space => (-(1/2 : ℝ)) * (χ x ^ 2 * A x)) :=
        h_int_smul (-(1/2 : ℝ)) (fun x => χ x ^ 2 * A x) h_int_A
      have hB_s : Integrable (fun x : Space => (ν/2 : ℝ) * (χ x ^ 2 * B x)) :=
        h_int_smul (ν/2 : ℝ) (fun x => χ x ^ 2 * B x) h_int_B
      rw [integral_add hA_s hB_s, integral_const_mul, integral_const_mul]
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
    have h_sq_apply (x : Space) :
        fderiv ℝ (fun y => χ y ^ 2) x (u t x) = 2 * χ x * fderiv ℝ χ x (u t x) :=
      fderiv_sq_apply hχ x (u t x)
    rw [h_transport]
    refine congrArg Neg.neg ?_
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [h_sq_apply x]
  have hIBP_B : ∫ x : Space, χ x ^ 2 * B x =
      ∫ x : Space, (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun y => χ y ^ 2) z (basisVector i)) x
        (basisVector i)) * officialEuclideanNorm (u t x) ^ 2 :=
    integral_cutoff_energy_laplacian_ibp hχ_sq hχ_sq_supp huC
  -- rewrite IBP results to use irreducible defs (avoids whnf on `basisVector` sums)
  have hIBP_B' : ∫ x : Space, χ x ^ 2 * B x =
      ∫ x : Space, laplacianChiSq χ x * officialEuclideanNorm (u t x) ^ 2 := by
    rw [hIBP_B]
    refine integral_congr_ae ?_
    filter_upwards with x
    simp [laplacianChiSq_eq χ x]
  have hC_rewrite : (∫ x : Space, χ x ^ 2 * C x) = (∫ x : Space, χ x ^ 2 * gradNormSq (u t) x) := by
    simp [C, gradNormSq_eq]
  have hA_rewrite : (∫ x : Space, χ x ^ 2 * A x) =
      -∫ x : Space, 2 * χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2 := hIBP_A
  -- apply rewrites to hLHS, then simplify to match the irreducible-def goal
  have hcalc_raw : (∫ x : Space, χ x ^ 2 * officialInner (u t x) (timeDerivative u t x))
      + ν * (∫ x : Space, χ x ^ 2 * gradNormSq (u t) x)
    = (∫ x : Space, χ x * fderiv ℝ χ x (u t x) *
        officialEuclideanNorm (u t x) ^ 2)
      - (∫ x : Space, χ x ^ 2 * fderiv ℝ (p t) x (u t x))
      + (ν / 2) * (∫ x : Space, laplacianChiSq χ x * officialEuclideanNorm (u t x) ^ 2) := by
    have htemp := hLHS
    rw [hC_rewrite, hIBP_B', hA_rewrite] at htemp
    -- htemp: LHS = -(1/2)*(-∫ ...) + (ν/2)*∫(laplacian... * |u|²) - ∫ D
    -- simplify -(1/2)*(-∫ ...) = ∫(χ*...)
    have h_simplify : -(1/2 : ℝ) * (-(∫ x : Space, 2 * χ x * fderiv ℝ χ x (u t x) *
        officialEuclideanNorm (u t x) ^ 2)) =
        (∫ x : Space, χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2) := by
      have h_temp : (∫ x : Space, 2 * χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2) =
          2 * (∫ x : Space, χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2) := by
        calc
          (∫ x : Space, 2 * χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2)
              = ∫ x : Space, 2 * (χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2) := by
                refine integral_congr_ae ?_
                filter_upwards with x; ring
          _ = 2 * (∫ x : Space, χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2) :=
                integral_const_mul (2 : ℝ) (fun x : Space => χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2)
      calc
        -(1/2 : ℝ) * (-(∫ x : Space, 2 * χ x * fderiv ℝ χ x (u t x) *
            officialEuclideanNorm (u t x) ^ 2))
            = (1/2 : ℝ) * (∫ x : Space, 2 * χ x * fderiv ℝ χ x (u t x) *
                officialEuclideanNorm (u t x) ^ 2) := by ring
        _ = (1/2 : ℝ) * (2 * (∫ x : Space, χ x * fderiv ℝ χ x (u t x) *
            officialEuclideanNorm (u t x) ^ 2)) := by rw [h_temp]
        _ = (∫ x : Space, χ x * fderiv ℝ χ x (u t x) * officialEuclideanNorm (u t x) ^ 2) := by ring
    rw [h_simplify] at htemp
    -- After simplification, htemp has LHS = (∫ χ*fderiv*|u|² + (ν/2)*∫(Δχ²*|u|²)) - ∫ D
    -- Goal has LHS = (∫ χ*fderiv*|u|² - ∫ D) + (ν/2)*∫(Δχ²*|u|²)
    -- These are equal by ring
    simpa [D, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using htemp
  simpa [hu_def, hp_def] using hcalc_raw

end Navier.Analysis.CutoffEnergyIbp