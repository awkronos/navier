import Navier.Analysis.CutoffEnstrophy

/-!
# Cutoff integration by parts (integral layer, part b)

The integration-by-parts remainders of the cutoff enstrophy balance: against
a smooth compactly supported cutoff `χ`, the transport and viscous terms of
`local_enstrophy_balance` convert into `∇χ`/`Δχ` remainders with **no
boundary terms** (compact support kills them — this is the finite-`R`
boundary-vanishing content):

* `integral_cutoff_directional_ibp` — `∫ χ ∂_v F = − ∫ (∂_v χ) F`
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` on the additive Haar
  volume of `Space`).
* `integral_cutoff_transport_ibp` — `∫ χ (w·∇F) = − ∫ (w·∇χ) F` for a
  divergence-free advecting field: coordinatewise IBP with multiplier `χ·wᵢ`,
  Leibniz, and the `div w = 0` cancellation.
* `integral_cutoff_laplacian_ibp` — `∫ χ ΔF = ∫ (Δχ) F`: two directional
  IBPs per coordinate.

Applied to `F = |ω(t,·)|²` along a classical solution and composed with the
cutoff enstrophy rate (`cutoffEnstrophy_hasDerivAt_balance`), this yields the
capstone of the integral layer:

  `E_χ'(t₀) = ∫ χ·2⟨ω,(ω·∇)u⟩ + ∫ (u·∇χ)|ω|² + ν∫ (Δχ)|ω|² − 2ν∫ χ|∇ω|²`

(`cutoffEnstrophy_hasDerivAt_ibp`) — Majda–Bertozzi §3.3 in cutoff form: the
stretching production, the two cutoff remainders, and the sign-definite
dissipation.

Residual (ladder rung 6, integral layer, part (c) — strictly lower): for the
scaled family `χ_R = χ(·/R)` the remainders `∫(u·∇χ_R)|ω|²` and
`∫(Δχ_R)|ω|²` vanish as `R → ∞` and `E_{χ_R} → E` under the
`LocallyDominatedEnstrophy` hypothesis plus a locally uniform velocity bound
on the support annuli; the limit of the capstone identity then delivers
`enstrophyDifferentialInequality` (`E' ≤ 2G·E` after
`stretching_pointwise_bound` and dropping the dissipation).

Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §3.3.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff
open MeasureTheory Set

namespace Navier.Analysis.CutoffIntegrationByParts

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Enstrophy
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.LocalEnstrophyBalance
open Navier.Analysis.CutoffEnstrophy

/-!
## Smoothness and support plumbing
-/

/-- The evaluated derivative field of a `C^∞` scalar is `C^∞`. -/
theorem contDiff_fderiv_apply {F : Space → ℝ} (hF : ContDiff ℝ ∞ F)
    (v : Space) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ F x v) :=
  (hF.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const

/-- The evaluated derivative field of a compactly supported scalar is
compactly supported. -/
theorem hasCompactSupport_fderiv_apply {χ : Space → ℝ}
    (hsupp : HasCompactSupport χ) (v : Space) :
    HasCompactSupport (fun x => fderiv ℝ χ x v) :=
  (hsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L v) rfl

/-- The squared official norm of a `C^∞` field is `C^∞`. -/
theorem contDiff_officialNormSq_comp {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x => officialEuclideanNorm (f x) ^ 2) := by
  have hshape : (fun x => officialEuclideanNorm (f x) ^ 2) =
      (fun x => ∑ i : Fin 3, f x i ^ 2) := by
    funext x
    exact officialEuclideanNorm_sq_eq_sum (f x)
  rw [hshape]
  apply ContDiff.sum
  intro i _
  exact ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) i).contDiff.comp hf).pow 2

/-- Basis expansion of a scalar directional derivative. -/
theorem fderiv_apply_eq_sum_basis {F : Space → ℝ} (x : Space) (w : Space) :
    fderiv ℝ F x w = ∑ i : Fin 3, w i * fderiv ℝ F x (basisVector i) := by
  have hbasis : w = ∑ i, (w i) • basisVector i := by
    simpa only [basisVector] using (pi_eq_sum_univ' w)
  calc fderiv ℝ F x w = fderiv ℝ F x (∑ i, (w i) • basisVector i) := by
        rw [← hbasis]
    _ = ∑ i, w i * fderiv ℝ F x (basisVector i) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul]

/-!
## The three integration-by-parts identities
-/

/-- **Directional integration by parts against the cutoff**:
`∫ χ ∂_v F = − ∫ (∂_v χ) F`.  No boundary term appears: the compact support
of `χ` carries the boundary vanishing at finite scale. -/
theorem integral_cutoff_directional_ibp
    {χ F : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    (hF : ContDiff ℝ ∞ F) (v : Space) :
    ∫ x : Space, χ x * fderiv ℝ F x v =
      - ∫ x : Space, fderiv ℝ χ x v * F x := by
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact ((contDiff_fderiv_apply hχ v).continuous.mul
      hF.continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply hχsupp v).mul_right)
  · exact (hχ.continuous.mul
      (contDiff_fderiv_apply hF v).continuous).integrable_of_hasCompactSupport
      hχsupp.mul_right
  · exact (hχ.continuous.mul hF.continuous).integrable_of_hasCompactSupport
      hχsupp.mul_right
  · exact fun x _ => (hχ.differentiable (by norm_num)).differentiableAt
  · exact fun x _ => (hF.differentiable (by norm_num)).differentiableAt

/-- **Transport integration by parts against the cutoff** (divergence-free
advecting field): `∫ χ (w·∇F) = − ∫ (w·∇χ) F`.  Coordinatewise IBP with
multiplier `χ·wᵢ`; the Leibniz `div`-term cancels by `staticDivergence w = 0`. -/
theorem integral_cutoff_transport_ibp
    {χ F : Space → ℝ} {w : VelocityField}
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    (hF : ContDiff ℝ ∞ F) (hw : ContDiff ℝ ∞ w)
    (hdiv : ∀ x, staticDivergence w x = 0) :
    ∫ x : Space, χ x * fderiv ℝ F x (w x) =
      - ∫ x : Space, fderiv ℝ χ x (w x) * F x := by
  have hdiffχ : ∀ x : Space, DifferentiableAt ℝ χ x := fun x =>
    (hχ.differentiable (by norm_num)).differentiableAt
  have hdiffF : ∀ x : Space, DifferentiableAt ℝ F x := fun x =>
    (hF.differentiable (by norm_num)).differentiableAt
  have hdiffw : ∀ x : Space, DifferentiableAt ℝ w x := fun x =>
    (hw.differentiable (by norm_num)).differentiableAt
  have hwi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x : Space => w x i) := fun i =>
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 3 => ℝ) i).contDiff.comp hw
  have hχwi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x : Space => χ x * w x i) :=
    fun i => hχ.mul (hwi i)
  have hstep : ∀ i : Fin 3,
      ∫ x : Space, (χ x * w x i) * fderiv ℝ F x (basisVector i) =
      - ∫ x : Space,
          fderiv ℝ (fun y => χ y * w y i) x (basisVector i) * F x := by
    intro i
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
    · exact ((contDiff_fderiv_apply (hχwi i) (basisVector i)).continuous.mul
        hF.continuous).integrable_of_hasCompactSupport
        ((hasCompactSupport_fderiv_apply hχsupp.mul_right
          (basisVector i)).mul_right)
    · exact (((hχwi i).continuous).mul
        (contDiff_fderiv_apply hF (basisVector i)).continuous
        ).integrable_of_hasCompactSupport hχsupp.mul_right.mul_right
    · exact (((hχwi i).continuous).mul hF.continuous
        ).integrable_of_hasCompactSupport hχsupp.mul_right.mul_right
    · exact fun x _ => ((hχwi i).differentiable (by norm_num)).differentiableAt
    · exact fun x _ => hdiffF x
  have hprod : ∀ (i : Fin 3) (x : Space),
      fderiv ℝ (fun y => χ y * w y i) x (basisVector i) =
      χ x * fderiv ℝ w x (basisVector i) i +
        w x i * fderiv ℝ χ x (basisVector i) := by
    intro i x
    rw [fderiv_fun_mul (hdiffχ x)
      (((hwi i).differentiable (by norm_num)).differentiableAt)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_component_apply w x (basisVector i) (hdiffw x) i]
  have hint1 : ∀ i : Fin 3, Integrable (fun x : Space =>
      (χ x * w x i) * fderiv ℝ F x (basisVector i)) := fun i =>
    (((hχwi i).continuous).mul (contDiff_fderiv_apply hF (basisVector i)
      ).continuous).integrable_of_hasCompactSupport hχsupp.mul_right.mul_right
  have hint2 : ∀ i : Fin 3, Integrable (fun x : Space =>
      fderiv ℝ (fun y => χ y * w y i) x (basisVector i) * F x) := fun i =>
    ((contDiff_fderiv_apply (hχwi i) (basisVector i)).continuous.mul
      hF.continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply hχsupp.mul_right
        (basisVector i)).mul_right)
  calc ∫ x : Space, χ x * fderiv ℝ F x (w x)
      = ∫ x : Space, ∑ i : Fin 3,
          (χ x * w x i) * fderiv ℝ F x (basisVector i) := by
        congr 1
        funext x
        rw [fderiv_apply_eq_sum_basis x (w x), Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i : Fin 3, ∫ x : Space,
          (χ x * w x i) * fderiv ℝ F x (basisVector i) :=
        integral_finsetSum _ fun i _ => hint1 i
    _ = ∑ i : Fin 3, - ∫ x : Space,
          fderiv ℝ (fun y => χ y * w y i) x (basisVector i) * F x :=
        Finset.sum_congr rfl fun i _ => hstep i
    _ = - ∑ i : Fin 3, ∫ x : Space,
          fderiv ℝ (fun y => χ y * w y i) x (basisVector i) * F x := by
        rw [Finset.sum_neg_distrib]
    _ = - ∫ x : Space, ∑ i : Fin 3,
          fderiv ℝ (fun y => χ y * w y i) x (basisVector i) * F x := by
        rw [integral_finsetSum _ fun i _ => hint2 i]
    _ = - ∫ x : Space, fderiv ℝ χ x (w x) * F x := by
        have hfun : (fun x : Space => ∑ i : Fin 3,
            fderiv ℝ (fun y => χ y * w y i) x (basisVector i) * F x) =
            (fun x : Space => fderiv ℝ χ x (w x) * F x) := by
          funext x
          have hsum : ∑ i : Fin 3,
              fderiv ℝ (fun y => χ y * w y i) x (basisVector i) * F x =
              (χ x * staticDivergence w x + fderiv ℝ χ x (w x)) * F x := by
            rw [show ∑ i : Fin 3,
                fderiv ℝ (fun y => χ y * w y i) x (basisVector i) * F x =
                (∑ i : Fin 3,
                  fderiv ℝ (fun y => χ y * w y i) x (basisVector i)) * F x from
              (Finset.sum_mul _ _ _).symm]
            congr 1
            rw [Finset.sum_congr rfl fun i _ => hprod i x,
              Finset.sum_add_distrib, ← Finset.mul_sum, staticDivergence,
              fderiv_apply_eq_sum_basis x (w x)]
          rw [hsum, hdiv x]
          ring
        rw [hfun]

/-- **Laplacian integration by parts against the cutoff**:
`∫ χ ΔF = ∫ (Δχ) F`, by two directional IBPs per coordinate. -/
theorem integral_cutoff_laplacian_ibp
    {χ F : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    (hF : ContDiff ℝ ∞ F) :
    ∫ x : Space, χ x * (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ F z (basisVector i)) x (basisVector i)) =
      ∫ x : Space, (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i))
        * F x := by
  have hstep : ∀ i : Fin 3,
      ∫ x : Space, χ x * fderiv ℝ (fun z => fderiv ℝ F z (basisVector i)) x
        (basisVector i) =
      ∫ x : Space, fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x
        (basisVector i) * F x := by
    intro i
    have h1 := integral_cutoff_directional_ibp hχ hχsupp
      (contDiff_fderiv_apply hF (basisVector i)) (basisVector i)
    have h2 := integral_cutoff_directional_ibp
      (contDiff_fderiv_apply hχ (basisVector i))
      (hasCompactSupport_fderiv_apply hχsupp (basisVector i)) hF (basisVector i)
    rw [h1, h2, neg_neg]
  have hint1 : ∀ i : Fin 3, Integrable (fun x : Space =>
      χ x * fderiv ℝ (fun z => fderiv ℝ F z (basisVector i)) x
        (basisVector i)) :=
    fun i => (hχ.continuous.mul (contDiff_fderiv_apply
      (contDiff_fderiv_apply hF (basisVector i)) (basisVector i)
      ).continuous).integrable_of_hasCompactSupport hχsupp.mul_right
  have hint2 : ∀ i : Fin 3, Integrable (fun x : Space =>
      fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i)
        * F x) :=
    fun i => ((contDiff_fderiv_apply (contDiff_fderiv_apply hχ (basisVector i))
      (basisVector i)).continuous.mul hF.continuous
      ).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply
        (hasCompactSupport_fderiv_apply hχsupp (basisVector i))
        (basisVector i)).mul_right)
  calc ∫ x : Space, χ x * (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ F z (basisVector i)) x (basisVector i))
      = ∫ x : Space, ∑ i : Fin 3, χ x *
          fderiv ℝ (fun z => fderiv ℝ F z (basisVector i)) x (basisVector i) := by
        congr 1
        funext x
        rw [Finset.mul_sum]
    _ = ∑ i : Fin 3, ∫ x : Space, χ x *
          fderiv ℝ (fun z => fderiv ℝ F z (basisVector i)) x (basisVector i) :=
        integral_finsetSum _ fun i _ => hint1 i
    _ = ∑ i : Fin 3, ∫ x : Space,
          fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i)
            * F x :=
        Finset.sum_congr rfl fun i _ => hstep i
    _ = ∫ x : Space, ∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i)
            * F x :=
        (integral_finsetSum _ fun i _ => hint2 i).symm
    _ = ∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x (basisVector i))
            * F x := by
        congr 1
        funext x
        rw [Finset.sum_mul]

/-!
## The capstone: cutoff enstrophy rate in integrated-by-parts form
-/

/-- **Cutoff enstrophy rate, integrated by parts** (ladder rung 6, integral
layer, parts (a)+(b) composed).  Along a classical solution satisfying the
Pattern-A domination hypothesis, for every smooth compactly supported cutoff
`χ` and interior time `t₀ ∈ (0,T)`:

  `E_χ'(t₀) = ∫ χ·2⟨ω,(ω·∇)u⟩ + ∫ (u·∇χ)|ω|² + ν∫ (Δχ)|ω|² − 2ν∫ χ|∇ω|²`.

The transport term of the balance has become the `∇χ` remainder (by
incompressibility) and the viscous term the `Δχ` remainder; the boundary
terms vanished with the compact support.  The `R → ∞` limit of this identity
along `χ_R = χ(·/R)` is the named part-(c) residual feeding
`enstrophyDifferentialInequality`. -/
theorem cutoffEnstrophy_hasDerivAt_ibp
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    {T : ℝ} (hdom : LocallyDominatedEnstrophy u T)
    {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχsupp : HasCompactSupport χ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo 0 T) :
    HasDerivAt (cutoffEnstrophy χ u)
      ((∫ x : Space, χ x * (2 * officialInner (vorticity u t₀ x)
          (spatialDerivative u t₀ x (vorticity u t₀ x))))
        + (∫ x : Space, fderiv ℝ χ x (u t₀ x) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2)
        + ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x
              (basisVector i)) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2)
        - 2 * ν * (∫ x : Space, χ x * (∑ i : Fin 3,
            officialEuclideanNorm
              (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2))) t₀ := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : Space, |χ x| ≤ C := by
    obtain ⟨x₀, hx₀⟩ :=
      hχ.continuous.abs.exists_forall_ge_of_hasCompactSupport hχsupp.abs
    exact ⟨|χ x₀|, hx₀⟩
  have h := cutoffEnstrophy_hasDerivAt_balance hsol hdom hχ.continuous hC ht₀
  -- slice smoothness and continuity inputs
  have huAll : ContDiff ℝ ∞ (u t₀) := contDiff_iff_contDiffAt.mpr fun y =>
    VorticityTransport.contDiffAt_spatial_slice hsol.velocity_smooth
      ht₀.1.le y
  have hωC : ContDiff ℝ ∞ (vorticity u t₀) := vorticity_contDiff hsol ht₀.1.le
  have hFsq : ContDiff ℝ ∞
      (fun y => officialEuclideanNorm (vorticity u t₀ y) ^ 2) :=
    contDiff_officialNormSq_comp hωC
  have hdivfree : ∀ x : Space, staticDivergence (u t₀) x = 0 := fun x =>
    hsol.incompressible t₀ ht₀.1.le x
  -- integrability of the four balance pieces against the cutoff
  have iA : Integrable (fun x : Space =>
      χ x * (2 * officialInner (vorticity u t₀ x)
        (spatialDerivative u t₀ x (vorticity u t₀ x)))) :=
    (hχ.continuous.mul (continuous_const.mul (continuous_officialInner_comp
      hωC.continuous ((huAll.continuous_fderiv (by norm_num)).clm_apply
        hωC.continuous)))).integrable_of_hasCompactSupport hχsupp.mul_right
  have iB : Integrable (fun x : Space =>
      χ x * fderiv ℝ (fun y =>
        officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x)) :=
    (hχ.continuous.mul ((hFsq.continuous_fderiv (by norm_num)).clm_apply
      huAll.continuous)).integrable_of_hasCompactSupport hχsupp.mul_right
  have iC : Integrable (fun x : Space =>
      χ x * (∑ i : Fin 3, fderiv ℝ (fun z =>
        fderiv ℝ (fun y => officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
          (basisVector i)) x (basisVector i))) :=
    (hχ.continuous.mul (continuous_finsetSum _ fun i _ =>
      (contDiff_fderiv_apply (contDiff_fderiv_apply hFsq (basisVector i))
        (basisVector i)).continuous)).integrable_of_hasCompactSupport
      hχsupp.mul_right
  have iD : Integrable (fun x : Space =>
      χ x * (∑ i : Fin 3, officialEuclideanNorm
        (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2)) :=
    (hχ.continuous.mul (continuous_finsetSum _ fun i _ =>
      continuous_officialNormSq_comp
        (((hωC.fderiv_right (m := ∞) (by norm_num)).clm_apply
          contDiff_const).continuous))).integrable_of_hasCompactSupport
      hχsupp.mul_right
  -- split the balance integral into the four pieces
  have hsplit : (∫ x : Space, χ x *
      (2 * officialInner (vorticity u t₀ x)
          (spatialDerivative u t₀ x (vorticity u t₀ x))
        - fderiv ℝ (fun y =>
            officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x)
        + ν * (∑ i : Fin 3,
            fderiv ℝ (fun z =>
              fderiv ℝ (fun y =>
                officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
                (basisVector i)) x (basisVector i))
        - 2 * ν * (∑ i : Fin 3,
            officialEuclideanNorm
              (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2))) =
      (∫ x : Space, χ x * (2 * officialInner (vorticity u t₀ x)
          (spatialDerivative u t₀ x (vorticity u t₀ x))))
        - (∫ x : Space, χ x * fderiv ℝ (fun y =>
            officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x))
        + ν * (∫ x : Space, χ x * (∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ (fun y =>
              officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
              (basisVector i)) x (basisVector i)))
        - 2 * ν * (∫ x : Space, χ x * (∑ i : Fin 3,
            officialEuclideanNorm
              (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2)) := by
    have hpt : (fun x : Space => χ x *
        (2 * officialInner (vorticity u t₀ x)
            (spatialDerivative u t₀ x (vorticity u t₀ x))
          - fderiv ℝ (fun y =>
              officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x)
          + ν * (∑ i : Fin 3,
              fderiv ℝ (fun z =>
                fderiv ℝ (fun y =>
                  officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
                  (basisVector i)) x (basisVector i))
          - 2 * ν * (∑ i : Fin 3,
              officialEuclideanNorm
                (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2))) =
        (fun x : Space =>
          ((χ x * (2 * officialInner (vorticity u t₀ x)
              (spatialDerivative u t₀ x (vorticity u t₀ x)))
            - χ x * fderiv ℝ (fun y =>
                officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x))
            + ν * (χ x * (∑ i : Fin 3,
                fderiv ℝ (fun z => fderiv ℝ (fun y =>
                  officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
                  (basisVector i)) x (basisVector i))))
            - 2 * ν * (χ x * (∑ i : Fin 3,
                officialEuclideanNorm
                  (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2))) := by
      funext x
      ring
    have iAB : Integrable (fun x : Space =>
        χ x * (2 * officialInner (vorticity u t₀ x)
          (spatialDerivative u t₀ x (vorticity u t₀ x)))
        - χ x * fderiv ℝ (fun y =>
            officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x)) :=
      iA.sub iB
    have iC' : Integrable (fun x : Space => ν * (χ x * (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun y =>
          officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
          (basisVector i)) x (basisVector i)))) := iC.const_mul ν
    have iD' : Integrable (fun x : Space => 2 * ν * (χ x * (∑ i : Fin 3,
        officialEuclideanNorm
          (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2))) :=
      iD.const_mul (2 * ν)
    have iABC : Integrable (fun x : Space =>
        (χ x * (2 * officialInner (vorticity u t₀ x)
            (spatialDerivative u t₀ x (vorticity u t₀ x)))
          - χ x * fderiv ℝ (fun y =>
              officialEuclideanNorm (vorticity u t₀ y) ^ 2) x (u t₀ x))
        + ν * (χ x * (∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ (fun y =>
              officialEuclideanNorm (vorticity u t₀ y) ^ 2) z
              (basisVector i)) x (basisVector i)))) := iAB.add iC'
    rw [hpt, integral_sub iABC iD', integral_add iAB iC', integral_sub iA iB,
      integral_const_mul, integral_const_mul]
  -- integrate the transport and viscous terms by parts
  have hT := integral_cutoff_transport_ibp hχ hχsupp hFsq huAll hdivfree
  have hL := integral_cutoff_laplacian_ibp hχ hχsupp hFsq
  rw [hsplit, hT, hL] at h
  have hfinal : (∫ x : Space, χ x * (2 * officialInner (vorticity u t₀ x)
        (spatialDerivative u t₀ x (vorticity u t₀ x))))
      - (- ∫ x : Space, fderiv ℝ χ x (u t₀ x) *
          officialEuclideanNorm (vorticity u t₀ x) ^ 2)
      + ν * (∫ x : Space, (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x
            (basisVector i)) *
          officialEuclideanNorm (vorticity u t₀ x) ^ 2)
      - 2 * ν * (∫ x : Space, χ x * (∑ i : Fin 3,
          officialEuclideanNorm
            (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2)) =
      (∫ x : Space, χ x * (2 * officialInner (vorticity u t₀ x)
          (spatialDerivative u t₀ x (vorticity u t₀ x))))
        + (∫ x : Space, fderiv ℝ χ x (u t₀ x) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2)
        + ν * (∫ x : Space, (∑ i : Fin 3,
            fderiv ℝ (fun z => fderiv ℝ χ z (basisVector i)) x
              (basisVector i)) *
            officialEuclideanNorm (vorticity u t₀ x) ^ 2)
        - 2 * ν * (∫ x : Space, χ x * (∑ i : Fin 3,
            officialEuclideanNorm
              (fderiv ℝ (vorticity u t₀) x (basisVector i)) ^ 2)) := by
    ring
  rw [hfinal] at h
  exact h

end Navier.Analysis.CutoffIntegrationByParts
