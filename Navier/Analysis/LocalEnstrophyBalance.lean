import Navier.Analysis.Enstrophy
import Navier.Analysis.EnstrophyPointwise

/-!
# The pointwise local enstrophy balance (integrand of `E_R'`)

Along a classical solution, at every nonnegative time and point,

  `2⟨ω, ∂ₜω⟩ = 2⟨ω, (ω·∇)u⟩ − (u·∇)|ω|² + ν Δ(|ω|²) − 2ν|∇ω|²`,

where `|∇ω|² = ∑ᵢ|∂ᵢω|²` and `Δ(|ω|²)`, `(u·∇)|ω|²` are the repository's
coordinate scalar Laplacian and directional derivative of the enstrophy
density `|ω|²`.  This is the pointwise integrand of the cutoff enstrophy rate

  `E_R'(t) = ∫ χ_R · ∂ₜ(|ω|²) = ∫ χ_R (2⟨ω,(ω·∇)u⟩ − (u·∇)|ω|² + νΔ|ω|² − 2ν|∇ω|²)`

after multiplying by a cutoff and integrating.  It composes three established
facts and no measure theory:
* the vorticity transport equation `vorticityTransportEquation`
  (`∂ₜω = (ω·∇)u + νΔω − (u·∇)ω`);
* the transport-integrand identity `fderiv_normSq_apply`
  (`(u·∇)|ω|² = 2⟨ω,(u·∇)ω⟩`);
* the pointwise Bochner identity `scalarLaplacian_normSq`
  (`Δ|ω|² = 2⟨ω,Δω⟩ + 2|∇ω|²`).

Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §3.3.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix ContDiff

namespace Navier.Analysis.LocalEnstrophyBalance

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Enstrophy
open Navier.Analysis.EnstrophyPointwise

/-!
## Smoothness of the vorticity field along a classical solution
-/

/-- The curl of a globally `C^∞` velocity field is globally `C^∞`. -/
theorem staticCurl_contDiff (w : VelocityField) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (staticCurl w) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ w) := hw.fderiv_right (by simp)
  rw [show staticCurl w = fun x => ∑ i : Fin 3,
      (crossProduct (basisVector i)) (fderiv ℝ w x (basisVector i)) from rfl]
  apply ContDiff.sum
  intro i _
  exact (crossProduct (basisVector i)).toContinuousLinearMap.contDiff.comp
    (hfd.clm_apply contDiff_const)

/-- Along a classical solution the vorticity time-slice is globally `C^∞`. -/
theorem vorticity_contDiff
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (vorticity u t) := by
  have huAll : ContDiff ℝ ∞ (u t) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      VorticityTransport.contDiffAt_spatial_slice hsol.velocity_smooth ht y
  exact staticCurl_contDiff (u t) huAll

/-!
## Inner-product linearity in the second argument (coordinate form)
-/

theorem officialInner_add_right (a b c : Space) :
    officialInner a (b + c) = officialInner a b + officialInner a c := by
  simp only [officialInner_eq_sum, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

theorem officialInner_sub_right (a b c : Space) :
    officialInner a (b - c) = officialInner a b - officialInner a c := by
  simp only [officialInner_eq_sum, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

theorem officialInner_smul_right (r : ℝ) (a b : Space) :
    officialInner a (r • b) = r * officialInner a b := by
  simp only [officialInner_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-!
## The local enstrophy balance
-/

/-- **Pointwise local enstrophy balance.**  Along a classical solution, at
every nonnegative time and point,

  `2⟨ω, ∂ₜω⟩ = 2⟨ω, (ω·∇)u⟩ − (u·∇)|ω|² + ν Δ(|ω|²) − 2ν|∇ω|²`.

The left side is `2⟨ω, ∂ₜω⟩` with `∂ₜω = timeDerivative (fun s => vorticity u s)`.
The right side is the integrand of the cutoff enstrophy rate: stretching
production, the transport term written as `(u·∇)|ω|²` (a divergence after
`div u = 0`, killed by the cutoff at `R → ∞`), the viscous term written as
`ν Δ|ω|²` (a divergence), and the dissipative gradient square `−2ν|∇ω|²`
(sign-definite).  Established from the transport equation, the transport
integrand identity, and the pointwise Bochner identity. -/
theorem local_enstrophy_balance
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) {t : ℝ} (ht : 0 ≤ t)
    (x : Space) :
    2 * officialInner (vorticity u t x)
        (timeDerivative (fun s => vorticity u s) t x) =
      2 * officialInner (vorticity u t x)
          (spatialDerivative u t x (vorticity u t x))
      - fderiv ℝ (fun y => officialEuclideanNorm (vorticity u t y) ^ 2) x (u t x)
      + ν * (∑ i : Fin 3,
          fderiv ℝ (fun z =>
            fderiv ℝ (fun y => officialEuclideanNorm (vorticity u t y) ^ 2) z
              (basisVector i)) x (basisVector i))
      - 2 * ν * (∑ i : Fin 3,
          officialEuclideanNorm (fderiv ℝ (vorticity u t) x (basisVector i)) ^ 2) := by
  -- Smoothness/differentiability of the vorticity slice
  have hCD : ContDiff ℝ ∞ (vorticity u t) := vorticity_contDiff hsol ht
  have hdiffAll : ∀ y : Space, DifferentiableAt ℝ (vorticity u t) y :=
    fun y => (hCD.differentiable (by norm_num)).differentiableAt
  have hdiff2 : DifferentiableAt ℝ (fderiv ℝ (vorticity u t)) x :=
    ((hCD.fderiv_right (m := ∞) (by norm_num)).differentiable
      (by norm_num)).differentiableAt
  -- Transport equation solved for ∂ₜω:  ∂ₜω = (ω·∇)u + νΔω − (u·∇)ω
  have hpde := Enstrophy.vorticityTransportEquation hsol t ht x
  have hT : timeDerivative (fun s => vorticity u s) t x =
      spatialDerivative u t x (vorticity u t x)
        + ν • laplacian (fun s => vorticity u s) t x
        - spatialDerivative (fun s => vorticity u s) t x (u t x) :=
    eq_sub_of_add_eq hpde
  -- Convection direction as an fderiv; transport integrand identity
  have hconv : spatialDerivative (fun s => vorticity u s) t x (u t x) =
      fderiv ℝ (vorticity u t) x (u t x) := rfl
  have htransport :
      fderiv ℝ (fun y => officialEuclideanNorm (vorticity u t y) ^ 2) x (u t x) =
      2 * officialInner (vorticity u t x) (fderiv ℝ (vorticity u t) x (u t x)) :=
    fderiv_normSq_apply (vorticity u t) x (u t x) (hdiffAll x)
  -- The vector laplacian in the transport eq matches the Bochner inner sum
  have hLapEq : laplacian (fun s => vorticity u s) t x =
      ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (vorticity u t) z (basisVector i)) x
          (basisVector i) := rfl
  -- Pointwise Bochner:  Δ|ω|² = 2⟨ω,Δω⟩ + 2|∇ω|²
  have hbochner := scalarLaplacian_normSq (vorticity u t) x hdiffAll hdiff2
  -- Expand the LHS by inner linearity and substitute the pieces
  rw [hT, officialInner_sub_right, officialInner_add_right,
    officialInner_smul_right, hconv, hLapEq, htransport]
  -- Everything is now scalar; close with the Bochner identity
  linear_combination -ν * hbochner

/-!
## The pointwise enstrophy differential-inequality integrand
-/

/-- **Pointwise enstrophy differential inequality (integrand form).**  Along a
classical solution with `0 ≤ ν`, at a point where the stretching deformation
`(ω·∇)u` is dominated by `G·|ω|` in official coordinates,

  `2⟨ω, ∂ₜω⟩ ≤ 2G|ω|² − (u·∇)|ω|² + ν Δ(|ω|²)`.

Obtained from `local_enstrophy_balance` by bounding the stretching production
`2⟨ω,(ω·∇)u⟩ ≤ 2G|ω|²` (`stretching_pointwise_bound`) and dropping the
sign-definite dissipation `−2ν|∇ω|² ≤ 0`.  This is the pointwise integrand
whose cutoff integral gives the enstrophy differential inequality
`E' ≤ 2G·E`: the transport term `(u·∇)|ω|²` is a divergence killed by the
cutoff at `R → ∞`, and `∫ χ_R Δ(|ω|²) = ∫ (Δχ_R)|ω|² → 0`.  The remaining
integral layer (differentiation under the integral over `χ_R` and the
`R → ∞` interchange) is the named residual of
`Navier.Analysis.Enstrophy.enstrophyDifferentialInequality`; it requires a
local-uniform-in-time domination hypothesis (a Pattern-A strengthening
automatic for `H^m`/Schwartz-regular solutions but not carried by
`IsClassicalSolution`). -/
theorem pointwise_enstrophy_differential_inequality
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p) {t : ℝ} (ht : 0 ≤ t)
    (x : Space) {G : ℝ} (hν : 0 ≤ ν)
    (hG : officialEuclideanNorm (spatialDerivative u t x (vorticity u t x)) ≤
      G * officialEuclideanNorm (vorticity u t x)) :
    2 * officialInner (vorticity u t x)
        (timeDerivative (fun s => vorticity u s) t x) ≤
      2 * G * officialEuclideanNorm (vorticity u t x) ^ 2
      - fderiv ℝ (fun y => officialEuclideanNorm (vorticity u t y) ^ 2) x (u t x)
      + ν * (∑ i : Fin 3,
          fderiv ℝ (fun z =>
            fderiv ℝ (fun y => officialEuclideanNorm (vorticity u t y) ^ 2) z
              (basisVector i)) x (basisVector i)) := by
  have hbal := local_enstrophy_balance hsol ht x
  have hstretch : officialInner (vorticity u t x)
      (spatialDerivative u t x (vorticity u t x)) ≤
      G * officialEuclideanNorm (vorticity u t x) ^ 2 :=
    stretching_pointwise_bound (vorticity u t x)
      (spatialDerivative u t x (vorticity u t x)) hG
  have hgrad : 0 ≤ ∑ i : Fin 3,
      officialEuclideanNorm (fderiv ℝ (vorticity u t) x (basisVector i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hbal]
  nlinarith [hstretch, hgrad, hν, mul_nonneg hν hgrad]

end Navier.Analysis.LocalEnstrophyBalance
