import Navier.Analysis.VorticityTransport

/-!
# The convection–curl identity: `curl((u·∇)u) = (u·∇)ω − (ω·∇)u`

This file derives the convection–curl identity — the single residual named by
`vorticityTransport_eq_partial_and_convection_curl` for the full
Majda–Bertozzi (1.33) vorticity transport PDE.  For a `C^∞` velocity slice
`w` with `staticDivergence w x = 0`,

  `curl((w·∇)w)(x) = (D(curl w) x)(w x) − (Dw x)(curl w x)`,

i.e. `curl((w·∇)w) = (w·∇)ω − (ω·∇)w` at `x` with `ω = curl w`.

The derivation splits into
1. the bilinear product rule `fderiv_convection_slice` for
   `y ↦ (Dw y)(w y)` (Mathlib's `fderiv_clm_apply`);
2. the second-derivative symmetry `IsSymmSndFDerivAt` (Clairaut), turning the
   `∑ i, eᵢ ⨯₃ (D²w x eᵢ)(w x)` half into the transport term `(w·∇)ω`; and
3. the **gradient-square cross identity** `cross_matrix_identity`, a pure
   finite algebraic identity valid for arbitrary `3 × 3` data:
   `∑ i, eᵢ ⨯₃ A(A eᵢ) = (tr A) • ω_A − A ω_A` with `ω_A = ∑ i, eᵢ ⨯₃ A eᵢ`;
   under `tr A = div w = 0` it yields the stretching term `−(ω·∇)w`.

Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §1.3;
the identity is the standard `∇×((u·∇)u) = (u·∇)ω − (ω·∇)u + ω(∇·u)`
specialized to divergence-free fields.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix ContDiff

namespace Navier.Analysis.ConvectionCurl

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.VorticityTransport

/-!
## Pure algebra: matrix expansion and the gradient-square cross identity
-/

/-- Matrix-entry expansion of a continuous linear map on `ℝ³`: the image of
`v` is the entry-weighted sum of the images of the basis vectors. -/
theorem clm_apply_eq_sum (A : Space →L[ℝ] Space) (v : Space) :
    A v = ∑ j : Fin 3, v j • A (basisVector j) := by
  have hbasis : v = ∑ j : Fin 3, v j • basisVector j := by
    simpa only [basisVector] using (pi_eq_sum_univ' v)
  calc A v = A (∑ j : Fin 3, v j • basisVector j) := congrArg A hbasis
    _ = ∑ j : Fin 3, v j • A (basisVector j) := by simp only [map_sum, map_smul]

/-- **Gradient-square cross identity (pure algebra).**  For arbitrary columns
`a : Fin 3 → Space` (think `a i = A (basisVector i)`),

  `∑ i, eᵢ ⨯₃ (A(A eᵢ)) = (tr A) • ω_A − A ω_A`,  `ω_A = ∑ i, eᵢ ⨯₃ a i`,

with every application of `A` written out as an entry-weighted column sum.
This is the algebraic core `εₖᵢⱼ (∂ᵢuₗ)(∂ₗuⱼ) = ωₖ (div u) − ((ω·∇)u)ₖ` of the
convection–curl identity, valid for every `3 × 3` matrix — no symmetry and no
PDE input.  Verified here by componentwise expansion and `ring`. -/
theorem cross_matrix_identity (a : Fin 3 → Space) :
    ∑ i : Fin 3, basisVector i ⨯₃ (∑ j : Fin 3, a i j • a j) =
      (∑ j : Fin 3, a j j) • (∑ i : Fin 3, basisVector i ⨯₃ a i) -
        ∑ j : Fin 3, (∑ i : Fin 3, basisVector i ⨯₃ a i) j • a j := by
  funext k
  fin_cases k <;>
    simp [cross_apply, basisVector, Finset.sum_apply, Fin.sum_univ_three,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply] <;> ring

/-- The gradient-square cross identity in continuous-linear-map form:
`∑ i, eᵢ ⨯₃ A(A eᵢ) = (∑ j, (A eⱼ)ⱼ) • ω_A − A ω_A` for any
`A : ℝ³ →L[ℝ] ℝ³`, where `ω_A = ∑ i, eᵢ ⨯₃ A eᵢ`. -/
theorem sum_cross_comp_self (A : Space →L[ℝ] Space) :
    ∑ i : Fin 3, basisVector i ⨯₃ A (A (basisVector i)) =
      (∑ j : Fin 3, A (basisVector j) j) •
          (∑ i : Fin 3, basisVector i ⨯₃ A (basisVector i)) -
        A (∑ i : Fin 3, basisVector i ⨯₃ A (basisVector i)) := by
  have hexp : ∑ i : Fin 3, basisVector i ⨯₃ A (A (basisVector i)) =
      ∑ i : Fin 3, basisVector i ⨯₃
        (∑ j : Fin 3, (A (basisVector i)) j • A (basisVector j)) :=
    Finset.sum_congr rfl fun i _ => by
      rw [← clm_apply_eq_sum A (A (basisVector i))]
  rw [hexp, cross_matrix_identity (fun i => A (basisVector i)),
    ← clm_apply_eq_sum A (∑ i : Fin 3, basisVector i ⨯₃ A (basisVector i))]

/-!
## Analytic bridges (local copies of the `CurlIdentities` private lemmas)
-/

/-- Eval-CLM bridge: the derivative of `y ↦ (Dw y) a` at `x` in direction `h`
is the second Fréchet derivative applied to `h` then `a`. -/
private theorem eval_deriv_bridge (w : VelocityField) (x : Space)
    (a h : Space) (hw : DifferentiableAt ℝ (fderiv ℝ w) x) :
    fderiv ℝ (fun y => fderiv ℝ w y a) x h =
      (fderiv ℝ (fderiv ℝ w) x h) a := by
  let T : (Space →L[ℝ] Space) →L[ℝ] Space := ContinuousLinearMap.apply ℝ Space a
  have hcomp := (HasFDerivAt.comp x T.hasFDerivAt hw.hasFDerivAt).fderiv
  change (fderiv ℝ (⇑T ∘ fderiv ℝ w) x) h = ((fderiv ℝ (fderiv ℝ w) x) h) a
  rw [hcomp]
  rfl

/-- Each cross-product summand of `staticCurl w` is differentiable at `x`
when `fderiv ℝ w` is. -/
private theorem cross_summand_differentiable (w : VelocityField) (x : Space)
    (i : Fin 3) (hw : DifferentiableAt ℝ (fderiv ℝ w) x) :
    DifferentiableAt ℝ
      (fun y => basisVector i ⨯₃ fderiv ℝ w y (basisVector i)) x := by
  let L : Space →ₗ[ℝ] Space := crossProduct (basisVector i)
  have hdg : DifferentiableAt ℝ (fun y => fderiv ℝ w y (basisVector i)) x := by
    have heq : (fun y => fderiv ℝ w y (basisVector i)) =
        (ContinuousLinearMap.apply ℝ Space (basisVector i) ∘ fderiv ℝ w) := rfl
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ Space
      (basisVector i)).differentiableAt.comp x hw
  have heq : (fun y => basisVector i ⨯₃ fderiv ℝ w y (basisVector i)) =
      (L.toContinuousLinearMap ∘ (fun y => fderiv ℝ w y (basisVector i))) := rfl
  rw [heq]
  exact L.toContinuousLinearMap.differentiableAt.comp x hdg

/-- Chain-rule bridge: the derivative of the `i`-th cross-product summand of
`staticCurl` in direction `h` factors through the second derivative. -/
private theorem cross_summand_fderiv (w : VelocityField) (x h : Space)
    (i : Fin 3) (hw : DifferentiableAt ℝ (fderiv ℝ w) x) :
    fderiv ℝ (fun y => basisVector i ⨯₃ fderiv ℝ w y (basisVector i)) x h =
      basisVector i ⨯₃ ((fderiv ℝ (fderiv ℝ w) x h) (basisVector i)) := by
  let L : Space →ₗ[ℝ] Space := crossProduct (basisVector i)
  have hg : fderiv ℝ (fun y => fderiv ℝ w y (basisVector i)) x h =
      (fderiv ℝ (fderiv ℝ w) x h) (basisVector i) :=
    eval_deriv_bridge w x (basisVector i) h hw
  have hdg : DifferentiableAt ℝ (fun y => fderiv ℝ w y (basisVector i)) x := by
    have heq : (fun y => fderiv ℝ w y (basisVector i)) =
        (ContinuousLinearMap.apply ℝ Space (basisVector i) ∘ fderiv ℝ w) := rfl
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ Space
      (basisVector i)).differentiableAt.comp x hw
  have hL : HasFDerivAt (fun v => L v) L.toContinuousLinearMap
      (fderiv ℝ w x (basisVector i)) := L.toContinuousLinearMap.hasFDerivAt
  have hcomp := (HasFDerivAt.comp x hL hdg.hasFDerivAt).fderiv
  change (fderiv ℝ ((fun v => L v) ∘
    (fun y => fderiv ℝ w y (basisVector i))) x) h = _
  rw [hcomp]
  change L ((fderiv ℝ (fun y => fderiv ℝ w y (basisVector i)) x) h) = _
  rw [hg]

/-- The derivative of the static curl in direction `h`, expanded through the
second Fréchet derivative: `(D(curl w) x)(h) = ∑ i, eᵢ ⨯₃ (D²w x h)(eᵢ)`. -/
theorem fderiv_staticCurl_apply (w : VelocityField) (x h : Space)
    (hw : DifferentiableAt ℝ (fderiv ℝ w) x) :
    fderiv ℝ (fun y => staticCurl w y) x h =
      ∑ i : Fin 3, basisVector i ⨯₃
        ((fderiv ℝ (fderiv ℝ w) x h) (basisVector i)) := by
  have hsum : (fun y => staticCurl w y) = ∑ i : Fin 3,
      (fun y => basisVector i ⨯₃ fderiv ℝ w y (basisVector i)) := by
    funext y
    simp only [staticCurl, Finset.sum_apply]
  rw [hsum, fderiv_sum fun i _ => cross_summand_differentiable w x i hw]
  rw [sum_apply]
  exact Finset.sum_congr rfl fun i _ => cross_summand_fderiv w x h i hw

/-!
## The product rule for the convection slice
-/

/-- **Bilinear product rule for the convection field.**  The derivative of
`y ↦ (Dw y)(w y)` in direction `h` is `(D²w x h)(w x) + (Dw x)((Dw x) h)`. -/
theorem fderiv_convection_slice (w : VelocityField) (x h : Space)
    (hw1 : DifferentiableAt ℝ w x)
    (hw2 : DifferentiableAt ℝ (fderiv ℝ w) x) :
    fderiv ℝ (fun y => fderiv ℝ w y (w y)) x h =
      (fderiv ℝ (fderiv ℝ w) x h) (w x) +
        fderiv ℝ w x (fderiv ℝ w x h) := by
  have hprod := fderiv_clm_apply hw2 hw1
  rw [show (fun y => fderiv ℝ w y (w y)) =
      (fun y => (fderiv ℝ w y) (w y)) from rfl, hprod]
  simp only [add_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.flip_apply]
  exact add_comm _ _

/-!
## The convection–curl identity
-/

/-- **Convection–curl identity (static form).**  For a `C^∞`-at-`x` velocity
field with vanishing divergence at `x`,

  `curl((w·∇)w)(x) = (D(curl w) x)(w x) − (Dw x)(curl w x)`,

i.e. `curl((w·∇)w) = (w·∇)ω − (ω·∇)w` at `x`.  Product rule + Clairaut
(second-derivative symmetry) + the gradient-square cross identity with
`tr = div w x = 0`. -/
theorem staticCurl_convection_eq (w : VelocityField) (x : Space)
    (hw : ContDiffAt ℝ ∞ w x) (hdiv : staticDivergence w x = 0) :
    staticCurl (fun y => fderiv ℝ w y (w y)) x =
      fderiv ℝ (fun y => staticCurl w y) x (w x) -
        fderiv ℝ w x (staticCurl w x) := by
  have hw1 : DifferentiableAt ℝ w x := hw.differentiableAt (by decide)
  have hwfd : ContDiffAt ℝ ∞ (fderiv ℝ w) x := hw.fderiv_right (by simp)
  have hw2 : DifferentiableAt ℝ (fderiv ℝ w) x :=
    hwfd.differentiableAt (by decide)
  have hsymm : IsSymmSndFDerivAt ℝ w x :=
    hw.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
  -- Expand the curl of the convection field through the product rule.
  have hexpand : staticCurl (fun y => fderiv ℝ w y (w y)) x =
      (∑ i : Fin 3, basisVector i ⨯₃
        ((fderiv ℝ (fderiv ℝ w) x (basisVector i)) (w x))) +
      (∑ i : Fin 3, basisVector i ⨯₃
        (fderiv ℝ w x (fderiv ℝ w x (basisVector i)))) := by
    rw [show staticCurl (fun y => fderiv ℝ w y (w y)) x =
        ∑ i : Fin 3, basisVector i ⨯₃
          (fderiv ℝ (fun y => fderiv ℝ w y (w y)) x (basisVector i)) from rfl]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [fderiv_convection_slice w x (basisVector i) hw1 hw2, map_add]
  -- Transport half: Clairaut swaps the derivative slots, giving `(w·∇)ω`.
  have htransport : ∑ i : Fin 3, basisVector i ⨯₃
      ((fderiv ℝ (fderiv ℝ w) x (basisVector i)) (w x)) =
      fderiv ℝ (fun y => staticCurl w y) x (w x) := by
    rw [fderiv_staticCurl_apply w x (w x) hw2]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hsymm (basisVector i) (w x)]
  -- Stretching half: the gradient-square identity with vanishing trace.
  have hstretch : ∑ i : Fin 3, basisVector i ⨯₃
      (fderiv ℝ w x (fderiv ℝ w x (basisVector i))) =
      - fderiv ℝ w x (staticCurl w x) := by
    have halg := sum_cross_comp_self (fderiv ℝ w x)
    have htr : ∑ j : Fin 3, fderiv ℝ w x (basisVector j) j = 0 := hdiv
    have hω : ∑ i : Fin 3, basisVector i ⨯₃ fderiv ℝ w x (basisVector i) =
        staticCurl w x := rfl
    rw [htr, hω] at halg
    rw [show (∑ i : Fin 3, basisVector i ⨯₃
        (fderiv ℝ w x (fderiv ℝ w x (basisVector i)))) =
        (∑ i : Fin 3, basisVector i ⨯₃
          (fderiv ℝ w x) ((fderiv ℝ w x) (basisVector i))) from rfl, halg]
    rw [zero_smul, zero_sub]
  rw [hexpand, htransport, hstretch]
  exact (sub_eq_add_neg _ _).symm

/-- **Convection–curl identity (evolution form).**  Along a classical
solution, at every nonnegative time and every point,

  `curl((u·∇)u) = (u·∇)ω − (ω·∇)u`,

stated exactly in the shape consumed by
`vorticityTransport_eq_partial_and_convection_curl`. -/
theorem staticCurl_convection_evolution
    {ν : ℝ} {u₀ : SchwartzVelocity} {u : VelocityEvolution}
    {p : PressureEvolution}
    (hsol : IsClassicalSolution ν zeroForce u₀ u p)
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    staticCurl (fun y => convection u t y) x =
      spatialDerivative (fun s => vorticity u s) t x (u t x) -
        spatialDerivative u t x (vorticity u t x) := by
  have huA : ContDiffAt ℝ ∞ (u t) x :=
    contDiffAt_spatial_slice hsol.velocity_smooth ht x
  have hdiv : staticDivergence (u t) x = 0 := hsol.incompressible t ht x
  exact staticCurl_convection_eq (u t) x huA hdiv

end Navier.Analysis.ConvectionCurl
