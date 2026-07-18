import Navier.Analysis.Vorticity
import Navier.Analysis.VectorCalculus
import Navier.Analysis.OfficialABEncoding
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The four curl identities for the BKM assembly line

This file establishes the four vector-calculus identities that the
Beale–Kato–Majda vorticity-transport assembly chain uses as link #2:

1. `staticCurl_staticGradient_eq_zero` — the curl of a gradient vanishes
   (`∇ × (∇f) = 0`).
2. `staticDivergence_staticCurl_eq_zero` — the divergence of a curl vanishes
   (`∇ · (∇ × u) = 0`).
3. `staticCurl_smul` — the scalar-vector product rule for curl
   (`∇ × (f • u) = (∇f) × u + f • (∇ × u)`), used in the Biot–Savart
   vorticity transport step.
4. `staticDivergence_cross` — the cross-product divergence identity
   (`∇ · (u × v) = u · (∇ × v) − v · (∇ × u)`), the scalar triple product
   rearrangement underlying the Biot–Savart energy estimate.

The four identities are stated at a point under `ContDiffAt ℝ 2` hypotheses,
which give the symmetry of mixed second partial derivatives via
`ContDiffAt.isSymmSndFDerivAt`.  The curl, gradient, divergence and cross
product are the repository's coordinate operators from `Navier.Problem` and
`Navier.Analysis.Vorticity`; no new analytic infrastructure is introduced.

These are mechanical coordinate identities, not the singular-integral
estimates (links #6/#8/#9 of the assembly chain) which remain named open
leaves; the singular-integral analysis stays untouched this round.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

namespace Navier.Analysis.CurlIdentities

open Navier
open Navier.Analysis.Vorticity

/-!
## Auxiliary cross-product component lemmas
-/

/-- The cross product of the 0th basis vector with `w` has explicit
components `![0, -w 2, w 1]`. -/
private lemma cross_basisVector_zero (w : Space) :
    basisVector 0 ⨯₃ w = ![0, -(w 2), w 1] := by
  ext k; fin_cases k <;> simp [basisVector, cross_apply]

/-- The cross product of the 1st basis vector with `w` has explicit
components `![w 2, 0, -w 0]`. -/
private lemma cross_basisVector_one (w : Space) :
    basisVector 1 ⨯₃ w = ![w 2, 0, -(w 0)] := by
  ext k; fin_cases k <;> simp [basisVector, cross_apply]

/-- The cross product of the 2nd basis vector with `w` has explicit
components `![-w 1, w 0, 0]`. -/
private lemma cross_basisVector_two (w : Space) :
    basisVector 2 ⨯₃ w = ![-(w 1), w 0, 0] := by
  ext k; fin_cases k <;> simp [basisVector, cross_apply]

/-- **Algebraic core.**  If `w : Fin 3 → Space` is componentwise symmetric
(`w i j = w j i` for all `i j`), then `∑ i, basisVector i ⨯₃ w i = 0`.
This is the antisymmetric-times-symmetric cancellation that underlies
both `curl ∘ grad = 0` and `div ∘ curl = 0`. -/
private lemma curl_symmetric_eq_zero
    (w : Fin 3 → Space) (hsymm : ∀ i j : Fin 3, w i j = w j i) :
    ∑ i : Fin 3, basisVector i ⨯₃ w i = 0 := by
  ext k
  simp only [Finset.sum_apply]
  rw [Fin.sum_univ_three,
    cross_basisVector_zero (w 0),
    cross_basisVector_one (w 1),
    cross_basisVector_two (w 2)]
  fin_cases k
  all_goals simp only [Pi.add_apply, Pi.zero_apply]
  all_goals simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · linarith [hsymm 1 2]
  · linarith [hsymm 2 0]
  · linarith [hsymm 0 1]

/-!
## Coordinate-form symmetry and the `ContDiffAt` bridge
-/

/-- Operative-regime hypothesis: the mixed second partial derivatives of a
scalar field `f` are symmetric at `x`, in coordinate form. -/
def HasSymmetricMixedPartialAt (f : PressureField) (x : Space) : Prop :=
  ∀ (i j : Fin 3),
    fderiv ℝ (fun y => fderiv ℝ f y (basisVector j)) x (basisVector i) =
      fderiv ℝ (fun y => fderiv ℝ f y (basisVector i)) x (basisVector j)

/-- `ContDiffAt ℝ 2` at a point gives symmetric mixed partials in coordinate
form.  Bridge from Mathlib's `IsSymmSndFDerivAt`. -/
theorem ContDiffAt.hasSymmetricMixedPartialAt
    {f : PressureField} {x : Space} (hf : ContDiffAt ℝ 2 f x) :
    HasSymmetricMixedPartialAt f x := by
  have hsymm : IsSymmSndFDerivAt ℝ f x :=
    hf.isSymmSndFDerivAt (by simp [minSmoothness])
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have h2 : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf.fderiv_right le_rfl
    exact h2.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  intro i j
  have hEval : ∀ (v w : Space),
      fderiv ℝ (fun y => fderiv ℝ f y w) x v = (fderiv ℝ (fderiv ℝ f) x v) w := by
    intro v w
    let T : (Space →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ w
    have hT : HasFDerivAt (fun L : Space →L[ℝ] ℝ => L w) T (fderiv ℝ f x) :=
      T.hasFDerivAt
    have hcomp := (hT.comp x hdiff.hasFDerivAt).fderiv
    rw [show (fun y => fderiv ℝ f y w) = (fun L => L w) ∘ (fderiv ℝ f) from rfl, hcomp]
    rfl
  rw [hEval, hEval]
  exact hsymm _ _

/-- `DifferentiableAt (fderiv f) x` gives `DifferentiableAt` of each
coordinate component `(fun y => fderiv f y (basisVector j))` at `x`. -/
private theorem DifferentiableAt.fderiv_component
    {f : PressureField} {x : Space} (hf : DifferentiableAt ℝ (fderiv ℝ f) x)
    (j : Fin 3) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f y (basisVector j)) x := by
  have : (fun y => fderiv ℝ f y (basisVector j)) =
    ((ContinuousLinearMap.apply ℝ ℝ (basisVector j) :
      (Space →L[ℝ] ℝ) →L[ℝ] ℝ) ∘ (fderiv ℝ f)) := rfl
  rw [this]
  exact (ContinuousLinearMap.apply ℝ ℝ (basisVector j)).differentiableAt.comp x hf

/-!
## Identity 1: `∇ × (∇f) = 0`
-/

/-- **Identity 1 (curl of gradient).**  The curl of the gradient of `f`
vanishes at `x`, under the `C²` hypothesis that gives symmetric mixed partials. -/
theorem staticCurl_staticGradient_eq_zero
    (f : PressureField) (x : Space) (hf : ContDiffAt ℝ 2 f x) :
    staticCurl (fun y => staticGradient f y) x = 0 := by
  have hsymm := ContDiffAt.hasSymmetricMixedPartialAt hf
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have h2 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right le_rfl
    exact h2.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  -- The Pi-valued fderiv: fderiv (staticGradient f) x h at component j is
  -- fderiv (fun y => fderiv f y (basisVector j)) x h
  have hpi : ∀ (h : Space) (j : Fin 3),
      (fderiv ℝ (staticGradient f) x h) j =
        fderiv ℝ (fun y => fderiv ℝ f y (basisVector j)) x h := by
    intro h j
    have hpi' := fderiv_pi (𝕜 := ℝ) (E := Space) (x := x)
      (φ := fun j y => fderiv ℝ f y (basisVector j))
      (fun j => DifferentiableAt.fderiv_component hdiff j)
    rw [show (fun x => fun j => (fun y => fderiv ℝ f y (basisVector j)) x) = staticGradient f
        from rfl] at hpi'
    rw [hpi']
    rfl
  -- Define w so that staticCurl (staticGradient f) x = ∑ i, basisVector i ⨯₃ w i
  set w : Fin 3 → Space := fun i => fderiv ℝ (fun y => staticGradient f y) x (basisVector i)
  have hwsymm : ∀ i j, w i j = w j i := by
    intro i j
    simp only [w]
    rw [hpi, hpi]
    exact hsymm i j
  rw [staticCurl]
  exact curl_symmetric_eq_zero w hwsymm


/-!
## Identity 2: `∇ · (∇ × u) = 0`
-/

/-- **Algebraic core for `div(curl u) = 0`.**  If `T : Fin 3 → Fin 3 → Space`
is symmetric in its first two arguments, then the double Levi-Civita
contraction vanishes. -/
private lemma div_curl_symmetric_eq_zero
    (T : Fin 3 → Fin 3 → Space) (hsymm : ∀ k i : Fin 3, T k i = T i k) :
    ∑ k : Fin 3, ∑ i : Fin 3, (basisVector i ⨯₃ T k i) k = 0 := by
  simp only [Fin.sum_univ_three]
  simp only [cross_basisVector_zero, cross_basisVector_one, cross_basisVector_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [hsymm 0 1, hsymm 0 2, hsymm 1 2]
  ring

/-- Chain-rule lemma: the derivative of the `i`-th cross-product summand of
`staticCurl` factors through the linear cross-product and the eval-CLM bridge. -/
private lemma fderiv_cross_basisVector_apply
    (u : VelocityField) (x h : Space) (i : Fin 3)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    fderiv ℝ (fun y => basisVector i ⨯₃ fderiv ℝ u y (basisVector i)) x h =
      basisVector i ⨯₃ ((fderiv ℝ (fderiv ℝ u) x h) (basisVector i)) := by
  let L : Space →ₗ[ℝ] Space := crossProduct (basisVector i)
  have hg : fderiv ℝ (fun y => fderiv ℝ u y (basisVector i)) x h =
      (fderiv ℝ (fderiv ℝ u) x h) (basisVector i) := by
    let T : (Space →L[ℝ] Space) →L[ℝ] Space :=
      ContinuousLinearMap.apply ℝ Space (basisVector i)
    have hcomp := (HasFDerivAt.comp x T.hasFDerivAt hu.hasFDerivAt).fderiv
    change (fderiv ℝ (⇑T ∘ fderiv ℝ u) x) h = ((fderiv ℝ (fderiv ℝ u) x) h) (basisVector i)
    rw [hcomp]
    rfl
  have hdg : DifferentiableAt ℝ (fun y => fderiv ℝ u y (basisVector i)) x := by
    have heq : (fun y => fderiv ℝ u y (basisVector i)) =
      (ContinuousLinearMap.apply ℝ Space (basisVector i) ∘ fderiv ℝ u) := rfl
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ Space (basisVector i)).differentiableAt.comp x hu
  have hL : HasFDerivAt (fun w => L w) L.toContinuousLinearMap
      (fderiv ℝ u x (basisVector i)) :=
    L.toContinuousLinearMap.hasFDerivAt
  have hcomp := (HasFDerivAt.comp x hL hdg.hasFDerivAt).fderiv
  change (fderiv ℝ ((fun w => L w) ∘ (fun y => fderiv ℝ u y (basisVector i))) x) h = _
  rw [hcomp]
  change L ((fderiv ℝ (fun y => fderiv ℝ u y (basisVector i)) x) h) = _
  rw [hg]

/-- Each summand of `staticCurl u` is differentiable at `x` when `fderiv u` is. -/
private lemma DifferentiableAt.staticCurl_summand
    (u : VelocityField) (x : Space) (i : Fin 3)
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    DifferentiableAt ℝ (fun y => basisVector i ⨯₃ fderiv ℝ u y (basisVector i)) x := by
  let L : Space →ₗ[ℝ] Space := crossProduct (basisVector i)
  have hdg : DifferentiableAt ℝ (fun y => fderiv ℝ u y (basisVector i)) x := by
    have heq : (fun y => fderiv ℝ u y (basisVector i)) =
      (ContinuousLinearMap.apply ℝ Space (basisVector i) ∘ fderiv ℝ u) := rfl
    rw [heq]
    exact (ContinuousLinearMap.apply ℝ Space (basisVector i)).differentiableAt.comp x hu
  have heq : (fun y => basisVector i ⨯₃ fderiv ℝ u y (basisVector i)) =
    (L.toContinuousLinearMap ∘ (fun y => fderiv ℝ u y (basisVector i))) := rfl
  rw [heq]
  exact L.toContinuousLinearMap.differentiableAt.comp x hdg

/-- **Identity 2 (divergence of curl).**  The divergence of the curl of `u`
vanishes at `x`, under the `C²` hypothesis on `u`.  Reference: Majda–Bertozzi,
*Vorticity and Incompressible Flow*, §1.2 equation (1.8). -/
theorem staticDivergence_staticCurl_eq_zero
    (u : VelocityField) (x : Space) (hu : ContDiffAt ℝ 2 u x) :
    staticDivergence (fun y => staticCurl u y) x = 0 := by
  have hsymm_u : IsSymmSndFDerivAt ℝ u x :=
    hu.isSymmSndFDerivAt (by simp [minSmoothness])
  have hdiff_u : DifferentiableAt ℝ (fderiv ℝ u) x := by
    have h2 : ContDiffAt ℝ 1 (fderiv ℝ u) x := hu.fderiv_right le_rfl
    exact h2.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  set T : Fin 3 → Fin 3 → Space :=
    fun k i => (fderiv ℝ (fderiv ℝ u) x (basisVector k)) (basisVector i)
  have hTsymm : ∀ k i, T k i = T i k := by
    intro k i; simp only [T]; exact hsymm_u _ _
  -- fderiv (staticCurl u) x (basisVector k) = ∑ i, basisVector i ⨯₃ T k i
  have hkey : ∀ k : Fin 3,
      (fderiv ℝ (fun y => staticCurl u y) x (basisVector k)) =
        (∑ i, basisVector i ⨯₃ T k i) := by
    intro k
    change (fderiv ℝ
      (∑ i, (fun y => basisVector i ⨯₃ fderiv ℝ u y (basisVector i))) x) (basisVector k) = _
    rw [fderiv_sum (fun i _ => DifferentiableAt.staticCurl_summand u x i hdiff_u)]
    change (∑ i, (fderiv ℝ (fun y => basisVector i ⨯₃ fderiv ℝ u y (basisVector i)) x)
        (basisVector k)) = (∑ i, basisVector i ⨯₃ T k i)
    exact Finset.sum_congr rfl (fun i _ =>
      fderiv_cross_basisVector_apply u x (basisVector k) i hdiff_u)
  rw [staticDivergence]
  simp only [hkey]
  exact div_curl_symmetric_eq_zero T hTsymm

set_option maxHeartbeats 2000000 in
/- **Identity 3 (scalar-vector curl product rule).**  The curl of a
scalar-times-vector field `f • u` decomposes as the cross product of the
gradient of `f` with `u` plus `f` times the curl of `u`.  Biot–Savart
vorticity transport step. -/
theorem staticCurl_smul
    (f : PressureField) (u : VelocityField) (x : Space)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) :
    staticCurl (fun y => f y • u y) x =
      staticGradient f x ⨯₃ u x + f x • staticCurl u x := by
  have hfu : ∀ i : Fin 3,
      fderiv ℝ (fun y => f y • u y) x (Pi.single i (1:ℝ)) =
        f x • fderiv ℝ u x (Pi.single i (1:ℝ)) +
          fderiv ℝ f x (Pi.single i (1:ℝ)) • u x := by
    intro i
    have h := fderiv_fun_smul hf hu
    rw [h]
    rfl
  unfold staticCurl staticGradient
  ext k
  fin_cases k
  all_goals simp [hfu, cross_apply, basisVector, Finset.sum_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  all_goals try ring


/-- Component bridge: the `j`-th component of the Fréchet derivative of a
velocity field equals the Fréchet derivative of the `j`-th scalar component
function (Pi-rule on the eta-identified field). -/
private lemma fderiv_apply_component
    (w : VelocityField) (x : Space)
    (hw : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => w y k) x)
    (h : Space) (j : Fin 3) :
    (fderiv ℝ w x h) j = fderiv ℝ (fun y => w y j) x h := by
  have hpi' := fderiv_pi (𝕜 := ℝ) (E := Space) (x := x)
    (φ := fun k : Fin 3 => fun y : Space => w y k) hw
  rw [show (fun y : Space => fun k : Fin 3 => w y k) = w from rfl] at hpi'
  rw [hpi']
  rfl

/-- Componentwise differentiability of a differentiable velocity field. -/
private lemma differentiableAt_component
    (w : VelocityField) (x : Space) (hw : DifferentiableAt ℝ w x) (k : Fin 3) :
    DifferentiableAt ℝ (fun y => w y k) x :=
  differentiableAt_pi.mp hw k

/-- **Bilinear product rule for the cross product**, evaluated on the `k`-th
divergence summand: the derivative of `y ↦ u y ⨯₃ v y` splits into the
`v`-derivative cross term plus the `u`-derivative cross term. -/
private lemma fderiv_cross_apply
    (u v : VelocityField) (x : Space)
    (hu : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => u y k) x)
    (hv : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => v y k) x)
    (k : Fin 3) :
    (fderiv ℝ (fun y => u y ⨯₃ v y) x (basisVector k)) k =
      (u x ⨯₃ (fderiv ℝ v x (basisVector k))) k +
        ((fderiv ℝ u x (basisVector k)) ⨯₃ v x) k := by
  have hdiff : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => (u y ⨯₃ v y) j) x := by
    intro j
    fin_cases j
    · simp [cross_apply]
      exact ((hu 1).mul (hv 2)).sub ((hu 2).mul (hv 1))
    · simp [cross_apply]
      exact ((hu 2).mul (hv 0)).sub ((hu 0).mul (hv 2))
    · simp [cross_apply]
      exact ((hu 0).mul (hv 1)).sub ((hu 1).mul (hv 0))
  have hpi : ∀ (h : Space) (j : Fin 3),
      (fderiv ℝ (fun y => u y ⨯₃ v y) x h) j =
        fderiv ℝ (fun y => (u y ⨯₃ v y) j) x h := by
    intro h j
    have hpi' := fderiv_pi (𝕜 := ℝ) (E := Space) (x := x)
      (φ := fun j : Fin 3 => fun y : Space => (u y ⨯₃ v y) j) hdiff
    rw [show (fun y : Space => fun j : Fin 3 => (u y ⨯₃ v y) j) =
        (fun y => u y ⨯₃ v y) from rfl] at hpi'
    rw [hpi']
    rfl
  fin_cases k
  · rw [hpi _ _]
    simp [cross_apply]
    have hm1 : DifferentiableAt ℝ (fun y => u y 1 * v y 2) x := (hu 1).mul (hv 2)
    have hm2 : DifferentiableAt ℝ (fun y => u y 2 * v y 1) x := (hu 2).mul (hv 1)
    rw [fderiv_fun_sub hm1 hm2, fderiv_fun_mul (hu 1) (hv 2),
      fderiv_fun_mul (hu 2) (hv 1)]
    simp only [sub_apply, add_apply,
      smul_apply, smul_eq_mul,
      fderiv_apply_component v x hv, fderiv_apply_component u x hu]
    ring
  · rw [hpi _ _]
    simp [cross_apply]
    have hm1 : DifferentiableAt ℝ (fun y => u y 2 * v y 0) x := (hu 2).mul (hv 0)
    have hm2 : DifferentiableAt ℝ (fun y => u y 0 * v y 2) x := (hu 0).mul (hv 2)
    rw [fderiv_fun_sub hm1 hm2, fderiv_fun_mul (hu 2) (hv 0),
      fderiv_fun_mul (hu 0) (hv 2)]
    simp only [sub_apply, add_apply,
      smul_apply, smul_eq_mul,
      fderiv_apply_component v x hv, fderiv_apply_component u x hu]
    ring
  · rw [hpi _ _]
    simp [cross_apply]
    have hm1 : DifferentiableAt ℝ (fun y => u y 0 * v y 1) x := (hu 0).mul (hv 1)
    have hm2 : DifferentiableAt ℝ (fun y => u y 1 * v y 0) x := (hu 1).mul (hv 0)
    rw [fderiv_fun_sub hm1 hm2, fderiv_fun_mul (hu 0) (hv 1),
      fderiv_fun_mul (hu 1) (hv 0)]
    simp only [sub_apply, add_apply,
      smul_apply, smul_eq_mul,
      fderiv_apply_component v x hv, fderiv_apply_component u x hu]
    ring

/-- **Falsification witness (Step-0e).**  The sign-flipped triple-product
rearrangement `∑ₖ (a ⨯₃ Vₖ)ₖ + (Uₖ × b)ₖ = a ⬝ᵥ (∑ eᵢ ⨯₃ Vᵢ) − b ⬝ᵥ (∑ eᵢ ⨯₃ Uᵢ)`
is FALSE: at `a = e₀`, `b = 0`, `U = 0`, `V = ![0, e₂, 0]` the left side
evaluates to `−1` while the right side evaluates to `1`.  This kernel-checked
counterexample corrected the original statement of Identity 4; the true
rearrangement is `div_cross_algebra` below. -/
theorem div_cross_algebra_sign_flipped_false :
    ¬ (∀ (a b : Space) (U V : Fin 3 → Space),
        (∑ k : Fin 3, (a ⨯₃ V k) k) + (∑ k : Fin 3, (U k ⨯₃ b) k) =
          a ⬝ᵥ (∑ i : Fin 3, basisVector i ⨯₃ V i) -
            b ⬝ᵥ (∑ i : Fin 3, basisVector i ⨯₃ U i)) := by
  intro h
  have hw := h (basisVector 0) 0 0 ![0, basisVector 2, 0]
  simp [Fin.sum_univ_three, Finset.sum_apply, dotProduct, basisVector,
    cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons] at hw
  norm_num at hw

/-- **Algebraic core for Identity 4.**  For any vectors `a b` and derivative
families `U V`, the expanded divergence-of-cross sum equals the scalar triple
product rearrangement `b ⬝ᵥ (∑ eᵢ ⨯₃ Uᵢ) − a ⬝ᵥ (∑ eᵢ ⨯₃ Vᵢ)`.
Pure `Fin 3` component algebra. -/
private lemma div_cross_algebra
    (a b : Space) (U V : Fin 3 → Space) :
    (∑ k : Fin 3, (a ⨯₃ V k) k) + (∑ k : Fin 3, (U k ⨯₃ b) k) =
      b ⬝ᵥ (∑ i : Fin 3, basisVector i ⨯₃ U i) -
        a ⬝ᵥ (∑ i : Fin 3, basisVector i ⨯₃ V i) := by
  simp [dotProduct, basisVector, Fin.sum_univ_three, Finset.sum_apply,
    cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons]
  ring

/-- **Identity 4 (cross-product divergence).**  The divergence of the cross
product `u × v` equals `v · curl(u) − u · curl(v)`, the scalar triple
product rearrangement underlying the Biot–Savart energy estimate.

The sign-flipped form `u · curl(v) − v · curl(u)` is FALSE — see the
kernel-checked counterexample `div_cross_algebra_sign_flipped_false` (caught
by Step-0e: the algebraic core of the flipped form does not close, and
`u₀ = y₁, v₁ = y₂` gives `∇·(u×v) = y₁` against the flipped claim `−y₁`).

Route: the `k`-th divergence summand expands by the bilinear product rule
(`fderiv_cross_apply`, componentwise via `fderiv_pi` + `fderiv_fun_mul` +
`fderiv_fun_sub`), and the resulting finite contraction is `div_cross_algebra`.
Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §1.2. -/
theorem staticDivergence_cross
    (u v : VelocityField) (x : Space)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    staticDivergence (fun y => u y ⨯₃ v y) x =
      v x ⬝ᵥ staticCurl u x - u x ⬝ᵥ staticCurl v x := by
  have hu' : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => u y k) x :=
    fun k => differentiableAt_component u x hu k
  have hv' : ∀ k : Fin 3, DifferentiableAt ℝ (fun y => v y k) x :=
    fun k => differentiableAt_component v x hv k
  rw [staticDivergence,
    Finset.sum_congr rfl (fun k _ => fderiv_cross_apply u v x hu' hv' k),
    Finset.sum_add_distrib]
  exact div_cross_algebra (u x) (v x)
    (fun k => fderiv ℝ u x (basisVector k)) (fun k => fderiv ℝ v x (basisVector k))

end Navier.Analysis.CurlIdentities
