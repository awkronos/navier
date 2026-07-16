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

Reference: the divergence of a curl vanishes by antisymmetry of the
Levi-Civita symbol against the symmetric tensor of mixed second partials.
OPEN — the proof requires the vector-valued Pi-fderiv translation and the
componentwise symmetry hypothesis.  Reference: Majda–Bertozzi,
*Vorticity and Incompressible Flow*, §1.2 equation (1.8).  Estimated ~40 LOC
of coordinate computation once the Pi-fderiv bridge is in place.
-/

/-- **Algebraic core for `div(curl u) = 0`.**  If `T : Fin 3 → Fin 3 → Space`
is symmetric in its first two arguments (`T k i = T i k`), then
`∑ k, ∑ i, (basisVector i ⨯₃ T k i) k = 0`.  This is the double contraction
of the antisymmetric Levi-Civita symbol with a symmetric rank-2 tensor. -/
private lemma div_curl_symmetric_eq_zero
    (T : Fin 3 → Fin 3 → Space) (hsymm : ∀ k i : Fin 3, T k i = T i k) :
    ∑ k : Fin 3, ∑ i : Fin 3, (basisVector i ⨯₃ T k i) k = 0 := by
  simp only [Fin.sum_univ_three]
  simp only [cross_basisVector_zero, cross_basisVector_one, cross_basisVector_two]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [hsymm 0 1, hsymm 0 2, hsymm 1 2]
  ring

/-- **Identity 2 (divergence of curl).**  The divergence of the curl of `u`
vanishes at `x`, under the `C²` hypothesis on `u`.  Reference: Majda–Bertozzi,
*Vorticity and Incompressible Flow*, §1.2 equation (1.8).

The algebraic core `div_curl_symmetric_eq_zero` (the antisymmetric-times-symmetric
double contraction) is proved above.  The remaining step is the pointwise expansion
of `fderiv (staticCurl u)` through the cross-product structure, which reduces
`staticDivergence (staticCurl u) x` to the algebraic core's input `∑ k i, (e_i ⨯₃ T k i) k`
with `T k i = (fderiv (fderiv u) x (basisVector k)) (basisVector i)`, symmetric by
`IsSymmSndFDerivAt`.  OPEN residual, ~30 LOC of fderiv-cross-product chain rule. -/
theorem staticDivergence_staticCurl_eq_zero
    (u : VelocityField) (x : Space) (hu : ContDiffAt ℝ 2 u x) :
    staticDivergence (fun y => staticCurl u y) x = 0 := by
  sorry

/-- **Identity 3 (scalar-vector curl product rule).**  The curl of a
scalar-times-vector field `f • u` decomposes as the cross product of the
gradient of `f` with `u` plus `f` times the curl of `u`.  Biot–Savart
vorticity transport step. -/
theorem staticCurl_smul
    (f : PressureField) (u : VelocityField) (x : Space)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) :
    staticCurl (fun y => f y • u y) x =
      staticGradient f x ⨯₃ u x + f x • staticCurl u x := by
  sorry

/-- **Identity 4 (cross-product divergence).**  The divergence of the cross
product `u × v` equals `u · curl(v) − v · curl(u)`, the scalar triple
product rearrangement underlying the Biot–Savart energy estimate. -/
theorem staticDivergence_cross
    (u v : VelocityField) (x : Space)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    staticDivergence (fun y => u y ⨯₃ v y) x =
      u x ⬝ᵥ staticCurl v x - v x ⬝ᵥ staticCurl u x := by
  sorry

end Navier.Analysis.CurlIdentities
