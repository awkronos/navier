import Navier.Analysis.Enstrophy

/-!
# Pointwise enstrophy-integrand identities (Majda–Bertozzi §3.3, integrand level)

The pointwise identities that the enstrophy differential inequality
(`Navier.Analysis.Enstrophy.enstrophyDifferentialInequality`) integrates.
All are unconditional facts about differentiable fields in the official
Euclidean coordinates — no solution hypotheses and no measure theory:

* `fderiv_normSq_apply` — `∂_v(|w|²) = 2⟨w, (Dw) v⟩`.  With `w = ω(t,·)` and
  `v = u(t,x)` this is the transport-term integrand identity
  `(u·∇)|ω|² = 2⟨ω, (u·∇)ω⟩`, whose integral dies by incompressibility.
* `scalarLaplacian_normSq` — the pointwise **Bochner identity**
  `Δ(|w|²) = 2⟨w, Δw⟩ + 2∑ᵢ|∂ᵢw|²`, with both Laplacians written in the
  repository's coordinate shape (`Navier.laplacian` componentwise).
* `two_mul_inner_laplacian_le` — viscous dissipativity: for `0 ≤ ν`,
  `2ν⟨w, Δw⟩ ≤ ν·Δ(|w|²)` pointwise, dropping the signed gradient square.
  This is the sign that makes the viscous term of the enstrophy estimate
  dissipative.

Supporting layer: coordinate forms of `officialInner` and the squared
official norm, and the component bridges `differentiableAt_component` /
`fderiv_component_apply`.

Reference: Majda–Bertozzi, *Vorticity and Incompressible Flow*, §3.3; the
Bochner identity is the standard `Δ|w|² = 2⟨w, Δw⟩ + 2|∇w|²`.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.EnstrophyPointwise

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Enstrophy

/-- Coordinate form of the official inner product. -/
theorem officialInner_eq_sum (x y : Space) :
    officialInner x y = ∑ i : Fin 3, x i * y i := by
  simp only [officialInner, officialEuclideanPoint, PiLp.inner_apply,
    RCLike.inner_apply, starRingEnd_apply, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Coordinate form of the squared official norm. -/
theorem officialEuclideanNorm_sq_eq_sum (x : Space) :
    officialEuclideanNorm x ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  rw [← officialInner_self, officialInner_eq_sum]
  exact Finset.sum_congr rfl fun i _ => (sq (x i)).symm

/-- The official inner product distributes over finite sums on the right. -/
theorem officialInner_sum_right (a : Space) (v : Fin 3 → Space) :
    officialInner a (∑ i : Fin 3, v i) = ∑ i : Fin 3, officialInner a (v i) := by
  simp only [officialInner_eq_sum, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Components of a differentiable field are differentiable. -/
theorem differentiableAt_component (w : VelocityField) (x : Space)
    (hw : DifferentiableAt ℝ w x) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => w y j) x :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ)
    j).differentiableAt).comp x hw

/-- Component bridge: the derivative of the `j`-th component is the `j`-th
component of the derivative. -/
theorem fderiv_component_apply (w : VelocityField) (x v : Space)
    (hw : DifferentiableAt ℝ w x) (j : Fin 3) :
    fderiv ℝ (fun y => w y j) x v = fderiv ℝ w x v j := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ)
    j).hasFDerivAt.comp x hw.hasFDerivAt).fderiv
  change (fderiv ℝ ((ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Fin 3 => ℝ) j) ∘ w) x) v = _
  rw [h]
  rfl

/-- **Derivative of the squared official norm**: `∂_v(|w|²)(x) = 2⟨w x, (Dw x) v⟩`. -/
theorem fderiv_normSq_apply (w : VelocityField) (x v : Space)
    (hw : DifferentiableAt ℝ w x) :
    fderiv ℝ (fun y => officialEuclideanNorm (w y) ^ 2) x v =
      2 * officialInner (w x) (fderiv ℝ w x v) := by
  have hcomp : ∀ j : Fin 3, DifferentiableAt ℝ (fun y => w y j) x :=
    differentiableAt_component w x hw
  have hrw : (fun y => officialEuclideanNorm (w y) ^ 2) =
      (fun y => ∑ j : Fin 3, w y j * w y j) := by
    funext y
    rw [officialEuclideanNorm_sq_eq_sum]
    exact Finset.sum_congr rfl fun j _ => sq (w y j)
  rw [hrw, fderiv_fun_sum fun j _ => (hcomp j).fun_mul (hcomp j), sum_apply,
    officialInner_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_fun_mul (hcomp j) (hcomp j)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_component_apply w x v hw j]
  ring

/-- **Pointwise Bochner identity**: `Δ(|w|²) = 2⟨w, Δw⟩ + 2∑ᵢ|∂ᵢw|²`. -/
theorem scalarLaplacian_normSq (w : VelocityField) (x : Space)
    (hw1 : ∀ y : Space, DifferentiableAt ℝ w y)
    (hw2 : DifferentiableAt ℝ (fderiv ℝ w) x) :
    ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun y => officialEuclideanNorm (w y) ^ 2) z
        (basisVector i)) x (basisVector i) =
      2 * officialInner (w x) (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) x (basisVector i)) +
        2 * ∑ i : Fin 3,
          officialEuclideanNorm (fderiv ℝ w x (basisVector i)) ^ 2 := by
  have hFdiff : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun z => fderiv ℝ w z (basisVector i)) x := by
    intro i
    exact (ContinuousLinearMap.apply ℝ Space
      (basisVector i)).differentiableAt.comp x hw2
  have hwj : ∀ j : Fin 3, DifferentiableAt ℝ (fun z => w z j) x :=
    differentiableAt_component w x (hw1 x)
  have hFj : ∀ i j : Fin 3, DifferentiableAt ℝ
      (fun z => fderiv ℝ w z (basisVector i) j) x := fun i j =>
    differentiableAt_component _ x (hFdiff i) j
  -- Step 1: the inner derivative function through the first-derivative identity
  have hstep1 : ∀ i : Fin 3,
      (fun z => fderiv ℝ (fun y => officialEuclideanNorm (w y) ^ 2) z
        (basisVector i)) =
      (fun z => 2 * ∑ j : Fin 3, w z j * fderiv ℝ w z (basisVector i) j) := by
    intro i
    funext z
    rw [fderiv_normSq_apply w z (basisVector i) (hw1 z), officialInner_eq_sum]
  -- Step 2: each product summand differentiates by the Leibniz rule
  have hstep2 : ∀ i j : Fin 3,
      fderiv ℝ (fun z => w z j * fderiv ℝ w z (basisVector i) j) x
        (basisVector i) =
      fderiv ℝ w x (basisVector i) j * fderiv ℝ w x (basisVector i) j +
        w x j * fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) x
          (basisVector i) j := by
    intro i j
    rw [fderiv_fun_mul (hwj j) (hFj i j)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [fderiv_component_apply w x (basisVector i) (hw1 x) j,
      fderiv_component_apply (fun z => fderiv ℝ w z (basisVector i)) x
        (basisVector i) (hFdiff i) j]
    ring
  -- Step 3: assemble
  have hmain : ∀ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun y => officialEuclideanNorm (w y) ^ 2) z
        (basisVector i)) x (basisVector i) =
      2 * officialInner (w x)
          (fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) x (basisVector i)) +
        2 * officialEuclideanNorm (fderiv ℝ w x (basisVector i)) ^ 2 := by
    intro i
    have hd : DifferentiableAt ℝ
        (fun z => ∑ j : Fin 3, w z j * fderiv ℝ w z (basisVector i) j) x := by
      apply DifferentiableAt.fun_sum
      intro j _
      exact (hwj j).fun_mul (hFj i j)
    rw [hstep1 i, fderiv_const_mul hd 2]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_fun_sum fun j _ => (hwj j).fun_mul (hFj i j), sum_apply]
    rw [Finset.sum_congr rfl fun j _ => hstep2 i j, Finset.sum_add_distrib]
    rw [officialInner_eq_sum, officialEuclideanNorm_sq_eq_sum]
    simp only [mul_add, Finset.mul_sum, pow_two]
    exact add_comm _ _
  calc ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun y => officialEuclideanNorm (w y) ^ 2) z
        (basisVector i)) x (basisVector i)
      = ∑ i : Fin 3, (2 * officialInner (w x)
          (fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) x (basisVector i)) +
        2 * officialEuclideanNorm (fderiv ℝ w x (basisVector i)) ^ 2) :=
      Finset.sum_congr rfl fun i _ => hmain i
    _ = (∑ i : Fin 3, 2 * officialInner (w x)
          (fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) x (basisVector i))) +
        ∑ i : Fin 3,
          2 * officialEuclideanNorm (fderiv ℝ w x (basisVector i)) ^ 2 :=
      Finset.sum_add_distrib
    _ = 2 * officialInner (w x) (∑ i : Fin 3,
          fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) x (basisVector i)) +
        2 * ∑ i : Fin 3,
          officialEuclideanNorm (fderiv ℝ w x (basisVector i)) ^ 2 := by
      rw [officialInner_sum_right, Finset.mul_sum, Finset.mul_sum]

/-- **Viscous dissipativity, pointwise.**  For `0 ≤ ν`, the viscous
production `2ν⟨w, Δw⟩` is dominated by `ν·Δ(|w|²)`: the difference is the
gradient square `2ν∑ᵢ|∂ᵢw|²` from the Bochner identity, which has a sign.
This is the pointwise inequality behind dropping `−2ν∫|∇ω|²` in the
enstrophy estimate. -/
theorem two_mul_inner_laplacian_le (w : VelocityField) (x : Space)
    (hw1 : ∀ y : Space, DifferentiableAt ℝ w y)
    (hw2 : DifferentiableAt ℝ (fderiv ℝ w) x)
    {ν : ℝ} (hν : 0 ≤ ν) :
    2 * ν * officialInner (w x) (∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ w z (basisVector i)) x (basisVector i)) ≤
      ν * ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun y => officialEuclideanNorm (w y) ^ 2) z
          (basisVector i)) x (basisVector i) := by
  rw [scalarLaplacian_normSq w x hw1 hw2]
  have hsq : 0 ≤ ∑ i : Fin 3,
      officialEuclideanNorm (fderiv ℝ w x (basisVector i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [mul_nonneg hν hsq]

end Navier.Analysis.EnstrophyPointwise
