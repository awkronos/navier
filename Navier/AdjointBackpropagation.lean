/-
Copyright (c) 2026 Awkronos. All rights reserved.
Released under the terms of the Apache 2.0 license found in the file
'LICENSE'.
Authors: Kagami W34-L1 (Beacon lane)

# Adjoint (backpropagation) gradient identities for linearized flow
observation

Crown shape. For a bounded linear forward-observation operator `L` between
real inner-product (Hilbert) spaces and data `z`, the misfit

    J(u) = ½ ‖L u − z‖²

has gradient

    ∇J(u) = L† (L u − z),

where `L†` is the Hilbert-space adjoint (`ContinuousLinearMap.adjoint`).
This file proves:

1. **Abstract core** (`Navier.gradient_obsMisfit`, over general real inner
   product spaces, via Mathlib's `InnerProductSpace` and the `gradient` /
   `HasGradientAt` API). The exact linearization lemma
   `Navier.obsMisfit_remainder` shows the increment of `J` minus the
   candidate gradient pairing is *literally* ½‖L h‖²; the little-o crown
   `Navier.hasGradientAt_obsMisfit` bounds that remainder by the operator
   norm, so no finite dimensionality is used anywhere in the abstract part.

2. **Matrix instantiation — backprop as actually implemented in a solver.**
   On `EuclideanSpace` (ℓ² column vectors), the forward operator is the
   explicit matrix–vector map `mulVecCLM A`, and its Hilbert adjoint is the
   literal matrix transpose `Matrix.conjTranspose A`
   (`Navier.adjoint_mulVecCLM`, proved by the finite sum swap
   `Finset.sum_comm` — computed, not axiomatized). The corollary
   `Navier.gradient_mulVec` is the classical backprop rule
   `∇J(u) = Aᵀ (A u − z)` for a one-layer linear forward model.

3. **Named non-vacuity data.** `sampleA = (2 1; 1 3)` (symmetric positive
   definite), `sampleZ = (1, 1)`, `sampleU = (1, 2)`, with the fully
   computed gradient `∇J(sampleU) = (12, 21)` (`Navier.gradient_sample`)
   and `Navier.sample_forward` exhibiting the forward operator non-degenerate
   on the named input. Together with the ∀-form `gradient_mulVec` the class
   statement is shown inhabited by explicit data.

## Relation to the existing Navier self-adjointness neighbourhood

`Navier/Analysis/GalerkinBasis.lean` constructs the finite-mode Stokes
operator `W.stokesOperator m : EuclideanSpace ℝ (Fin m) →L[ℝ]
EuclideanSpace ℝ (Fin m)` from `schwartzL2Inner` pairings; its
`stokesOperator_pairing` is weak self-adjointness of that operator. That
operator is exactly the carrier class this module consumes. The wiring at
the consumer is the one line — to be placed in `GalerkinBasis.lean` (or any
future Oseen / adjoint-replay module), which imports *this* module:

    gradient (Navier.obsMisfit (W.stokesOperator m) z) u
      = (W.stokesOperator m).adjoint (W.stokesOperator m u - z) :=
    Navier.gradient_obsMisfit _ _ _

The import direction GalerkinBasis → AdjointBackpropagation (never the
reverse) is deliberate: the lane build contract forbids multi-module olean
cone rebuilds, so the connection is recorded here as an exact one-line
proof term plus the consumer-side import, not a duplicated carrier.
This module reuses that file's conventions verbatim: operators built from
`WithLp.toLp 2` applied pointwise, continuity via
`LinearMap.toContinuousLinearMap`, inner products unfolded by
`PiLp.inner_apply` / `RCLike.inner_apply` / `conj_trivial`, and status
prose that states its own scope.

## Honest scope

This is the reverse-mode identity for a *linearized* forward problem: each
step of a full Navier–Stokes backpropagation sweep is an application of a
`gradient_obsMisfit`-shape identity (composed by the chain rule) once the
forward operator is linearized. Composing this with a *nonlinear* forward
step additionally requires differentiability of the NS solution/sensitivity
operator at the chosen discretization; that object is not constructed in
this repository as of this commit and is the named remaining dependency of
the full-solver crown — an unbuilt carrier, not a refuted route.

Verified single-file against Mathlib git#v4.34.0-rc2, toolchain
v4.34.0-rc2: `lake env lean Navier/AdjointBackpropagation.lean`.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

namespace Navier

open Finset Filter Matrix
open scoped BigOperators Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The linearized flow-observation misfit `u ↦ ½‖L u − z‖²` for a bounded
linear forward operator `L`. -/
def obsMisfit (L : E →L[ℝ] F) (z : F) (u : E) : ℝ :=
  (1 / 2) * ‖L u - z‖ ^ 2

/-- **Exact linearization.** The increment of the misfit along a step `h`,
minus the pairing of `h` with the candidate adjoint gradient, is *exactly*
the quadratic remainder ½‖L h‖². This is the algebraic core of the backprop
identity: the linear part of the increment is `⟪L†(Lu−z), h⟫` and nothing
else. -/
theorem obsMisfit_remainder (L : E →L[ℝ] F) (z : F) (u h : E) :
    obsMisfit L z (u + h) - obsMisfit L z u -
      inner ℝ (L.adjoint (L u - z)) h =
      (1 / 2 : ℝ) * ‖L h‖ ^ 2 := by
  unfold obsMisfit
  have hw : L (u + h) - z = (L u - z) + L h := by rw [map_add]; abel
  have h1 : inner ℝ (L.adjoint (L u - z)) h = inner ℝ (L u - z) (L h) :=
    ContinuousLinearMap.adjoint_inner_left L h (L u - z)
  rw [hw, h1, norm_add_sq_real]
  ring

/-- **Gradient existence (little-o crown).** The quadratic remainder is
`o(‖h‖)` by the operator-norm bound `‖L h‖ ≤ ‖L‖ ‖h‖`, so `h ↦ ½‖L h‖²` is
`o(‖h‖)` at the origin — `L†(Lu−z)` is *the* gradient of the misfit. -/
theorem hasGradientAt_obsMisfit (L : E →L[ℝ] F) (z : F) (u : E) :
    HasGradientAt (obsMisfit L z) (L.adjoint (L u - z)) u := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have key : (fun h : E => obsMisfit L z (u + h) - obsMisfit L z u -
      inner ℝ (L.adjoint (L u - z)) h) = fun h : E => (1 / 2 : ℝ) * ‖L h‖ ^ 2 :=
    funext fun h => obsMisfit_remainder L z u h
  rw [key]
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  set k := (1 / 2 : ℝ) * ‖L‖ ^ 2 with hk
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hb : (0 : ℝ) < c / (1 + k) := div_pos hc (by positivity)
  have hev : ∀ᶠ h : E in 𝓝 0, ‖h‖ < c / (1 + k) := by
    have ht : Tendsto (fun x : E => ‖x‖) (𝓝 0) (𝓝 0) := by
      simpa using continuous_norm.tendsto (0 : E)
    exact ht.eventually (eventually_lt_nhds hb)
  filter_upwards [hev] with h hh
  have hkh : k * ‖h‖ ≤ c := by
    have h1 : k * ‖h‖ ≤ k * (c / (1 + k)) :=
      mul_le_mul_of_nonneg_left hh.le hk0
    have h2 : k / (1 + k) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have h3 : k * (c / (1 + k)) < c := by
      calc k * (c / (1 + k)) = (k / (1 + k)) * c := by ring
        _ < 1 * c := mul_lt_mul_of_pos_right h2 hc
        _ = c := one_mul c
    linarith
  calc ‖(1 / 2 : ℝ) * ‖L h‖ ^ 2‖
      = (1 / 2 : ℝ) * ‖L h‖ ^ 2 :=
        RCLike.norm_of_nonneg' (by positivity)
    _ ≤ (1 / 2 : ℝ) * (‖L‖ * ‖h‖) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm L h) 2)
          (by positivity)
    _ = k * ‖h‖ ^ 2 := by rw [hk]; ring
    _ = ‖h‖ * (k * ‖h‖) := by ring
    _ ≤ ‖h‖ * c := mul_le_mul_of_nonneg_left hkh (norm_nonneg _)
    _ = c * ‖h‖ := by ring

/-- **Fréchet form of the crown.** The Fréchet derivative of the misfit is
the dual of the adjoint residual: `dJ(u) = (L†(Lu−z))♭`. -/
theorem fderiv_obsMisfit (L : E →L[ℝ] F) (z : F) (u : E) :
    fderiv ℝ (obsMisfit L z) u =
      InnerProductSpace.toDual ℝ E (L.adjoint (L u - z)) :=
  ((Navier.hasGradientAt_obsMisfit L z u).hasFDerivAt).fderiv

/-- **Abstract crown: the adjoint/backpropagation identity.**
For the linearized flow observation `J(u) = ½‖Lu − z‖²` over real inner
product (Hilbert) spaces, `∇J(u) = L†(Lu − z)` — the gradient is the adjoint
applied to the residual. No finite-dimensionality or spectral assumption is
used. -/
theorem gradient_obsMisfit (L : E →L[ℝ] F) (z : F) (u : E) :
    gradient (obsMisfit L z) u = L.adjoint (L u - z) :=
  (Navier.hasGradientAt_obsMisfit L z u).gradient

/-! ## The matrix instantiation: backprop with the transpose -/

/-- `n`-dimensional real Euclidean column vectors: Mathlib's
`EuclideanSpace` (the ℓ² structure on `Fin n → ℝ`). -/
abbrev Eu (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- Matrix–vector application as a bare linear map between Euclidean
spaces: the forward operator of a linear solver layer. -/
def mulVecLM {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) : Eu q →ₗ[ℝ] Eu p where
  toFun v := WithLp.toLp 2 (A.mulVec ⇑v)
  map_add' a b := by
    ext i
    simp [Matrix.mulVec_add]
  map_smul' c v := by
    ext i
    simp [Matrix.mulVec_smul]

/-- Pointwise application of the matrix forward operator. -/
@[simp] theorem mulVecLM_apply {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (v : Eu q) : (mulVecLM A v).ofLp = A.mulVec ⇑v := by
  simp [mulVecLM]

/-- The Hilbert-space adjunction identity for the matrix forward operator:
`⟪A x, y⟫ = ⟪x, Aᵀ y⟫`, proved by exchanging the finite sums
(`Finset.sum_comm`) — the computation that makes the transpose the adjoint. -/
theorem mulVecLM_adjunct {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (x : Eu q) (y : Eu p) :
    inner ℝ (mulVecLM A x) y = inner ℝ x (mulVecLM (Matrix.conjTranspose A) y) := by
  simp only [PiLp.inner_apply, mulVecLM_apply, RCLike.inner_apply, conj_trivial]
  rw [show A.mulVec ⇑x = fun i => ∑ j : Fin q, A i j * x.ofLp j from by
      ext i; simp [Matrix.mulVec_apply, dotProduct, Matrix.row]]
  rw [show (Matrix.conjTranspose A).mulVec ⇑y =
        fun i => ∑ j : Fin p, A j i * y.ofLp j from by
      ext i; simp [Matrix.mulVec_apply, dotProduct, Matrix.row]]
  dsimp only
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- The adjoint of the matrix forward operator **is the matrix transpose**:
`(mulVecLM A)† = mulVecLM (Aᵀ)` in the finite-dimensional linear-map adjoint. -/
theorem adjoint_mulVecLM {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    LinearMap.adjoint (mulVecLM A) = mulVecLM (Matrix.conjTranspose A) := by
  apply LinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [real_inner_comm, LinearMap.adjoint_inner_left, real_inner_comm,
    mulVecLM_adjunct]

/-- Matrix–vector application as a **continuous linear map** on Euclidean
space (finite-dimensional continuity, via the `LinearMap` model above). -/
def mulVecCLM {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) : Eu q →L[ℝ] Eu p :=
  (mulVecLM A).toContinuousLinearMap

/-- **Adjoint = transpose, for continuous linear maps.** The Hilbert-space
adjoint of the matrix–vector operator is the transpose, computed from
`sum_comm`, not assumed. This is the discrete identity every solver's
backprop pass silently uses. -/
theorem adjoint_mulVecCLM {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    (mulVecCLM A).adjoint = mulVecCLM (Matrix.conjTranspose A) := by
  unfold mulVecCLM
  rw [← LinearMap.adjoint_toContinuousLinearMap, adjoint_mulVecLM]

/-- **Matrix backprop crown (∀-form for the class).** For *every* matrix
`A : Fin p → Fin q → ℝ`, data `z`, and state `u`:
`∇ ½‖A u − z‖² = Aᵀ (A u − z)`. -/
theorem gradient_mulVec {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ)
    (z : Eu p) (u : Eu q) :
    gradient (obsMisfit (mulVecCLM A) z) u =
      mulVecCLM (Matrix.conjTranspose A) (mulVecCLM A u - z) := by
  rw [gradient_obsMisfit, adjoint_mulVecCLM]

/-! ## Named non-vacuity data -/

/-- A named forward operator: the symmetric positive-definite 2×2 matrix. -/
def sampleA : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 3]

/-- Named data `z = (1, 1)`. -/
def sampleZ : Eu 2 := WithLp.toLp 2 ![1, 1]

/-- Named state `u = (1, 2)`. -/
def sampleU : Eu 2 := WithLp.toLp 2 ![1, 2]

/-- The named operator is symmetric: equal to its own adjoint/transpose. -/
theorem sampleA_symm : Matrix.conjTranspose sampleA = sampleA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sampleA, Matrix.conjTranspose_apply]

/-- The named forward operator is non-degenerate on the named state:
`A u = (4, 7) ≠ 0` — the crown's data actually moves. -/
theorem sample_forward : mulVecCLM sampleA sampleU = WithLp.toLp 2 ![4, 7] := by
  ext i
  fin_cases i <;>
    simp [mulVecCLM, mulVecLM_apply, Matrix.mulVec_apply, dotProduct,
      Matrix.row, sampleA, sampleU, Fin.sum_univ_two] <;>
    ring

/-- `A z = (3, 4)` on the named data. -/
theorem sample_forward_z : mulVecCLM sampleA sampleZ = WithLp.toLp 2 ![3, 4] := by
  ext i
  fin_cases i <;>
    simp [mulVecCLM, mulVecLM_apply, Matrix.mulVec_apply, dotProduct,
      Matrix.row, sampleA, sampleZ, Fin.sum_univ_two] <;>
    ring

/-- **Crown instantiated on explicit data.** The gradient of the misfit at
the named `(A, z, u)` is the computed vector `(12, 21)`: residual
`A u − z = (3, 6)`, backprop `Aᵀ (3,6)ᵀ = (2·3+1·6, 1·3+3·6)ᵀ = (12,21)`.
No `sorry`, no decision procedure beyond arithmetic: the identity follows
from the adjoint crown and pointwise finite-sum computation. -/
theorem gradient_sample :
    gradient (obsMisfit (mulVecCLM sampleA) sampleZ) sampleU =
      WithLp.toLp 2 ![12, 21] := by
  rw [gradient_mulVec, sampleA_symm, map_sub (mulVecCLM sampleA),
    sample_forward, sample_forward_z]
  -- goal: A(4,7) − A(3,4) = (12,21) with A = (2 1; 1 3)
  have h1 : mulVecCLM sampleA (WithLp.toLp 2 ![4, 7]) =
      WithLp.toLp 2 ![15, 25] := by
    ext i
    fin_cases i <;>
      simp [mulVecCLM, mulVecLM_apply, Matrix.mulVec_apply, dotProduct,
        Matrix.row, sampleA, Fin.sum_univ_two] <;>
      ring
  rw [h1]
  ext i
  fin_cases i <;>
    simp [PiLp.sub_apply] <;>
    ring

end Navier
