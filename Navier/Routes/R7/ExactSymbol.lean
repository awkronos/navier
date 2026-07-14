import Navier.Problem

/-!
# Exact-symbol R7 leaf

This file isolates two logically separate facts.

1. The denominator-free Leray numerator
   `L_k(v) = (k dot k) v - (v dot k) k` is orthogonal to `k`, and the exact
   projected convection interaction `(a dot l) L_{k+l}(b)` vanishes for the
   self-interaction of one divergence-free Fourier mode.
2. Energy cancellation alone is weaker: the explicit bilinear map
   `B(u,v) = u cross (M v)` satisfies `u dot B(u,u) = 0` for every `u`, while
   `B(u,u)` is nonzero for a concrete `u`.

The second construction is only an algebraic countermodel. It is not claimed
to be Tao's averaged operator, a Navier--Stokes Fourier multiplier, or a source
of critical summability or global regularity.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace Navier.Routes.R7

/-- The denominator-free numerator of the Leray projection at frequency `k`. -/
def lerayNumerator (k v : Space) : Space :=
  (k ⬝ᵥ k) • v - (v ⬝ᵥ k) • k

/-- The Leray numerator always lies in the plane orthogonal to its frequency. -/
theorem dot_lerayNumerator (k v : Space) :
    k ⬝ᵥ lerayNumerator k v = 0 := by
  simp only [lerayNumerator, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm k v]
  ring

/-- The real, denominator-free part of one exact projected convection-mode
interaction. The omitted Fourier factor `i` is irrelevant to vanishing. -/
def projectedConvectionInteraction (a b k l : Space) : Space :=
  (a ⬝ᵥ l) • lerayNumerator (k + l) b

/-- A single divergence-free Fourier mode has zero quadratic self-interaction. -/
theorem divergenceFree_singleMode_selfInteraction_zero
    (k a : Space) (hdiv : k ⬝ᵥ a = 0) :
    projectedConvectionInteraction a a k k = 0 := by
  have hak : a ⬝ᵥ k = 0 := by
    rw [dotProduct_comm]
    exact hdiv
  simp [projectedConvectionInteraction, hak]

/-- A concrete non-scalar linear map, diagonal with entries `1, 2, 3`. -/
def countermodelM : Space →ₗ[ℝ] Space :=
  Matrix.mulVecLin (Matrix.diagonal ![(1 : ℝ), 2, 3])

/-- An explicit bilinear countermodel `B(u,v) = u cross (M v)`. -/
def countermodelB : Space →ₗ[ℝ] Space →ₗ[ℝ] Space where
  toFun u :=
    { toFun := fun v => u ⨯₃ countermodelM v
      map_add' := by
        intro v w
        simp
      map_smul' := by
        intro c v
        simp }
  map_add' := by
    intro u v
    ext w i
    simp
  map_smul' := by
    intro c u
    ext v i
    simp

/-- The countermodel has the same quadratic energy-cancellation identity. -/
theorem countermodel_energyCancellation (u : Space) :
    u ⬝ᵥ countermodelB u u = 0 := by
  exact dot_self_cross u (countermodelM u)

/-- A concrete vector on which the countermodel self-interaction is nonzero. -/
def countermodelWitness : Space := ![(1 : ℝ), 1, 0]

theorem countermodel_witness_value :
    countermodelB countermodelWitness countermodelWitness = ![(0 : ℝ), 0, 1] := by
  ext i
  fin_cases i <;>
    norm_num [countermodelB, countermodelWitness, countermodelM,
      Matrix.mulVecLin_apply, Matrix.mulVec_diagonal, cross_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Energy cancellation does not force the exact single-mode vanishing property. -/
theorem countermodel_selfInteraction_ne_zero :
    countermodelB countermodelWitness countermodelWitness ≠ 0 := by
  rw [countermodel_witness_value]
  intro h
  have h2 := congrFun h (2 : Fin 3)
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h2

end Navier.Routes.R7
