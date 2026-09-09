import Navier.Problem
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# A smooth polynomial fold of a complex zero set

This module studies the explicit complex field

`psi(t,x,y) = (x^2 - t) + i y`.

Its zero set is empty for `t < 0`, consists of the degenerate origin at
`t = 0`, and consists of two regular zeros for `t > 0`.  The real Jacobian of
`(re psi, im psi)` is `diag(2x,1)`, so the two positive-time zeros have
opposite determinant signs.

This is a kinematic polynomial example.  No theorem here says that `psi`
solves Gross--Pitaevskii, Schrödinger, Navier--Stokes, or any other evolution
equation.  It demonstrates only that a jointly smooth finite complex field
can change the topology of its zero set through a derivative degeneracy,
without a singularity of the field itself.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff Matrix

namespace Navier.Analysis.QuantumVortexTopologyChange

/-- The physical plane used by the explicit example. -/
abbrev Plane := ℝ × ℝ

/-- The real two-component map `(re psi, im psi)`. -/
def realFold (t : ℝ) (z : Plane) : Plane :=
  (z.1 * z.1 - t, z.2)

/-- `psi(t,x,y) = (x^2-t) + i y`. -/
def foldWave (t : ℝ) (z : Plane) : ℂ :=
  Complex.equivRealProdCLM.symm (realFold t z)

@[simp] theorem foldWave_re (t : ℝ) (z : Plane) :
    (foldWave t z).re = z.1 ^ 2 - t := by
  simp [foldWave, realFold, pow_two]

@[simp] theorem foldWave_im (t : ℝ) (z : Plane) :
    (foldWave t z).im = z.2 := by
  simp [foldWave, realFold]

/-- Exact zero equations for the complex polynomial. -/
theorem foldWave_eq_zero_iff (t : ℝ) (z : Plane) :
    foldWave t z = 0 ↔ z.1 ^ 2 = t ∧ z.2 = 0 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    constructor
    · simpa [foldWave, realFold, pow_two] using sub_eq_zero.mp hre
    · simpa [foldWave, realFold] using him
  · rintro ⟨hx, hy⟩
    apply Complex.ext
    · simpa [foldWave, realFold, pow_two] using sub_eq_zero.mpr hx
    · simp [foldWave, realFold, hy]

/-- The field has no zero before the fold time. -/
theorem no_zero_of_negative_time {t : ℝ} (ht : t < 0) :
    ¬ ∃ z : Plane, foldWave t z = 0 := by
  rintro ⟨z, hz⟩
  have hs := (foldWave_eq_zero_iff t z).mp hz |>.1
  nlinarith [sq_nonneg z.1]

/-- At the fold time, the origin is the unique zero. -/
theorem zero_at_time_zero_iff (z : Plane) :
    foldWave 0 z = 0 ↔ z = (0, 0) := by
  rw [foldWave_eq_zero_iff]
  constructor
  · rintro ⟨hx, hy⟩
    have hx0 : z.1 = 0 := sq_eq_zero_iff.mp hx
    exact Prod.ext hx0 hy
  · rintro rfl
    simp

/-- At positive time there are exactly two zeros, at `x = ±sqrt(t)` and
`y = 0`. -/
theorem zero_of_positive_time_iff {t : ℝ} (ht : 0 < t) (z : Plane) :
    foldWave t z = 0 ↔
      z = (Real.sqrt t, 0) ∨ z = (-Real.sqrt t, 0) := by
  rw [foldWave_eq_zero_iff]
  have hsqrt : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  constructor
  · rintro ⟨hx, hy⟩
    have hsq : z.1 ^ 2 = Real.sqrt t ^ 2 := hx.trans hsqrt.symm
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hpos | hneg
    · exact Or.inl (Prod.ext hpos hy)
    · exact Or.inr (Prod.ext hneg hy)
  · rintro (rfl | rfl)
    · exact ⟨hsqrt, rfl⟩
    · exact ⟨by simpa using hsqrt, rfl⟩

/-- The complex field is jointly smooth in time and both spatial variables. -/
theorem foldWave_joint_contDiff :
    ContDiff ℝ ∞ (fun q : ℝ × Plane => foldWave q.1 q.2) := by
  apply Complex.equivRealProdCLM.symm.contDiff.comp
  unfold realFold
  fun_prop

/-- The real representation is jointly smooth as well. -/
theorem realFold_joint_contDiff :
    ContDiff ℝ ∞ (fun q : ℝ × Plane => realFold q.1 q.2) := by
  unfold realFold
  fun_prop

/-- The actual Fréchet derivative of `(x,y) |-> (x^2-t,y)`. -/
def realFoldDerivative (z : Plane) : Plane →L[ℝ] Plane :=
  (z.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      z.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

theorem hasFDerivAt_realFold (t : ℝ) (z : Plane) :
    HasFDerivAt (realFold t) (realFoldDerivative z) z := by
  have hx := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).mul
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hx' := hx.sub_const t
  have hy := hasFDerivAt_snd (𝕜 := ℝ) (p := z)
  change HasFDerivAt (fun w : ℝ × ℝ => (w.1 * w.1 - t, w.2))
    (realFoldDerivative z) z
  exact hx'.prodMk hy

/-- The coordinate matrix of the preceding derivative. -/
def realFoldJacobian (z : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * z.1, 0;
     0,       1]

/-- The first Jacobian column agrees with the Fréchet derivative applied to
the first coordinate basis vector. -/
theorem realFoldDerivative_apply_ex (z : Plane) :
    realFoldDerivative z (1, 0) = (2 * z.1, 0) := by
  simp [realFoldDerivative]
  ring

/-- The second Jacobian column agrees with the Fréchet derivative applied to
the second coordinate basis vector. -/
theorem realFoldDerivative_apply_ey (z : Plane) :
    realFoldDerivative z (0, 1) = (0, 1) := by
  simp [realFoldDerivative]

/-- The native two-dimensional determinant is exactly `2x`. -/
theorem det_realFoldJacobian (z : Plane) :
    (realFoldJacobian z).det = 2 * z.1 := by
  rw [Matrix.det_fin_two]
  simp [realFoldJacobian]

/-- The unique zero at the fold time is derivative-degenerate. -/
theorem fold_zero_derivative_degenerate :
    (realFoldJacobian (0, 0)).det = 0 := by
  simp [det_realFoldJacobian]

/-- The positive-root zero has positive orientation. -/
theorem positive_root_determinant_pos {t : ℝ} (ht : 0 < t) :
    0 < (realFoldJacobian (Real.sqrt t, 0)).det := by
  rw [det_realFoldJacobian]
  positivity

/-- The negative-root zero has negative orientation. -/
theorem negative_root_determinant_neg {t : ℝ} (ht : 0 < t) :
    (realFoldJacobian (-Real.sqrt t, 0)).det <  0 := by
  rw [det_realFoldJacobian]
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  linarith

/-- Consequently both positive-time zeros are regular and have opposite
orientation signs. -/
theorem positive_time_roots_regular_opposite_orientation
    {t : ℝ} (ht : 0 < t) :
    (realFoldJacobian (Real.sqrt t, 0)).det ≠ 0 ∧
    (realFoldJacobian (-Real.sqrt t, 0)).det ≠ 0 ∧
    (realFoldJacobian (Real.sqrt t, 0)).det =
      -(realFoldJacobian (-Real.sqrt t, 0)).det := by
  have hp := positive_root_determinant_pos ht
  have hn := negative_root_determinant_neg ht
  refine ⟨hp.ne', hn.ne, ?_⟩
  simp [det_realFoldJacobian]

end Navier.Analysis.QuantumVortexTopologyChange

#print axioms Navier.Analysis.QuantumVortexTopologyChange.foldWave_eq_zero_iff
#print axioms Navier.Analysis.QuantumVortexTopologyChange.no_zero_of_negative_time
#print axioms Navier.Analysis.QuantumVortexTopologyChange.zero_at_time_zero_iff
#print axioms Navier.Analysis.QuantumVortexTopologyChange.zero_of_positive_time_iff
#print axioms Navier.Analysis.QuantumVortexTopologyChange.foldWave_joint_contDiff
#print axioms Navier.Analysis.QuantumVortexTopologyChange.hasFDerivAt_realFold
#print axioms Navier.Analysis.QuantumVortexTopologyChange.det_realFoldJacobian
#print axioms Navier.Analysis.QuantumVortexTopologyChange.positive_time_roots_regular_opposite_orientation
