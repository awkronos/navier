import Navier.Analysis.ForceMultiIndexConvention

/-!
# Order sensitivity in the raw multilinear derivative representation

The ordered coordinate adapter evaluates an arbitrary continuous multilinear
map on a list of spacetime directions.  Such a map is not automatically
symmetric: the explicit witness below distinguishes the time-then-space and
space-then-time orders.

This is a falsifier for the route that tries to erase ordering using only the
multilinear representation API.  It is not a counterexample to equality of
mixed partials for a smooth force.  Retiring the official
`forceFrechetCoordinatewiseEquivalence` residual still requires a theorem
that actual iterated derivatives of a smooth force are invariant under slot
permutations, followed by comparison with the intended textual multi-index
convention.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ForceMultiIndexObstruction

open Navier
open Navier.Breakdown.OfficialCDEncoding

/-- The bilinear form `(u, v) ↦ u.time * v.space₀`, before continuity is
bundled. -/
def orderSensitiveBilinearLinear :
    (ℝ × Space) →ₗ[ℝ] (ℝ × Space) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => u.1 * v.2 0)
    (by intros; simp [add_mul])
    (by intros; simp only [Prod.smul_fst, smul_eq_mul]; ring)
    (by intros; simp only [Prod.snd_add, Pi.add_apply]; ring)
    (by intros; simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; ring)

/-- A continuous order-sensitive bilinear form on spacetime directions. -/
def orderSensitiveBilinear :
    (ℝ × Space) →L[ℝ] (ℝ × Space) →L[ℝ] ℝ :=
  orderSensitiveBilinearLinear.mkContinuous₂ 1 (by
    intro u v
    simp only [orderSensitiveBilinearLinear, LinearMap.mk₂_apply, one_mul,
      Real.norm_eq_abs]
    calc
      |u.1 * v.2 0| = |u.1| * |v.2 0| := abs_mul _ _
      _ ≤ ‖u‖ * ‖v‖ := mul_le_mul
        (by simpa only [Real.norm_eq_abs] using norm_fst_le u)
        ((norm_le_pi_norm v.2 0).trans (norm_snd_le v))
        (abs_nonneg _) (norm_nonneg _))

/-- The same witness in the exact `Fin 2` continuous-multilinear
representation used by second Fréchet derivatives. -/
def orderSensitiveSecondOrderForm :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ × Space) ℝ :=
  ContinuousLinearMap.uncurryLeft
    ((continuousMultilinearCurryFin1 ℝ (ℝ × Space) ℝ).symm.toContinuousLinearMap.comp
      orderSensitiveBilinear)

/-- Evaluating time first and spatial coordinate zero second gives one. -/
theorem orderSensitiveSecondOrderForm_time_space :
    orderSensitiveSecondOrderForm ![
        spacetimeCoordinateDirection none,
        spacetimeCoordinateDirection (some 0)] = 1 := by
  norm_num [orderSensitiveSecondOrderForm, orderSensitiveBilinear,
    orderSensitiveBilinearLinear, spacetimeCoordinateDirection, basisVector,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Evaluating the same two directions in the opposite order gives zero. -/
theorem orderSensitiveSecondOrderForm_space_time :
    orderSensitiveSecondOrderForm ![
        spacetimeCoordinateDirection (some 0),
        spacetimeCoordinateDirection none] = 0 := by
  norm_num [orderSensitiveSecondOrderForm, orderSensitiveBilinear,
    orderSensitiveBilinearLinear, spacetimeCoordinateDirection, basisVector,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Continuous multilinearity alone cannot justify forgetting the ordering of
the time and space-zero derivative slots. -/
theorem continuousMultilinearMap_not_automatically_permutationInvariant :
    ¬ ∀ L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℝ × Space) ℝ,
      L ![spacetimeCoordinateDirection none,
          spacetimeCoordinateDirection (some 0)] =
        L ![spacetimeCoordinateDirection (some 0),
            spacetimeCoordinateDirection none] := by
  intro h
  have hfalse := h orderSensitiveSecondOrderForm
  rw [orderSensitiveSecondOrderForm_time_space,
    orderSensitiveSecondOrderForm_space_time] at hfalse
  norm_num at hfalse

end Navier.Analysis.ForceMultiIndexObstruction
