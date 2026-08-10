import Navier.Breakdown.OfficialCDEncoding

/-!
# Coordinate expansion for force derivatives

Fefferman's force clauses are written using the time direction and the three
spatial coordinate directions.  `OfficialCDEncoding` defines the corresponding
evaluations of the total within-Fréchet derivative.  This file supplies the
finite-dimensional algebraic converse: those four directions span every
spacetime slot, hence their iterated evaluations determine the total bundle.

This is only a coordinate-expansion fact.  It neither assumes a terminal norm
bound nor changes the norm used by an existing force predicate.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Analysis.ForceCoordinateBridge

open Navier
open Navier.Breakdown.OfficialCDEncoding

/-- The coefficient of a spacetime vector in one of Fefferman's four
coordinate directions. -/
def spacetimeCoordinateCoefficient (z : ℝ × Space) : Option (Fin 3) → ℝ
  | none => z.1
  | some i => z.2 i

/-- A spacetime vector is the sum of its time and spatial coordinate parts. -/
theorem spacetime_eq_sum_coordinateDirections (z : ℝ × Space) :
    z = ∑ a : Option (Fin 3),
      spacetimeCoordinateCoefficient z a • spacetimeCoordinateDirection a := by
  rcases z with ⟨s, x⟩
  have hx : x = ∑ i : Fin 3, x i • basisVector i := by
    simpa only [basisVector] using (pi_eq_sum_univ' x)
  rw [Fintype.sum_option]
  ext
  · simp [spacetimeCoordinateCoefficient, spacetimeCoordinateDirection,
      Prod.fst_sum, Prod.smul_mk]
  · simpa [spacetimeCoordinateCoefficient, spacetimeCoordinateDirection,
      Prod.snd_sum, Prod.smul_mk] using congrFun hx _

/-- A continuous multilinear map on spacetime slots is reconstructed from its
values on the time/spatial coordinate directions. -/
theorem continuousMultilinearMap_apply_eq_sum_coordinateDirections
    (n : ℕ)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × Space) Space)
    (v : Fin n → ℝ × Space) :
    L v = ∑ axes : Fin n → Option (Fin 3),
      (∏ j, spacetimeCoordinateCoefficient (v j) (axes j)) •
        L (fun j => spacetimeCoordinateDirection (axes j)) := by
  calc
    L v = L (fun j => ∑ a : Option (Fin 3),
        spacetimeCoordinateCoefficient (v j) a • spacetimeCoordinateDirection a) := by
          congr 1
          funext j
          rw [← spacetime_eq_sum_coordinateDirections]
    _ = ∑ axes : Fin n → Option (Fin 3),
        L (fun j => spacetimeCoordinateCoefficient (v j) (axes j) •
          spacetimeCoordinateDirection (axes j)) := by
          exact L.map_sum (fun j a =>
            spacetimeCoordinateCoefficient (v j) a • spacetimeCoordinateDirection a)
    _ = ∑ axes : Fin n → Option (Fin 3),
        (∏ j, spacetimeCoordinateCoefficient (v j) (axes j)) •
          L (fun j => spacetimeCoordinateDirection (axes j)) := by
          apply Finset.sum_congr rfl
          intro axes _
          rw [L.map_smul_univ]

/-- The value of an iterated within-Fréchet derivative on an arbitrary
spacetime list is an explicit finite combination of Fefferman's mixed
time/spatial coordinate evaluations. -/
theorem iteratedFDerivWithin_apply_eq_sum_coordinateDirections
    (f : ForceField) (n : ℕ) (t : ℝ) (x : Space) (v : Fin n → ℝ × Space) :
    (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x)) v =
      ∑ axes : Fin n → Option (Fin 3),
        (∏ j, spacetimeCoordinateCoefficient (v j) (axes j)) •
          coordinateDirectionalForceDerivativeWithin f n axes t x := by
  exact continuousMultilinearMap_apply_eq_sum_coordinateDirections n
    (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x)) v

/-- **Consumer smoke theorem for the force Fréchet/coordinate residual.**
At a fixed nonnegative-spacetime point, all scalar mixed coordinate
evaluations being zero forces the complete iterated within-Fréchet derivative
bundle to be zero.  Thus the coordinate family is genuinely determining; the
remaining residual concerns quantitative decay constants and the comparison
with Fefferman's textual partial-derivative convention. -/
theorem iteratedFDerivWithin_eq_zero_of_coordinateForceDerivativeWithin_eq_zero
    (f : ForceField) (n : ℕ) (t : ℝ) (x : Space)
    (hzero : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      coordinateForceDerivativeWithin f n axes component t x = 0) :
    iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x) = 0 := by
  ext v
  rw [iteratedFDerivWithin_apply_eq_sum_coordinateDirections]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_eq_zero
  intro axes _
  rw [show coordinateDirectionalForceDerivativeWithin f n axes t x _ = 0 by
    exact hzero axes _]
  simp

end Navier.Analysis.ForceCoordinateBridge
