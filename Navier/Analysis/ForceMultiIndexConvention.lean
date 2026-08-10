import Navier.Analysis.ForceCoordinateDecayBridge

/-!
# A typed finite multi-index convention for force derivatives

This module gives a small formal syntax for an **ordered** spacetime
multi-index: every slot is either the time coordinate or one of the three
spatial coordinates.  It is intentionally a typed convention adapter only.
No claim is made here that Fefferman's prose fixes this ordering convention or
that mixed partials have been identified with a different syntactic API.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ForceMultiIndexConvention

open Navier
open Navier.Breakdown.OfficialCDEncoding

/-- One coordinate in the formal spacetime multi-index syntax. -/
inductive SpacetimeCoordinate
  | time
  | space (i : Fin 3)
  deriving DecidableEq, Repr

/-- Translation from the explicit syntax to the existing time/spatial-axis
encoding used by `OfficialCDEncoding`. -/
def SpacetimeCoordinate.toAxis : SpacetimeCoordinate → Option (Fin 3)
  | .time => none
  | .space i => some i

/-- An ordered finite spacetime multi-index of total order `n`.  The order is
retained because the current iterated Fréchet API is indexed by `Fin n`. -/
abbrev OrderedSpacetimeMultiIndex (n : ℕ) := Fin n → SpacetimeCoordinate

/-- The coordinate direction selected by an ordered multi-index slot. -/
def OrderedSpacetimeMultiIndex.direction
    {n : ℕ} (α : OrderedSpacetimeMultiIndex n) : Fin n → ℝ × Space :=
  fun j => spacetimeCoordinateDirection (α j).toAxis

/-- The explicit ordered-multi-index iterated within-Fréchet derivative of a
force field. -/
def iteratedCoordinateDerivativeWithin
    (f : ForceField) (n : ℕ) (α : OrderedSpacetimeMultiIndex n)
    (t : ℝ) (x : Space) : Space :=
  (iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
    nonnegativeSpacetime (t, x)) α.direction

/-- The explicit multi-index derivative is exactly the existing coordinate
directional evaluation after translating its finite syntax. -/
theorem iteratedCoordinateDerivativeWithin_eq_coordinateDirectional
    (f : ForceField) (n : ℕ) (α : OrderedSpacetimeMultiIndex n)
    (t : ℝ) (x : Space) :
    iteratedCoordinateDerivativeWithin f n α t x =
      coordinateDirectionalForceDerivativeWithin f n
        (fun j => (α j).toAxis) t x := rfl

/-- Componentwise explicit multi-index derivatives agree with the existing
scalar coordinate evaluations. -/
theorem iteratedCoordinateDerivativeWithin_component_eq_coordinateForceDerivative
    (f : ForceField) (n : ℕ) (α : OrderedSpacetimeMultiIndex n)
    (component : Fin 3) (t : ℝ) (x : Space) :
    iteratedCoordinateDerivativeWithin f n α t x component =
      coordinateForceDerivativeWithin f n (fun j => (α j).toAxis)
        component t x := rfl

/-- Translation of an explicit ordered multi-index is a valid current axis
family, so the existing coordinatewise bounds consume it directly. -/
theorem wholeSpaceCoordinatewise_bound_orderedMultiIndex
    {f : ForceField} (hf : WholeSpaceCoordinatewiseForceDecay f)
    (n K : ℕ) (α : OrderedSpacetimeMultiIndex n) (component : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      (1 + euclideanNorm x + t) ^ K *
        |iteratedCoordinateDerivativeWithin f n α t x component| ≤ C := by
  simpa only [iteratedCoordinateDerivativeWithin_component_eq_coordinateForceDerivative]
    using hf n K (fun j => (α j).toAxis) component

/-- Likewise, periodic typed-coordinate decay consumes every explicit ordered
multi-index. -/
theorem periodicCoordinatewise_bound_orderedMultiIndex
    {f : ForceField} (hf : PeriodicCoordinatewiseForceDecay f)
    (n K : ℕ) (α : OrderedSpacetimeMultiIndex n) (component : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      (1 + t) ^ K * |iteratedCoordinateDerivativeWithin f n α t x component| ≤ C := by
  simpa only [iteratedCoordinateDerivativeWithin_component_eq_coordinateForceDerivative]
    using hf n K (fun j => (α j).toAxis) component

end Navier.Analysis.ForceMultiIndexConvention
