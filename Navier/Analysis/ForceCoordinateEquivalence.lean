import Navier.Analysis.ForceRecursivePartials

/-!
# Exact force-coordinate equivalence

Fefferman's force hypotheses quantify over ordinary successive time and spatial
coordinate derivatives.  The formal C/D predicates quantify instead over the
operator norm of the full iterated within-Fréchet derivative on the closed
half-space `t ≥ 0`.  This file closes that representation gap for the explicit
ordered-coordinate convention.

The recursive derivative below is the genuine derivative of the previously
obtained function, rather than an alias for a multilinear-map evaluation.
Smoothness identifies it with the corresponding Fréchet jet, and the four
coordinate directions span the faithful spacetime carrier `ℝ × (Fin 3 → ℝ)`.
Consequently, bounds for every ordered coordinate list and output component
are equivalent to bounds for the complete Fréchet bundle.  The reverse
estimate has the explicit basis-expansion factor `4^n` represented as
the cardinality of the set of coordinate lists.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ForceCoordinateEquivalence

open Navier
open Navier.Analysis.ForceCoordinateBridge
open Navier.Analysis.ForceCoordinateDecayBridge
open Navier.Analysis.ForceRecursivePartials
open Navier.Breakdown.OfficialCDEncoding

/-- Rapid Euclidean-space/time decay of every genuine ordered coordinate
partial of a whole-space force.  Smoothness is kept outside this predicate so
the exact regularity needed to compare successive partials with Fréchet jets
remains visible in the equivalence theorem. -/
def WholeSpaceSuccessivePartialDecay (f : ForceField) : Prop :=
  ∀ (n K : ℕ) (axes : Fin n → Option (Fin 3)) (component : Fin 3),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        (1 + euclideanNorm x + t) ^ K *
          |successivePartialWithin (fun z => f z.1 z.2) n
            (fun j => spacetimeCoordinateDirection (axes j)) (t, x) component| ≤ C

/-- Rapid time decay of every genuine ordered coordinate partial of a
spatially periodic force. -/
def PeriodicSuccessivePartialDecay (f : ForceField) : Prop :=
  ∀ (n K : ℕ) (axes : Fin n → Option (Fin 3)) (component : Fin 3),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
        (1 + t) ^ K *
          |successivePartialWithin (fun z => f z.1 z.2) n
            (fun j => spacetimeCoordinateDirection (axes j)) (t, x) component| ≤ C

/-- On the nonnegative-time half-space, genuine successive coordinate
partials of a smooth force are exactly its iterated within-Fréchet derivative
evaluated on the same ordered coordinate directions. -/
theorem successivePartialWithin_coordinateDirections_eq_coordinateDirectional
    {f : ForceField} (hf : SmoothForceOnNonnegativeTime f)
    (n : ℕ) (axes : Fin n → Option (Fin 3))
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    successivePartialWithin (fun z => f z.1 z.2) n
        (fun j => spacetimeCoordinateDirection (axes j)) (t, x) =
      coordinateDirectionalForceDerivativeWithin f n axes t x := by
  rw [successivePartialWithin_eq_iteratedFDerivWithin hf n _
    (z := (t, x)) ⟨ht, Set.mem_univ x⟩]
  rfl

/-- Component form of the exact recursive-partial/Fréchet-jet comparison. -/
theorem successivePartialWithin_coordinateDirections_component_eq
    {f : ForceField} (hf : SmoothForceOnNonnegativeTime f)
    (n : ℕ) (axes : Fin n → Option (Fin 3)) (component : Fin 3)
    (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    successivePartialWithin (fun z => f z.1 z.2) n
        (fun j => spacetimeCoordinateDirection (axes j)) (t, x) component =
      coordinateForceDerivativeWithin f n axes component t x := by
  rw [successivePartialWithin_coordinateDirections_eq_coordinateDirectional
    hf n axes t ht x]
  rfl

/-- A pointwise scalar bound on all genuine ordered coordinate partials
controls the complete iterated Fréchet jet.  The loss is exactly the number of
ordered coordinate words of length `n`, exposed rather than hidden in an
unspecified finite-dimensional equivalence constant. -/
theorem iteratedFDerivWithin_opNorm_le_successivePartialBound
    {f : ForceField} (hf : SmoothForceOnNonnegativeTime f)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Space) (C : ℝ) (hC : 0 ≤ C)
    (hpartials : ∀ (axes : Fin n → Option (Fin 3)) (component : Fin 3),
      |successivePartialWithin (fun z => f z.1 z.2) n
        (fun j => spacetimeCoordinateDirection (axes j)) (t, x) component| ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x)‖ ≤
      (Fintype.card (Fin n → Option (Fin 3)) : ℝ) * C := by
  apply iteratedFDerivWithin_opNorm_le_uniformCoordinateBound f n t x C hC
  intro axes component
  rw [← successivePartialWithin_coordinateDirections_component_eq
    hf n axes component t ht x]
  exact hpartials axes component

/-- Under precisely the smoothness already present in the official force
surface, whole-space bounds on genuine successive partials are equivalent to
the typed coordinate evaluations of the full Fréchet jet. -/
theorem wholeSpaceSuccessivePartialDecay_iff_coordinatewise
    {f : ForceField} (hf : SmoothForceOnNonnegativeTime f) :
    WholeSpaceSuccessivePartialDecay f ↔ WholeSpaceCoordinatewiseForceDecay f := by
  constructor
  · intro h n K axes component
    obtain ⟨C, hC, hbound⟩ := h n K axes component
    refine ⟨C, hC, ?_⟩
    intro t ht x
    rw [← successivePartialWithin_coordinateDirections_component_eq
      hf n axes component t ht x]
    exact hbound t ht x
  · intro h n K axes component
    obtain ⟨C, hC, hbound⟩ := h n K axes component
    refine ⟨C, hC, ?_⟩
    intro t ht x
    rw [successivePartialWithin_coordinateDirections_component_eq
      hf n axes component t ht x]
    exact hbound t ht x

/-- The corresponding exact equivalence for the periodic force decay
surface. -/
theorem periodicSuccessivePartialDecay_iff_coordinatewise
    {f : ForceField} (hf : SmoothForceOnNonnegativeTime f) :
    PeriodicSuccessivePartialDecay f ↔ PeriodicCoordinatewiseForceDecay f := by
  constructor
  · intro h n K axes component
    obtain ⟨C, hC, hbound⟩ := h n K axes component
    refine ⟨C, hC, ?_⟩
    intro t ht x
    rw [← successivePartialWithin_coordinateDirections_component_eq
      hf n axes component t ht x]
    exact hbound t ht x
  · intro h n K axes component
    obtain ⟨C, hC, hbound⟩ := h n K axes component
    refine ⟨C, hC, ?_⟩
    intro t ht x
    rw [successivePartialWithin_coordinateDirections_component_eq
      hf n axes component t ht x]
    exact hbound t ht x

/-- **Whole-space representation theorem.**  The force predicate consumed by
official alternative C is equivalent to half-space smoothness together with
rapid decay of every genuine ordered time/spatial coordinate partial. -/
theorem forcedDataRapidDecay_iff_successivePartials (f : ForceField) :
    ForcedDataRapidDecay f ↔
      SmoothForceOnNonnegativeTime f ∧ WholeSpaceSuccessivePartialDecay f := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    exact (wholeSpaceSuccessivePartialDecay_iff_coordinatewise hf.1).2
      ((forcedDataRapidDecay_iff_typedCoordinatewise f).1 hf).2
  · rintro ⟨hsmooth, hpartials⟩
    apply (forcedDataRapidDecay_iff_typedCoordinatewise f).2
    exact ⟨hsmooth,
      (wholeSpaceSuccessivePartialDecay_iff_coordinatewise hsmooth).1 hpartials⟩

/-- **Periodic representation theorem.**  The force predicate consumed by
official alternative D is equivalent to periodicity, half-space smoothness,
and rapid decay of every genuine ordered time/spatial coordinate partial. -/
theorem periodicForcedDataRapidDecay_iff_successivePartials (f : ForceField) :
    PeriodicForcedDataRapidDecay f ↔
      SpatiallyPeriodicForce f ∧ SmoothForceOnNonnegativeTime f ∧
        PeriodicSuccessivePartialDecay f := by
  constructor
  · intro hf
    have htyped := (periodicForcedDataRapidDecay_iff_typedCoordinatewise f).1 hf
    exact ⟨htyped.1, htyped.2.1,
      (periodicSuccessivePartialDecay_iff_coordinatewise htyped.2.1).2 htyped.2.2⟩
  · rintro ⟨hperiodic, hsmooth, hpartials⟩
    apply (periodicForcedDataRapidDecay_iff_typedCoordinatewise f).2
    exact ⟨hperiodic, hsmooth,
      (periodicSuccessivePartialDecay_iff_coordinatewise hsmooth).1 hpartials⟩

end Navier.Analysis.ForceCoordinateEquivalence

#print axioms Navier.Analysis.ForceCoordinateEquivalence.successivePartialWithin_coordinateDirections_eq_coordinateDirectional
#print axioms Navier.Analysis.ForceCoordinateEquivalence.iteratedFDerivWithin_opNorm_le_successivePartialBound
#print axioms Navier.Analysis.ForceCoordinateEquivalence.forcedDataRapidDecay_iff_successivePartials
#print axioms Navier.Analysis.ForceCoordinateEquivalence.periodicForcedDataRapidDecay_iff_successivePartials
