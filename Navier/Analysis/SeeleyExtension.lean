import Navier.Analysis.HalfSpaceSmoothnessBridge

/-!
# Seeley extension (ladder rung 2 skeleton)

`HalfSpaceSmoothnessBridge` reduced the open direction of the
`halfSpaceSmoothnessEquivalence` encoding residual to the single named
classical property `SeeleyExtensionProperty`: every within-smooth field on
the closed nonnegative-time half-space is the restriction of a globally
smooth spacetime field.  This file turns that named property into a
compiler-visible obligation.

**[SKELETON — R. T. Seeley, *Extension of C^∞ functions defined in a half
space*, Proc. Amer. Math. Soc. 15 (1964) 625–626; est ~600 LOC.]**
Closure route (Seeley's reflection series): choose `bₖ = 2^k` and weights
`aₖ` with `∑ₖ aₖ (−bₖ)^n = 1` for every `n` (an infinite Vandermonde system
with rapidly decaying solution), set

  `E g(t, x) = ∑ₖ aₖ · φ(−bₖ t) · g(−bₖ t, x)`  for `t < 0`

with a smooth cutoff `φ`; every iterated derivative converges uniformly and
matches the within-derivatives at `t = 0`.  Mathlib-absent: the weighted
reflection series and its derivative-wise uniform convergence.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.HalfSpaceSmoothnessBridge

/-- **[SKELETON — Seeley 1964; est ~600 LOC; route in the module docstring.]**
The Seeley extension property holds: within-smooth fields on the closed
half-space extend to globally smooth fields.  Together with
`halfSpaceSmooth_iff_extension_of_seeley` this closes the open direction of
the `halfSpaceSmoothnessEquivalence` encoding residual. -/
theorem seeleyExtensionProperty_holds : SeeleyExtensionProperty := by
  sorry

/-- With the Seeley skeleton in place, the half-space equivalence is available
as a consumable (conditional on the skeleton's `sorryAx`, disclosed): a field
is within-smooth on the closed half-space iff it is the restriction of a
globally smooth spacetime field. -/
theorem halfSpaceSmooth_iff_extension
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') :
    HalfSpaceSmooth g ↔ Nonempty (HalfSpaceSmoothExtension g) :=
  halfSpaceSmooth_iff_extension_of_seeley seeleyExtensionProperty_holds g

end Navier.Analysis.HalfSpaceSmoothnessBridge
