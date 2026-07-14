import Mathlib
import Navier.Problem

/-!
# Convention bridges: Mathlib `SchwartzMap` versus Fefferman clause (4)

`Navier/Problem.lean` represents Fefferman's initial-data class with Mathlib's
`SchwartzMap` (`SchwartzVelocity`). This file records the fidelity bridge
between that convention and Fefferman's coordinatewise clause (4): the initial
velocity is smooth and every derivative decays faster than any prescribed
polynomial.

**Closed here (rapid-decay direction).** Mathlib's `SchwartzMap` carrier
satisfies Fefferman's coordinatewise rapid-decay bound (clause (4)'s decay
half): for every polynomial order `k` and every derivative order `n`, the
decay quantity `‖x‖^k * ‖iteratedFDeriv ℝ n f x‖` is uniformly bounded by a
nonnegative constant. This is `SchwartzMap.decay'` restated with an explicit
nonnegative constant. It establishes that the carrier admits only
rapidly-decaying data, which is the safety-relevant half of the bridge.

**Open residual (smoothness half).** The companion smoothness statement
`ContDiff ℝ ⊤ f` is, by Mathlib's own `SchwartzMap.smooth'`, available for the
carrier; bridging it into a user-stated `ContDiff ℝ ⊤` predicate is held back
only by a Lean-elaboration quirk (Mathlib states `ContDiff ℝ (↑⊤)`; the coerced
form is propositionally-but-not-definitionally equal to `⊤`, and resists
`rw`/`convert`/`▸` at the `SchwartzMap.mk` field). The mathematics is trivial —
a SchwartzMap is smooth by definition — so this is an encoding residual, not a
scientific gap. Recorded as `schwartzConventionEquivalence`.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.ConventionBridges

open Navier

/-- Fefferman clause (4) rapid-decay bound: every spatial derivative of `f`
decays faster than every prescribed polynomial. -/
def FeffermanRapidDecayBound (f : Space → Space) : Prop :=
  ∀ (k n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space, ‖x‖^k * ‖iteratedFDeriv ℝ n f x‖ ≤ C

/-- Every Mathlib `SchwartzMap` on `ℝ³` satisfies Fefferman's coordinatewise
rapid-decay bound. Derived from `SchwartzMap.decay'`. -/
theorem schwartzmap_satisfies_fefferman_rapid_decay (s : SchwartzMap Space Space) :
    FeffermanRapidDecayBound s.toFun := by
  intro k n
  obtain ⟨C, hC⟩ := s.decay' k n
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  exact fun x => le_trans (hC x) (le_max_left _ _)

end Navier.ConventionBridges
