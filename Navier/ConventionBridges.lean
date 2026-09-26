import Mathlib
import Navier.Problem

/-!
# Convention bridges: Mathlib `SchwartzMap` versus Fefferman clause (4)

`Navier/Problem.lean` represents Fefferman's initial-data class with Mathlib's
`SchwartzMap` (`SchwartzVelocity`). This file records the fidelity bridge
between that convention and Fefferman's clause (4): the initial velocity is
smooth and every derivative decays faster than any prescribed polynomial.

Scope of the predicate: `FeffermanRapidDecayBound` is the Schwartz-seminorm
form `‖x‖^k * ‖iteratedFDeriv ℝ n f x‖ ≤ C` (sup norm on `x`, operator norm on
the derivative bundle) — Mathlib's `SchwartzMap.decay'` field restated, not
Fefferman's literal coordinate form `|∂ₓ^α u°(x)| ≤ C_{αK} (1 + |x|)^{-K}`.
The equivalence of the literal coordinate-partial form with `SchwartzMap`
membership is kernel-checked downstream in grails
(grails file Grails/Audit/NavierStokesSoundness.lean, theorem
feffermanClauseFourLiteral_iff_schwartz, 2026-09-25); the Euclidean-norm variant of this predicate is
`Analysis.EnergyNormBridge.feffermanRapidDecayBound_iff_fullyEuclidean`.

**Closed here (rapid-decay direction).** Mathlib's `SchwartzMap` carrier
satisfies the Schwartz-seminorm rapid-decay bound (clause (4)'s decay
half, in seminorm form): for every polynomial order `k` and every derivative order `n`, the
decay quantity `‖x‖^k * ‖iteratedFDeriv ℝ n f x‖` is uniformly bounded by a
nonnegative constant. This is `SchwartzMap.decay'` restated with an explicit
nonnegative constant. It establishes that the carrier admits only
rapidly-decaying data, which is the safety-relevant half of the bridge.

**Closed here (smoothness direction).** The companion `C^infinity` statement
is Mathlib's `SchwartzMap.smooth'`.  Its regularity index is `∞`, the coerced
top element of `ℕ∞`; Mathlib's distinct `ω` index denotes analytic regularity.

**Converse direction (closed elsewhere).**  The representation from
the seminorm-form conditions to a bundled `SchwartzMap` is proved in
`Navier.Analysis.SchwartzConventionEquivalence`
(`fefferman_clause_four_iff_schwartz`, landed `3c000fd`), which upgrades the
two halves recorded here to the full equivalence — so
the retired schwartzConventionEquivalence residual is no longer open.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.ConventionBridges

open Navier
open scoped ContDiff

/-- Fefferman clause (4) rapid-decay bound: every spatial derivative of `f`
decays faster than every prescribed polynomial. -/
def FeffermanRapidDecayBound (f : Space → Space) : Prop :=
  ∀ (k n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space, ‖x‖^k * ‖iteratedFDeriv ℝ n f x‖ ≤ C

/-- Every Mathlib `SchwartzMap` on `ℝ³` satisfies the seminorm-form rapid-decay
bound. Derived from `SchwartzMap.decay'`. -/
theorem schwartzmap_satisfies_fefferman_rapid_decay (s : SchwartzMap Space Space) :
    FeffermanRapidDecayBound s.toFun := by
  intro k n
  obtain ⟨C, hC⟩ := s.decay' k n
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  exact fun x => le_trans (hC x) (le_max_left _ _)

/-- Every Mathlib `SchwartzMap` on `ℝ³` is smooth as an ordinary function.

This is the smoothness direction of Fefferman clause (4).  The converse
representation theorem from seminorm-form smooth rapid decay to Mathlib's
bundled `SchwartzMap` is proved in `Navier.Analysis.SchwartzConventionEquivalence`
(`fefferman_clause_four_iff_schwartz`); see the module header. -/
theorem schwartzmap_satisfies_fefferman_smoothness (s : SchwartzMap Space Space) :
    ContDiff ℝ ∞ s.toFun := by
  exact s.smooth'

end Navier.ConventionBridges
