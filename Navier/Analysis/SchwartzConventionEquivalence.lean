import Navier.ConventionBridges

/-!
# Schwartz convention equivalence: Fefferman clause (4) realizes `SchwartzMap`

`Navier/ConventionBridges.lean` proved the forward half of the
`schwartzConventionEquivalence` residual: every Mathlib `SchwartzMap` datum is
smooth and satisfies Fefferman's coordinatewise rapid-decay bound.  This file
closes the converse representation: every smooth field satisfying Fefferman's
clause-(4) rapid-decay bound is realized pointwise by a bundled `SchwartzMap`.

Together the two directions give the full equivalence
`(smooth ∧ rapid decay) ↔ (realized by a SchwartzMap)`, so the statement-A
initial-data convention quantifies over exactly the official clause-(4) class.
The final theorem transports statement A itself: if the formal surface holds,
then every coordinatewise-admissible divergence-free datum in Fefferman's
prose class launches a classical solution attaining it.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.SchwartzConventionEquivalence

open Navier
open Navier.ConventionBridges
open scoped ContDiff

/-- Bundle Fefferman clause-(4) data (smoothness plus coordinatewise rapid
decay) into a Mathlib Schwartz velocity. -/
def schwartzOfFeffermanData (f : Space → Space)
    (hs : ContDiff ℝ ∞ f) (hd : FeffermanRapidDecayBound f) :
    SchwartzVelocity where
  toFun := f
  smooth' := hs
  decay' := fun k n => ((hd k n).imp fun _C hC => hC.2)

@[simp] theorem schwartzOfFeffermanData_apply (f : Space → Space)
    (hs : ContDiff ℝ ∞ f) (hd : FeffermanRapidDecayBound f) (x : Space) :
    schwartzOfFeffermanData f hs hd x = f x := rfl

/-- The full `schwartzConventionEquivalence` bridge: a velocity field
satisfies Fefferman's clause (4) iff some bundled Schwartz velocity realizes
it pointwise. -/
theorem fefferman_clause_four_iff_schwartz (f : Space → Space) :
    (ContDiff ℝ ∞ f ∧ FeffermanRapidDecayBound f) ↔
      ∃ s : SchwartzVelocity, ∀ x : Space, s x = f x := by
  constructor
  · rintro ⟨hs, hd⟩
    exact ⟨schwartzOfFeffermanData f hs hd, fun _ => rfl⟩
  · rintro ⟨s, hsf⟩
    have hfun : s.toFun = f := funext hsf
    refine ⟨?_, ?_⟩
    · exact hfun ▸ schwartzmap_satisfies_fefferman_smoothness s
    · exact hfun ▸ schwartzmap_satisfies_fefferman_rapid_decay s

/-- **Divergence-freedom depends only on the pointwise values**: it holds for
ANY Schwartz realization of a divergence-free field, not merely the
definitional bundling.  This is the content-bearing transport lemma — the
realization `s` is an arbitrary Schwartz velocity agreeing with `f`
pointwise, so the derivative-level predicate `staticDivergence` must be
transported through the function-level identification. -/
theorem divergenceFreeInitial_of_realizes {f : Space → Space}
    {s : SchwartzVelocity} (hsf : ∀ x : Space, s x = f x)
    (hdiv : ∀ x : Space, staticDivergence f x = 0) :
    DivergenceFreeInitial s := by
  intro x
  rw [show (fun y => s y) = f from funext hsf]
  exact hdiv x

/-- Divergence freedom transports along the clause-(4) realization.
Specialization of `divergenceFreeInitial_of_realizes` to the definitional
realization `schwartzOfFeffermanData` (whose coercion is `f` by `rfl`). -/
theorem divergenceFreeInitial_schwartzOfFeffermanData
    {f : Space → Space}
    (hs : ContDiff ℝ ∞ f) (hd : FeffermanRapidDecayBound f)
    (hdiv : ∀ x : Space, staticDivergence f x = 0) :
    DivergenceFreeInitial (schwartzOfFeffermanData f hs hd) :=
  divergenceFreeInitial_of_realizes (fun _ => rfl) hdiv

/-- Statement-A coverage of the official clause-(4) class: if the formal
statement-A surface holds, then every smooth, rapidly decaying,
divergence-free datum in Fefferman's coordinatewise prose class launches a
smooth bounded-energy classical solution attaining it at time zero. -/
theorem statementA_covers_fefferman_data (hA : Clay.StatementA)
    (ν : ℝ) (hν : 0 < ν) (f : Space → Space)
    (hs : ContDiff ℝ ∞ f) (hd : FeffermanRapidDecayBound f)
    (hdiv : ∀ x : Space, staticDivergence f x = 0) :
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution ν zeroForce (schwartzOfFeffermanData f hs hd) u p ∧
        ∀ x : Space, u 0 x = f x := by
  obtain ⟨u, p, hup⟩ := hA ν hν (schwartzOfFeffermanData f hs hd)
    (divergenceFreeInitial_schwartzOfFeffermanData hs hd hdiv)
  exact ⟨u, p, hup, fun x => hup.initial_condition x⟩

end Navier.Analysis.SchwartzConventionEquivalence
