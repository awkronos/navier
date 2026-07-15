import Navier.Analysis.CriticalL3

/-!
# Integrability-faithful scale-critical `L^3` bounds

`CriticalL3.criticalL3Mass` is a useful raw change-of-variables functional, but
Mathlib defines the integral of a nonintegrable function to be zero.  A mass
inequality alone therefore does not assert that a spatial slice genuinely has
finite `L^3` mass.

This module repairs the bound interface by requiring integrability of the
scalar mass density `x ↦ ‖u(t,x)‖^3` at every selected time, in addition to a
nonnegative uniform bound.  Positive parabolic scaling preserves and reflects
that integrability by the Haar-measure dilation equivalence; combining it with
the existing mass identity proves exact covariance on arbitrary time sets and
finite half-open time intervals.

These are representation/transport theorems.  They do not produce a critical
bound for any Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.CriticalL3Integrable

open Navier
open Navier.Analysis.Covariance
open Navier.Analysis.CriticalL3

/-- A spatial time slice has a genuinely integrable cubic norm density.  This
explicit condition rules out the zero-by-convention value of a nonintegrable
Bochner integral. -/
def L3SliceIntegrable (u : VelocityEvolution) (t : ℝ) : Prop :=
  Integrable (fun x : Space => ‖u t x‖ ^ 3) volume

/-- A nonnegative uniform critical `L^3` mass bound whose every selected time
slice is explicitly integrable. -/
def IntegrableCriticalL3BoundOn
    (u : VelocityEvolution) (times : Set ℝ) (M : ℝ) : Prop :=
  0 ≤ M ∧
    ∀ t ∈ times,
      L3SliceIntegrable u t ∧ criticalL3Mass u t ≤ M

/-- The repaired bound contract projects to the earlier raw mass-bound
contract.  The converse is intentionally absent because a raw integral bound
does not imply integrability. -/
theorem integrableCriticalL3BoundOn_to_raw
    {u : VelocityEvolution} {times : Set ℝ} {M : ℝ}
    (h : IntegrableCriticalL3BoundOn u times M) :
    CriticalL3BoundOn u times M := by
  intro t ht
  exact (h.2 t ht).2

/-- Positive parabolic scaling preserves and reflects genuine integrability
of the cubic norm density on each corresponding spatial slice. -/
theorem l3SliceIntegrable_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (t : ℝ) :
    L3SliceIntegrable (parabolicScaledVelocity lambda u) t ↔
      L3SliceIntegrable u (lambda ^ 2 * t) := by
  let g : Space → ℝ := fun y => ‖u (lambda ^ 2 * t) y‖ ^ 3
  calc
    L3SliceIntegrable (parabolicScaledVelocity lambda u) t ↔
        Integrable (fun x : Space => lambda ^ 3 * g (lambda • x)) volume := by
      simp only [L3SliceIntegrable, parabolicScaledVelocity, norm_smul,
        Real.norm_eq_abs, abs_of_pos hLambda, mul_pow, g]
    _ ↔ Integrable (fun x : Space => g (lambda • x)) volume :=
      integrable_const_mul_iff
        (isUnit_iff_ne_zero.mpr (pow_ne_zero 3 hLambda.ne')) _
    _ ↔ Integrable g volume :=
      integrable_comp_smul_iff volume g hLambda.ne'
    _ ↔ L3SliceIntegrable u (lambda ^ 2 * t) := by
      rfl

/-- The integrability-faithful critical bound is exactly covariant when the
time set is transported by parabolic dilation. -/
theorem integrableCriticalL3BoundOn_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (times : Set ℝ) (M : ℝ) :
    IntegrableCriticalL3BoundOn
        (parabolicScaledVelocity lambda u) times M ↔
      IntegrableCriticalL3BoundOn u
        ((fun t : ℝ => lambda ^ 2 * t) '' times) M := by
  constructor
  · rintro ⟨hM, h⟩
    refine ⟨hM, ?_⟩
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    have hAt := h t ht
    constructor
    · exact
        (l3SliceIntegrable_parabolicScaled_iff lambda hLambda u t).mp hAt.1
    · rw [← criticalL3Mass_parabolicScaled lambda hLambda u t]
      exact hAt.2
  · rintro ⟨hM, h⟩
    refine ⟨hM, ?_⟩
    intro t ht
    have hAt := h (lambda ^ 2 * t) ⟨t, ht, rfl⟩
    constructor
    · exact
        (l3SliceIntegrable_parabolicScaled_iff lambda hLambda u t).mpr hAt.1
    · rw [criticalL3Mass_parabolicScaled lambda hLambda u t]
      exact hAt.2

/-- Integrability-faithful uniform critical control before a finite time is
invariant under positive parabolic scaling, with the endpoint time rescaled by
`lambda^2`. -/
theorem integrableCriticalL3BoundBefore_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (T M : ℝ) :
    IntegrableCriticalL3BoundOn
        (parabolicScaledVelocity lambda u) (Set.Ico 0 T) M ↔
      IntegrableCriticalL3BoundOn
        u (Set.Ico 0 (lambda ^ 2 * T)) M := by
  rw [integrableCriticalL3BoundOn_parabolicScaled_iff lambda hLambda]
  rw [time_dilation_image_Ico lambda T hLambda]

end Navier.Analysis.CriticalL3Integrable
