import Navier.Analysis.Covariance
import Navier.EnergyObstruction

/-!
# Scale-critical `L^3` mass on finite time intervals

This module turns the previously separate spatial `L^3` change-of-variables
identity and pointwise parabolic field scaling into a nested-in-time critical
bound interface.  The functional is the integral of the third norm power,
rather than its cube root; boundedness is equivalent because the cube root is
monotone on nonnegative reals.

The final theorem proves that a uniform critical `L^3`-mass bound before time
`T` is exactly invariant when both the velocity and its time interval are
parabolically rescaled.  It does not establish such a bound for solutions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.CriticalL3

open Navier
open Navier.Analysis.Covariance
open Navier.EnergyObstruction

/-- The spatial integral of the third power of the velocity norm at time `t`.
This is the cube of the usual `L^3` norm whenever the field is in `L^3`. -/
def criticalL3Mass (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, ‖u t x‖ ^ 3

/-- A uniform bound for the critical `L^3` mass on an explicit set of times. -/
def CriticalL3BoundOn
    (u : VelocityEvolution) (times : Set ℝ) (M : ℝ) : Prop :=
  ∀ t ∈ times, criticalL3Mass u t ≤ M

/-- At each time, parabolic velocity scaling transports the critical `L^3`
mass to the corresponding scaled time without changing its value. -/
theorem criticalL3Mass_parabolicScaled
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (t : ℝ) :
    criticalL3Mass (parabolicScaledVelocity lambda u) t =
      criticalL3Mass u (lambda ^ 2 * t) := by
  exact l3_critical_dilation lambda hLambda (u (lambda ^ 2 * t))

/-- A critical bound on arbitrary times is equivalent to the same bound on
their image under parabolic time dilation. -/
theorem criticalL3BoundOn_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (times : Set ℝ) (M : ℝ) :
    CriticalL3BoundOn (parabolicScaledVelocity lambda u) times M ↔
      CriticalL3BoundOn u ((fun t : ℝ => lambda ^ 2 * t) '' times) M := by
  constructor
  · intro h s hs
    rcases hs with ⟨t, ht, rfl⟩
    rw [← criticalL3Mass_parabolicScaled lambda hLambda u t]
    exact h t ht
  · intro h t ht
    rw [criticalL3Mass_parabolicScaled lambda hLambda u t]
    exact h (lambda ^ 2 * t) ⟨t, ht, rfl⟩

/-- Positive parabolic time dilation maps `[0,T)` exactly onto
`[0,lambda^2*T)`. -/
theorem time_dilation_image_Ico
    (lambda T : ℝ) (hLambda : 0 < lambda) :
    (fun t : ℝ => lambda ^ 2 * t) '' Set.Ico 0 T =
      Set.Ico 0 (lambda ^ 2 * T) := by
  ext s
  constructor
  · rintro ⟨t, ⟨ht0, htT⟩, rfl⟩
    constructor
    · exact mul_nonneg (sq_nonneg lambda) ht0
    · exact mul_lt_mul_of_pos_left htT (sq_pos_of_pos hLambda)
  · intro hs
    have hsq : 0 < lambda ^ 2 := sq_pos_of_pos hLambda
    refine ⟨s / lambda ^ 2, ?_, ?_⟩
    · constructor
      · exact div_nonneg hs.1 hsq.le
      · apply (div_lt_iff₀ hsq).2
        simpa [mul_comm] using hs.2
    · field_simp

/-- Uniform critical `L^3` control before a finite time is invariant under the
full parabolic scaling, including the required rescaling of the time interval.

This is a representation/transport theorem.  Its two sides both assume the
critical bound; it does not produce the unconditional estimate required for
global regularity. -/
theorem criticalL3BoundBefore_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (T M : ℝ) :
    CriticalL3BoundOn (parabolicScaledVelocity lambda u) (Set.Ico 0 T) M ↔
      CriticalL3BoundOn u (Set.Ico 0 (lambda ^ 2 * T)) M := by
  rw [criticalL3BoundOn_parabolicScaled_iff lambda hLambda]
  rw [time_dilation_image_Ico lambda T hLambda]

end Navier.Analysis.CriticalL3
