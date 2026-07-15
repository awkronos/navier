import Navier.Breakdown.MaximalNonextension

/-!
# Restriction laws for partial classical solutions

This file supplies the interval-restriction layer needed before restart,
overlap uniqueness, or maximal gluing can be stated faithfully.  Restriction
does not extend a solution and carries no continuation or global-regularity
assumption.
-/

set_option autoImplicit false

open scoped ContDiff

namespace Navier.Breakdown

/-- Half-open spacetime regions are monotone in their terminal time. -/
theorem spacetimeBefore_mono {S T : ℝ} (hST : S ≤ T) :
    spacetimeBefore S ⊆ spacetimeBefore T := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  exact ⟨⟨ht.1, ht.2.trans_le hST⟩, hx⟩

/-- Restrict a partial classical solution to any shorter genuine interval. -/
def PartialClassicalSolution.restrict
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {S T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (hS : 0 < S) (hST : S ≤ T) :
    PartialClassicalSolution ν f u₀ S where
  terminalTime_pos := hS
  velocity := sol.velocity
  pressure := sol.pressure
  velocity_smooth := sol.velocity_smooth.mono (spacetimeBefore_mono hST)
  pressure_smooth := sol.pressure_smooth.mono (spacetimeBefore_mono hST)
  initial_condition := sol.initial_condition
  incompressible t ht0 htS x :=
    sol.incompressible t ht0 (htS.trans_le hST) x
  equation t ht0 htS x := sol.equation t ht0 (htS.trans_le hST) x

@[simp] theorem PartialClassicalSolution.restrict_velocity
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {S T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (hS : 0 < S) (hST : S ≤ T) :
    (sol.restrict hS hST).velocity = sol.velocity := rfl

@[simp] theorem PartialClassicalSolution.restrict_pressure
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {S T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (hS : 0 < S) (hST : S ≤ T) :
    (sol.restrict hS hST).pressure = sol.pressure := rfl

/-- Restricting twice agrees with direct restriction.  The local fields are
unchanged; proof irrelevance identifies the certificate fields. -/
theorem PartialClassicalSolution.restrict_restrict
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {R S T : ℝ}
    (sol : PartialClassicalSolution ν f u₀ T)
    (hR : 0 < R) (hS : 0 < S) (hRS : R ≤ S) (hST : S ≤ T) :
    (sol.restrict hS hST).restrict hR hRS =
      sol.restrict hR (hRS.trans hST) := by
  rfl

/-- Velocity agreement is reflexive on every interval. -/
theorem velocityAgreesBefore_refl (T : ℝ) (u : VelocityEvolution) :
    VelocityAgreesBefore T u u := by
  intro _ _ _
  rfl

/-- Velocity agreement is symmetric. -/
theorem velocityAgreesBefore_symm {T : ℝ} {u v : VelocityEvolution}
    (h : VelocityAgreesBefore T u v) : VelocityAgreesBefore T v u := by
  intro t ht0 htT
  exact (h t ht0 htT).symm

/-- Velocity agreement is transitive. -/
theorem velocityAgreesBefore_trans {T : ℝ} {u v w : VelocityEvolution}
    (huv : VelocityAgreesBefore T u v)
    (hvw : VelocityAgreesBefore T v w) :
    VelocityAgreesBefore T u w := by
  intro t ht0 htT
  exact (huv t ht0 htT).trans (hvw t ht0 htT)

/-- Agreement on a longer interval restricts to every shorter interval. -/
theorem velocityAgreesBefore_mono {S T : ℝ} {u v : VelocityEvolution}
    (hST : S ≤ T) (h : VelocityAgreesBefore T u v) :
    VelocityAgreesBefore S u v := by
  intro t ht0 htS
  exact h t ht0 (htS.trans_le hST)

end Navier.Breakdown
