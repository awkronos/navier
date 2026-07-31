import Navier.Analysis.CriticalMildBoundedContinuation

/-!
# Quantitative crown core for critical mild restarts

This module records what the completed heat/Duhamel dynamics actually give
toward the global continuation consumer.  The one-step estimate supplies a
radius recurrence and a positive restart time; it does not construct the
uniform terminal critical-norm bound consumed by
`CriticalMildTerminalNormBound`.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.GlobalRegularityCrownCore

open Navier.Analysis.CriticalMildQuantitativeRestart

/-- The selected bounded restart duration has the exact fourth-power
dependence on the selected radius. -/
theorem criticalMildBoundedHorizon_eq_viscosity_div_radius_fourth
    (ν M : ℝ) (hν : 0 < ν) (hM : 0 ≤ M) :
    criticalMildBoundedHorizon ν M =
      ν / (64 * (criticalMildBoundedRadius M) ^ 4) := by
  unfold criticalMildBoundedHorizon
  have hR : 0 < criticalMildBoundedRadius M := by
    unfold criticalMildBoundedRadius
    linarith
  have hden : 8 * (criticalMildBoundedRadius M) ^ 2 ≠ 0 := by
    positivity
  have hsqrt : (Real.sqrt ν) ^ 2 = ν := (Real.sq_sqrt hν.le)
  field_simp
  nlinarith [sq_nonneg (criticalMildBoundedRadius M)]

/-- The heat/Duhamel scalar majorant cannot close a nonzero fixed radius over
any positive time: its nonlinear increment is strictly positive.  This is an
obstruction of this estimate, not a claimed counterexample to the PDE. -/
theorem restart_scalar_budget_strict_above_fixed_radius
    (ν R r : ℝ) (hν : 0 < ν) (hR : 0 < R) (hr : 0 < r) :
    R < R + (2 * Real.sqrt r / Real.sqrt ν) * R ^ 2 := by
  have hsqrtr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsqrtnu : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hinc : 0 < (2 * Real.sqrt r / Real.sqrt ν) * R ^ 2 := by
    positivity
  linarith

/-- Consequently the available critical-norm recurrence supplies no
fixed-positive-radius invariant ball by itself. -/
theorem not_restart_scalar_budget_le_fixed_radius
    (ν R r : ℝ) (hν : 0 < ν) (hR : 0 < R) (hr : 0 < r) :
    ¬ (R + (2 * Real.sqrt r / Real.sqrt ν) * R ^ 2 ≤ R) := by
  exact not_le_of_gt (restart_scalar_budget_strict_above_fixed_radius ν R r hν hR hr)

end Navier.Analysis.GlobalRegularityCrownCore

#print axioms Navier.Analysis.GlobalRegularityCrownCore.criticalMildBoundedHorizon_eq_viscosity_div_radius_fourth
#print axioms Navier.Analysis.GlobalRegularityCrownCore.restart_scalar_budget_strict_above_fixed_radius
#print axioms Navier.Analysis.GlobalRegularityCrownCore.not_restart_scalar_budget_le_fixed_radius
