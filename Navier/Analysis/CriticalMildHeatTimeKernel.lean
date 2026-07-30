import Navier.Analysis.CriticalMildHeatCarrierLift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The integrable positive-time heat singularity

This file isolates the scalar time kernel that controls the completed
heat-lift/global-output estimate and computes its exact finite-time integral.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatTimeKernel

open MeasureTheory Set
open Navier.Analysis.CriticalMildHeatCarrierLift

/-- The scale-invariant positive-time singularity. -/
def inverseSqrtTime (τ : ℝ) : ℝ := τ ^ (-(1 / 2 : ℝ))

/-- The singularity is interval-integrable at the initial time. -/
theorem inverseSqrtTime_intervalIntegrable (T : ℝ) :
    IntervalIntegrable inverseSqrtTime volume 0 T := by
  exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)

/-- Its exact integral is `2 sqrt(T)`. -/
theorem integral_inverseSqrtTime_zero (T : ℝ) (hT : 0 ≤ T) :
    (∫ τ in (0 : ℝ)..T, inverseSqrtTime τ) = 2 * Real.sqrt T := by
  rw [show inverseSqrtTime = fun τ : ℝ => τ ^ (-(1 / 2 : ℝ)) by rfl,
    integral_rpow (Or.inl (by norm_num))]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring]
  simp [Real.sqrt_eq_rpow, hT]
  ring

/-- The scalar majorant carried by the completed heat lift. -/
def heatTimeMajorant (ν τ : ℝ) : ℝ :=
  1 + (Real.sqrt ν)⁻¹ * inverseSqrtTime τ

/-- The actual heat gain equals the scalar majorant at positive viscosity and
positive time. -/
theorem heatTimeMajorant_eq (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    heatTimeMajorant ν τ = 1 + (Real.sqrt (ν * τ))⁻¹ := by
  rw [heatTimeMajorant, inverseSqrtTime, Real.rpow_neg hτ.le,
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hν.le, mul_inv]

/-- The exact `O(sqrt T)` integral of the full inhomogeneous heat majorant. -/
theorem integral_heatTimeMajorant_zero (ν T : ℝ) (hT : 0 ≤ T) :
    (∫ τ in (0 : ℝ)..T, heatTimeMajorant ν τ) =
      T + 2 * Real.sqrt T / Real.sqrt ν := by
  simp_rw [heatTimeMajorant]
  rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_const
      ((inverseSqrtTime_intervalIntegrable T).const_mul _),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul,
    integral_inverseSqrtTime_zero T hT]
  simp
  ring

end Navier.Analysis.CriticalMildHeatTimeKernel

#print axioms Navier.Analysis.CriticalMildHeatTimeKernel.inverseSqrtTime_intervalIntegrable
#print axioms Navier.Analysis.CriticalMildHeatTimeKernel.integral_inverseSqrtTime_zero
#print axioms Navier.Analysis.CriticalMildHeatTimeKernel.heatTimeMajorant_eq
#print axioms Navier.Analysis.CriticalMildHeatTimeKernel.integral_heatTimeMajorant_zero

end
