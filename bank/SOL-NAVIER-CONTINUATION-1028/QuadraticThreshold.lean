import Mathlib

/-!
Exact arithmetic obstruction to removing the small-radius hypothesis from
Navier.Analysis.ContinuationEstimateProof.continuousMildImage_self_map_ball_twelfth.
This is a counterexample to the proposed estimate-only inference, not a
counterexample to Navier--Stokes regularity. No PDE or continuation conclusion
is assumed or established. The source consumer currently lacks a materialized
olean on this host, so this probe deliberately imports Mathlib only.
-/
namespace SolNavierContinuation1028

/-- For a positive ball radius, the existing quadratic majorant fits the
radius-2R ball exactly in the small-data regime R <= viscosity/12. -/
theorem quadratic_budget_iff (ν R : ℝ) (hν : 0 < ν) (hR : 0 < R) :
    R + 12 * ν⁻¹ * R ^ 2 ≤ 2 * R ↔ R ≤ ν / 12 := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  have hi : 0 < ν⁻¹ := inv_pos.mpr hν
  have hid : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hν0
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h hν.le
    have hpoly : 12 * R ^ 2 ≤ ν * R := by
      nlinarith [hid]
    by_contra hn
    have hr : ν / 12 < R := lt_of_not_ge hn
    have : 0 < R * (12 * R - ν) := mul_pos hR (by linarith)
    nlinarith
  · intro h
    have hlin : 12 * R ≤ ν := by linarith
    have hs := mul_le_mul_of_nonneg_left hlin hi.le
    have hscaled : 12 * ν⁻¹ * R ≤ 1 := by
      nlinarith [hid]
    have := mul_le_mul_of_nonneg_right hscaled hR.le
    nlinarith

/-- Concrete refutation of the same-radius large-data arithmetic step. -/
theorem unrestricted_quadratic_budget_false :
    ¬ (∀ (ν R : ℝ), 0 < ν → 0 ≤ R →
      R + 12 * ν⁻¹ * R ^ 2 ≤ 2 * R) := by
  intro h
  have hc := h 1 1 (by norm_num) (by norm_num)
  norm_num at hc

/-- Positive control: the exact threshold is accepted, not rejected together
with the false unrestricted claim. -/
theorem boundary_budget :
    (1 / 12 : ℝ) + 12 * (1 : ℝ)⁻¹ * (1 / 12 : ℝ) ^ 2 ≤
      2 * (1 / 12 : ℝ) := by norm_num

end SolNavierContinuation1028

#check @SolNavierContinuation1028.quadratic_budget_iff
#print axioms SolNavierContinuation1028.quadratic_budget_iff
#print axioms SolNavierContinuation1028.unrestricted_quadratic_budget_false
#print axioms SolNavierContinuation1028.boundary_budget
