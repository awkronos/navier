import Navier.Analysis.LerayProjection

/-!
# One-frequency heat--Leray multiplier

This file combines the canonical real Leray projection with the scalar heat
decay at one Fourier frequency.  It proves the exact semigroup law,
transversality, and the nonexpansive estimate at nonnegative viscosity and
time.

This is finite-dimensional frequencywise infrastructure.  It does not define
a Fourier transform, prove an integrable heat-kernel estimate, construct a
Duhamel map, or produce a local Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.FrequencyHeatLeray

open Navier.Analysis.LerayProjection

/-- Scalar heat decay at frequency `q`. -/
def heatDecay (ν t : ℝ) (q : E3) : ℝ :=
  Real.exp (-ν * t * ‖q‖ ^ 2)

/-- The one-frequency heat evolution followed by Leray projection. -/
def frequencyHeatLeray (ν t : ℝ) (q : E3) : E3 →L[ℝ] E3 :=
  (heatDecay ν t q) • euclideanLeray q

theorem frequencyHeatLeray_apply (ν t : ℝ) (q v : E3) :
    frequencyHeatLeray ν t q v =
      (heatDecay ν t q) • euclideanLeray q v := by
  rfl

/-- The heat multiplier at time zero is exactly the Leray projection. -/
theorem frequencyHeatLeray_zero_time (ν : ℝ) (q v : E3) :
    frequencyHeatLeray ν 0 q v = euclideanLeray q v := by
  simp [frequencyHeatLeray, heatDecay]

/-- At zero frequency the totalized heat--Leray multiplier is the identity. -/
theorem frequencyHeatLeray_zero_frequency (ν t : ℝ) (v : E3) :
    frequencyHeatLeray ν t 0 v = v := by
  rw [frequencyHeatLeray_apply, euclideanLeray_formula]
  simp [heatDecay]

/-- Every output is transverse to its frequency. -/
theorem frequencyHeatLeray_transverse (ν t : ℝ) (q v : E3) :
    inner ℝ q (frequencyHeatLeray ν t q v) = 0 := by
  rw [frequencyHeatLeray_apply, inner_smul_right,
    inner_euclideanLeray]
  simp

theorem heatDecay_nonneg (ν t : ℝ) (q : E3) :
    0 ≤ heatDecay ν t q :=
  Real.exp_nonneg _

/-- Forward heat decay is at most one for nonnegative viscosity and time. -/
theorem heatDecay_le_one
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (q : E3) :
    heatDecay ν t q ≤ 1 := by
  rw [heatDecay, Real.exp_le_one_iff]
  calc
    -ν * t * ‖q‖ ^ 2 = -(ν * t * ‖q‖ ^ 2) := by ring
    _ ≤ 0 := neg_nonpos.mpr
      (mul_nonneg (mul_nonneg hν ht) (sq_nonneg ‖q‖))

/-- The one-frequency heat--Leray multiplier contracts the Euclidean norm. -/
theorem frequencyHeatLeray_norm_le
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (q v : E3) :
    ‖frequencyHeatLeray ν t q v‖ ≤ ‖v‖ := by
  rw [frequencyHeatLeray_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (heatDecay_nonneg ν t q)]
  calc
    heatDecay ν t q * ‖euclideanLeray q v‖ ≤
        heatDecay ν t q * ‖v‖ :=
      mul_le_mul_of_nonneg_left (euclideanLeray_norm_le q v)
        (heatDecay_nonneg ν t q)
    _ ≤ 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right (heatDecay_le_one hν ht q) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- Exact semigroup law at one frequency. -/
theorem frequencyHeatLeray_semigroup (ν t s : ℝ) (q v : E3) :
    frequencyHeatLeray ν (t + s) q v =
      frequencyHeatLeray ν t q (frequencyHeatLeray ν s q v) := by
  simp only [frequencyHeatLeray_apply]
  rw [map_smul, euclideanLeray_idempotent, smul_smul]
  congr 1
  unfold heatDecay
  rw [← Real.exp_add]
  congr 1
  ring

end Navier.Analysis.FrequencyHeatLeray
