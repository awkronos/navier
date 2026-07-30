import Navier.Analysis.CriticalMildGlobalClosure

/-!
# Weighted lattice heat representations

The one- and two-derivative coefficient representations are both carried by
Mathlib's complete `ℓ¹` type; their distinction is the explicit decoding
weight.  The presently checked heat API supplies contraction at nonnegative
time.  A frequency-gain estimate with a time singularity is a separate,
currently unproved analytic leaf.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatSmoothing

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.LerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedSpace

/-- A Mathlib complete `ℓ¹` representative intended to encode one lattice
weight.  Decoding by `latticeModeWeight⁻¹` is defined in the preceding file. -/
abbrev LatticeWeightOneCarrier := lp (fun _ : LatticeMode => ComplexE3) 1

/-- A Mathlib complete `ℓ¹` representative intended to encode two lattice
weights.  The representation is distinct semantically through the displayed
decoder, not through bespoke norm axioms. -/
abbrev LatticeWeightTwoCarrier := lp (fun _ : LatticeMode => ComplexE3) 1

/-- Decode a two-weight representative to a complex Fourier coefficient. -/
def latticeWeightTwoCoefficient (u : LatticeWeightTwoCarrier)
    (m : LatticeMode) : ComplexSpace :=
  WithLp.ofLp ((latticeModeWeight m ^ 2)⁻¹ • u m)

/-- The exact heat--Leray multiplier is contractive at nonnegative time in
the Hermitian Euclidean coefficient norm. -/
theorem complexEuclideanNorm_heatLeray_le (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (k : LatticeMode) (z : ComplexSpace) :
    complexEuclideanNorm
      (complexFrequencyHeatLeray ν τ (latticeFrequency k) z) ≤
      complexEuclideanNorm z :=
  complexEuclideanNorm_complexFrequencyHeatLeray_le hν hτ _ _

/-- The scalar part of the actual heat multiplier is nonnegative and at most
one at nonnegative time. -/
theorem latticeHeatDecay_bounds (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (k : LatticeMode) :
    0 ≤ complexHeatDecay ν τ (latticeFrequency k) ∧
      complexHeatDecay ν τ (latticeFrequency k) ≤ 1 :=
  ⟨complexHeatDecay_nonneg _ _ _, complexHeatDecay_le_one hν hτ _⟩

/-- A sharp-order scalar heat gain with an explicit (non-optimal) constant.
The estimate is the elementary boundedness of `x exp (-x²)` after the
parabolic scaling `x = √a r`. -/
theorem mul_exp_neg_mul_sq_le_inv_sqrt {a r : ℝ} (ha : 0 < a) :
    r * Real.exp (-(a * r * r)) ≤ (Real.sqrt a)⁻¹ := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hs0 : 0 ≤ (Real.sqrt a)⁻¹ := inv_nonneg.mpr hs.le
  have hunit := Real.mulExpNegMulSq_one_le_one (Real.sqrt a * r)
  calc
    r * Real.exp (-(a * r * r)) =
        (Real.sqrt a)⁻¹ * Real.mulExpNegMulSq 1 (Real.sqrt a * r) := by
      unfold Real.mulExpNegMulSq
      field_simp
      congr 2
      rw [Real.sq_sqrt ha.le]
    _ ≤ (Real.sqrt a)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hunit hs0
    _ = (Real.sqrt a)⁻¹ := mul_one _

/-- The real and complex Euclidean frequency representations have identical
norms. -/
theorem complexFrequency_norm_eq_official (q : Space) :
    ‖complexFrequency q‖ = ‖officialEuclideanPoint q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [complexFrequency_norm_sq, officialPoint_norm_sq_eq_dotProduct]

/-- Scalar heat smoothing at a concrete lattice frequency.  The inhomogeneous
zero mode still requires the additive `1` in a full weight estimate. -/
theorem latticeHeat_frequency_gain (ν τ : ℝ) (hντ : 0 < ν * τ)
    (k : LatticeMode) :
    ‖complexFrequency (latticeFrequency k)‖ *
      complexHeatDecay ν τ (latticeFrequency k) ≤ (Real.sqrt (ν * τ))⁻¹ := by
  unfold complexHeatDecay heatDecay
  rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
  convert mul_exp_neg_mul_sq_le_inv_sqrt hντ using 1 <;> ring

end Navier.Analysis.CriticalMildHeatSmoothing
