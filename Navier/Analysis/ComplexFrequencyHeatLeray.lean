import Navier.Analysis.FrequencyHeatLeray
import Navier.Analysis.ComplexLerayNorm

/-!
# Complex one-frequency heat--Leray multiplier

This file combines the exact scalar heat decay from
`Navier.Analysis.FrequencyHeatLeray` with the canonical complex-linear Leray
map.  It proves the coordinate formula, zero-time and zero-frequency laws,
bilinear and Hermitian transversality, Hermitian Euclidean norm contraction,
the exact semigroup law, and compatibility with complex conjugation.

All results remain finite-dimensional and frequencywise.  This file does not
construct a Fourier transform, an Oseen kernel, a function-space estimate, a
Duhamel fixed point, or a local Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ComplexFrequencyHeatLeray

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm

/-- The exact real scalar heat decay evaluated at the official Euclidean
representation of a real frequency. -/
def complexHeatDecay (ν t : ℝ) (q : Space) : ℝ :=
  heatDecay ν t (officialEuclideanPoint q)

/-- The canonical complex one-frequency heat evolution followed by the
complex-linear Leray projection. -/
def complexFrequencyHeatLeray
    (ν t : ℝ) (q : Space) : ComplexSpace →ₗ[ℂ] ComplexSpace :=
  (complexHeatDecay ν t q : ℂ) • complexLeray q

theorem complexFrequencyHeatLeray_apply
    (ν t : ℝ) (q : Space) (z : ComplexSpace) :
    complexFrequencyHeatLeray ν t q z =
      (complexHeatDecay ν t q : ℂ) • complexLeray q z := by
  rfl

theorem complexFrequencyHeatLeray_apply_coordinate
    (ν t : ℝ) (q : Space) (z : ComplexSpace) (i : Fin 3) :
    complexFrequencyHeatLeray ν t q z i =
      (complexHeatDecay ν t q : ℂ) * complexLeray q z i := by
  rfl

/-- Fully expanded coordinate formula for the heat--Leray multiplier. -/
theorem complexFrequencyHeatLeray_coordinate_formula
    (ν t : ℝ) (q : Space) (z : ComplexSpace) (i : Fin 3) :
    complexFrequencyHeatLeray ν t q z i =
      (complexHeatDecay ν t q : ℂ) *
        (z i -
          ((∑ j, (q j : ℂ) * z j) /
            ((q ⬝ᵥ q : ℝ) : ℂ)) * (q i : ℂ)) := by
  rw [complexFrequencyHeatLeray_apply_coordinate, complexLeray_formula]

@[simp] theorem complexEuclideanPoint_smul
    (a : ℂ) (z : ComplexSpace) :
    complexEuclideanPoint (a • z) = a • complexEuclideanPoint z :=
  rfl

/-- At time zero the heat multiplier is exactly the complex Leray
projection. -/
theorem complexFrequencyHeatLeray_zero_time
    (ν : ℝ) (q : Space) (z : ComplexSpace) :
    complexFrequencyHeatLeray ν 0 q z = complexLeray q z := by
  simp [complexFrequencyHeatLeray, complexHeatDecay, heatDecay]

/-- At zero frequency the totalized heat--Leray multiplier is the identity. -/
theorem complexFrequencyHeatLeray_zero_frequency
    (ν t : ℝ) (z : ComplexSpace) :
    complexFrequencyHeatLeray ν t 0 z = z := by
  simp [complexFrequencyHeatLeray, complexHeatDecay, heatDecay,
    officialEuclideanPoint]

theorem complexHeatDecay_nonneg (ν t : ℝ) (q : Space) :
    0 ≤ complexHeatDecay ν t q :=
  heatDecay_nonneg _ _ _

/-- Forward complex heat decay is at most one for nonnegative viscosity and
time. -/
theorem complexHeatDecay_le_one
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (q : Space) :
    complexHeatDecay ν t q ≤ 1 :=
  heatDecay_le_one hν ht _

/-- Euclidean transport identifies the coordinate multiplier with scalar heat
decay times the canonical Hermitian star projection. -/
theorem complexEuclideanPoint_complexFrequencyHeatLeray
    (ν t : ℝ) (q : Space) (z : ComplexSpace) :
    complexEuclideanPoint (complexFrequencyHeatLeray ν t q z) =
      (complexHeatDecay ν t q : ℂ) •
        complexEuclideanLeray q (complexEuclideanPoint z) := by
  rw [complexFrequencyHeatLeray_apply, complexEuclideanPoint_smul,
    complexEuclideanPoint_complexLeray]

/-- Hermitian transversality of the complex heat--Leray multiplier. -/
theorem complexFrequencyHeatLeray_hermitian_transverse
    (ν t : ℝ) (q : Space) (z : ComplexSpace) :
    inner ℂ (complexFrequency q)
      (complexEuclideanPoint (complexFrequencyHeatLeray ν t q z)) = 0 := by
  rw [complexEuclideanPoint_complexFrequencyHeatLeray, inner_smul_right,
    inner_complexEuclideanLeray]
  simp

/-- Bilinear Fourier transversality, kept distinct from the Hermitian theorem
and connected to it only through the embedded-real-frequency bridge. -/
theorem complexFrequencyHeatLeray_bilinear_transverse
    (ν t : ℝ) (q : Space) (z : ComplexSpace) :
    ∑ i, (q i : ℂ) * complexFrequencyHeatLeray ν t q z i = 0 := by
  rw [← inner_complexFrequency]
  exact complexFrequencyHeatLeray_hermitian_transverse _ _ _ _

/-- For nonnegative viscosity and time, the complex one-frequency multiplier
contracts the Hermitian Euclidean norm. -/
theorem complexEuclideanNorm_complexFrequencyHeatLeray_le
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (q : Space) (z : ComplexSpace) :
    complexEuclideanNorm (complexFrequencyHeatLeray ν t q z) ≤
      complexEuclideanNorm z := by
  rw [complexEuclideanNorm,
    complexEuclideanPoint_complexFrequencyHeatLeray,
    norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (complexHeatDecay_nonneg ν t q)]
  calc
    complexHeatDecay ν t q *
          ‖complexEuclideanLeray q (complexEuclideanPoint z)‖ ≤
        complexHeatDecay ν t q * ‖complexEuclideanPoint z‖ :=
      mul_le_mul_of_nonneg_left
        (complexEuclideanLeray_norm_le _ _)
        (complexHeatDecay_nonneg ν t q)
    _ ≤ 1 * ‖complexEuclideanPoint z‖ :=
      mul_le_mul_of_nonneg_right
        (complexHeatDecay_le_one hν ht q) (norm_nonneg _)
    _ = ‖complexEuclideanPoint z‖ := one_mul _

/-- Exact additive-time law for the scalar heat decay. -/
theorem complexHeatDecay_add (ν t s : ℝ) (q : Space) :
    complexHeatDecay ν (t + s) q =
      complexHeatDecay ν t q * complexHeatDecay ν s q := by
  unfold complexHeatDecay heatDecay
  rw [← Real.exp_add]
  congr 1
  ring

/-- Exact semigroup law at one real frequency. -/
theorem complexFrequencyHeatLeray_semigroup
    (ν t s : ℝ) (q : Space) (z : ComplexSpace) :
    complexFrequencyHeatLeray ν (t + s) q z =
      complexFrequencyHeatLeray ν t q
        (complexFrequencyHeatLeray ν s q z) := by
  simp only [complexFrequencyHeatLeray_apply]
  rw [map_smul, complexLeray_idempotent, smul_smul]
  rw [complexHeatDecay_add]
  norm_cast

/-- Real heat decay and the real-frequency Leray map commute with complex
conjugation. -/
theorem complexFrequencyHeatLeray_conjugate
    (ν t : ℝ) (q : Space) (z : ComplexSpace) :
    complexFrequencyHeatLeray ν t q (complexConjugate z) =
      complexConjugate (complexFrequencyHeatLeray ν t q z) := by
  rw [complexFrequencyHeatLeray_apply,
    complexFrequencyHeatLeray_apply, complexLeray_conjugate]
  ext i
  simp [complexConjugate]

end Navier.Analysis.ComplexFrequencyHeatLeray
