import Navier.Analysis.CriticalMildModeDifferentiation
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary mode mixing versus a Navier--Stokes heat triad

The three lattice modes `(3,0,0)`, `(0,4,0)`, and `(-3,-4,0)` have squared
Euclidean frequencies `9`, `16`, and `25`.  A cyclic permutation of their
three amplitudes is an explicit determinant-one unitary matrix, hence an
element of `SU(3)`.  It does not commute with the actual diagonal heat
generator because those three rates differ.

This separates four notions.  Translation phases are diagonal and commute
with heat damping.  The cyclic matrix is a unitary relabeling of three modal
coordinates.  It is not a physical spatial rotation, since such rotations
preserve frequency length while the cycle exchanges unequal lengths.  Most
importantly, membership in `SU(3)` alone does not make the relabeling a symmetry
of these modal dynamics.  The result disproves this precise full-modal-action
candidate; it makes no claim about every possible `SU(3)` representation.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.TriadUnitarySymmetry

open scoped Matrix
open Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization

/-- The `3-4-5` zero-sum lattice triad. -/
def triadMode : Fin 3 → LatticeMode :=
  ![(3, (0, 0)), (0, (4, 0)), (-3, (-4, 0))]

theorem triadMode_sum_zero :
    triadMode 0 + triadMode 1 + triadMode 2 = 0 := by
  change ((3, (0, 0)) : LatticeMode) + (0, (4, 0)) + (-3, (-4, 0)) = 0
  norm_num

/-- The exact squared Euclidean frequencies of the three modes. -/
theorem triadMode_frequency_norm_sq (i : Fin 3) :
    ‖officialEuclideanPoint (latticeFrequency (triadMode i))‖ ^ 2 =
      ![(9 : ℝ), 16, 25] i := by
  fin_cases i <;>
    simp [triadMode, latticeFrequency, officialEuclideanPoint,
      EuclideanSpace.norm_eq, Fin.sum_univ_three] <;> norm_num

/-- The repository's exact scalar heat rate on this triad. -/
theorem rawModeDecayRate_triadMode (μ : ℝ) (i : Fin 3) :
    rawModeDecayRate μ (triadMode i) = μ * ![(9 : ℝ), 16, 25] i := by
  unfold rawModeDecayRate
  rw [triadMode_frequency_norm_sq]

/-- No physical linear rotation can implement even the first step of the
three-cycle, because the first two frequencies have different lengths. -/
theorem no_euclidean_rotation_sends_first_mode_to_second :
    ¬ ∃ R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      R (officialEuclideanPoint (latticeFrequency (triadMode 0))) =
        officialEuclideanPoint (latticeFrequency (triadMode 1)) := by
  rintro ⟨R, hR⟩
  have hn := congrArg norm hR
  rw [R.norm_map] at hn
  have h0 := triadMode_frequency_norm_sq (0 : Fin 3)
  have h1 := triadMode_frequency_norm_sq (1 : Fin 3)
  norm_num at h0 h1
  nlinarith [norm_nonneg
    (officialEuclideanPoint (latticeFrequency (triadMode 0))),
    norm_nonneg (officialEuclideanPoint (latticeFrequency (triadMode 1)))]

/-- Diagonal heat generator on the three selected modal amplitudes. -/
def triadHeatGenerator (μ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => -(rawModeDecayRate μ (triadMode i) : ℂ))

/-- The cyclic permutation matrix on the three modal coordinates. -/
def cycleMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]

/-- The cyclic modal relabeling is an actual element of matrix `SU(3)`. -/
theorem cycleMatrix_mem_specialUnitary :
    cycleMatrix ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycleMatrix, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  · simp [cycleMatrix, Matrix.det_fin_three]

/-- The corresponding concrete `SU(3)` element. -/
def cycleSU3 : Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  ⟨cycleMatrix, cycleMatrix_mem_specialUnitary⟩

/-- The determinant-one unitary cycle fails the symmetry test for every
positive heat coefficient. -/
theorem cycleMatrix_not_commute_triadHeatGenerator
    {μ : ℝ} (hμ : 0 < μ) :
    cycleMatrix * triadHeatGenerator μ ≠
      triadHeatGenerator μ * cycleMatrix := by
  intro h
  have h01 := congrFun (congrFun h (0 : Fin 3)) (1 : Fin 3)
  simp [cycleMatrix, triadHeatGenerator, Matrix.mul_apply,
    Fin.sum_univ_three, rawModeDecayRate_triadMode] at h01
  linarith

/-- Translation of the physical torus acts by a diagonal phase on the three
modes. -/
def triadTranslation (x : Space) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => latticeCharacter (triadMode i) x)

/-- Unlike the cyclic relabeling, every translation phase commutes with the
diagonal heat generator. -/
theorem triadTranslation_commute_triadHeatGenerator
    (μ : ℝ) (x : Space) :
    triadTranslation x * triadHeatGenerator μ =
      triadHeatGenerator μ * triadTranslation x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [triadTranslation, triadHeatGenerator, Matrix.mul_apply,
      Fin.sum_univ_three] <;> ring

end Navier.Analysis.TriadUnitarySymmetry
