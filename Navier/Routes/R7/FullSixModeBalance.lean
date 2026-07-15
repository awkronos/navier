import Navier.Routes.R7.FullFieldLeakage
import Navier.Routes.R7.FullSixModeReceiverRates

/-!
# Exact finite six-mode balance

This file folds the exhaustive occupied-receiver table into constant-weight
and squared-frequency balances.  The simultaneous off-support leakage identity
records why this finite calculation is not a closed Fourier evolution.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Routes.R7

/-- Constant-weight transfer rate over the six occupied receivers. -/
def fullSixModeEnergyRate (s : ℝ) : ℝ :=
  ∑ output : SymWitnessMode, fullSixModeReceiverRate s output

/-- The occupied six-mode rates conserve their constant-weight sum. -/
theorem fullSixModeEnergyRate_eq_zero
    {s : ℝ} (hs : s ≠ 0) :
    fullSixModeEnergyRate s = 0 := by
  unfold fullSixModeEnergyRate
  rw [sum_symWitnessMode]
  simp only [fullSixModeReceiverRate_eq hs, expectedSixModeReceiverRate]
  ring

/-- Squared Euclidean frequency attached to one symmetric witness mode. -/
def symWitnessModeSquaredFrequency
    (s : ℝ) (mode : SymWitnessMode) : ℝ :=
  scaledSymWitnessModeWave s mode ⬝ᵥ
    scaledSymWitnessModeWave s mode

/-- Squared-frequency-weighted rate over the six occupied receivers. -/
def fullSixModeSquaredFrequencyRate (s : ℝ) : ℝ :=
  ∑ output : SymWitnessMode,
    symWitnessModeSquaredFrequency s output *
      fullSixModeReceiverRate s output

/-- The exact occupied-support squared-frequency rate is `2 s³`. -/
theorem fullSixModeSquaredFrequencyRate_eq_two_cubes
    {s : ℝ} (hs : s ≠ 0) :
    fullSixModeSquaredFrequencyRate s = 2 * s ^ 3 := by
  unfold fullSixModeSquaredFrequencyRate
  rw [sum_symWitnessMode]
  simp only [fullSixModeReceiverRate_eq hs, expectedSixModeReceiverRate]
  norm_num [symWitnessModeSquaredFrequency,
    scaledSymWitnessModeWave, scaledWitnessK, scaledWitnessL, scaledWitnessM,
    witnessK, witnessL, witnessM,
    Matrix.vec3_dotProduct, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  ring

theorem fullSixModeSquaredFrequencyRate_pos
    (s : ℝ) (hs : 0 < s) :
    0 < fullSixModeSquaredFrequencyRate s := by
  rw [fullSixModeSquaredFrequencyRate_eq_two_cubes (ne_of_gt hs)]
  positivity

/-- Complete finite calculation: occupied rates, their two balances, and the
nonzero off-support leakage coefficient are recorded in one conjunction. -/
theorem fullSixModeBalance
    {s : ℝ} (hs : s ≠ 0) :
    (∀ output, fullSixModeReceiverRate s output =
      expectedSixModeReceiverRate s output) ∧
    fullSixModeEnergyRate s = 0 ∧
    fullSixModeSquaredFrequencyRate s = 2 * s ^ 3 ∧
    fullSixModeProjectedLeakCoefficient s = s := by
  exact ⟨fullSixModeReceiverRate_eq hs,
    fullSixModeEnergyRate_eq_zero hs,
    fullSixModeSquaredFrequencyRate_eq_two_cubes hs,
    fullSixModeProjectedLeakCoefficient_eq_scale hs⟩

end Navier.Routes.R7
