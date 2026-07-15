import Navier.Routes.R7.FullSixModePairClassification
import Navier.Routes.R7.WeightedShellTransfer

/-!
# Exhaustive receiver rates on the occupied six-mode support

This file evaluates all 36 ordered input pairs at each of the six occupied
receivers.  It retains both the normalized Leray multiplier and the declared
Fourier phases.  Off-support outputs are not discarded by this calculation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Routes.R7

/-- Full normalized projected rate at one occupied receiver. -/
def fullSixModeReceiverRate
    (s : ℝ) (output : SymWitnessMode) : ℝ := by
  classical
  exact
    ∑ first : SymWitnessMode, ∑ second : SymWitnessMode,
      if PairProducesModeOutput s first second output then
        phasedNormalizedProjectedCoefficient
          (symWitnessModePhase first) (symWitnessModePhase second)
          (symWitnessModePhase output)
          (symWitnessModeAmplitude first)
          (symWitnessModeAmplitude second)
          (symWitnessModeAmplitude output)
          (scaledSymWitnessModeWave s second)
          (scaledSymWitnessModeWave s output)
      else 0

/-- The same exhaustive sum before eliminating the Leray multiplier by
receiver transversality. -/
def fullSixModeReceiverOrderedRate
    (s : ℝ) (output : SymWitnessMode) : ℝ := by
  classical
  exact
    ∑ first : SymWitnessMode, ∑ second : SymWitnessMode,
      if PairProducesModeOutput s first second output then
        phasedOrderedCoefficient
          (symWitnessModePhase first) (symWitnessModePhase second)
          (symWitnessModePhase output)
          (symWitnessModeAmplitude first)
          (symWitnessModeAmplitude second)
          (symWitnessModeAmplitude output)
          (scaledSymWitnessModeWave s second)
      else 0

theorem symWitnessModeAmplitude_transverse_scaled
    (s : ℝ) (mode : SymWitnessMode) :
    symWitnessModeAmplitude mode ⬝ᵥ scaledSymWitnessModeWave s mode = 0 := by
  cases mode <;>
    norm_num [symWitnessModeAmplitude, scaledSymWitnessModeWave,
      scaledWitnessK, scaledWitnessL, scaledWitnessM,
      symWitnessA, symWitnessB, symWitnessC,
      witnessK, witnessL, witnessM,
      Matrix.vec3_dotProduct, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]

/-- Receiver transversality removes the normalized Leray correction in every
one of the 36 pair slots. -/
theorem fullSixModeReceiverRate_eq_orderedRate
    (s : ℝ) (output : SymWitnessMode) :
    fullSixModeReceiverRate s output =
      fullSixModeReceiverOrderedRate s output := by
  classical
  unfold fullSixModeReceiverRate fullSixModeReceiverOrderedRate
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  by_cases h : PairProducesModeOutput s first second output
  · simp only [h, if_true]
    exact phasedNormalizedProjectedCoefficient_eq_ordered
      (symWitnessModePhase first) (symWitnessModePhase second)
      (symWitnessModePhase output)
      (symWitnessModeAmplitude first)
      (symWitnessModeAmplitude second)
      (symWitnessModeAmplitude output)
      (scaledSymWitnessModeWave s second)
      (scaledSymWitnessModeWave s output)
      (symWitnessModeAmplitude_transverse_scaled s output)
  · simp [h]

/-- The exact table `(0,-s,s,0,-s,s)` in constructor order. -/
def expectedSixModeReceiverRate
    (s : ℝ) : SymWitnessMode → ℝ
  | .posK => 0
  | .posL => -s
  | .posM => s
  | .negK => 0
  | .negL => -s
  | .negM => s

private theorem fullSixModeReceiverOrderedRate_eq
    {s : ℝ} (hs : s ≠ 0) (output : SymWitnessMode) :
    fullSixModeReceiverOrderedRate s output =
      expectedSixModeReceiverRate s output := by
  cases output <;>
    unfold fullSixModeReceiverOrderedRate expectedSixModeReceiverRate <;>
    rw [sum_symWitnessMode] <;>
    repeat' rw [sum_symWitnessMode]
  all_goals
    simp only [pairProducesModeOutput_iff hs, receiverInputPair, Prod.swap,
      Prod.mk.injEq, reduceCtorEq, and_self, and_false, false_and,
      or_false, false_or, if_true, if_false, add_zero, zero_add]
    norm_num [symWitnessModePhase, symWitnessModeAmplitude,
      scaledSymWitnessModeWave, scaledWitnessK, scaledWitnessL,
      scaledWitnessM, phasedOrderedCoefficient, orderedTransfer,
      symWitnessA, symWitnessB, symWitnessC, witnessK, witnessL, witnessM,
      Matrix.vec3_dotProduct, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]

/-- Exhaustive full projected receiver-rate table. -/
theorem fullSixModeReceiverRate_eq
    {s : ℝ} (hs : s ≠ 0) (output : SymWitnessMode) :
    fullSixModeReceiverRate s output =
      expectedSixModeReceiverRate s output := by
  rw [fullSixModeReceiverRate_eq_orderedRate]
  exact fullSixModeReceiverOrderedRate_eq hs output

end Navier.Routes.R7
