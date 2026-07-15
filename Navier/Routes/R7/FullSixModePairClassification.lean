import Navier.Routes.R7.FullFieldLeakage

/-!
# Exact in-support pair classification for the six-mode witness

For nonzero wave scale, this file enumerates exactly which ordered pairs of
the six signed modes add to each occupied receiver.  The classification is
finite algebra and does not claim that the six-mode support is invariant.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Routes.R7

/-- Two signed witness modes produce an occupied output at scale `s`. -/
def PairProducesModeOutput
    (s : ℝ) (first second output : SymWitnessMode) : Prop :=
  scaledSymWitnessModeWave s first + scaledSymWitnessModeWave s second =
    scaledSymWitnessModeWave s output

/-- The canonical unordered input pair for each occupied receiver. -/
def receiverInputPair :
    SymWitnessMode → SymWitnessMode × SymWitnessMode
  | .posK => (.negL, .negM)
  | .posL => (.negK, .negM)
  | .posM => (.negK, .negL)
  | .negK => (.posL, .posM)
  | .negL => (.posK, .posM)
  | .negM => (.posK, .posL)

private theorem basePair_posK_iff (first second : SymWitnessMode) :
    symWitnessModeWave first + symWitnessModeWave second =
        symWitnessModeWave .posK ↔
      (first, second) = receiverInputPair .posK ∨
        (first, second) = Prod.swap (receiverInputPair .posK) := by
  cases first <;> cases second <;>
    norm_num [receiverInputPair, symWitnessModeWave,
      witnessK, witnessL, witnessM,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    simp

private theorem basePair_posL_iff (first second : SymWitnessMode) :
    symWitnessModeWave first + symWitnessModeWave second =
        symWitnessModeWave .posL ↔
      (first, second) = receiverInputPair .posL ∨
        (first, second) = Prod.swap (receiverInputPair .posL) := by
  cases first <;> cases second <;>
    norm_num [receiverInputPair, symWitnessModeWave,
      witnessK, witnessL, witnessM,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    simp

private theorem basePair_posM_iff (first second : SymWitnessMode) :
    symWitnessModeWave first + symWitnessModeWave second =
        symWitnessModeWave .posM ↔
      (first, second) = receiverInputPair .posM ∨
        (first, second) = Prod.swap (receiverInputPair .posM) := by
  cases first <;> cases second <;>
    norm_num [receiverInputPair, symWitnessModeWave,
      witnessK, witnessL, witnessM,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    simp

private theorem basePair_negK_iff (first second : SymWitnessMode) :
    symWitnessModeWave first + symWitnessModeWave second =
        symWitnessModeWave .negK ↔
      (first, second) = receiverInputPair .negK ∨
        (first, second) = Prod.swap (receiverInputPair .negK) := by
  cases first <;> cases second <;>
    norm_num [receiverInputPair, symWitnessModeWave,
      witnessK, witnessL, witnessM,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    simp

private theorem basePair_negL_iff (first second : SymWitnessMode) :
    symWitnessModeWave first + symWitnessModeWave second =
        symWitnessModeWave .negL ↔
      (first, second) = receiverInputPair .negL ∨
        (first, second) = Prod.swap (receiverInputPair .negL) := by
  cases first <;> cases second <;>
    norm_num [receiverInputPair, symWitnessModeWave,
      witnessK, witnessL, witnessM,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    simp

private theorem basePair_negM_iff (first second : SymWitnessMode) :
    symWitnessModeWave first + symWitnessModeWave second =
        symWitnessModeWave .negM ↔
      (first, second) = receiverInputPair .negM ∨
        (first, second) = Prod.swap (receiverInputPair .negM) := by
  cases first <;> cases second <;>
    norm_num [receiverInputPair, symWitnessModeWave,
      witnessK, witnessL, witnessM,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;>
    simp

private theorem basePair_iff
    (first second output : SymWitnessMode) :
    symWitnessModeWave first + symWitnessModeWave second =
        symWitnessModeWave output ↔
      (first, second) = receiverInputPair output ∨
        (first, second) = Prod.swap (receiverInputPair output) := by
  cases output
  · exact basePair_posK_iff first second
  · exact basePair_posL_iff first second
  · exact basePair_posM_iff first second
  · exact basePair_negK_iff first second
  · exact basePair_negL_iff first second
  · exact basePair_negM_iff first second

/-- At nonzero scale, exactly the canonical pair and its swap produce each
occupied receiver. -/
theorem pairProducesModeOutput_iff
    {s : ℝ} (hs : s ≠ 0) (first second output : SymWitnessMode) :
    PairProducesModeOutput s first second output ↔
      (first, second) = receiverInputPair output ∨
        (first, second) = Prod.swap (receiverInputPair output) := by
  rw [PairProducesModeOutput,
    scaledSymWitnessModeWave_eq_smul s first,
    scaledSymWitnessModeWave_eq_smul s second,
    scaledSymWitnessModeWave_eq_smul s output]
  constructor
  · intro h
    apply (basePair_iff first second output).mp
    apply smul_right_injective Space hs
    simpa only [smul_add] using h
  · intro h
    have hbase := (basePair_iff first second output).mpr h
    calc
      s • symWitnessModeWave first + s • symWitnessModeWave second =
          s • (symWitnessModeWave first + symWitnessModeWave second) := by
            rw [smul_add]
      _ = s • symWitnessModeWave output :=
        congrArg (fun v : Space => s • v) hbase

/-- Expand a sum over the six signed witness modes in constructor order. -/
theorem sum_symWitnessMode (f : SymWitnessMode → ℝ) :
    (∑ mode : SymWitnessMode, f mode) =
      f .posK + f .posL + f .posM + f .negK + f .negL + f .negM := by
  rw [show (Finset.univ : Finset SymWitnessMode) =
      {.posK, .posL, .posM, .negK, .negL, .negM} by decide]
  simp
  ring

end Navier.Routes.R7
