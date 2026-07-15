import Navier.Routes.R7.FieldLeakage

/-!
# Full six-mode projected-convolution leakage

`FieldLeakage` isolates the two exchanged orderings of one off-support
interaction.  This file sums the normalized, phase-aware receiver coefficient
over every ordered pair of the six declared signed modes.  At nonzero scale,
an exhaustive classification proves that exactly `(.negK, .posL)` and
`(.posL, .negK)` hit `leakOutputWave`; consequently the complete 36-pair sum is
the earlier symmetrized coefficient and equals the scale.

This closes only the finite algebraic leakage check.  It does not construct an
invariant enlarged network, a shell flux, or a Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier.Routes.R7

/-- Every signed scaled wave is the common scale times its base wave. -/
theorem scaledSymWitnessModeWave_eq_smul
    (s : ℝ) (mode : SymWitnessMode) :
    scaledSymWitnessModeWave s mode = s • symWitnessModeWave mode := by
  cases mode <;>
    simp [scaledSymWitnessModeWave, symWitnessModeWave,
      scaledWitnessK, scaledWitnessL, scaledWitnessM]

/-- The leakage output has the same common-scale factorization. -/
theorem leakOutputWave_eq_smul_base (s : ℝ) :
    leakOutputWave s = s • (-witnessK + witnessL) := by
  simp [leakOutputWave, scaledWitnessK, scaledWitnessL, smul_add]

/-- An ordered pair produces the selected leakage output. -/
def PairProducesLeakOutput
    (s : ℝ) (first second : SymWitnessMode) : Prop :=
  scaledSymWitnessModeWave s first + scaledSymWitnessModeWave s second =
    leakOutputWave s

/--
At nonzero scale, exactly two of the 36 ordered pairs produce the selected
output.  They are the two convolution orderings already symmetrized in
`FieldLeakage`.
-/
theorem pairProducesLeakOutput_iff
    {s : ℝ} (hs : s ≠ 0) (first second : SymWitnessMode) :
    PairProducesLeakOutput s first second ↔
      (first = .negK ∧ second = .posL) ∨
        (first = .posL ∧ second = .negK) := by
  change
    scaledSymWitnessModeWave s first + scaledSymWitnessModeWave s second =
        leakOutputWave s ↔ _
  constructor
  · intro h
    rw [scaledSymWitnessModeWave_eq_smul s first,
      scaledSymWitnessModeWave_eq_smul s second,
      leakOutputWave_eq_smul_base] at h
    have hbase :
        symWitnessModeWave first + symWitnessModeWave second =
          -witnessK + witnessL := by
      apply smul_right_injective Space hs
      simpa only [smul_add] using h
    cases first <;> cases second
    all_goals
      norm_num [symWitnessModeWave, witnessK, witnessL, witnessM,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hbase
    all_goals simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · simp [scaledSymWitnessModeWave, leakOutputWave,
        scaledWitnessK, scaledWitnessL]
    · simp [scaledSymWitnessModeWave, leakOutputWave,
        scaledWitnessK, scaledWitnessL]
      abel

private theorem sum_symWitnessMode (f : SymWitnessMode → ℝ) :
    (∑ mode : SymWitnessMode, f mode) =
      f .posK + f .posL + f .posM + f .negK + f .negL + f .negM := by
  rw [show (Finset.univ : Finset SymWitnessMode) =
      {.posK, .posL, .posM, .negK, .negL, .negM} by decide]
  simp
  ring

/--
The complete receiver coefficient at `leakOutputWave`, summed over all
`6 × 6 = 36` ordered pairs of the declared mode table.  Terms whose two
wavevectors do not add to the selected output contribute zero.
-/
def fullSixModeProjectedLeakCoefficient (s : ℝ) : ℝ := by
  classical
  exact
    ∑ first : SymWitnessMode, ∑ second : SymWitnessMode,
      if PairProducesLeakOutput s first second then
        phasedNormalizedProjectedCoefficient
          (symWitnessModePhase first) (symWitnessModePhase second) 1
          (symWitnessModeAmplitude first) (symWitnessModeAmplitude second)
          leakReceiver (scaledSymWitnessModeWave s second) (leakOutputWave s)
      else 0

/-- The full 36-pair sum reduces to the one surviving symmetrized pair. -/
theorem fullSixModeProjectedLeakCoefficient_eq_pair
    {s : ℝ} (hs : s ≠ 0) :
    fullSixModeProjectedLeakCoefficient s =
      phasedSymmetrizedOutputCoefficient Complex.I 1 1
        symWitnessA symWitnessB leakReceiver
        (-scaledWitnessK s) (scaledWitnessL s) (leakOutputWave s) := by
  unfold fullSixModeProjectedLeakCoefficient
  rw [sum_symWitnessMode]
  repeat' rw [sum_symWitnessMode]
  simp only [pairProducesLeakOutput_iff hs, reduceCtorEq, and_self,
    and_false, false_and, or_false, false_or, if_true, if_false,
    add_zero, zero_add]
  simp only [symWitnessModePhase, symWitnessModeAmplitude,
    scaledSymWitnessModeWave, phasedSymmetrizedOutputCoefficient]
  ac_rfl

/-- The complete six-mode receiver coefficient is exactly the scale. -/
theorem fullSixModeProjectedLeakCoefficient_eq_scale
    {s : ℝ} (hs : s ≠ 0) :
    fullSixModeProjectedLeakCoefficient s = s := by
  rw [fullSixModeProjectedLeakCoefficient_eq_pair hs]
  exact phased_symmetrized_scaled_leak_coefficient s

/-- The complete coefficient is nonzero at every nonzero scale. -/
theorem fullSixModeProjectedLeakCoefficient_ne_zero
    {s : ℝ} (hs : s ≠ 0) :
    fullSixModeProjectedLeakCoefficient s ≠ 0 := by
  rw [fullSixModeProjectedLeakCoefficient_eq_scale hs]
  exact hs

/-- Full-sum leakage certificate, including the off-support conclusion. -/
theorem fullSixMode_has_nonzero_off_support_coefficient
    {s : ℝ} (hs : s ≠ 0) :
    fullSixModeProjectedLeakCoefficient s ≠ 0 ∧
      ¬ InScaledSymWitnessSupport s (leakOutputWave s) :=
  ⟨fullSixModeProjectedLeakCoefficient_ne_zero hs,
    leakOutputWave_not_in_six_mode_support hs⟩

end Navier.Routes.R7
