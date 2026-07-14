import Navier.Routes.R7.SymmetrizedWitness

/-!
# Exact off-support leakage from the six-mode R7 field table

The negative `k` mode and positive `l` mode of the real six-mode table have a
nonzero symmetrized interaction at output `-k + l`.  Pairing the normalized
projected output against the transverse `z` receiver gives exactly the common
wavevector scale.  At every nonzero scale, this output differs from all six
signed witness wavevectors.

This is an exact algebraic falsification of quadratic invariance for that
six-mode support.  It does not construct an invariant enlarged network, sum
all generated modes, establish shell flux, or solve Navier--Stokes.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

/-- A transverse probe detecting the off-support projected output. -/
def leakReceiver : Space := ![(0 : ℝ), 0, 1]

/-- Output wavevector of the interaction between modes `-k` and `l`. -/
def leakOutputWave (s : ℝ) : Space :=
  -scaledWitnessK s + scaledWitnessL s

theorem leakOutputWave_coordinates (s : ℝ) :
    leakOutputWave s = ![-s, s, (0 : ℝ)] := by
  ext i
  fin_cases i <;>
    simp [leakOutputWave, scaledWitnessK, scaledWitnessL,
      witnessK, witnessL, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- The probe is transverse to the leakage output at every real scale. -/
theorem leak_receiver_transverse (s : ℝ) :
    leakReceiver ⬝ᵥ leakOutputWave s = 0 := by
  norm_num [leakReceiver, leakOutputWave, scaledWitnessK, scaledWitnessL,
    witnessK, witnessL, Matrix.vec3_dotProduct, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- The normalized, phase-aware, two-ordering coefficient of the leakage
interaction is exactly its common wavevector scale. -/
theorem phased_symmetrized_scaled_leak_coefficient (s : ℝ) :
    phasedSymmetrizedOutputCoefficient Complex.I 1 1
      symWitnessA symWitnessB leakReceiver
      (-scaledWitnessK s) (scaledWitnessL s) (leakOutputWave s) = s := by
  rw [phasedSymmetrizedOutputCoefficient_eq_ordered_sum
    Complex.I 1 1 symWitnessA symWitnessB leakReceiver
    (-scaledWitnessK s) (scaledWitnessL s) (leakOutputWave s)
    (leak_receiver_transverse s)]
  simp [phasedOrderedCoefficient, orderedTransfer, leakReceiver,
    scaledWitnessK, scaledWitnessL,
    symWitnessA, symWitnessB, witnessK, witnessL]

theorem phased_symmetrized_base_leak_coefficient :
    phasedSymmetrizedOutputCoefficient Complex.I 1 1
      symWitnessA symWitnessB leakReceiver
      (-witnessK) witnessL (-witnessK + witnessL) = 1 := by
  simpa [scaledWitnessK, scaledWitnessL, leakOutputWave] using
    phased_symmetrized_scaled_leak_coefficient 1

/-- The detected leakage coefficient is not uniformly bounded across positive
common wavevector scales. -/
theorem phased_symmetrized_leak_unbounded_across_positive_scale (M : ℝ) :
    ∃ s : ℝ, 0 < s ∧
      M < phasedSymmetrizedOutputCoefficient Complex.I 1 1
        symWitnessA symWitnessB leakReceiver
        (-scaledWitnessK s) (scaledWitnessL s) (leakOutputWave s) := by
  refine ⟨|M| + 1, by positivity, ?_⟩
  rw [phased_symmetrized_scaled_leak_coefficient]
  exact lt_of_le_of_lt (le_abs_self M) (lt_add_one |M|)

/-- The wavevector table of the six signed modes at scale `s`. -/
def scaledSymWitnessModeWave (s : ℝ) : SymWitnessMode → Space
  | .posK => scaledWitnessK s
  | .posL => scaledWitnessL s
  | .posM => scaledWitnessM s
  | .negK => -scaledWitnessK s
  | .negL => -scaledWitnessL s
  | .negM => -scaledWitnessM s

def InScaledSymWitnessSupport (s : ℝ) (wave : Space) : Prop :=
  ∃ mode : SymWitnessMode, wave = scaledSymWitnessModeWave s mode

/-- For nonzero scale, the leakage output differs from each of the six signed
wavevectors separately. -/
theorem leakOutputWave_ne_six_modes {s : ℝ} (hs : s ≠ 0) :
    leakOutputWave s ≠ scaledWitnessK s ∧
    leakOutputWave s ≠ -scaledWitnessK s ∧
    leakOutputWave s ≠ scaledWitnessL s ∧
    leakOutputWave s ≠ -scaledWitnessL s ∧
    leakOutputWave s ≠ scaledWitnessM s ∧
    leakOutputWave s ≠ -scaledWitnessM s := by
  constructor
  · intro h
    have hcoord := congrArg (fun v : Space => v 1) h
    simp [leakOutputWave, scaledWitnessK, scaledWitnessL,
      witnessK, witnessL, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hcoord
    exact hs hcoord
  constructor
  · intro h
    have hcoord := congrArg (fun v : Space => v 1) h
    simp [leakOutputWave, scaledWitnessK, scaledWitnessL,
      witnessK, witnessL, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hcoord
    exact hs hcoord
  constructor
  · intro h
    have hcoord := congrArg (fun v : Space => v 0) h
    simp [leakOutputWave, scaledWitnessK, scaledWitnessL,
      witnessK, witnessL, Matrix.cons_val_zero] at hcoord
    exact hs hcoord
  constructor
  · intro h
    have hcoord := congrArg (fun v : Space => v 0) h
    simp [leakOutputWave, scaledWitnessK, scaledWitnessL,
      witnessK, witnessL, Matrix.cons_val_zero] at hcoord
    exact hs hcoord
  constructor
  · intro h
    have hcoord := congrArg (fun v : Space => v 1) h
    simp [leakOutputWave, scaledWitnessK, scaledWitnessL, scaledWitnessM,
      witnessK, witnessL, witnessM, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hcoord
    exact hs (by linarith)
  · intro h
    have hcoord := congrArg (fun v : Space => v 0) h
    simp [leakOutputWave, scaledWitnessK, scaledWitnessL, scaledWitnessM,
      witnessK, witnessL, witnessM, Matrix.cons_val_zero] at hcoord
    exact hs (by linarith)

/-- The exact leakage wave is outside the six-mode support at every nonzero
scale. -/
theorem leakOutputWave_not_in_six_mode_support {s : ℝ} (hs : s ≠ 0) :
    ¬ InScaledSymWitnessSupport s (leakOutputWave s) := by
  rcases leakOutputWave_ne_six_modes hs with
    ⟨hK, hnK, hL, hnL, hM, hnM⟩
  rintro ⟨mode, hmode⟩
  cases mode with
  | posK => exact hK hmode
  | posL => exact hL hmode
  | posM => exact hM hmode
  | negK => exact hnK hmode
  | negL => exact hnL hmode
  | negM => exact hnM hmode

/-- Constructive falsification certificate: at each nonzero scale the
six-mode field table has a nonzero quadratic interaction whose output lies
outside its support. -/
theorem six_mode_support_has_nonzero_off_support_interaction
    {s : ℝ} (hs : s ≠ 0) :
    phasedSymmetrizedOutputCoefficient Complex.I 1 1
        symWitnessA symWitnessB leakReceiver
        (-scaledWitnessK s) (scaledWitnessL s) (leakOutputWave s) ≠ 0 ∧
      ¬ InScaledSymWitnessSupport s (leakOutputWave s) := by
  constructor
  · rw [phased_symmetrized_scaled_leak_coefficient]
    exact hs
  · exact leakOutputWave_not_in_six_mode_support hs

end Navier.Routes.R7
