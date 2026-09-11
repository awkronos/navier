import Navier.Routes.R7.SymmetrizedPhase

/-!
# Noncancelling symmetrized R7 witness and finite real Fourier table

This module replaces the first polarization triple by one for which the two
input orderings at the same output add to a nonzero phase-aware coefficient.
The scaled coefficient is exactly the common wavevector scale.

The six signed modes are also packaged as a concrete coefficient table.  Its
opposite modes have negated wavevectors and conjugate complex coefficients,
and every mode is divergence-free.  These facts make the table compatible
with a real finite Fourier polynomial, but do not assert a Navier--Stokes
evolution, a shell flux, or a regularity/breakdown conclusion.  In particular,
the six-mode support is not closed under the quadratic convolution: interactions
can leak to wavevectors outside this table.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

def symWitnessA : Space := ![(0 : ℝ), 1, 1]
def symWitnessB : Space := ![(1 : ℝ), 0, 0]
def symWitnessC : Space := ![(1 : ℝ), -1, 1]

/-- The new polarizations are divergence-free at the original wavevector
triad. -/
theorem sym_witness_admissible :
    witnessK + witnessL + witnessM = 0 ∧
    witnessK ⬝ᵥ symWitnessA = 0 ∧
    witnessL ⬝ᵥ symWitnessB = 0 ∧
    witnessM ⬝ᵥ symWitnessC = 0 := by
  constructor
  · ext i
    fin_cases i <;>
      norm_num [witnessK, witnessL, witnessM,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  · norm_num [witnessK, witnessL, witnessM,
      symWitnessA, symWitnessB, symWitnessC,
      Matrix.vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

/-- Common wavevector scaling preserves the triad and all three new
divergence constraints. -/
theorem sym_scaled_witness_admissible (s : ℝ) :
    scaledWitnessK s + scaledWitnessL s + scaledWitnessM s = 0 ∧
    scaledWitnessK s ⬝ᵥ symWitnessA = 0 ∧
    scaledWitnessL s ⬝ᵥ symWitnessB = 0 ∧
    scaledWitnessM s ⬝ᵥ symWitnessC = 0 := by
  rcases sym_witness_admissible with ⟨htriad, ha, hb, hc⟩
  constructor
  · simp only [scaledWitnessK, scaledWitnessL, scaledWitnessM, ← smul_add,
      htriad, smul_zero]
  · simp only [scaledWitnessK, scaledWitnessL, scaledWitnessM,
      smul_dotProduct, smul_eq_mul, ha, hb, hc, mul_zero, and_self]

/-- Each receiver is transverse to the output produced by the other two
scaled modes. -/
theorem sym_scaled_witness_receiver_transverse_outputs (s : ℝ) :
    symWitnessC ⬝ᵥ (scaledWitnessK s + scaledWitnessL s) = 0 ∧
    symWitnessB ⬝ᵥ (scaledWitnessK s + scaledWitnessM s) = 0 ∧
    symWitnessA ⬝ᵥ (scaledWitnessL s + scaledWitnessM s) = 0 := by
  rcases sym_scaled_witness_admissible s with ⟨htriad, ha, hb, hc⟩
  have hKML :
      scaledWitnessK s + scaledWitnessM s + scaledWitnessL s = 0 := by
    calc
      scaledWitnessK s + scaledWitnessM s + scaledWitnessL s =
          scaledWitnessK s + scaledWitnessL s + scaledWitnessM s := by abel
      _ = 0 := htriad
  have hLMK :
      scaledWitnessL s + scaledWitnessM s + scaledWitnessK s = 0 := by
    calc
      scaledWitnessL s + scaledWitnessM s + scaledWitnessK s =
          scaledWitnessK s + scaledWitnessL s + scaledWitnessM s := by abel
      _ = 0 := htriad
  exact ⟨
    receiver_orthogonal_output_of_triad
      (scaledWitnessK s) (scaledWitnessL s) (scaledWitnessM s)
      symWitnessC htriad hc,
    receiver_orthogonal_output_of_triad
      (scaledWitnessK s) (scaledWitnessM s) (scaledWitnessL s)
      symWitnessB hKML hb,
    receiver_orthogonal_output_of_triad
      (scaledWitnessL s) (scaledWitnessM s) (scaledWitnessK s)
      symWitnessA hLMK ha⟩

theorem sym_witness_receiver_orthogonal_output :
    symWitnessC ⬝ᵥ (witnessK + witnessL) = 0 := by
  norm_num [symWitnessC, witnessK, witnessL,
    Matrix.vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

theorem sym_scaled_witness_receiver_orthogonal_output (s : ℝ) :
    symWitnessC ⬝ᵥ (scaledWitnessK s + scaledWitnessL s) = 0 :=
  (sym_scaled_witness_receiver_transverse_outputs s).1

/-- At base scale, the two phase-aware input orderings add to `1`. -/
theorem phased_symmetrized_witness_coefficient :
    phasedSymmetrizedOutputCoefficient (-Complex.I) 1 1
      symWitnessA symWitnessB symWitnessC witnessK witnessL
      (witnessK + witnessL) = 1 := by
  rw [phasedSymmetrizedOutputCoefficient_eq_ordered_sum
    (-Complex.I) 1 1 symWitnessA symWitnessB symWitnessC witnessK witnessL
    (witnessK + witnessL) sym_witness_receiver_orthogonal_output]
  norm_num [phasedOrderedCoefficient, orderedTransfer,
    symWitnessA, symWitnessB, symWitnessC, witnessK, witnessL,
    Matrix.vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- At common wavevector scale `s`, the noncancelling symmetrized coefficient
is exactly `s`. -/
theorem phased_symmetrized_scaled_witness_coefficient (s : ℝ) :
    phasedSymmetrizedOutputCoefficient (-Complex.I) 1 1
      symWitnessA symWitnessB symWitnessC
      (scaledWitnessK s) (scaledWitnessL s)
      (scaledWitnessK s + scaledWitnessL s) = s := by
  rw [phasedSymmetrizedOutputCoefficient_eq_ordered_sum
    (-Complex.I) 1 1 symWitnessA symWitnessB symWitnessC
    (scaledWitnessK s) (scaledWitnessL s)
    (scaledWitnessK s + scaledWitnessL s)
    (sym_scaled_witness_receiver_orthogonal_output s)]
  simp [phasedOrderedCoefficient, orderedTransfer,
    scaledWitnessK, scaledWitnessL, symWitnessA, symWitnessB, symWitnessC,
    witnessK, witnessL]

/-- No real upper bound controls this nonzero symmetrized coefficient across
positive common wavevector scales. -/
theorem phased_symmetrized_coefficient_unbounded_across_positive_scale
    (M : ℝ) :
    ∃ s : ℝ, 0 < s ∧
      M < phasedSymmetrizedOutputCoefficient (-Complex.I) 1 1
        symWitnessA symWitnessB symWitnessC
        (scaledWitnessK s) (scaledWitnessL s)
        (scaledWitnessK s + scaledWitnessL s) := by
  refine ⟨|M| + 1, by positivity, ?_⟩
  rw [phased_symmetrized_scaled_witness_coefficient]
  exact lt_of_le_of_lt (le_abs_self M) (lt_add_one |M|)

/-- The six nonzero modes of the finite real Fourier witness. -/
inductive SymWitnessMode where
  | posK | posL | posM | negK | negL | negM
  deriving DecidableEq, Repr

/-- Explicit enumeration of the six witness modes. -/
def SymWitnessMode.enumList : List SymWitnessMode :=
  [.posK, .posL, .posM, .negK, .negL, .negM]

theorem SymWitnessMode.enumList_nodup : SymWitnessMode.enumList.Nodup := by
  decide

instance : Fintype SymWitnessMode :=
  ⟨SymWitnessMode.enumList.toFinset, by
    intro x
    cases x <;> decide⟩

def SymWitnessMode.opposite : SymWitnessMode → SymWitnessMode
  | .posK => .negK
  | .posL => .negL
  | .posM => .negM
  | .negK => .posK
  | .negL => .posL
  | .negM => .posM

theorem SymWitnessMode.opposite_involutive (mode : SymWitnessMode) :
    mode.opposite.opposite = mode := by
  cases mode <;> rfl

def symWitnessModeWave : SymWitnessMode → Space
  | .posK => witnessK
  | .posL => witnessL
  | .posM => witnessM
  | .negK => -witnessK
  | .negL => -witnessL
  | .negM => -witnessM

theorem symWitnessModeWave_opposite (mode : SymWitnessMode) :
    symWitnessModeWave mode.opposite = -symWitnessModeWave mode := by
  cases mode <;> simp [SymWitnessMode.opposite, symWitnessModeWave]

def symWitnessModePhase : SymWitnessMode → ℂ
  | .posK => -Complex.I
  | .posL => 1
  | .posM => 1
  | .negK => Complex.I
  | .negL => 1
  | .negM => 1

def symWitnessModeAmplitude : SymWitnessMode → Space
  | .posK => symWitnessA
  | .posL => symWitnessB
  | .posM => symWitnessC
  | .negK => symWitnessA
  | .negL => symWitnessB
  | .negM => symWitnessC

abbrev SymWitnessComplexSpace := Fin 3 → ℂ

def symPhaseTimesReal
    (phase : ℂ) (amplitude : Space) : SymWitnessComplexSpace :=
  fun i => phase * (amplitude i : ℂ)

/-- The phase-times-real complex Fourier coefficient assigned to each signed
mode. -/
def symWitnessModeCoefficient
    (mode : SymWitnessMode) : SymWitnessComplexSpace :=
  symPhaseTimesReal
    (symWitnessModePhase mode) (symWitnessModeAmplitude mode)

def conjugateSymWitnessComplexSpace
    (coefficient : SymWitnessComplexSpace) : SymWitnessComplexSpace :=
  fun i => starRingEnd ℂ (coefficient i)

/-- Opposite Fourier modes have conjugate coefficients, the exact finite-table
reality condition. -/
theorem symWitnessModeCoefficient_conjugate (mode : SymWitnessMode) :
    symWitnessModeCoefficient mode.opposite =
      conjugateSymWitnessComplexSpace (symWitnessModeCoefficient mode) := by
  cases mode <;> ext i <;>
    simp [SymWitnessMode.opposite, symWitnessModeCoefficient,
      symWitnessModePhase, symWitnessModeAmplitude, symPhaseTimesReal,
      conjugateSymWitnessComplexSpace]

def symComplexDivergenceCoefficient
    (wave : Space) (coefficient : SymWitnessComplexSpace) : ℂ :=
  ∑ i, (wave i : ℂ) * coefficient i

theorem symComplexDivergenceCoefficient_phaseTimesReal
    (wave amplitude : Space) (phase : ℂ) :
    symComplexDivergenceCoefficient wave (symPhaseTimesReal phase amplitude) =
      phase * ((wave ⬝ᵥ amplitude : ℝ) : ℂ) := by
  simp [symComplexDivergenceCoefficient, symPhaseTimesReal,
    dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every signed mode in the concrete coefficient table is divergence-free. -/
theorem symWitnessMode_divergence_free (mode : SymWitnessMode) :
    symComplexDivergenceCoefficient
      (symWitnessModeWave mode) (symWitnessModeCoefficient mode) = 0 := by
  rw [symWitnessModeCoefficient,
    symComplexDivergenceCoefficient_phaseTimesReal]
  cases mode <;>
    norm_num [symWitnessModeWave, symWitnessModePhase,
      symWitnessModeAmplitude, witnessK, witnessL, witnessM,
      symWitnessA, symWitnessB, symWitnessC,
      Matrix.vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]

end Navier.Routes.R7
