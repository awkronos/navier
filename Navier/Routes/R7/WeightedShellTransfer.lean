import Navier.Routes.R7.SymmetrizedWitness

/-!
# Weighted collective transfer for the noncancelling R7 witness

This file evaluates all three receiver outputs of the conjugate-compatible
triad from `SymmetrizedWitness`.  The complete phase-aware, two-ordering rates
are exactly `(0, -s, s)`: unweighted energy cancels collectively, while a
nonconstant shell weight detects transfer between the equal-radius `K/L`
shell and the larger-radius `M` shell.

In particular, weighting by squared frequency gives the positive value `s^3`
at positive scale.  This is an exact finite-dimensional symbol calculation.
It is not yet a Fourier-series shell balance or a Navier--Stokes evolution;
`FieldLeakage` separately records that the six-mode table is not invariant
under the quadratic convolution.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

/-- Symmetrized rate at the output `L + M = -K`, paired with the `K`-mode
polarization and the Hermitian-table phase `+i` of the `-K` mode. -/
def symWitnessRateK (s : ℝ) : ℝ :=
  phasedSymmetrizedOutputCoefficient
    1 1 Complex.I
    symWitnessB symWitnessC symWitnessA
    (scaledWitnessL s) (scaledWitnessM s)
    (scaledWitnessL s + scaledWitnessM s)

/-- Symmetrized rate paired with the `L`-mode polarization. -/
def symWitnessRateL (s : ℝ) : ℝ :=
  phasedSymmetrizedOutputCoefficient
    (-Complex.I) 1 1
    symWitnessA symWitnessC symWitnessB
    (scaledWitnessK s) (scaledWitnessM s)
    (scaledWitnessK s + scaledWitnessM s)

/-- Symmetrized rate paired with the `M`-mode polarization. -/
def symWitnessRateM (s : ℝ) : ℝ :=
  phasedSymmetrizedOutputCoefficient
    (-Complex.I) 1 1
    symWitnessA symWitnessB symWitnessC
    (scaledWitnessK s) (scaledWitnessL s)
    (scaledWitnessK s + scaledWitnessL s)

theorem symWitnessRateK_eq_zero (s : ℝ) : symWitnessRateK s = 0 := by
  rw [symWitnessRateK,
    phasedSymmetrizedOutputCoefficient_eq_ordered_sum
      1 1 Complex.I symWitnessB symWitnessC symWitnessA
      (scaledWitnessL s) (scaledWitnessM s)
      (scaledWitnessL s + scaledWitnessM s)
      (sym_scaled_witness_receiver_transverse_outputs s).2.2]
  simp [phasedOrderedCoefficient, orderedTransfer,
    scaledWitnessL, scaledWitnessM, symWitnessA, symWitnessB, symWitnessC,
    witnessL, witnessM]

theorem symWitnessRateL_eq_neg (s : ℝ) : symWitnessRateL s = -s := by
  rw [symWitnessRateL,
    phasedSymmetrizedOutputCoefficient_eq_ordered_sum
      (-Complex.I) 1 1 symWitnessA symWitnessC symWitnessB
      (scaledWitnessK s) (scaledWitnessM s)
      (scaledWitnessK s + scaledWitnessM s)
      (sym_scaled_witness_receiver_transverse_outputs s).2.1]
  simp [phasedOrderedCoefficient, orderedTransfer,
    scaledWitnessK, scaledWitnessM, symWitnessA, symWitnessB, symWitnessC,
    witnessK, witnessM]

theorem symWitnessRateM_eq (s : ℝ) : symWitnessRateM s = s := by
  exact phased_symmetrized_scaled_witness_coefficient s

/-- An arbitrary real weight assigned to each of the three receiver modes. -/
def symWitnessWeightedRate
    (weightK weightL weightM s : ℝ) : ℝ :=
  weightK * symWitnessRateK s +
    weightL * symWitnessRateL s +
    weightM * symWitnessRateM s

/-- Only the difference between the `M` and `L` weights survives. -/
theorem symWitnessWeightedRate_eq
    (weightK weightL weightM s : ℝ) :
    symWitnessWeightedRate weightK weightL weightM s =
      s * (weightM - weightL) := by
  rw [symWitnessWeightedRate, symWitnessRateK_eq_zero,
    symWitnessRateL_eq_neg, symWitnessRateM_eq]
  ring

/-- Constant weights recover exact collective energy cancellation. -/
theorem symWitness_constantWeight_cancels (weight s : ℝ) :
    symWitnessWeightedRate weight weight weight s = 0 := by
  rw [symWitnessWeightedRate_eq]
  ring

/-- The squared-frequency weighted collective rate of the concrete triad. -/
def symWitnessSquaredFrequencyRate (s : ℝ) : ℝ :=
  (scaledWitnessK s ⬝ᵥ scaledWitnessK s) * symWitnessRateK s +
    (scaledWitnessL s ⬝ᵥ scaledWitnessL s) * symWitnessRateL s +
    (scaledWitnessM s ⬝ᵥ scaledWitnessM s) * symWitnessRateM s

/-- The `K` and `L` modes have squared frequency `s^2`, while `M` has squared
frequency `2s^2`; the resulting weighted rate is exactly `s^3`. -/
theorem symWitnessSquaredFrequencyRate_eq_cube (s : ℝ) :
    symWitnessSquaredFrequencyRate s = s ^ 3 := by
  rw [symWitnessSquaredFrequencyRate, symWitnessRateK_eq_zero,
    symWitnessRateL_eq_neg, symWitnessRateM_eq]
  simp [scaledWitnessK, scaledWitnessL, scaledWitnessM,
    witnessK, witnessL, witnessM]
  ring

/-- At every positive scale the squared-frequency weight sees strictly
positive transfer, despite the exact constant-weight cancellation. -/
theorem symWitnessSquaredFrequencyRate_pos
    (s : ℝ) (hs : 0 < s) :
    0 < symWitnessSquaredFrequencyRate s := by
  rw [symWitnessSquaredFrequencyRate_eq_cube]
  positivity

end Navier.Routes.R7
