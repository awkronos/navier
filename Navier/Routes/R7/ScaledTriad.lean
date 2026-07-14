import Navier.Routes.R7.Triad

/-!
# Scale saturation for the exact triad witness

This module scales the wavevectors in the concrete admissible triad from
`Navier.Routes.R7.Triad` while leaving its amplitudes fixed.  The collective
six-transfer cancellation survives, but the nonzero ordered transfer grows
linearly with frequency scale.

This is a falsifier for an unweighted, frequency-uniform bound on individual
transfers.  It does not rule out weighted or collective shell estimates and
does not establish Fourier summability or Navier--Stokes regularity.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

/-- Scale the three witness wavevectors by the same real factor. -/
def scaledWitnessK (s : ℝ) : Space := s • witnessK
def scaledWitnessL (s : ℝ) : Space := s • witnessL
def scaledWitnessM (s : ℝ) : Space := s • witnessM

/-- Common scaling preserves the wavevector triad and the three
divergence-free amplitude constraints. -/
theorem scaled_witness_admissible (s : ℝ) :
    scaledWitnessK s + scaledWitnessL s + scaledWitnessM s = 0 ∧
    scaledWitnessK s ⬝ᵥ witnessA = 0 ∧
    scaledWitnessL s ⬝ᵥ witnessB = 0 ∧
    scaledWitnessM s ⬝ᵥ witnessC = 0 := by
  rcases witness_admissible with ⟨htriad, ha, hb, hc⟩
  constructor
  · simp only [scaledWitnessK, scaledWitnessL, scaledWitnessM, ← smul_add,
      htriad, smul_zero]
  · simp only [scaledWitnessK, scaledWitnessL, scaledWitnessM,
      smul_dotProduct, smul_eq_mul, ha, hb, hc, mul_zero, and_self]

/-- With amplitudes fixed, the concrete nonzero ordered transfer is exactly
the frequency scale `s`. -/
theorem scaled_witness_orderedTransfer (s : ℝ) :
    orderedTransfer witnessA witnessB witnessC (scaledWitnessL s) = s := by
  simp only [orderedTransfer, scaledWitnessL, dotProduct_smul]
  norm_num [witnessA, witnessB, witnessC, witnessL,
    Matrix.vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

/-- Collective energy cancellation persists at every common frequency
scale, even though an individual transfer need not vanish. -/
theorem scaled_witness_sixTransferSum (s : ℝ) :
    sixTransferSum (scaledWitnessK s) (scaledWitnessL s) (scaledWitnessM s)
      witnessA witnessB witnessC = 0 := by
  rcases scaled_witness_admissible s with ⟨htriad, ha, hb, hc⟩
  exact six_transfer_sum_zero
    (scaledWitnessK s) (scaledWitnessL s) (scaledWitnessM s)
    witnessA witnessB witnessC htriad ha hb hc

/-- Individual unweighted transfer is not uniformly bounded across frequency
scale: for every proposed upper bound, a positive scale exceeds it. -/
theorem orderedTransfer_unbounded_across_scale (M : ℝ) :
    ∃ s : ℝ, 0 < s ∧
      M < orderedTransfer witnessA witnessB witnessC (scaledWitnessL s) := by
  refine ⟨|M| + 1, by positivity, ?_⟩
  rw [scaled_witness_orderedTransfer]
  exact lt_of_le_of_lt (le_abs_self M) (lt_add_one |M|)

end Navier.Routes.R7
