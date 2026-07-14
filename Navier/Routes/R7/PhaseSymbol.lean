import Navier.Routes.R7.ScaledTriad

/-!
# Phase-aware normalized R7 symbol coefficient

This file closes two representation gaps in the earlier real triad coefficient
probe while keeping the scope finite-dimensional and explicit.

* `normalizedLeraySymbol` is the normalized real Leray multiplier, totalized at
  zero frequency by the identity convention.
* `phasedOrderedCoefficient` restores a declared Fourier derivative factor `i`
  and complex scalar phase factors for real polarization vectors, conjugating
  the receiver phase as in a Hermitian energy pairing.
* The preserved witness has fixed polarizations and fixed unit phases while a
  common positive wavevector scale makes one normalized coefficient unbounded.

This is symbol algebra for a phase-times-real-polarization ansatz.  It does not
construct a Fourier transform or series, a conjugate-symmetric finite-energy
velocity field, a shell flux, a Navier--Stokes solution, or a regularity result.
Overall signs and nonzero constants depend on the stated Fourier convention;
the nonvanishing and frequency-growth conclusions do not.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

/-- The normalized Leray multiplier on real polarizations.  Lean's field
division convention makes the correction vanish at `q = 0`, so the zero mode
is explicitly totalized by the identity map. -/
def normalizedLeraySymbol (q v : Space) : Space :=
  v - ((v ⬝ᵥ q) / (q ⬝ᵥ q)) • q

theorem normalizedLeraySymbol_zero (v : Space) :
    normalizedLeraySymbol 0 v = v := by
  simp [normalizedLeraySymbol]

/-- Pairing the normalized symbol against an output-transverse receiver removes
the longitudinal correction, including under the declared zero-mode
totalization. -/
theorem receiver_dot_normalizedLeraySymbol
    (q b c : Space) (hc : c ⬝ᵥ q = 0) :
    c ⬝ᵥ normalizedLeraySymbol q b = b ⬝ᵥ c := by
  simp [normalizedLeraySymbol, hc, dotProduct_comm c b]

/-- One normalized, projected, ordered real symbol coefficient before the
Fourier derivative phase is applied. -/
def normalizedProjectedOrderedCoefficient
    (advector advected receiver advectedWave outputWave : Space) : ℝ :=
  (advector ⬝ᵥ advectedWave) *
    (receiver ⬝ᵥ normalizedLeraySymbol outputWave advected)

/-- On an output-transverse receiver, the normalized projected coefficient is
the earlier denominator-free `orderedTransfer` coefficient. -/
theorem normalizedProjectedOrderedCoefficient_eq_orderedTransfer
    (advector advected receiver advectedWave outputWave : Space)
    (hreceiver : receiver ⬝ᵥ outputWave = 0) :
    normalizedProjectedOrderedCoefficient
        advector advected receiver advectedWave outputWave =
      orderedTransfer advector advected receiver advectedWave := by
  simp [normalizedProjectedOrderedCoefficient, orderedTransfer,
    receiver_dot_normalizedLeraySymbol outputWave advected receiver hreceiver]

/-- In a wavevector triad, divergence-freeness at the receiver's own wavevector
makes it transverse to the output of the other two modes. -/
theorem receiver_orthogonal_output_of_triad
    (k l m c : Space)
    (htriad : k + l + m = 0)
    (hc : m ⬝ᵥ c = 0) :
    c ⬝ᵥ (k + l) = 0 := by
  have hkl : k + l = -m := by
    calc
      k + l = (k + l + m) - m := by abel
      _ = -m := by rw [htriad]; simp
  calc
    c ⬝ᵥ (k + l) = c ⬝ᵥ (-m) := by rw [hkl]
    _ = -(c ⬝ᵥ m) := by simp
    _ = 0 := by rw [dotProduct_comm c m, hc]; simp

/-- Under the convention `widehat(partial_j f) = i xi_j widehat(f)`, this is
the real phase-aware value of one ordered symbol coefficient.  The complex
arguments are scalar factors multiplying the three real polarizations; no full
Fourier field is constructed here. -/
def phasedOrderedCoefficient
    (advectorPhase advectedPhase receiverPhase : ℂ)
    (advector advected receiver advectedWave : Space) : ℝ :=
  (Complex.I * advectorPhase * advectedPhase *
    (starRingEnd ℂ receiverPhase) *
    (orderedTransfer advector advected receiver advectedWave : ℂ)).re

/-- The corresponding phase-aware coefficient with the normalized Leray symbol
still present. -/
def phasedNormalizedProjectedCoefficient
    (advectorPhase advectedPhase receiverPhase : ℂ)
    (advector advected receiver advectedWave outputWave : Space) : ℝ :=
  (Complex.I * advectorPhase * advectedPhase *
    (starRingEnd ℂ receiverPhase) *
    (normalizedProjectedOrderedCoefficient
      advector advected receiver advectedWave outputWave : ℂ)).re

theorem phasedNormalizedProjectedCoefficient_eq_ordered
    (advectorPhase advectedPhase receiverPhase : ℂ)
    (advector advected receiver advectedWave outputWave : Space)
    (hreceiver : receiver ⬝ᵥ outputWave = 0) :
    phasedNormalizedProjectedCoefficient
        advectorPhase advectedPhase receiverPhase
        advector advected receiver advectedWave outputWave =
      phasedOrderedCoefficient
        advectorPhase advectedPhase receiverPhase
        advector advected receiver advectedWave := by
  rw [phasedNormalizedProjectedCoefficient, phasedOrderedCoefficient,
    normalizedProjectedOrderedCoefficient_eq_orderedTransfer
      advector advected receiver advectedWave outputWave hreceiver]

/-- Restoring `i` with no compensating complex phase makes the earlier real
witness contribute zero real part. -/
theorem unphased_witness_real_part_zero :
    phasedOrderedCoefficient 1 1 1
      witnessA witnessB witnessC witnessL = 0 := by
  rw [phasedOrderedCoefficient, witness_nontermwise_cancellation.1]
  norm_num

/-- Fixed unit phases `(-i, 1, 1)` turn the preserved nonzero real coefficient
into the real phase-aware value `1`. -/
theorem phased_witness_orderedCoefficient :
    phasedOrderedCoefficient (-Complex.I) 1 1
      witnessA witnessB witnessC witnessL = 1 := by
  rw [phasedOrderedCoefficient, witness_nontermwise_cancellation.1]
  norm_num

theorem witness_phase_factors_have_unit_norm :
    ‖(-Complex.I)‖ = 1 ∧ ‖(1 : ℂ)‖ = 1 ∧ ‖(1 : ℂ)‖ = 1 := by
  norm_num

theorem witness_receiver_orthogonal_output :
    witnessC ⬝ᵥ (witnessK + witnessL) = 0 := by
  rcases witness_admissible with ⟨htriad, _, _, hc⟩
  exact receiver_orthogonal_output_of_triad
    witnessK witnessL witnessM witnessC htriad hc

/-- The nonzero witness survives the normalized Leray multiplier at its actual
output wavevector. -/
theorem phased_normalized_witness_coefficient :
    phasedNormalizedProjectedCoefficient (-Complex.I) 1 1
      witnessA witnessB witnessC witnessL (witnessK + witnessL) = 1 := by
  rw [phasedNormalizedProjectedCoefficient_eq_ordered
    (-Complex.I) 1 1 witnessA witnessB witnessC witnessL
    (witnessK + witnessL) witness_receiver_orthogonal_output]
  exact phased_witness_orderedCoefficient

/-- The opposite ordered real coefficient in the same preserved triad is
negative. -/
theorem witness_opposite_orderedCoefficient :
    orderedTransfer witnessA witnessC witnessB witnessM = -1 := by
  norm_num [orderedTransfer, witnessA, witnessB, witnessC, witnessM,
    Matrix.vec3_dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]

theorem scaled_witness_receiver_orthogonal_output (s : ℝ) :
    witnessC ⬝ᵥ (scaledWitnessK s + scaledWitnessL s) = 0 := by
  rcases scaled_witness_admissible s with ⟨htriad, _, _, hc⟩
  exact receiver_orthogonal_output_of_triad
    (scaledWitnessK s) (scaledWitnessL s) (scaledWitnessM s)
    witnessC htriad hc

/-- With phases and polarizations fixed, the normalized phase-aware coefficient
is exactly the common wavevector scale. -/
theorem phased_scaled_normalized_coefficient (s : ℝ) :
    phasedNormalizedProjectedCoefficient (-Complex.I) 1 1
      witnessA witnessB witnessC (scaledWitnessL s)
      (scaledWitnessK s + scaledWitnessL s) = s := by
  rw [phasedNormalizedProjectedCoefficient_eq_ordered
    (-Complex.I) 1 1 witnessA witnessB witnessC (scaledWitnessL s)
    (scaledWitnessK s + scaledWitnessL s)
    (scaled_witness_receiver_orthogonal_output s)]
  simp [phasedOrderedCoefficient, scaled_witness_orderedTransfer]

/-- Every proposed real upper bound is exceeded at a positive common wavevector
scale.  The conclusion carries the full admissibility certificate for the
three scaled wavevectors while all real polarizations and complex phases remain
fixed. -/
theorem phased_normalized_coefficient_unbounded_across_positive_scale (M : ℝ) :
    ∃ s : ℝ, 0 < s ∧
      (scaledWitnessK s + scaledWitnessL s + scaledWitnessM s = 0 ∧
       scaledWitnessK s ⬝ᵥ witnessA = 0 ∧
       scaledWitnessL s ⬝ᵥ witnessB = 0 ∧
       scaledWitnessM s ⬝ᵥ witnessC = 0) ∧
      M < phasedNormalizedProjectedCoefficient (-Complex.I) 1 1
        witnessA witnessB witnessC (scaledWitnessL s)
        (scaledWitnessK s + scaledWitnessL s) := by
  refine ⟨|M| + 1, by positivity, scaled_witness_admissible (|M| + 1), ?_⟩
  rw [phased_scaled_normalized_coefficient]
  exact lt_of_le_of_lt (le_abs_self M) (lt_add_one |M|)

end Navier.Routes.R7
