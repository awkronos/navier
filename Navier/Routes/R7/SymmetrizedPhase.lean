import Navier.Routes.R7.PhaseSymbol

/-!
# Two-ordering phase-aware R7 output coefficient

The Fourier convolution at one output receives both orderings of two input
modes.  This file records that symmetrization explicitly: the first mode
advects the second and is then exchanged with it, including their phases and
wavevectors, while the receiver and output wavevector stay fixed.

For the original scaled witness in `PhaseSymbol`, the ordered coefficient that
grows like the common frequency scale is canceled exactly by its exchanged
ordering.  Consequently that witness falsifies a termwise bound, but cannot by
itself witness a nonzero symmetrized output.  No Fourier field, shell flux, or
Navier--Stokes solution is constructed here.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Routes.R7

/-- The fully symmetrized phase-aware coefficient at one fixed output and
receiver.  `firstWave` and `secondWave` are the wavevectors belonging to the
corresponding inputs; the derivative factor in each ordered term therefore
uses the wavevector of that term's advected input. -/
def phasedSymmetrizedOutputCoefficient
    (firstPhase secondPhase receiverPhase : ℂ)
    (first second receiver firstWave secondWave outputWave : Space) : ℝ :=
  phasedNormalizedProjectedCoefficient
      firstPhase secondPhase receiverPhase
      first second receiver secondWave outputWave +
    phasedNormalizedProjectedCoefficient
      secondPhase firstPhase receiverPhase
      second first receiver firstWave outputWave

/-- An output-transverse receiver removes the normalized Leray correction in
both convolution orderings. -/
theorem phasedSymmetrizedOutputCoefficient_eq_ordered_sum
    (firstPhase secondPhase receiverPhase : ℂ)
    (first second receiver firstWave secondWave outputWave : Space)
    (hreceiver : receiver ⬝ᵥ outputWave = 0) :
    phasedSymmetrizedOutputCoefficient
        firstPhase secondPhase receiverPhase
        first second receiver firstWave secondWave outputWave =
      phasedOrderedCoefficient
          firstPhase secondPhase receiverPhase
          first second receiver secondWave +
        phasedOrderedCoefficient
          secondPhase firstPhase receiverPhase
          second first receiver firstWave := by
  rw [phasedSymmetrizedOutputCoefficient]
  rw [phasedNormalizedProjectedCoefficient_eq_ordered
      firstPhase secondPhase receiverPhase
      first second receiver secondWave outputWave hreceiver]
  rw [phasedNormalizedProjectedCoefficient_eq_ordered
      secondPhase firstPhase receiverPhase
      second first receiver firstWave outputWave hreceiver]

/-- At every real common wavevector scale, the two input orderings of the
repository's original phase witness cancel exactly at their shared output. -/
theorem phased_symmetrized_scaled_witness_cancels (s : ℝ) :
    phasedSymmetrizedOutputCoefficient
      (-Complex.I) 1 1
      witnessA witnessB witnessC
      (scaledWitnessK s) (scaledWitnessL s)
      (scaledWitnessK s + scaledWitnessL s) = 0 := by
  rw [phasedSymmetrizedOutputCoefficient]
  rw [phasedNormalizedProjectedCoefficient_eq_ordered
      (-Complex.I) 1 1 witnessA witnessB witnessC (scaledWitnessL s)
      (scaledWitnessK s + scaledWitnessL s)
      (scaled_witness_receiver_orthogonal_output s)]
  rw [phasedNormalizedProjectedCoefficient_eq_ordered
      1 (-Complex.I) 1 witnessB witnessA witnessC (scaledWitnessK s)
      (scaledWitnessK s + scaledWitnessL s)
      (scaled_witness_receiver_orthogonal_output s)]
  simp [phasedOrderedCoefficient, orderedTransfer,
    scaledWitnessK, scaledWitnessL, witnessA, witnessB, witnessC,
    witnessK, witnessL]

/-- The first ordered term still equals the scale `s`, but the physically
required exchanged input ordering makes their symmetrized output zero. -/
theorem scaled_ordered_growth_does_not_give_symmetrized_nonzero (s : ℝ) :
    phasedNormalizedProjectedCoefficient (-Complex.I) 1 1
        witnessA witnessB witnessC (scaledWitnessL s)
        (scaledWitnessK s + scaledWitnessL s) = s ∧
      phasedSymmetrizedOutputCoefficient
        (-Complex.I) 1 1
        witnessA witnessB witnessC
        (scaledWitnessK s) (scaledWitnessL s)
        (scaledWitnessK s + scaledWitnessL s) = 0 :=
  ⟨phased_scaled_normalized_coefficient s,
    phased_symmetrized_scaled_witness_cancels s⟩

/-- No scale in the original witness family has a nonzero symmetrized output
coefficient, despite its unbounded first ordered term. -/
theorem no_scaled_witness_nonzero_symmetrized_output :
    ¬ ∃ s : ℝ,
      phasedSymmetrizedOutputCoefficient
        (-Complex.I) 1 1
        witnessA witnessB witnessC
        (scaledWitnessK s) (scaledWitnessL s)
        (scaledWitnessK s + scaledWitnessL s) ≠ 0 := by
  rintro ⟨s, hs⟩
  exact hs (phased_symmetrized_scaled_witness_cancels s)

end Navier.Routes.R7
