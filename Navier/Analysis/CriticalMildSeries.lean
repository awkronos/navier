import Navier.Analysis.CriticalMildConvolution

/-!
# Countable lattice Fourier convolution for the mild layer

This module supplies the countable `ℤ³` carrier missing from the finite-mode
convolution layer.  Its convergence hypothesis is a literal weighted `ℓ¹`
summability statement for the displayed Fourier terms; it neither postulates a
limit nor asserts a PDE endpoint estimate.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildSeries

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamel

/-- The concrete countable Fourier-mode carrier `ℤ³`. -/
abbrev LatticeMode := ℤ × (ℤ × ℤ)

/-- Embed an integer lattice mode as its corresponding real frequency in
three-dimensional physical space. -/
def latticeFrequency (m : LatticeMode) : Space :=
  ![(m.1 : ℝ), (m.2.1 : ℝ), (m.2.2 : ℝ)]

/-- The actual projected transport summand for one ordered pair of lattice
modes.  It contributes to `k` exactly when the two lattice indices add to
`k`. -/
def latticeSpectralTerm (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) : ComplexE3 :=
  if ij.1 + ij.2 = k then
    complexEuclideanPoint
      (spectralTransport (latticeFrequency ij.2) (v ij.1) (w ij.2))
  else 0

/-- The countable Fourier convolution is the `tsum` of its literal lattice
transport summands. -/
def latticeSpectralConvolution (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) : ComplexE3 :=
  ∑' ij : LatticeMode × LatticeMode, latticeSpectralTerm k v w ij

/-- The scalar weighted `ℓ¹` majorant of the actual transport series. -/
def latticeSpectralMajorant (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) : ℝ :=
  if ij.1 + ij.2 = k then
    ‖complexFrequency (latticeFrequency ij.2)‖ *
      complexEuclideanNorm (v ij.1) * complexEuclideanNorm (w ij.2)
  else 0

/-- The explicit weighted `ℓ¹` hypothesis for a single output lattice mode.
This is solely summability of the displayed scalar majorant. -/
def LatticeConvolutionWeightedL1 (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) : Prop :=
  Summable (latticeSpectralMajorant k v w)

/-- Each actual lattice transport term is controlled by the displayed
frequency-weighted scalar majorant. -/
theorem norm_latticeSpectralTerm_le_majorant (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (ij : LatticeMode × LatticeMode) :
    ‖latticeSpectralTerm k v w ij‖ ≤ latticeSpectralMajorant k v w ij := by
  by_cases hij : ij.1 + ij.2 = k
  · rw [latticeSpectralTerm, latticeSpectralMajorant, if_pos hij, if_pos hij]
    simpa [complexEuclideanNorm] using
      complexEuclideanNorm_spectralTransport_le
        (latticeFrequency ij.2) (v ij.1) (w ij.2)
  · rw [latticeSpectralTerm, latticeSpectralMajorant, if_neg hij, if_neg hij]
    simp

/-- The explicit weighted `ℓ¹` majorant gives genuine convergence of the
countable lattice convolution. -/
theorem summable_latticeSpectralTerm_of_weightedL1 (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (h : LatticeConvolutionWeightedL1 k v w) :
    Summable (latticeSpectralTerm k v w) := by
  exact h.of_norm_bounded (norm_latticeSpectralTerm_le_majorant k v w)

/-- Norm control for the countable actual lattice convolution from its
explicit weighted `ℓ¹` majorant. -/
theorem norm_latticeSpectralConvolution_le_weighted_tsum (k : LatticeMode)
    (v w : LatticeMode → ComplexSpace) (h : LatticeConvolutionWeightedL1 k v w) :
    ‖latticeSpectralConvolution k v w‖ ≤ ∑' ij : LatticeMode × LatticeMode,
      latticeSpectralMajorant k v w ij := by
  unfold latticeSpectralConvolution
  exact tsum_of_norm_bounded h.hasSum
    (norm_latticeSpectralTerm_le_majorant k v w)

end Navier.Analysis.CriticalMildSeries
