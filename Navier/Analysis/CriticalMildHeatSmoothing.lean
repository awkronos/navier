import Navier.Analysis.CriticalMildGlobalClosure

/-!
# Weighted lattice heat representations

The one- and two-derivative coefficient representations are both carried by
Mathlib's complete `ℓ¹` type; their distinction is the explicit decoding
weight.  The presently checked heat API supplies contraction at nonnegative
time.  A frequency-gain estimate with a time singularity is a separate,
currently unproved analytic leaf.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatSmoothing

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedSpace

/-- A Mathlib complete `ℓ¹` representative intended to encode one lattice
weight.  Decoding by `latticeModeWeight⁻¹` is defined in the preceding file. -/
abbrev LatticeWeightOneCarrier := lp (fun _ : LatticeMode => ComplexE3) 1

/-- A Mathlib complete `ℓ¹` representative intended to encode two lattice
weights.  The representation is distinct semantically through the displayed
decoder, not through bespoke norm axioms. -/
abbrev LatticeWeightTwoCarrier := lp (fun _ : LatticeMode => ComplexE3) 1

/-- Decode a two-weight representative to a complex Fourier coefficient. -/
def latticeWeightTwoCoefficient (u : LatticeWeightTwoCarrier)
    (m : LatticeMode) : ComplexSpace :=
  WithLp.ofLp ((latticeModeWeight m ^ 2)⁻¹ • u m)

/-- The exact heat--Leray multiplier is contractive at nonnegative time in
the Hermitian Euclidean coefficient norm. -/
theorem complexEuclideanNorm_heatLeray_le (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (k : LatticeMode) (z : ComplexSpace) :
    complexEuclideanNorm
      (complexFrequencyHeatLeray ν τ (latticeFrequency k) z) ≤
      complexEuclideanNorm z :=
  complexEuclideanNorm_complexFrequencyHeatLeray_le hν hτ _ _

/-- The scalar part of the actual heat multiplier is nonnegative and at most
one at nonnegative time. -/
theorem latticeHeatDecay_bounds (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (k : LatticeMode) :
    0 ≤ complexHeatDecay ν τ (latticeFrequency k) ∧
      complexHeatDecay ν τ (latticeFrequency k) ≤ 1 :=
  ⟨complexHeatDecay_nonneg _ _ _, complexHeatDecay_le_one hν hτ _⟩

end Navier.Analysis.CriticalMildHeatSmoothing
