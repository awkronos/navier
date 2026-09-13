import Navier.Analysis.CriticalMildWeightedSpace

/-!
# Complete weighted lattice coefficient carrier

The carrier here is Mathlib's complete `ℓ¹` space over the concrete lattice,
with a coefficient decoder that divides by the already checked frequency
weight.  No bespoke normed-space axioms are introduced.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildWeightedBanach

open scoped ENNReal
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace

/-- The complete Mathlib `ℓ¹` carrier for weighted lattice coefficients,
represented after multiplication by `latticeModeWeight`. -/
abbrev WeightedLatticeBanach := lp (fun _ : LatticeMode => ComplexE3) 1

/-- Decode an `ℓ¹` representative to the physical complex coefficient by
dividing by the positive lattice weight. -/
def weightedLatticeCoefficient (u : WeightedLatticeBanach)
    (m : LatticeMode) : ComplexSpace :=
  WithLp.ofLp ((latticeModeWeight m)⁻¹ • u m)

/-- A coordinate evaluation in the Mathlib `ℓ¹` carrier is norm controlled. -/
theorem norm_weightedLattice_eval_le (u : WeightedLatticeBanach) (m : LatticeMode) :
    ‖u m‖ ≤ ‖u‖ :=
  lp.norm_apply_le_norm one_ne_zero u m

/-- Decoding preserves the intended weighted amplitude exactly. -/
theorem latticeWeightedAmplitude_coefficient (u : WeightedLatticeBanach)
    (m : LatticeMode) :
    latticeWeightedAmplitude (weightedLatticeCoefficient u) m = ‖u m‖ := by
  unfold latticeWeightedAmplitude weightedLatticeCoefficient complexEuclideanNorm
  rw [complexEuclideanPoint]
  rw [norm_smul]
  have hpos : 0 < latticeModeWeight m :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m)
  have hm : latticeModeWeight m ≠ 0 := by
    exact ne_of_gt hpos
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  field_simp

/-- Every member of the Mathlib carrier decodes to a sequence satisfying the
explicit weighted `ℓ¹` contract used by the transport-series estimate. -/
theorem latticeWeightedL1_coefficient (u : WeightedLatticeBanach) :
    LatticeWeightedL1 (weightedLatticeCoefficient u) := by
  change Summable (latticeWeightedAmplitude (weightedLatticeCoefficient u))
  rw [show latticeWeightedAmplitude (weightedLatticeCoefficient u) = fun m => ‖u m‖ by
    funext m
    exact latticeWeightedAmplitude_coefficient u m]
  exact .of_norm (by simpa using u.2.summable)

/-- The `ℓ¹` norm is exactly the weighted-amplitude sum of the decoded
coefficient sequence. -/
theorem tsum_latticeWeightedAmplitude_coefficient (u : WeightedLatticeBanach) :
    (∑' m, latticeWeightedAmplitude (weightedLatticeCoefficient u) m) = ‖u‖ := by
  rw [show latticeWeightedAmplitude (weightedLatticeCoefficient u) = fun m => ‖u m‖ by
    funext m
    exact latticeWeightedAmplitude_coefficient u m]
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp [ENNReal.toReal_one]

/-- The actual countable lattice transport convolution evaluated on decoded
complete-space coefficients. -/
def weightedLatticeSpectralConvolution (k : LatticeMode)
    (u z : WeightedLatticeBanach) : ComplexE3 :=
  latticeSpectralConvolution k (weightedLatticeCoefficient u)
    (weightedLatticeCoefficient z)

/-- The actual transport series has the expected product bound on the
complete Mathlib carrier. -/
theorem norm_weightedLatticeSpectralConvolution_le (k : LatticeMode)
    (u z : WeightedLatticeBanach) :
    ‖weightedLatticeSpectralConvolution k u z‖ ≤ ‖u‖ * ‖z‖ := by
  unfold weightedLatticeSpectralConvolution
  calc
    ‖latticeSpectralConvolution k (weightedLatticeCoefficient u)
        (weightedLatticeCoefficient z)‖ ≤
      (∑' m, latticeWeightedAmplitude (weightedLatticeCoefficient u) m) *
        ∑' n, latticeWeightedAmplitude (weightedLatticeCoefficient z) n :=
      norm_latticeSpectralConvolution_le_weightedProduct k
        (weightedLatticeCoefficient u) (weightedLatticeCoefficient z)
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient z)
    _ = ‖u‖ * ‖z‖ := by
      rw [tsum_latticeWeightedAmplitude_coefficient,
        tsum_latticeWeightedAmplitude_coefficient]

end Navier.Analysis.CriticalMildWeightedBanach
