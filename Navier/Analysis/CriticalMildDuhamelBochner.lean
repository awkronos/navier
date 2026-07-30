import Navier.Analysis.CriticalMildHeatCoefficientLift
import Navier.Analysis.CriticalMildWeightedBanach

/-!
# Output-frequency heat regularization of the actual lattice nonlinearity

The heat multiplier is deliberately applied after forming the literal lattice
transport convolution, at its output frequency.  This file does not heat an
input and does not assert a same-weight global closure without a lattice heat
kernel summability proof.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildDuhamelBochner

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatCoefficientLift

/-- The physical nonlinear coefficient is the existing actual countable
lattice convolution of two decoded one-weight carrier inputs. -/
def spectralOutputCoefficient (k : LatticeMode)
    (u v : WeightedLatticeBanach) : ComplexSpace :=
  WithLp.ofLp (weightedLatticeSpectralConvolution k u v)

/-- Apply the actual heat--Leray multiplier only after the nonlinear output
fiber has been formed, then encode its one output weight. -/
def heatRegularizedSpectralOutputFiber (ν τ : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) : ComplexE3 :=
  latticeModeWeight k • complexEuclideanPoint
    (complexFrequencyHeatLeray ν τ (latticeFrequency k)
      (spectralOutputCoefficient k u v))

/-- The physical output coefficient has exactly the norm of the existing
completed convolution fiber. -/
theorem complexEuclideanNorm_spectralOutputCoefficient (k : LatticeMode)
    (u v : WeightedLatticeBanach) :
    complexEuclideanNorm (spectralOutputCoefficient k u v) =
      ‖weightedLatticeSpectralConvolution k u v‖ := by
  unfold spectralOutputCoefficient complexEuclideanNorm
  rfl

/-- Per-output-mode heat regularization gains the exact positive-time
inhomogeneous factor while requiring only the two one-weight input carriers. -/
theorem norm_heatRegularizedSpectralOutputFiber_le (ν τ : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) :
    ‖heatRegularizedSpectralOutputFiber ν τ k u v‖ ≤
      (1 + (Real.sqrt (ν * τ))⁻¹) * ‖u‖ * ‖v‖ := by
  unfold heatRegularizedSpectralOutputFiber
  rw [norm_smul, Real.norm_of_nonneg
    (zero_le_one.trans (one_le_latticeModeWeight k))]
  change latticeModeWeight k * complexEuclideanNorm
    (complexFrequencyHeatLeray ν τ (latticeFrequency k)
      (spectralOutputCoefficient k u v)) ≤ _
  calc
    latticeModeWeight k * complexEuclideanNorm
        (complexFrequencyHeatLeray ν τ (latticeFrequency k)
          (spectralOutputCoefficient k u v)) ≤
        (1 + (Real.sqrt (ν * τ))⁻¹) *
          complexEuclideanNorm (spectralOutputCoefficient k u v) :=
      latticeModeWeight_heatLeray_coefficient_le ν τ hν hτ k
        (spectralOutputCoefficient k u v)
    _ = (1 + (Real.sqrt (ν * τ))⁻¹) *
        ‖weightedLatticeSpectralConvolution k u v‖ := by
      rw [complexEuclideanNorm_spectralOutputCoefficient]
    _ ≤ (1 + (Real.sqrt (ν * τ))⁻¹) * (‖u‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_weightedLatticeSpectralConvolution_le k u v)
        (by positivity)
    _ = (1 + (Real.sqrt (ν * τ))⁻¹) * ‖u‖ * ‖v‖ := by ring

end Navier.Analysis.CriticalMildDuhamelBochner
