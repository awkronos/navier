import Navier.Analysis.CriticalMildHeatCoefficientLift
import Navier.Analysis.CriticalMildWeightedBanach
import Navier.Analysis.CriticalMildDuhamel
import Navier.Analysis.CriticalMildGlobalWeightedOutput

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
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildGlobalReindex

/-- The physical Fourier divergence-free constraint on a completed weighted
carrier: every decoded mode is Hermitian-transverse to its own frequency. -/
def LatticeDivergenceFree (u : WeightedLatticeBanach) : Prop :=
  ∀ m : LatticeMode, inner ℂ (complexFrequency (latticeFrequency m))
    (complexEuclideanPoint (weightedLatticeCoefficient u m)) = 0

/-- The complex frequency embedding respects lattice addition. -/
theorem complexFrequency_latticeFrequency_add (i j : LatticeMode) :
    complexFrequency (latticeFrequency (i + j)) =
      complexFrequency (latticeFrequency i) + complexFrequency (latticeFrequency j) := by
  rw [latticeFrequency_add]
  ext a
  simp [complexFrequency, complexEuclideanPoint, complexOfReal, complexOfParts]

/-- Divergence freedom transfers the advecting derivative from the second
input frequency to the output frequency of an exact triad. -/
theorem spectralTransport_frequency_transfer
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (i j k : LatticeMode) (hijk : i + j = k) :
    spectralTransport (latticeFrequency j) (weightedLatticeCoefficient u i)
      (weightedLatticeCoefficient v j) =
    spectralTransport (latticeFrequency k) (weightedLatticeCoefficient u i)
      (weightedLatticeCoefficient v j) := by
  unfold spectralTransport
  congr 1
  subst k
  rw [complexFrequency_latticeFrequency_add, inner_add_left, hu i, zero_add]

/-- The actual transport norm can therefore be estimated with output
frequency on every exact lattice triad. -/
theorem complexEuclideanNorm_spectralTransport_output_le
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (i j k : LatticeMode) (hijk : i + j = k) :
    complexEuclideanNorm
      (spectralTransport (latticeFrequency j) (weightedLatticeCoefficient u i)
        (weightedLatticeCoefficient v j)) ≤
      ‖complexFrequency (latticeFrequency k)‖ *
        complexEuclideanNorm (weightedLatticeCoefficient u i) *
          complexEuclideanNorm (weightedLatticeCoefficient v j) := by
  rw [spectralTransport_frequency_transfer u v hu i j k hijk]
  exact complexEuclideanNorm_spectralTransport_le _ _ _

/-- On an exact triad, output heat controls the transferred derivative and
the remaining output weight is allocated to the two one-weight inputs. -/
theorem latticeWeighted_heatLeray_spectralTransport_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (i j k : LatticeMode) (hijk : i + j = k) :
    latticeModeWeight k * complexEuclideanNorm
      (complexFrequencyHeatLeray ν τ (latticeFrequency k)
        (spectralTransport (latticeFrequency j) (weightedLatticeCoefficient u i)
          (weightedLatticeCoefficient v j))) ≤
      (Real.sqrt (ν * τ))⁻¹ *
        (latticeModeWeight i * complexEuclideanNorm (weightedLatticeCoefficient u i)) *
          (latticeModeWeight j * complexEuclideanNorm (weightedLatticeCoefficient v j)) := by
  have hwk : 0 ≤ latticeModeWeight k :=
    zero_le_one.trans (one_le_latticeModeWeight k)
  have hdec : 0 ≤ complexHeatDecay ν τ (latticeFrequency k) :=
    complexHeatDecay_nonneg _ _ _
  have htransport := complexEuclideanNorm_spectralTransport_output_le u v hu i j k hijk
  have hheat := complexEuclideanNorm_heatLeray_le_decay ν τ k
    (spectralTransport (latticeFrequency j) (weightedLatticeCoefficient u i)
      (weightedLatticeCoefficient v j))
  have hweight : latticeModeWeight k ≤ latticeModeWeight i * latticeModeWeight j := by
    rw [← hijk]
    exact latticeModeWeight_add_le_mul i j
  have hgain := latticeHeat_frequency_gain ν τ (mul_pos hν hτ) k
  calc
    latticeModeWeight k * complexEuclideanNorm
        (complexFrequencyHeatLeray ν τ (latticeFrequency k)
          (spectralTransport (latticeFrequency j) (weightedLatticeCoefficient u i)
            (weightedLatticeCoefficient v j))) ≤
        latticeModeWeight k * (complexHeatDecay ν τ (latticeFrequency k) *
          complexEuclideanNorm
            (spectralTransport (latticeFrequency j) (weightedLatticeCoefficient u i)
              (weightedLatticeCoefficient v j))) :=
      mul_le_mul_of_nonneg_left hheat hwk
    _ ≤ latticeModeWeight k * (complexHeatDecay ν τ (latticeFrequency k) *
        (‖complexFrequency (latticeFrequency k)‖ *
          complexEuclideanNorm (weightedLatticeCoefficient u i) *
            complexEuclideanNorm (weightedLatticeCoefficient v j))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htransport hdec) hwk
    _ = (latticeModeWeight k *
        (‖complexFrequency (latticeFrequency k)‖ *
          complexHeatDecay ν τ (latticeFrequency k))) *
        (complexEuclideanNorm (weightedLatticeCoefficient u i) *
          complexEuclideanNorm (weightedLatticeCoefficient v j)) := by ring
    _ ≤ ((latticeModeWeight i * latticeModeWeight j) *
        (Real.sqrt (ν * τ))⁻¹) *
        (complexEuclideanNorm (weightedLatticeCoefficient u i) *
          complexEuclideanNorm (weightedLatticeCoefficient v j)) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul hweight hgain
          (mul_nonneg (norm_nonneg _) hdec)
          (mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight i))
            (zero_le_one.trans (one_le_latticeModeWeight j)))
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = (Real.sqrt (ν * τ))⁻¹ *
        (latticeModeWeight i * complexEuclideanNorm (weightedLatticeCoefficient u i)) *
          (latticeModeWeight j * complexEuclideanNorm (weightedLatticeCoefficient v j)) := by
      ring

/-- The summable two-input majorant produced by output-frequency derivative
transfer.  It uses exactly one input weight on each carrier. -/
def outputHeatPairMajorant (ν τ : ℝ) (u v : WeightedLatticeBanach) :
    LatticeMode × LatticeMode → ℝ := fun ij =>
  (Real.sqrt (ν * τ))⁻¹ *
    latticeWeightedAmplitude (weightedLatticeCoefficient u) ij.1 *
      latticeWeightedAmplitude (weightedLatticeCoefficient v) ij.2

/-- The transferred output-heat majorant is summable on the full pair lattice. -/
theorem summable_outputHeatPairMajorant (ν τ : ℝ)
    (u v : WeightedLatticeBanach) :
    Summable (outputHeatPairMajorant ν τ u v) := by
  have hu := latticeWeightedL1_coefficient u
  have hv := latticeWeightedL1_coefficient v
  have hu0 : ∀ m, 0 ≤ latticeWeightedAmplitude (weightedLatticeCoefficient u) m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hv0 : ∀ m, 0 ≤ latticeWeightedAmplitude (weightedLatticeCoefficient v) m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  rw [show outputHeatPairMajorant ν τ u v = fun ij => (Real.sqrt (ν * τ))⁻¹ *
      (latticeWeightedAmplitude (weightedLatticeCoefficient u) ij.1 *
        latticeWeightedAmplitude (weightedLatticeCoefficient v) ij.2) by
    funext ij
    unfold outputHeatPairMajorant
    ring]
  exact (hu.mul_of_nonneg hv hu0 hv0).mul_left ((Real.sqrt (ν * τ))⁻¹)

/-- The actual heat-regularized summand on one exact constrained output
fiber.  The heat operator acts on the triad output frequency. -/
def constrainedHeatRegularizedFiberTerm (ν τ : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) : ComplexE3 :=
  latticeModeWeight k • complexEuclideanPoint
    (complexFrequencyHeatLeray ν τ (latticeFrequency k)
      (spectralTransport (latticeFrequency ij.1.2)
        (weightedLatticeCoefficient u ij.1.1)
        (weightedLatticeCoefficient v ij.1.2)))

/-- The constrained actual heat term is controlled by the global pair
majorant via the proved divergence-free derivative transfer. -/
theorem norm_constrainedHeatRegularizedFiberTerm_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖constrainedHeatRegularizedFiberTerm ν τ k u v ij‖ ≤
      outputHeatPairMajorant ν τ u v ij.1 := by
  unfold constrainedHeatRegularizedFiberTerm
  rw [norm_smul, Real.norm_of_nonneg
    (zero_le_one.trans (one_le_latticeModeWeight k))]
  change latticeModeWeight k * complexEuclideanNorm
    (complexFrequencyHeatLeray ν τ (latticeFrequency k)
      (spectralTransport (latticeFrequency ij.1.2)
        (weightedLatticeCoefficient u ij.1.1)
        (weightedLatticeCoefficient v ij.1.2))) ≤ _
  rw [show outputHeatPairMajorant ν τ u v ij.1 =
      (Real.sqrt (ν * τ))⁻¹ *
        (latticeModeWeight ij.1.1 * complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1)) *
          (latticeModeWeight ij.1.2 * complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) by
    unfold outputHeatPairMajorant latticeWeightedAmplitude
    rfl]
  exact latticeWeighted_heatLeray_spectralTransport_le ν τ hν hτ u v hu
    ij.1.1 ij.1.2 k ij.2

/-- Each actual constrained heat fiber is absolutely summable. -/
theorem summable_constrainedHeatRegularizedFiberTerm
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    Summable (constrainedHeatRegularizedFiberTerm ν τ k u v) := by
  exact ((summable_outputHeatPairMajorant ν τ u v).subtype
    (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))).of_norm_bounded
      (norm_constrainedHeatRegularizedFiberTerm_le ν τ hν hτ u v hu k)

/-- The completed constrained fiber obtained by summing the actual heat
terms.  Its identification with heat applied after the pre-existing full
convolution is the remaining explicit `tsum`-interchange bridge. -/
def constrainedHeatRegularizedFiber (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) : ComplexE3 :=
  ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
    constrainedHeatRegularizedFiberTerm ν τ k u v ij

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
