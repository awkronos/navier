import Navier.Analysis.CriticalMildHeatCoefficientLift
import Navier.Analysis.CriticalMildGlobalWeightedOutput

/-!
# Completed heat lift from one to two lattice weights

The carrier below is Mathlib's actual `ℓ¹` space.  Its coordinates are the
two-weight encoding of the heat--Leray evolution of a decoded one-weight
input; the positive-time hypothesis retains the singular gain explicitly.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatCarrierLift

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildHeatCoefficientLift
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildAsymmetricPairSummable

/-- The physical coefficient obtained by applying the actual heat--Leray
multiplier to the decoded one-weight input. -/
def heatLiftCoefficient (ν τ : ℝ) (u : WeightedLatticeBanach)
    (m : LatticeMode) : ComplexSpace :=
  complexFrequencyHeatLeray ν τ (latticeFrequency m) (weightedLatticeCoefficient u m)

/-- The two-weight `lp` coordinate corresponding to `heatLiftCoefficient`. -/
def heatLiftCoordinate (ν τ : ℝ) (u : WeightedLatticeBanach)
    (m : LatticeMode) : ComplexE3 :=
  latticeModeWeight m ^ 2 • complexEuclideanPoint (heatLiftCoefficient ν τ u m)

/-- Each encoded heat coordinate is bounded by the singular heat gain times
the decoded one-weight coordinate. -/
theorem norm_heatLiftCoordinate_le (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    ‖heatLiftCoordinate ν τ u m‖ ≤
      (1 + (Real.sqrt (ν * τ))⁻¹) *
        (latticeModeWeight m * complexEuclideanNorm (weightedLatticeCoefficient u m)) := by
  unfold heatLiftCoordinate
  rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  change latticeModeWeight m ^ 2 * complexEuclideanNorm (heatLiftCoefficient ν τ u m) ≤ _
  calc
    latticeModeWeight m ^ 2 * complexEuclideanNorm (heatLiftCoefficient ν τ u m) =
        latticeModeWeight m *
          (latticeModeWeight m * complexEuclideanNorm (heatLiftCoefficient ν τ u m)) := by ring
    _ ≤ latticeModeWeight m *
        ((1 + (Real.sqrt (ν * τ))⁻¹) *
          complexEuclideanNorm (weightedLatticeCoefficient u m)) :=
      mul_le_mul_of_nonneg_left
        (latticeModeWeight_heatLeray_coefficient_le ν τ hν hτ m
          (weightedLatticeCoefficient u m))
        (zero_le_one.trans (one_le_latticeModeWeight m))
    _ = (1 + (Real.sqrt (ν * τ))⁻¹) *
        (latticeModeWeight m * complexEuclideanNorm
          (weightedLatticeCoefficient u m)) := by ring

/-- The genuine completed two-weight carrier for the heat lift. -/
def heatLift (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) : LatticeWeightTwoCarrier :=
  ⟨heatLiftCoordinate ν τ u, memℓp_gen (by
    have hbase := latticeWeightedL1_coefficient u
    have hsum : Summable (fun m : LatticeMode =>
        (1 + (Real.sqrt (ν * τ))⁻¹) *
          (latticeModeWeight m * complexEuclideanNorm (weightedLatticeCoefficient u m))) := by
      exact hbase.mul_left _
    have hbound : Summable (fun m : LatticeMode => ‖heatLiftCoordinate ν τ u m‖) :=
      hsum.of_nonneg_of_le
        (fun _ => norm_nonneg _)
        (norm_heatLiftCoordinate_le ν τ hν hτ u)
    simpa using hbound)⟩

/-- Decoding the completed carrier recovers the actual heat--Leray coefficient. -/
theorem latticeWeightTwoCoefficient_heatLift (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    latticeWeightTwoCoefficient (heatLift ν τ hν hτ u) m = heatLiftCoefficient ν τ u m := by
  unfold latticeWeightTwoCoefficient heatLift heatLiftCoordinate
  rw [smul_smul]
  have hm : latticeModeWeight m ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m)))
  rw [inv_mul_cancel₀ hm, one_smul]
  exact WithLp.ofLp_toLp _ _

/-- The decoded heat lift satisfies the actual two-weight summability contract. -/
theorem latticeTwoWeightL1_heatLift (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) :
    LatticeTwoWeightL1 (latticeWeightTwoCoefficient (heatLift ν τ hν hτ u)) := by
  change Summable (fun m => latticeModeWeight m ^ 2 *
    complexEuclideanNorm (latticeWeightTwoCoefficient (heatLift ν τ hν hτ u) m))
  have hnorm : (fun m : LatticeMode => latticeModeWeight m ^ 2 *
      complexEuclideanNorm (heatLiftCoefficient ν τ u m)) =
      fun m => ‖heatLiftCoordinate ν τ u m‖ := by
    funext m
    unfold heatLiftCoordinate complexEuclideanNorm
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  rw [show latticeWeightTwoCoefficient (heatLift ν τ hν hτ u) = heatLiftCoefficient ν τ u by
    funext m
    exact latticeWeightTwoCoefficient_heatLift ν τ hν hτ u m, hnorm]
  simpa [heatLift] using (heatLift ν τ hν hτ u).2.summable

/-- The weighted two-weight sum of the decoded heat lift is exactly its
completed `lp` norm. -/
theorem tsum_latticeTwoWeight_heatLift_eq_norm (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) :
    (∑' m, latticeModeWeight m ^ 2 * complexEuclideanNorm
      (latticeWeightTwoCoefficient (heatLift ν τ hν hτ u) m)) = ‖heatLift ν τ hν hτ u‖ := by
  rw [show latticeWeightTwoCoefficient (heatLift ν τ hν hτ u) = heatLiftCoefficient ν τ u by
    funext m
    exact latticeWeightTwoCoefficient_heatLift ν τ hν hτ u m]
  have hnorm : (fun m : LatticeMode => latticeModeWeight m ^ 2 *
      complexEuclideanNorm (heatLiftCoefficient ν τ u m)) =
      fun m => ‖heatLiftCoordinate ν τ u m‖ := by
    funext m
    unfold heatLiftCoordinate complexEuclideanNorm
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  rw [hnorm, lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  change (∑' m : LatticeMode, ‖heatLiftCoordinate ν τ u m‖) =
    (∑' m : LatticeMode, ‖heatLiftCoordinate ν τ u m‖ ^ (1 : ℝ)) ^
      (1 / (1 : ℝ))
  rw [show (1 : ℝ) / 1 = 1 by norm_num, Real.rpow_one]
  apply congrArg tsum
  funext m
  exact (Real.rpow_one _).symm

/-- The completed heat lift has the inhomogeneous singular two-weight norm
bound.  The hypotheses exclude the genuine `τ = 0` singularity. -/
theorem norm_heatLift_le (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) :
    ‖heatLift ν τ hν hτ u‖ ≤ (1 + (Real.sqrt (ν * τ))⁻¹) * ‖u‖ := by
  have hbase := latticeWeightedL1_coefficient u
  have hsum : Summable (fun m : LatticeMode =>
      (1 + (Real.sqrt (ν * τ))⁻¹) *
        (latticeModeWeight m * complexEuclideanNorm (weightedLatticeCoefficient u m))) := by
    exact hbase.mul_left _
  have hcoords : Summable (fun m : LatticeMode => ‖heatLiftCoordinate ν τ u m‖) := by
    simpa [heatLift] using (heatLift ν τ hν hτ u).2.summable
  rw [← tsum_latticeTwoWeight_heatLift_eq_norm ν τ hν hτ u]
  have hnorm : (fun m : LatticeMode => latticeModeWeight m ^ 2 *
      complexEuclideanNorm (latticeWeightTwoCoefficient (heatLift ν τ hν hτ u) m)) =
      fun m => ‖heatLiftCoordinate ν τ u m‖ := by
    funext m
    rw [latticeWeightTwoCoefficient_heatLift]
    unfold heatLiftCoordinate complexEuclideanNorm
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  rw [hnorm]
  calc
    (∑' m : LatticeMode, ‖heatLiftCoordinate ν τ u m‖) ≤
        ∑' m : LatticeMode, (1 + (Real.sqrt (ν * τ))⁻¹) *
          (latticeModeWeight m * complexEuclideanNorm (weightedLatticeCoefficient u m)) :=
      Summable.tsum_le_tsum (norm_heatLiftCoordinate_le ν τ hν hτ u) hcoords hsum
    _ = (1 + (Real.sqrt (ν * τ))⁻¹) * ‖u‖ := by
      change (∑' m : LatticeMode, (1 + (Real.sqrt (ν * τ))⁻¹) *
        latticeWeightedAmplitude (weightedLatticeCoefficient u) m) = _
      rw [hbase.tsum_mul_left, tsum_latticeWeightedAmplitude_coefficient]

/-- The completed two-weight heat lift feeds directly into the asymmetric
global weighted spectral output, with the same explicit heat singularity. -/
theorem norm_globalWeightedSpectralOutput_heatLift_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (v : LatticeMode → ComplexSpace)
    (hv : LatticeWeightedL1 v) (u : WeightedLatticeBanach) :
    ‖globalWeightedSpectralOutput v
      (latticeWeightTwoCoefficient (heatLift ν τ hν hτ u)) hv
      (latticeTwoWeightL1_heatLift ν τ hν hτ u)‖ ≤
      (∑' m, globalWeightedInputFactor v m) *
        ((1 + (Real.sqrt (ν * τ))⁻¹) * ‖u‖) := by
  calc
    ‖globalWeightedSpectralOutput v
        (latticeWeightTwoCoefficient (heatLift ν τ hν hτ u)) hv
        (latticeTwoWeightL1_heatLift ν τ hν hτ u)‖ ≤
        (∑' m, globalWeightedInputFactor v m) *
          ∑' m, globalTwoWeightInputFactor
            (latticeWeightTwoCoefficient (heatLift ν τ hν hτ u)) m :=
      norm_globalWeightedSpectralOutput_le v
        (latticeWeightTwoCoefficient (heatLift ν τ hν hτ u)) hv
        (latticeTwoWeightL1_heatLift ν τ hν hτ u)
    _ = (∑' m, globalWeightedInputFactor v m) * ‖heatLift ν τ hν hτ u‖ := by
      rw [← tsum_latticeTwoWeight_heatLift_eq_norm ν τ hν hτ u]
      rfl
    _ ≤ (∑' m, globalWeightedInputFactor v m) *
        ((1 + (Real.sqrt (ν * τ))⁻¹) * ‖u‖) :=
      mul_le_mul_of_nonneg_left (norm_heatLift_le ν τ hν hτ u)
        (tsum_nonneg fun m => mul_nonneg
          (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _))

end Navier.Analysis.CriticalMildHeatCarrierLift
