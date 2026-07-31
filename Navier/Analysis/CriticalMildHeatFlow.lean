import Navier.Analysis.CriticalMildDuhamelBochner

/-!
# Same-weight heat--Leray flow on the completed critical lattice carrier

This file constructs the linear term required by the critical mild fixed-point
map.  Unlike the two-weight positive-time lift, this operator stays in the
one-weight `ℓ¹` carrier and is contractive for nonnegative time.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatFlow

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildDuhamelBochner

/-- The one-weight coordinate encoding of the heat--Leray evolution. -/
def weightedHeatFlowCoordinate (ν τ : ℝ) (u : WeightedLatticeBanach)
    (m : LatticeMode) : ComplexE3 :=
  latticeModeWeight m • complexEuclideanPoint
    (complexFrequencyHeatLeray ν τ (latticeFrequency m)
      (weightedLatticeCoefficient u m))

/-- At nonnegative viscosity and time, every encoded heat coordinate is
bounded by the corresponding input coordinate. -/
theorem norm_weightedHeatFlowCoordinate_le
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    ‖weightedHeatFlowCoordinate ν τ u m‖ ≤ ‖u m‖ := by
  unfold weightedHeatFlowCoordinate
  rw [norm_smul, Real.norm_of_nonneg
    (zero_le_one.trans (one_le_latticeModeWeight m))]
  change latticeModeWeight m *
      complexEuclideanNorm
        (complexFrequencyHeatLeray ν τ (latticeFrequency m)
          (weightedLatticeCoefficient u m)) ≤ ‖u m‖
  calc
    latticeModeWeight m *
        complexEuclideanNorm
          (complexFrequencyHeatLeray ν τ (latticeFrequency m)
            (weightedLatticeCoefficient u m)) ≤
      latticeModeWeight m *
        complexEuclideanNorm (weightedLatticeCoefficient u m) :=
      mul_le_mul_of_nonneg_left
        (complexEuclideanNorm_heatLeray_le ν τ hν hτ m
          (weightedLatticeCoefficient u m))
        (zero_le_one.trans (one_le_latticeModeWeight m))
    _ = ‖u m‖ := latticeWeightedAmplitude_coefficient u m

/-- The actual same-weight heat--Leray evolution in the complete critical
`ℓ¹` carrier. -/
def weightedHeatFlow
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) : WeightedLatticeBanach :=
  ⟨weightedHeatFlowCoordinate ν τ u, memℓp_gen (by
    have hsum : Summable (fun m : LatticeMode => ‖u m‖) := by
      simpa using u.2.summable
    have hbound : Summable
        (fun m : LatticeMode => ‖weightedHeatFlowCoordinate ν τ u m‖) :=
      hsum.of_nonneg_of_le
        (fun _ => norm_nonneg _)
        (norm_weightedHeatFlowCoordinate_le ν τ hν hτ u)
    simpa using hbound)⟩

/-- Decoding the completed one-weight heat flow recovers the literal
heat--Leray coefficient. -/
theorem weightedLatticeCoefficient_weightedHeatFlow
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    weightedLatticeCoefficient (weightedHeatFlow ν τ hν hτ u) m =
      complexFrequencyHeatLeray ν τ (latticeFrequency m)
        (weightedLatticeCoefficient u m) := by
  unfold weightedLatticeCoefficient weightedHeatFlow weightedHeatFlowCoordinate
  rw [smul_smul]
  have hm : latticeModeWeight m ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m))
  rw [inv_mul_cancel₀ hm, one_smul]
  exact WithLp.ofLp_toLp _ _

/-- The completed same-weight heat flow is contractive. -/
theorem norm_weightedHeatFlow_le
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) :
    ‖weightedHeatFlow ν τ hν hτ u‖ ≤ ‖u‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  change (∑' m : LatticeMode, ‖weightedHeatFlowCoordinate ν τ u m‖ ^ (1 : ℝ)) ^
      (1 / (1 : ℝ)) ≤ ‖u‖
  rw [show (1 : ℝ) / 1 = 1 by norm_num, Real.rpow_one]
  have hflow : Summable
      (fun m : LatticeMode => ‖weightedHeatFlowCoordinate ν τ u m‖) := by
    simpa [weightedHeatFlow] using
      (weightedHeatFlow ν τ hν hτ u).2.summable
  have hu : Summable (fun m : LatticeMode => ‖u m‖) := by
    simpa using u.2.summable
  calc
    (∑' m : LatticeMode, ‖weightedHeatFlowCoordinate ν τ u m‖ ^ (1 : ℝ)) =
        ∑' m : LatticeMode, ‖weightedHeatFlowCoordinate ν τ u m‖ := by
      apply congrArg tsum
      funext m
      exact Real.rpow_one _
    _ ≤ ∑' m : LatticeMode, ‖u m‖ :=
      Summable.tsum_le_tsum
        (norm_weightedHeatFlowCoordinate_le ν τ hν hτ u) hflow hu
    _ = ‖u‖ := by
      simpa [lp.norm_eq_tsum_rpow]

/-- Heat--Leray evolution lands in the divergence-free carrier at every
nonnegative time, independently of the input. -/
theorem weightedHeatFlow_divergenceFree
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) :
    LatticeDivergenceFree (weightedHeatFlow ν τ hν hτ u) := by
  intro m
  rw [weightedLatticeCoefficient_weightedHeatFlow]
  exact complexFrequencyHeatLeray_hermitian_transverse ν τ (latticeFrequency m)
    (weightedLatticeCoefficient u m)

end Navier.Analysis.CriticalMildHeatFlow

#print axioms Navier.Analysis.CriticalMildHeatFlow.norm_weightedHeatFlow_le
#print axioms Navier.Analysis.CriticalMildHeatFlow.weightedHeatFlow_divergenceFree
