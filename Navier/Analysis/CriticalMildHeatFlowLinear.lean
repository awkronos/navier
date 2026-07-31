import Navier.Analysis.CriticalMildHeatCarrierAlgebra

/-!
# Bounded linear completed critical heat flow
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatFlowLinear

open MeasureTheory
open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatCarrierAlgebra
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSeries

/-- Re-encoding a decoded coefficient recovers the completed carrier
coordinate exactly. -/
theorem latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    latticeModeWeight m • complexEuclideanPoint (weightedLatticeCoefficient u m) =
      u m := by
  unfold weightedLatticeCoefficient complexEuclideanPoint
  rw [WithLp.toLp_ofLp]
  rw [smul_smul]
  have hm : latticeModeWeight m ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m))
  field_simp
  simp

/-- At each nonnegative time, completed heat--Leray evolution is a bounded
complex-linear operator on the weighted carrier. -/
def weightedHeatFlowCLM
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) :
    WeightedLatticeBanach →L[ℂ] WeightedLatticeBanach :=
  LinearMap.mkContinuous
    { toFun := weightedHeatFlow ν τ hν hτ
      map_add' := by
        intro u v
        ext m i
        change weightedHeatFlowCoordinate ν τ (u + v) m i =
          weightedHeatFlowCoordinate ν τ u m i + weightedHeatFlowCoordinate ν τ v m i
        unfold weightedHeatFlowCoordinate
        rw [weightedLatticeCoefficient_add]
        change (latticeModeWeight m • complexEuclideanPoint
          (ComplexFrequencyHeatLeray.complexFrequencyHeatLeray ν τ
            (latticeFrequency m)
            (weightedLatticeCoefficient u m + weightedLatticeCoefficient v m))) i = _
        rw [map_add]
        have hpoint (a b : ComplexSpace) :
            complexEuclideanPoint (a + b) =
              complexEuclideanPoint a + complexEuclideanPoint b := by
          ext j
          rfl
        rw [hpoint, smul_add]
        rfl
      map_smul' := by
        intro c u
        ext m i
        change weightedHeatFlowCoordinate ν τ (c • u) m i =
          c • weightedHeatFlowCoordinate ν τ u m i
        unfold weightedHeatFlowCoordinate
        rw [weightedLatticeCoefficient_smul]
        change (latticeModeWeight m • complexEuclideanPoint
          (ComplexFrequencyHeatLeray.complexFrequencyHeatLeray ν τ
            (latticeFrequency m) (c • weightedLatticeCoefficient u m))) i = _
        rw [map_smul]
        rw [ComplexFrequencyHeatLeray.complexEuclideanPoint_smul, smul_comm]
        rfl }
    1
    (fun u => by
      simpa using norm_weightedHeatFlow_le ν τ hν hτ u)

@[simp] theorem weightedHeatFlowCLM_apply
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) :
    weightedHeatFlowCLM ν τ hν hτ u = weightedHeatFlow ν τ hν hτ u :=
  rfl

/-- Bounded heat flow commutes with every Bochner integral in the completed
carrier. -/
theorem weightedHeatFlow_integral_comm
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    {f : X → WeightedLatticeBanach} (hf : Integrable f μ) :
    weightedHeatFlow ν τ hν hτ (∫ x, f x ∂μ) =
      ∫ x, weightedHeatFlow ν τ hν hτ (f x) ∂μ := by
  symm
  exact (weightedHeatFlowCLM ν τ hν hτ).integral_comp_comm hf

/-- The complex Leray projection fixes a Hermitian-transverse Fourier
coefficient. -/
theorem complexLeray_eq_self_of_hermitian_transverse
    (q : Space) (z : ComplexSpace)
    (hz : inner ℂ (complexFrequency q) (complexEuclideanPoint z) = 0) :
    ComplexLerayProjection.complexLeray q z = z := by
  ext i
  rw [ComplexLerayNorm.complexLeray_formula,
    ← ComplexLerayNorm.inner_complexFrequency, hz]
  simp

/-- At time zero the completed heat flow is the identity on divergence-free
weighted carrier data. -/
theorem weightedHeatFlow_zero_of_divergenceFree
    (ν : ℝ) (hν : 0 ≤ ν) (u : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    weightedHeatFlow ν 0 hν le_rfl u = u := by
  ext m i
  rw [weightedHeatFlow_apply]
  unfold weightedHeatFlowCoordinate
  rw [ComplexFrequencyHeatLeray.complexFrequencyHeatLeray_zero_time]
  rw [complexLeray_eq_self_of_hermitian_transverse
    (latticeFrequency m) (weightedLatticeCoefficient u m) (hu m)]
  exact congrArg (fun z : ComplexE3 => z i)
    (latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient u m)

end Navier.Analysis.CriticalMildHeatFlowLinear

#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlowCLM
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlow_integral_comm
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlow_zero_of_divergenceFree
