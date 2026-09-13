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

open Topology
open scoped ENNReal
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.FrequencyHeatLeray
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
      rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
      simp [ENNReal.toReal_one]

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

/-- The same-weight heat--Leray evolution is strongly continuous in
nonnegative time in the completed weighted `ℓ¹` norm.  This is the linear-path
continuity leaf required by the critical mild fixed-point map.  Reference:
Tannery dominated convergence in Mathlib,
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Group/Tannery.html. -/
theorem continuous_weightedHeatFlow_nnreal
    (ν : ℝ) (hν : 0 ≤ ν) (u : WeightedLatticeBanach) :
    Continuous fun τ : NNReal =>
      weightedHeatFlow ν τ hν τ.property u := by
  rw [continuous_iff_continuousAt]
  intro τ₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcoordinate (m : LatticeMode) :
      Continuous fun τ : NNReal => weightedHeatFlowCoordinate ν τ u m := by
    unfold weightedHeatFlowCoordinate
    show Continuous (latticeModeWeight m •
      fun τ : NNReal => complexEuclideanPoint
        ((complexFrequencyHeatLeray ν τ (latticeFrequency m))
          (weightedLatticeCoefficient u m)))
    apply Continuous.const_smul
    apply CriticalMildHeatBochner.continuous_complexEuclideanPoint.comp
    rw [show (fun τ : NNReal =>
        complexFrequencyHeatLeray ν τ (latticeFrequency m)
          (weightedLatticeCoefficient u m)) =
      fun τ : NNReal => (complexHeatDecay ν (τ : ℝ) (latticeFrequency m) : ℂ) •
        complexLeray (latticeFrequency m) (weightedLatticeCoefficient u m) by
          funext τ
          exact complexFrequencyHeatLeray_apply ν τ (latticeFrequency m)
            (weightedLatticeCoefficient u m)]
    unfold complexHeatDecay heatDecay
    fun_prop
  have hpointwise (m : LatticeMode) :
      Filter.Tendsto
        (fun τ : NNReal =>
          ‖weightedHeatFlowCoordinate ν τ u m -
            weightedHeatFlowCoordinate ν τ₀ u m‖)
        (𝓝 τ₀) (𝓝 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mp (hcoordinate m).continuousAt
  have hdominated :
      ∀ᶠ τ : NNReal in 𝓝 τ₀, ∀ m : LatticeMode,
        ‖(‖weightedHeatFlowCoordinate ν τ u m -
            weightedHeatFlowCoordinate ν τ₀ u m‖ : ℝ)‖ ≤
          2 * ‖u m‖ := by
    refine Filter.Eventually.of_forall ?_
    intro (τ : NNReal)
    intro m
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖weightedHeatFlowCoordinate ν τ u m -
          weightedHeatFlowCoordinate ν τ₀ u m‖ ≤
        ‖weightedHeatFlowCoordinate ν τ u m‖ +
          ‖weightedHeatFlowCoordinate ν τ₀ u m‖ :=
        norm_sub_le _ _
      _ ≤ ‖u m‖ + ‖u m‖ :=
        add_le_add
          (norm_weightedHeatFlowCoordinate_le ν τ hν τ.property u m)
          (norm_weightedHeatFlowCoordinate_le ν τ₀ hν τ₀.property u m)
      _ = 2 * ‖u m‖ := by ring
  have hsum : Summable (fun m : LatticeMode => 2 * ‖u m‖) := by
    have huSum : Summable (fun m : LatticeMode => ‖u m‖) := by
      simpa using u.2.summable
    exact huSum.mul_left 2
  have htannery :
      Filter.Tendsto
        (fun τ : NNReal =>
          ∑' m : LatticeMode,
            ‖weightedHeatFlowCoordinate ν τ u m -
              weightedHeatFlowCoordinate ν τ₀ u m‖)
        (𝓝 τ₀) (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence
      hsum hpointwise hdominated
  convert htannery using 1
  funext τ
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one]
  apply congrArg tsum
  funext m
  rfl

end Navier.Analysis.CriticalMildHeatFlow

#print axioms Navier.Analysis.CriticalMildHeatFlow.norm_weightedHeatFlow_le
#print axioms Navier.Analysis.CriticalMildHeatFlow.weightedHeatFlow_divergenceFree
#print axioms Navier.Analysis.CriticalMildHeatFlow.continuous_weightedHeatFlow_nnreal
