import Navier.Analysis.CriticalMildHeatTimeKernel

/-!
# Positive-time completed heat lift

The actual completed heat lift is extended by zero at nonpositive time so it
has a total time-function type.  The singular estimate is used only on the
positive-time branch.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatBochner

open MeasureTheory Set Topology
open Navier
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildHeatCarrierLift
open Navier.Analysis.CriticalMildHeatTimeKernel

/-- The actual two-weight heat carrier, made total by its zero extension at
nonpositive elapsed time. -/
def positiveTimeHeatLift (ν : ℝ) (hν : 0 < ν) (u : WeightedLatticeBanach) :
    ℝ → LatticeWeightTwoCarrier := fun τ =>
  if hτ : 0 < τ then heatLift ν τ hν hτ u else 0

/-- On positive time, the total integrand is definitionally the actual
completed heat lift. -/
theorem positiveTimeHeatLift_of_pos (ν : ℝ) (hν : 0 < ν) (u : WeightedLatticeBanach)
    {τ : ℝ} (hτ : 0 < τ) :
    positiveTimeHeatLift ν hν u τ = heatLift ν τ hν hτ u := by
  simp [positiveTimeHeatLift, hτ]

/-- The explicit singular scalar majorant controls the actual carrier on its
positive-time branch. -/
theorem norm_positiveTimeHeatLift_le (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) {τ : ℝ} (hτ : 0 < τ) :
    ‖positiveTimeHeatLift ν hν u τ‖ ≤ heatTimeMajorant ν τ * ‖u‖ := by
  rw [positiveTimeHeatLift_of_pos ν hν u hτ, heatTimeMajorant_eq ν τ hν hτ]
  exact norm_heatLift_le ν τ hν hτ u

/-- Every physical Fourier coordinate of the actual heat--Leray evolution is
continuous in time.  This is the coordinatewise input to the missing `lp`
measurability bridge. -/
theorem continuous_heatLiftCoefficient_apply (ν : ℝ) (u : WeightedLatticeBanach)
    (m : LatticeMode) (i : Fin 3) :
    Continuous fun τ : ℝ => heatLiftCoefficient ν τ u m i := by
  rw [show (fun τ : ℝ => heatLiftCoefficient ν τ u m i) =
      fun τ => (complexHeatDecay ν τ (latticeFrequency m) : ℂ) *
        complexLeray (latticeFrequency m) (weightedLatticeCoefficient u m) i by
    funext τ
    exact complexFrequencyHeatLeray_apply_coordinate ν τ (latticeFrequency m)
      (weightedLatticeCoefficient u m) i]
  unfold complexHeatDecay heatDecay
  fun_prop

/-- The finite-dimensional Euclidean encoding is continuous; this is the
bridge from coordinate formulas to completed-coordinate truncations. -/
theorem continuous_complexEuclideanPoint :
    Continuous (complexEuclideanPoint : ComplexSpace → ComplexE3) := by
  change Continuous ((WithLp.linearEquiv 2 ℂ ComplexSpace).symm.toLinearMap)
  exact LinearMap.continuous_of_finiteDimensional _

/-- Each actual completed coordinate is continuous in time. -/
theorem continuous_heatLiftCoordinate_time (ν : ℝ) (u : WeightedLatticeBanach)
    (m : LatticeMode) : Continuous fun τ : ℝ => heatLiftCoordinate ν τ u m := by
  unfold heatLiftCoordinate heatLiftCoefficient
  apply Continuous.const_smul
  apply continuous_complexEuclideanPoint.comp
  rw [show (fun τ : ℝ => complexFrequencyHeatLeray ν τ (latticeFrequency m)
      (weightedLatticeCoefficient u m)) =
      fun τ => (complexHeatDecay ν τ (latticeFrequency m) : ℂ) •
        complexLeray (latticeFrequency m) (weightedLatticeCoefficient u m) by
    funext τ
    exact complexFrequencyHeatLeray_apply ν τ (latticeFrequency m)
      (weightedLatticeCoefficient u m)]
  unfold complexHeatDecay heatDecay
  fun_prop

/-- Evaluation of the total carrier is the continuous completed coordinate on
positive time. -/
theorem positiveTimeHeatLift_apply_of_pos (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) {τ : ℝ} (hτ : 0 < τ) (m : LatticeMode) :
    positiveTimeHeatLift ν hν u τ m = heatLiftCoordinate ν τ u m := by
  simp [positiveTimeHeatLift, hτ, heatLift]

/-- Every completed lattice coordinate of the total integrand is strongly
measurable, by its continuous positive-time branch and zero extension. -/
theorem stronglyMeasurable_positiveTimeHeatLift_apply (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    StronglyMeasurable (fun τ : ℝ => positiveTimeHeatLift ν hν u τ m) := by
  have hpiece : (fun τ : ℝ => positiveTimeHeatLift ν hν u τ m) =
      Set.piecewise (Ioi 0) (fun τ => heatLiftCoordinate ν τ u m) (fun _ => 0) := by
    funext τ
    by_cases hτ : 0 < τ
    · simp [hτ, positiveTimeHeatLift_apply_of_pos ν hν u hτ m]
    · simp [hτ, positiveTimeHeatLift]
  rw [hpiece]
  exact (continuous_heatLiftCoordinate_time ν u m).stronglyMeasurable.piecewise
    measurableSet_Ioi stronglyMeasurable_const

/-- Coordinate insertion into the completed carrier is Mathlib's continuous
linear `lp.single` map. -/
def heatLiftSingleLinear (m : LatticeMode) : ComplexE3 →ₗ[ℂ] LatticeWeightTwoCarrier :=
  lp.singleContinuousLinearMap ℂ (fun _ : LatticeMode => ComplexE3) 1 m

theorem continuous_heatLiftSingleLinear (m : LatticeMode) :
    Continuous (heatLiftSingleLinear m) :=
  LinearMap.continuous_of_finiteDimensional _

/-- A finite-coordinate truncation of the actual completed heat integrand. -/
def positiveTimeHeatLiftTruncation (s : Finset LatticeMode) (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) : ℝ → LatticeWeightTwoCarrier := fun τ =>
  ∑ m ∈ s, heatLiftSingleLinear m (positiveTimeHeatLift ν hν u τ m)

/-- Every finite-coordinate truncation is strongly measurable. -/
theorem stronglyMeasurable_positiveTimeHeatLiftTruncation
    (s : Finset LatticeMode) (ν : ℝ) (hν : 0 < ν) (u : WeightedLatticeBanach) :
    StronglyMeasurable (positiveTimeHeatLiftTruncation s ν hν u) := by
  unfold positiveTimeHeatLiftTruncation
  let f : LatticeMode → ℝ → LatticeWeightTwoCarrier := fun m τ =>
    heatLiftSingleLinear m (positiveTimeHeatLift ν hν u τ m)
  change StronglyMeasurable fun τ => ∑ m ∈ s, f m τ
  have hsum : StronglyMeasurable (∑ m ∈ s, f m) := Finset.stronglyMeasurable_sum s (fun m hm => by
    apply (continuous_heatLiftSingleLinear m).comp_stronglyMeasurable
    exact stronglyMeasurable_positiveTimeHeatLift_apply ν hν u m)
  have heq : (fun τ => ∑ m ∈ s, f m τ) = ∑ m ∈ s, f m := by
    funext τ
    simp
  rw [heq]
  exact hsum

/-- A concrete enumeration of the countable lattice. -/
def latticeModeEquivNat : LatticeMode ≃ ℕ :=
  (Equiv.prodCongr Equiv.intEquivNat
    (Equiv.prodCongr Equiv.intEquivNat Equiv.intEquivNat)).trans
    ((Equiv.prodCongr (Equiv.refl ℕ) Nat.pairEquiv).trans Nat.pairEquiv)

/-- The exhaustion truncations indexed by the concrete lattice enumeration. -/
def positiveTimeHeatLiftNatTruncation (n : ℕ) (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) : ℝ → LatticeWeightTwoCarrier := fun τ =>
  ∑ k ∈ Finset.range n, heatLiftSingleLinear (latticeModeEquivNat.symm k)
    (positiveTimeHeatLift ν hν u τ (latticeModeEquivNat.symm k))

theorem stronglyMeasurable_positiveTimeHeatLiftNatTruncation
    (n : ℕ) (ν : ℝ) (hν : 0 < ν) (u : WeightedLatticeBanach) :
    StronglyMeasurable (positiveTimeHeatLiftNatTruncation n ν hν u) := by
  unfold positiveTimeHeatLiftNatTruncation
  let f : ℕ → ℝ → LatticeWeightTwoCarrier := fun k τ =>
    heatLiftSingleLinear (latticeModeEquivNat.symm k)
      (positiveTimeHeatLift ν hν u τ (latticeModeEquivNat.symm k))
  change StronglyMeasurable fun τ => ∑ k ∈ Finset.range n, f k τ
  have hsum : StronglyMeasurable (∑ k ∈ Finset.range n, f k) :=
    Finset.stronglyMeasurable_sum _ (fun k hk => by
      apply (continuous_heatLiftSingleLinear _).comp_stronglyMeasurable
      exact stronglyMeasurable_positiveTimeHeatLift_apply ν hν u _)
  have heq : (fun τ => ∑ k ∈ Finset.range n, f k τ) = ∑ k ∈ Finset.range n, f k := by
    funext τ
    simp
  rw [heq]
  exact hsum

/-- The enumerated finite truncations converge pointwise in the actual
completed `lp` norm to the total positive-time carrier. -/
theorem tendsto_positiveTimeHeatLiftNatTruncation (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) (τ : ℝ) :
    Filter.Tendsto (fun n => positiveTimeHeatLiftNatTruncation n ν hν u τ)
      Filter.atTop (𝓝 (positiveTimeHeatLift ν hν u τ)) := by
  let f := positiveTimeHeatLift ν hν u τ
  have hsingle := lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
    (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤) f
  have hsum : Summable (fun n : ℕ => lp.single (E := fun _ : LatticeMode => ComplexE3)
      1 (latticeModeEquivNat.symm n)
      (f (latticeModeEquivNat.symm n))) := by
    exact latticeModeEquivNat.symm.summable_iff.mpr hsingle.summable
  have hsum_eq : (∑' n : ℕ, lp.single (E := fun _ : LatticeMode => ComplexE3)
      1 (latticeModeEquivNat.symm n)
      (f (latticeModeEquivNat.symm n))) = f := by
    calc
      (∑' n : ℕ, lp.single (E := fun _ : LatticeMode => ComplexE3)
          1 (latticeModeEquivNat.symm n)
          (f (latticeModeEquivNat.symm n))) =
          ∑' i : LatticeMode, lp.single (E := fun _ : LatticeMode => ComplexE3) 1 i (f i) :=
        latticeModeEquivNat.symm.tsum_eq
          (fun i : LatticeMode => lp.single (E := fun _ : LatticeMode => ComplexE3) 1 i (f i))
      _ = f := hsingle.tsum_eq
  have hhas : HasSum (fun n : ℕ => lp.single (E := fun _ : LatticeMode => ComplexE3)
      1 (latticeModeEquivNat.symm n)
      (f (latticeModeEquivNat.symm n))) f :=
    hsum.hasSum_iff.mpr hsum_eq
  exact hhas.tendsto_sum_nat

/-- The zero-extended actual completed heat lift is strongly measurable, by
the enumerated finite-coordinate approximation above. -/
theorem stronglyMeasurable_positiveTimeHeatLift (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) :
    StronglyMeasurable (positiveTimeHeatLift ν hν u) := by
  apply stronglyMeasurable_of_tendsto
    (f := fun n : ℕ => positiveTimeHeatLiftNatTruncation n ν hν u) Filter.atTop
  · intro n
    exact stronglyMeasurable_positiveTimeHeatLiftNatTruncation n ν hν u
  · rw [tendsto_pi_nhds]
    intro τ
    exact tendsto_positiveTimeHeatLiftNatTruncation ν hν u τ

/-- The actual total carrier is Bochner integrable on each positive finite
horizon; the singularity is controlled by the proved scalar majorant. -/
theorem integrableOn_positiveTimeHeatLift (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u : WeightedLatticeBanach) :
    IntegrableOn (positiveTimeHeatLift ν hν u) (Ioc 0 T) volume := by
  have hmajorant : IntervalIntegrable (heatTimeMajorant ν) volume 0 T := by
    unfold heatTimeMajorant
    exact intervalIntegral.intervalIntegrable_const.add
      ((inverseSqrtTime_intervalIntegrable T).const_mul _)
  have hmajorantU : IntervalIntegrable (fun τ => heatTimeMajorant ν τ * ‖u‖) volume 0 T :=
    hmajorant.mul_const _
  have hinterval : IntervalIntegrable (positiveTimeHeatLift ν hν u) volume 0 T :=
    IntervalIntegrable.mono_fun' hmajorantU
      (stronglyMeasurable_positiveTimeHeatLift ν hν u).aestronglyMeasurable (by
        rw [uIoc_of_le hT]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
        exact norm_positiveTimeHeatLift_le ν hν u hτ.1)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hinterval

/-- The genuine Bochner integral of the completed positive-time heat carrier. -/
def positiveTimeHeatLiftIntegral (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u : WeightedLatticeBanach) : LatticeWeightTwoCarrier :=
  ∫ τ in Ioc 0 T, positiveTimeHeatLift ν hν u τ

/-- The actual Bochner heat integral satisfies the exact finite-horizon
singular budget. -/
theorem norm_positiveTimeHeatLiftIntegral_le (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u : WeightedLatticeBanach) :
    ‖positiveTimeHeatLiftIntegral ν T hν hT u‖ ≤
      (T + 2 * Real.sqrt T / Real.sqrt ν) * ‖u‖ := by
  have hmajorant : IntervalIntegrable (fun τ => heatTimeMajorant ν τ * ‖u‖) volume 0 T := by
    unfold heatTimeMajorant
    exact (intervalIntegral.intervalIntegrable_const.add
      ((inverseSqrtTime_intervalIntegrable T).const_mul _)).mul_const _
  have hheat := integrableOn_positiveTimeHeatLift ν T hν hT u
  have hscalar := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hmajorant
  have hmono : (fun τ => ‖positiveTimeHeatLift ν hν u τ‖) ≤ᵐ[volume.restrict (Ioc 0 T)]
      fun τ => heatTimeMajorant ν τ * ‖u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact norm_positiveTimeHeatLift_le ν hν u hτ.1
  unfold positiveTimeHeatLiftIntegral
  calc
    ‖∫ τ in Ioc 0 T, positiveTimeHeatLift ν hν u τ‖ ≤
        ∫ τ in Ioc 0 T, ‖positiveTimeHeatLift ν hν u τ‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ τ in Ioc 0 T, heatTimeMajorant ν τ * ‖u‖ :=
      integral_mono_ae hheat.norm hscalar hmono
    _ = (∫ τ in (0 : ℝ)..T, heatTimeMajorant ν τ) * ‖u‖ := by
      rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_mul_const]
    _ = (T + 2 * Real.sqrt T / Real.sqrt ν) * ‖u‖ := by
      rw [integral_heatTimeMajorant_zero ν T hT]

/-- The scalar heat majorant is interval-integrable on every finite horizon. -/
theorem intervalIntegrable_heatTimeMajorant (ν T : ℝ) :
    IntervalIntegrable (heatTimeMajorant ν) volume 0 T := by
  unfold heatTimeMajorant
  exact intervalIntegral.intervalIntegrable_const.add
    ((inverseSqrtTime_intervalIntegrable T).const_mul _)

/-- The scalar budget governing the positive-time carrier has the exact
finite-horizon value. -/
theorem integral_heatTimeMajorant_positiveTime (ν T : ℝ) (hT : 0 ≤ T) :
    (∫ τ in (0 : ℝ)..T, heatTimeMajorant ν τ) =
      T + 2 * Real.sqrt T / Real.sqrt ν :=
  integral_heatTimeMajorant_zero ν T hT

end Navier.Analysis.CriticalMildHeatBochner
