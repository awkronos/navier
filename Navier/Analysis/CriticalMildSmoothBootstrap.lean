import Navier.Analysis.CriticalMildHigherMomentBootstrap
import Navier.Analysis.CriticalMildModeDifferentiation
import Navier.Analysis.CriticalMildGlobalWeightedOutput

/-!
# First joint time--space rung for the actual critical mild trajectory

The strict positive-time five-eighth-generator estimate gives more than the
two decoded lattice weights required by the literal transport convolution.
This file identifies the completed asymmetric convolution with the actual
spectral coefficient and uses that identification to prove absolute
summability of the genuine modewise time derivative.

This is a finite rung of the smooth bootstrap.  It supplies the first time
derivative together with more than two spatial derivatives at every positive
time.  It does not claim the still-unproved locally uniform induction through
all spacetime jets required by `FourierSpacetimeRapid`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace Navier.Analysis.CriticalMildSmoothBootstrap

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildFullPositiveTimeRegularity
open Navier.Analysis.CriticalMildHigherMomentBootstrap
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.CriticalMildGlobalClosure
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildAsymmetricPairSummable
open Navier.Analysis.CriticalMildFiberSums
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicPressureRecovery
open Navier.Analysis.CriticalMildModeDifferentiation

/-- The strict five-eighth-generator domain contains the two-weight decoded
input class needed by the global asymmetric transport estimate. -/
theorem latticeTwoWeightL1_of_fiveEighthGenerator
    (v : WeightedLatticeBanach)
    (hv : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖v k‖)) :
    LatticeTwoWeightL1 (weightedLatticeCoefficient v) := by
  have hbase : Summable fun k : LatticeMode => ‖v k‖ := by
    simpa using v.2.summable
  have hhalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖v k‖ := by
    apply hv.of_nonneg_of_le
    · intro k
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · intro k
      by_cases hk : k = 0
      · subst k
        have hz : latticeFrequency (0 : LatticeMode) = 0 := by
          ext i
          fin_cases i <;> simp [latticeFrequency]
        rw [hz, complexFrequency_zero]
        simp
      · have hq : 1 ≤ ‖complexFrequency (latticeFrequency k)‖ :=
          one_le_latticeModeSize_of_ne_zero hk
        have hquarter : 1 ≤ quarterFrequencyWeight k := by
          dsimp [quarterFrequencyWeight]
          rw [Real.one_le_sqrt, Real.one_le_sqrt]
          exact hq
        exact le_mul_of_one_le_left
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hquarter
  have hsum := hbase.add hhalf
  apply hsum.congr
  intro k
  rw [← latticeWeightedAmplitude_coefficient v k]
  unfold latticeWeightedAmplitude latticeModeWeight
  ring

/-- The completed asymmetric global output is the one-weight encoding of the
repository's literal spectral convolution.  This is the missing identification
that lets regularity of the actual mild carrier feed the global output bound. -/
theorem globalWeightedSpectralOutputFiber_eq_actualConvolution
    (k : LatticeMode) (v w : LatticeMode → ComplexSpace)
    (hv : LatticeWeightedL1 v) (hw : LatticeTwoWeightL1 w) :
    globalWeightedSpectralOutputFiber k v w hv hw =
      latticeModeWeight k • complexEuclideanPoint
        (WithLp.ofLp (latticeSpectralConvolution k v w)) := by
  let f : LatticeMode × LatticeMode → ComplexE3 := fun ij =>
    latticeModeWeight k • latticeSpectralTerm k v w ij
  have hw1 : LatticeWeightedL1 w := by
    apply hw.of_nonneg_of_le
    · intro m
      exact mul_nonneg
        (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
    · intro m
      have hweight : latticeModeWeight m ≤ latticeModeWeight m ^ 2 := by
        nlinarith [one_le_latticeModeWeight m]
      exact mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
  have hterm : Summable (latticeSpectralTerm k v w) :=
    summable_latticeSpectralTerm_of_weightedL1 k v w
      (latticeConvolutionWeightedL1_of_weightedL1 k v w hv hw1)
  calc
    globalWeightedSpectralOutputFiber k v w hv hw =
        ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode), f ij.1 := by
      apply tsum_congr
      intro ij
      unfold latticeWeightedFiberTerm f latticeSpectralTerm
      have hij := ij.2
      change latticeOutputMode ij.1 = k at hij
      change ij.1.1 + ij.1.2 = k at hij
      rw [if_pos hij]
    _ = ∑' ij : LatticeMode × LatticeMode,
        (latticeOutputMode ⁻¹' ({k} : Set LatticeMode)).indicator f ij :=
      tsum_subtype _ _
    _ = ∑' ij : LatticeMode × LatticeMode, f ij := by
      apply tsum_congr
      intro ij
      by_cases hij : ij.1 + ij.2 = k
      · have hmem : ij ∈ latticeOutputMode ⁻¹' ({k} : Set LatticeMode) := by
          change latticeOutputMode ij = k
          simpa [latticeOutputMode] using hij
        rw [Set.indicator_of_mem hmem]
      · have hmem : ij ∉ latticeOutputMode ⁻¹' ({k} : Set LatticeMode) := by
          intro hm
          change latticeOutputMode ij = k at hm
          apply hij
          simpa [latticeOutputMode] using hm
        rw [Set.indicator_of_notMem hmem]
        dsimp [f]
        rw [latticeSpectralTerm, if_neg hij]
        simp
    _ = latticeModeWeight k •
        (∑' ij : LatticeMode × LatticeMode, latticeSpectralTerm k v w ij) := by
      exact Summable.tsum_const_smul (latticeModeWeight k) hterm
    _ = latticeModeWeight k • complexEuclideanPoint
        (WithLp.ofLp (latticeSpectralConvolution k v w)) := by
      rfl

/-- With two decoded weights on the transported input, the actual nonlinear
coefficient has one summable output weight. -/
theorem summable_weighted_spectralOutputCoefficient
    (v w : WeightedLatticeBanach)
    (hw : LatticeTwoWeightL1 (weightedLatticeCoefficient w)) :
    Summable fun k : LatticeMode => latticeModeWeight k *
      complexEuclideanNorm (spectralOutputCoefficient k v w) := by
  let hv : LatticeWeightedL1 (weightedLatticeCoefficient v) :=
    latticeWeightedL1_coefficient v
  have hs := summable_norm_globalWeightedSpectralOutputFiber
    (weightedLatticeCoefficient v) (weightedLatticeCoefficient w) hv hw
  apply hs.congr
  intro k
  rw [globalWeightedSpectralOutputFiber_eq_actualConvolution k
    (weightedLatticeCoefficient v) (weightedLatticeCoefficient w) hv hw,
    norm_smul, Real.norm_of_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight k))]
  rfl

/-- The Leray projection preserves the summable one-output-weight estimate
for the actual nonlinear forcing. -/
theorem summable_weighted_projectedModeForcing
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hA : LatticeTwoWeightL1 (weightedLatticeCoefficient (A t))) :
    Summable fun k : LatticeMode => latticeModeWeight k *
      complexEuclideanNorm (projectedModeForcing A k t) := by
  have hs := summable_weighted_spectralOutputCoefficient (A t) (A t) hA
  apply hs.of_nonneg_of_le
  · intro k
    exact mul_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight k)) (norm_nonneg _)
  · intro k
    exact mul_le_mul_of_nonneg_left
      (complexEuclideanNorm_complexLeray_le (latticeFrequency k)
        (spectralOutputCoefficient k (A t) (A t)))
      (zero_le_one.trans (one_le_latticeModeWeight k))

/-- The strict spatial moment closes both terms of the genuine mode ODE:
the asymmetric global convolution controls the quadratic forcing and the
decoded two-derivative moment controls the viscous multiplier. -/
theorem summable_mildRawTimeDerivative_of_fiveEighth
    (μ : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hfive : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖complexFrequency (latticeFrequency k)‖ * ‖A t k‖)) :
    Summable fun k : LatticeMode =>
      complexEuclideanNorm (mildRawTimeDerivative μ A t k) := by
  have htwo := latticeTwoWeightL1_of_fiveEighthGenerator (A t) hfive
  have hforcingWeighted := summable_weighted_projectedModeForcing A t htwo
  have hforcing : Summable fun k : LatticeMode =>
      complexEuclideanNorm (projectedModeForcing A k t) := by
    apply hforcingWeighted.of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · intro k
      exact le_mul_of_one_le_left (norm_nonneg _)
        (one_le_latticeModeWeight k)
  have hspace :=
    summable_decoded_twoAndQuarterSpatialMoments_of_fiveEighth (A t) hfive
  have hspaceTwo : Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient (A t) k) := by
    apply hspace.of_nonneg_of_le
    · intro k
      exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
    · intro k
      by_cases hk : k = 0
      · subst k
        have hz : latticeFrequency (0 : LatticeMode) = 0 := by
          ext i
          fin_cases i <;> simp [latticeFrequency]
        rw [← complexFrequency_norm_eq_official, hz, complexFrequency_zero,
          norm_zero]
        simp
      · have hq : 1 ≤ ‖complexFrequency (latticeFrequency k)‖ :=
          one_le_latticeModeSize_of_ne_zero hk
        have hquarter : 1 ≤ quarterFrequencyWeight k := by
          dsimp [quarterFrequencyWeight]
          rw [Real.one_le_sqrt, Real.one_le_sqrt]
          exact hq
        exact le_mul_of_one_le_left
          (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hquarter
  have hviscous : Summable fun k : LatticeMode =>
      complexEuclideanNorm
        ((rawModeDecayRate μ k : ℂ) •
          weightedLatticeCoefficient (A t) k) := by
    have hs := hspaceTwo.mul_left |μ|
    apply hs.congr
    intro k
    have hsq : |‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2| =
        ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    unfold rawModeDecayRate complexEuclideanNorm
    rw [complexEuclideanPoint_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, hsq]
    ring
  have hsum := hforcing.add hviscous
  apply hsum.of_nonneg_of_le
  · intro k
    exact norm_nonneg _
  · intro k
    unfold mildRawTimeDerivative
    unfold complexEuclideanNorm
    change ‖complexEuclideanPoint (projectedModeForcing A k t) -
        complexEuclideanPoint
          ((rawModeDecayRate μ k : ℂ) •
            weightedLatticeCoefficient (A t) k)‖ ≤ _
    exact norm_sub_le _ _

/-- The physical `i/(2π)` decoder preserves the strict decoded
`2 + 1/4` spatial moment. -/
theorem summable_twoAndQuarterSpatialMoments_physicalCarrier
    {A : WeightedLatticeBanach}
    (hA : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient A k))) :
    Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm
          (weightedLatticeCoefficient (physicalCarrier A) k)) := by
  have hscaled := hA.mul_left ‖rawToPhysicalAmplitude‖
  apply hscaled.congr
  intro k
  unfold physicalCarrier complexEuclideanNorm
  rw [congrFun (weightedLatticeCoefficient_smul rawToPhysicalAmplitude A) k,
    Pi.smul_apply, complexEuclideanPoint_smul, norm_smul]
  ring

/-- Complex coefficient scaling preserves the decoded two-weight class. -/
theorem latticeTwoWeightL1_smul
    (c : ℂ) (A : WeightedLatticeBanach)
    (hA : LatticeTwoWeightL1 (weightedLatticeCoefficient A)) :
    LatticeTwoWeightL1 (weightedLatticeCoefficient (c • A)) := by
  have hs := hA.mul_left ‖c‖
  apply hs.congr
  intro k
  rw [congrFun (weightedLatticeCoefficient_smul c A) k]
  unfold complexEuclideanNorm
  rw [Pi.smul_apply, complexEuclideanPoint_smul, norm_smul]
  ring

/-- Two decoded weights make the recovered physical pressure gradient
absolutely summable.  The proof uses its exact identity as the longitudinal
part of the literal transport convolution. -/
theorem summable_recoveredPressureGradient_of_twoWeight
    (A : WeightedLatticeBanach)
    (hA : LatticeTwoWeightL1 (weightedLatticeCoefficient A)) :
    Summable fun k : LatticeMode => complexEuclideanNorm
      (periodOneGradientCoefficient k
        (periodOnePressureCoefficient k A A)) := by
  have houtWeighted := summable_weighted_spectralOutputCoefficient A A hA
  have hout : Summable fun k : LatticeMode =>
      complexEuclideanNorm (spectralOutputCoefficient k A A) := by
    apply houtWeighted.of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · intro k
      exact le_mul_of_one_le_left (norm_nonneg _)
        (one_le_latticeModeWeight k)
  have hconv : Summable fun k : LatticeMode =>
      complexEuclideanNorm (periodOneConvectionCoefficient k A A) := by
    have hs := hout.mul_left ‖periodOneDerivative‖
    apply hs.congr
    intro k
    unfold periodOneConvectionCoefficient spectralOutputCoefficient
    unfold complexEuclideanNorm
    rw [complexEuclideanPoint_smul, norm_smul]
  have hmajor := hconv.add hconv
  apply hmajor.of_nonneg_of_le
  · intro k
    exact norm_nonneg _
  · intro k
    rw [periodOnePressureCoefficient,
      periodOneGradient_pressureCoefficient]
    unfold complexEuclideanNorm
    calc
      ‖complexEuclideanPoint
          (complexLeray (latticeFrequency k)
            (periodOneConvectionCoefficient k A A) -
              periodOneConvectionCoefficient k A A)‖ =
          ‖complexEuclideanPoint
              (complexLeray (latticeFrequency k)
                (periodOneConvectionCoefficient k A A)) -
            complexEuclideanPoint
              (periodOneConvectionCoefficient k A A)‖ := rfl
      _ ≤ ‖complexEuclideanPoint
              (complexLeray (latticeFrequency k)
                (periodOneConvectionCoefficient k A A))‖ +
            ‖complexEuclideanPoint
              (periodOneConvectionCoefficient k A A)‖ := norm_sub_le _ _
      _ ≤ ‖complexEuclideanPoint
              (periodOneConvectionCoefficient k A A)‖ +
            ‖complexEuclideanPoint
              (periodOneConvectionCoefficient k A A)‖ :=
        add_le_add
          (complexEuclideanNorm_complexLeray_le (latticeFrequency k)
            (periodOneConvectionCoefficient k A A)) le_rfl

/-- **First joint time--space bootstrap for an actual positive-time mild
fixed point.**  At every positive interior time the decoded physical
coefficients have strictly more than two summable spatial derivatives, the
literal raw time derivative is absolutely summable, every coefficient has
that derivative, and the exact unprojected physical equation (including the
recovered pressure gradient) holds mode by mode. -/
theorem mildFixedPoint_firstJointBootstrap_at
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage (rawMildViscosity ν)
        (by unfold rawMildViscosity; positivity) u₀ A hdiv s hs.1) :
    (Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm
          (weightedLatticeCoefficient (physicalCarrier (A t)) k))) ∧
    (∀ k i, HasDerivAt (fun r => weightedLatticeCoefficient (A r) k i)
      (mildRawTimeDerivative (rawMildViscosity ν) A t k i) t) ∧
    (Summable fun k : LatticeMode => complexEuclideanNorm
      (mildRawTimeDerivative (rawMildViscosity ν) A t k)) ∧
    (Summable fun k : LatticeMode => complexEuclideanNorm
      (periodOneGradientCoefficient k
        (periodOnePressureCoefficient k
          (physicalCarrier (A t)) (physicalCarrier (A t))))) ∧
    ∀ k,
      rawToPhysicalAmplitude •
            mildRawTimeDerivative (rawMildViscosity ν) A t k +
          periodOneConvectionCoefficient k
            (physicalCarrier (A t)) (physicalCarrier (A t)) +
          periodOneViscousCoefficient ν k
            (weightedLatticeCoefficient (physicalCarrier (A t)) k) +
          periodOneGradientCoefficient k
            (periodOnePressureCoefficient k
              (physicalCarrier (A t)) (physicalCarrier (A t))) = 0 := by
  have hμ : 0 < rawMildViscosity ν := by
    unfold rawMildViscosity
    positivity
  have hboundt : ∀ s ∈ Ioc (0 : ℝ) t, ‖A s‖ ≤ R := by
    intro s hs
    exact hbound s ⟨hs.1, hs.2.trans ht.2.le⟩
  have hmildt : ∀ s (hs : s ∈ Icc (0 : ℝ) t),
      A s = criticalMildImage (rawMildViscosity ν) hμ u₀ A hdiv s hs.1 := by
    intro s hs
    exact hmild s ⟨hs.1, hs.2.trans ht.2.le⟩
  have hfive := mildTrajectory_fullPositiveTime_fiveEighthGenerator
    (rawMildViscosity ν) hμ u₀ hu₀ A hAc hdiv hR ht.1
      hboundt hmildt
  have hspaceRaw :=
    summable_decoded_twoAndQuarterSpatialMoments_of_fiveEighth (A t) hfive
  have hspacePhysical :=
    summable_twoAndQuarterSpatialMoments_physicalCarrier hspaceRaw
  have htime := summable_mildRawTimeDerivative_of_fiveEighth
    (rawMildViscosity ν) A t hfive
  have hpressure := summable_recoveredPressureGradient_of_twoWeight
    (physicalCarrier (A t))
    (latticeTwoWeightL1_smul rawToPhysicalAmplitude (A t)
      (latticeTwoWeightL1_of_fiveEighthGenerator (A t) hfive))
  have heq := mildFixedPoint_physicalUnprojected_at
    ν hν u₀ A hAc hdiv hR ht hbound hmild
  exact ⟨hspacePhysical, heq.1, htime, hpressure, heq.2⟩

end Navier.Analysis.CriticalMildSmoothBootstrap

#print axioms Navier.Analysis.CriticalMildSmoothBootstrap.latticeTwoWeightL1_of_fiveEighthGenerator
#print axioms Navier.Analysis.CriticalMildSmoothBootstrap.globalWeightedSpectralOutputFiber_eq_actualConvolution
#print axioms Navier.Analysis.CriticalMildSmoothBootstrap.summable_weighted_spectralOutputCoefficient
#print axioms Navier.Analysis.CriticalMildSmoothBootstrap.summable_weighted_projectedModeForcing
#print axioms Navier.Analysis.CriticalMildSmoothBootstrap.summable_mildRawTimeDerivative_of_fiveEighth
#print axioms Navier.Analysis.CriticalMildSmoothBootstrap.summable_recoveredPressureGradient_of_twoWeight
#print axioms Navier.Analysis.CriticalMildSmoothBootstrap.mildFixedPoint_firstJointBootstrap_at
