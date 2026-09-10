import Navier.Analysis.PeriodicSpatialSmoothReconstruction
import Navier.Analysis.CriticalMildPolynomialMomentConvolution
import Navier.Analysis.LeiLinCoerciveTerminal

/-!
# Spatial smoothness of the recovered periodic pressure

This module first proves the missing all-order polynomial estimate for the
literal unprojected lattice transport convolution.  The exact pressure
multiplier is then bounded by that convolution, so the all-moment positive-time
mild bootstrap yields a spatially `C∞` recovered physical pressure.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory Set

namespace Navier.Analysis.PeriodicPressureSpatialSmoothReconstruction

open Navier
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildHigherUniformMoments
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicPressureRecovery
open Navier.Analysis.PeriodicSpatialSmoothReconstruction

/-- One unprojected transport summand on an exact output fiber, with the
order-`s-1` output weight. -/
def polynomialUnprojectedFiberTerm (s : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) : ComplexE3 :=
  latticeModeWeight k ^ (s - 1) • complexEuclideanPoint
    (spectralTransport (latticeFrequency ij.1.2)
      (weightedLatticeCoefficient u ij.1.1)
      (weightedLatticeCoefficient v ij.1.2))

theorem norm_polynomialUnprojectedFiberTerm_le
    (s : ℝ) (hs : 1 ≤ s) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖polynomialUnprojectedFiberTerm s k u v ij‖ ≤
      polynomialMomentPairMajorant s u v ij.1 := by
  have hweight := outputDerivativeWeight_le_inputPolynomialWeights
    s hs ij.1.1 ij.1.2 k ij.2
  have htransport := complexEuclideanNorm_spectralTransport_le
    (latticeFrequency ij.1.2)
    (weightedLatticeCoefficient u ij.1.1)
    (weightedLatticeCoefficient v ij.1.2)
  have hwk0 : 0 ≤ latticeModeWeight k :=
    zero_le_one.trans (one_le_latticeModeWeight k)
  unfold polynomialUnprojectedFiberTerm
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hwk0 (s - 1))]
  change latticeModeWeight k ^ (s - 1) * complexEuclideanNorm
      (spectralTransport (latticeFrequency ij.1.2)
        (weightedLatticeCoefficient u ij.1.1)
        (weightedLatticeCoefficient v ij.1.2)) ≤ _
  calc
    latticeModeWeight k ^ (s - 1) * complexEuclideanNorm
        (spectralTransport (latticeFrequency ij.1.2)
          (weightedLatticeCoefficient u ij.1.1)
          (weightedLatticeCoefficient v ij.1.2)) ≤
      latticeModeWeight k ^ (s - 1) *
        (‖complexFrequency (latticeFrequency ij.1.2)‖ *
          complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
          complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) :=
      mul_le_mul_of_nonneg_left htransport
        (Real.rpow_nonneg hwk0 (s - 1))
    _ ≤ (latticeModeWeight ij.1.1 ^ s *
          latticeModeWeight ij.1.2 ^ s) *
        (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
          complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) := by
      calc
        _ = (latticeModeWeight k ^ (s - 1) *
              ‖complexFrequency (latticeFrequency ij.1.2)‖) *
            (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hweight
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = polynomialMomentPairMajorant s u v ij.1 := by
      unfold polynomialMomentPairMajorant polynomialMomentAmplitude
      ring

/-- Apply only the output polynomial weight to the encoded literal
convolution; unlike the projected estimate, this map contains no Leray factor. -/
def polynomialOutputCarrierCLM (s : ℝ) (k : LatticeMode) :
    ComplexE3 →L[ℂ] ComplexE3 :=
  ((latticeModeWeight k ^ (s - 1) : ℝ) : ℂ) •
    (complexEuclideanDecodeCLM.comp complexEuclideanEncodeCLM)

def polynomialUnprojectedSpectralOutputFiber (s : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) : ComplexE3 :=
  latticeModeWeight k ^ (s - 1) • complexEuclideanPoint
    (spectralOutputCoefficient k u v)

theorem polynomialOutputCarrierCLM_apply (s : ℝ) (k : LatticeMode)
    (z : ComplexE3) :
    polynomialOutputCarrierCLM s k z =
      latticeModeWeight k ^ (s - 1) •
        complexEuclideanPoint (WithLp.ofLp z) := by
  simp [polynomialOutputCarrierCLM, complexEuclideanDecodeCLM,
    complexEuclideanEncodeCLM, complexEuclideanPoint]

theorem polynomialOutputCarrierCLM_apply_latticeSpectralTerm
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    polynomialOutputCarrierCLM s k
        (latticeSpectralTerm k (weightedLatticeCoefficient u)
          (weightedLatticeCoefficient v) ij.1) =
      polynomialUnprojectedFiberTerm s k u v ij := by
  rw [polynomialOutputCarrierCLM_apply]
  have hij := ij.2
  change ij.1.1 + ij.1.2 = k at hij
  rw [latticeSpectralTerm, if_pos hij]
  rfl

theorem polynomialOutputCarrierCLM_map_tsum
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    polynomialOutputCarrierCLM s k
        (weightedLatticeSpectralConvolution k u v) =
      ∑' ij : LatticeMode × LatticeMode,
        polynomialOutputCarrierCLM s k
          (latticeSpectralTerm k (weightedLatticeCoefficient u)
            (weightedLatticeCoefficient v) ij) := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  exact ContinuousLinearMap.map_tsum _
    (summable_latticeSpectralTerm_of_weightedL1 k
      (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
      (latticeConvolutionWeightedL1_of_weightedL1 k
        (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient v)))

theorem polynomialOutputCarrierCLM_weightedLatticeSpectralConvolution
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    polynomialOutputCarrierCLM s k
        (weightedLatticeSpectralConvolution k u v) =
      polynomialUnprojectedSpectralOutputFiber s k u v := by
  rw [polynomialOutputCarrierCLM_apply]
  rfl

theorem tsum_polynomialUnprojectedFiberTerm_eq
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    (∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
      polynomialUnprojectedFiberTerm s k u v ij) =
      polynomialUnprojectedSpectralOutputFiber s k u v := by
  let f : LatticeMode × LatticeMode → ComplexE3 := fun ij =>
    polynomialOutputCarrierCLM s k
      (latticeSpectralTerm k (weightedLatticeCoefficient u)
        (weightedLatticeCoefficient v) ij)
  calc
    (∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        polynomialUnprojectedFiberTerm s k u v ij) =
        ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode), f ij.1 := by
      apply tsum_congr
      intro ij
      exact (polynomialOutputCarrierCLM_apply_latticeSpectralTerm
        s k u v ij).symm
    _ = ∑' ij : LatticeMode × LatticeMode,
        (latticeOutputMode ⁻¹' ({k} : Set LatticeMode)).indicator f ij :=
      tsum_subtype _ _
    _ = ∑' ij : LatticeMode × LatticeMode, f ij := by
      apply tsum_congr
      intro ij
      by_cases hij : ij.1 + ij.2 = k
      · rw [Set.indicator_of_mem]
        change latticeOutputMode ij = k
        simpa [latticeOutputMode] using hij
      · rw [Set.indicator_of_notMem]
        · dsimp [f]
          rw [latticeSpectralTerm, if_neg hij]
          simp
        · intro hm
          apply hij
          change latticeOutputMode ij = k at hm
          simpa [latticeOutputMode] using hm
    _ = polynomialOutputCarrierCLM s k
        (weightedLatticeSpectralConvolution k u v) :=
      (polynomialOutputCarrierCLM_map_tsum s k u v).symm
    _ = polynomialUnprojectedSpectralOutputFiber s k u v :=
      polynomialOutputCarrierCLM_weightedLatticeSpectralConvolution s k u v

theorem norm_polynomialUnprojectedSpectralOutputFiber_le
    (s : ℝ) (hs : 1 ≤ s) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    ‖polynomialUnprojectedSpectralOutputFiber s k u v‖ ≤
      polynomialMomentFiberMajorant s u v k := by
  rw [← tsum_polynomialUnprojectedFiberTerm_eq s k u v]
  exact tsum_of_norm_bounded
    ((summable_polynomialMomentPairMajorant s u v hu hv).subtype _).hasSum
    (norm_polynomialUnprojectedFiberTerm_le s hs k u v)

theorem norm_polynomialUnprojectedSpectralOutputFiber_eq
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    ‖polynomialUnprojectedSpectralOutputFiber s k u v‖ =
      latticeModeWeight k ^ (s - 1) *
        complexEuclideanNorm (spectralOutputCoefficient k u v) := by
  unfold polynomialUnprojectedSpectralOutputFiber
  rw [norm_smul, Real.norm_of_nonneg
    (Real.rpow_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight k)) (s - 1))]
  rfl

/-- The literal unprojected convolution loses exactly one polynomial Fourier
weight, at every real order `s ≥ 1`. -/
theorem summable_spectralOutputCoefficient_polynomial_sub_one
    (s : ℝ) (hs : 1 ≤ s) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    Summable fun k : LatticeMode => latticeModeWeight k ^ (s - 1) *
      complexEuclideanNorm (spectralOutputCoefficient k u v) := by
  simpa only [← norm_polynomialUnprojectedSpectralOutputFiber_eq] using
    (summable_polynomialMomentFiberMajorant s u v hu hv).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun k => norm_polynomialUnprojectedSpectralOutputFiber_le
        s hs k u v hu hv)

theorem one_le_norm_periodOneDerivative :
    1 ≤ ‖periodOneDerivative‖ := by
  calc
    1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    _ = ‖periodOneDerivative‖ := by
      unfold periodOneDerivative
      rw [norm_mul, Complex.norm_I, mul_one]
      norm_num [abs_of_pos Real.pi_pos]

/-- The exact zero-mean pressure multiplier costs at most one inhomogeneous
output weight.  At nonzero integer frequency its denominator has norm at
least one; Cauchy--Schwarz controls the numerator. -/
theorem norm_pressureCoefficient_le_weight_mul
    (k : LatticeMode) (z : ComplexSpace) :
    ‖pressureCoefficient k z‖ ≤
      latticeModeWeight k * complexEuclideanNorm z := by
  by_cases hk : k = 0
  · subst k
    rw [pressureCoefficient_zero_mode, norm_zero]
    exact mul_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight 0)) (norm_nonneg _)
  have hmode : 1 ≤ latticeModeSize k :=
    one_le_latticeModeSize_of_ne_zero hk
  have hdot : 1 ≤ latticeFrequency k ⬝ᵥ latticeFrequency k := by
    rw [← complexFrequency_norm_sq]
    unfold latticeModeSize at hmode
    nlinarith
  have hden : 1 ≤ ‖periodOneDerivative *
      ((latticeFrequency k ⬝ᵥ latticeFrequency k : ℝ) : ℂ)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one hdot)]
    nlinarith [one_le_norm_periodOneDerivative]
  have hnum : ‖∑ i : Fin 3, (latticeFrequency k i : ℂ) * z i‖ ≤
      ‖complexFrequency (latticeFrequency k)‖ *
        complexEuclideanNorm z := by
    rw [← inner_complexFrequency]
    exact norm_inner_le_norm _ _
  unfold pressureCoefficient
  rw [norm_div, norm_neg]
  calc
    ‖∑ i : Fin 3, (latticeFrequency k i : ℂ) * z i‖ /
        ‖periodOneDerivative *
          ((latticeFrequency k ⬝ᵥ latticeFrequency k : ℝ) : ℂ)‖ ≤
      ‖∑ i : Fin 3, (latticeFrequency k i : ℂ) * z i‖ :=
        div_le_self (norm_nonneg _) hden
    _ ≤ ‖complexFrequency (latticeFrequency k)‖ *
        complexEuclideanNorm z := hnum
    _ ≤ latticeModeWeight k * complexEuclideanNorm z := by
      have hnorm : 0 ≤ ‖complexFrequency (latticeFrequency k)‖ := norm_nonneg _
      exact mul_le_mul_of_nonneg_right
        (by unfold latticeModeWeight; linarith) (norm_nonneg _)

/-- If both physical coefficient carriers have order `r+2` moments, the
recovered scalar pressure coefficients have an order-`r` moment. -/
theorem summable_periodOnePressureCoefficient_polynomial
    (r : ℝ) (hr : 0 ≤ r) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment (r + 2) u)
    (hv : LatticePolynomialMoment (r + 2) v) :
    Summable fun k : LatticeMode => latticeModeWeight k ^ r *
      ‖periodOnePressureCoefficient k u v‖ := by
  have hspectral := summable_spectralOutputCoefficient_polynomial_sub_one
    (r + 2) (by linarith) u v hu hv
  have hmajor := hspectral.mul_left ‖periodOneDerivative‖
  apply hmajor.of_nonneg_of_le
  · intro k
    exact mul_nonneg
      (Real.rpow_nonneg
        (zero_le_one.trans (one_le_latticeModeWeight k)) r)
      (norm_nonneg _)
  · intro k
    have hp := norm_pressureCoefficient_le_weight_mul k
      (periodOneConvectionCoefficient k u v)
    calc
      latticeModeWeight k ^ r *
          ‖periodOnePressureCoefficient k u v‖ ≤
        latticeModeWeight k ^ r *
          (latticeModeWeight k * complexEuclideanNorm
            (periodOneConvectionCoefficient k u v)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [periodOnePressureCoefficient] using hp)
          (Real.rpow_nonneg
            (zero_le_one.trans (one_le_latticeModeWeight k)) r)
      _ = ‖periodOneDerivative‖ *
          (latticeModeWeight k ^ ((r + 2) - 1) *
            complexEuclideanNorm (spectralOutputCoefficient k u v)) := by
        unfold periodOneConvectionCoefficient spectralOutputCoefficient
          complexEuclideanNorm
        rw [complexEuclideanPoint_smul, norm_smul]
        rw [show (r + 2) - 1 = r + 1 by ring,
          Real.rpow_add
            (lt_of_lt_of_le zero_lt_one
              (one_le_latticeModeWeight k)),
          Real.rpow_one]
        ring

/-- One fixed-time mode of the exact recovered physical pressure series. -/
def fixedTimePhysicalPressureModeTerm
    (A : ℝ → WeightedLatticeBanach) (t : ℝ) (m : LatticeMode)
    (x : Space) : ℂ :=
  latticeCharacter m x * physicalPressureCoefficient A t m

theorem contDiff_fixedTimePhysicalPressureModeTerm
    (A : ℝ → WeightedLatticeBanach) (t : ℝ) (m : LatticeMode) :
    ContDiff ℝ ∞ (fixedTimePhysicalPressureModeTerm A t m) := by
  unfold fixedTimePhysicalPressureModeTerm
  exact (contDiff_latticeCharacter m).mul contDiff_const

def pressureSpatialJetMajorant
    (n : ℕ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (m : LatticeMode) : ℝ :=
  (n.factorial : ℝ) * 8 ^ n * 3 ^ n *
    (latticeModeWeight m ^ n * ‖physicalPressureCoefficient A t m‖)

theorem summable_pressureSpatialJetMajorant
    (n : ℕ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hA : LatticePolynomialMoment (n + 2) (physicalCarrier (A t))) :
    Summable (pressureSpatialJetMajorant n A t) := by
  have hp := summable_periodOnePressureCoefficient_polynomial
    n (by positivity) (physicalCarrier (A t)) (physicalCarrier (A t)) hA hA
  apply (hp.mul_left ((n.factorial : ℝ) * 8 ^ n * 3 ^ n)).congr
  intro m
  simp only [pressureSpatialJetMajorant, physicalPressureCoefficient,
    Real.rpow_natCast]

theorem norm_iteratedFDeriv_fixedTimePhysicalPressureModeTerm_le
    (n : ℕ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (m : LatticeMode) (x : Space) :
    ‖iteratedFDeriv ℝ n (fixedTimePhysicalPressureModeTerm A t m) x‖ ≤
      pressureSpatialJetMajorant n A t m := by
  let p : ℂ := physicalPressureCoefficient A t m
  let L : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℂ).smulRight p
  have hL : ‖L‖ ≤ ‖p‖ := by
    refine L.opNorm_le_bound (norm_nonneg p) ?_
    intro z
    simp only [L, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, norm_smul]
    rw [mul_comm]
  have hderiv :
      ‖iteratedFDeriv ℝ n (fixedTimePhysicalPressureModeTerm A t m) x‖ ≤
        ‖p‖ * ‖iteratedFDeriv ℝ n (latticeCharacter m) x‖ := by
    unfold fixedTimePhysicalPressureModeTerm
    change ‖iteratedFDeriv ℝ n
      (fun y => latticeCharacter m y • p) x‖ ≤ _
    rw [iteratedFDeriv_smul_const_apply
      ((contDiff_latticeCharacter m).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))]
    exact (L.norm_compContinuousMultilinearMap_le
      (iteratedFDeriv ℝ n (latticeCharacter m) x)).trans
        (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  calc
    ‖iteratedFDeriv ℝ n (fixedTimePhysicalPressureModeTerm A t m) x‖ ≤
        ‖p‖ * ((n.factorial : ℝ) * 8 ^ n *
          (3 * latticeModeWeight m) ^ n) :=
      hderiv.trans (mul_le_mul_of_nonneg_left
        (norm_iteratedFDeriv_latticeCharacter_le n m x) (norm_nonneg p))
    _ = pressureSpatialJetMajorant n A t m := by
      unfold pressureSpatialJetMajorant p
      rw [mul_pow]
      ring

/-- All polynomial moments of one physical coefficient state imply spatial
`C∞` regularity of its exact recovered zero-mean pressure. -/
theorem contDiff_physicalMildPressure_at_fixedTime_of_allMoments
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hA : ∀ n : ℕ,
      LatticePolynomialMoment n (physicalCarrier (A t))) :
    ContDiff ℝ ∞ (physicalMildPressure A t) := by
  have hmoment : ∀ n : ℕ,
      LatticePolynomialMoment ((n : ℝ) + 2) (physicalCarrier (A t)) := by
    intro n
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hA (n + 2)
  have hcomplex : ContDiff ℝ ∞ (fun x : Space =>
      ∑' m : LatticeMode, fixedTimePhysicalPressureModeTerm A t m x) :=
    contDiff_tsum
      (f := fun m => fixedTimePhysicalPressureModeTerm A t m)
      (v := fun n => pressureSpatialJetMajorant n A t)
      (fun m => contDiff_fixedTimePhysicalPressureModeTerm A t m)
      (fun n _hn => summable_pressureSpatialJetMajorant n A t (hmoment n))
      (fun n m x _hn =>
        norm_iteratedFDeriv_fixedTimePhysicalPressureModeTerm_le n A t m x)
  change ContDiff ℝ ∞ (fun x : Space =>
    (∑' m : LatticeMode,
      physicalSpacetimePressureModeTerm A m (t, x)).re)
  have hre : ContDiff ℝ ∞ (fun x : Space =>
      Complex.reCLM
        ((fun y : Space => ∑' m : LatticeMode,
          fixedTimePhysicalPressureModeTerm A t m y) x)) :=
    Complex.reCLM.contDiff.comp hcomplex
  simpa only [fixedTimePhysicalPressureModeTerm,
    physicalSpacetimePressureModeTerm, Complex.reCLM_apply] using hre

/-- The actual bounded critical mild trajectory has spatially `C∞` recovered
physical pressure at every positive time in its chart.  No pressure rapidity
or pressure smoothness premise is assumed. -/
theorem contDiff_physicalMildPressure_at_positiveTime
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ x, LatticeDivergenceFree (u x))
    {R T : ℝ} (hR : 0 ≤ R)
    (huR : ∀ x ∈ Ioc (0 : ℝ) T, ‖u x‖ ≤ R)
    (hmild : ∀ x (hx : x ∈ Icc (0 : ℝ) T),
      u x = criticalMildImage ν hν u₀ u hu x hx.1)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ContDiff ℝ ∞ (physicalMildPressure u t) := by
  obtain ⟨B, _hB, hall⟩ :=
    exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval
      ν hν u₀ hu₀ u huc hu hR ht htT huR hmild
  apply contDiff_physicalMildPressure_at_fixedTime_of_allMoments
  intro n
  apply latticePolynomialMoment_physicalCarrier
  have hhigh := (hall (2 * n) t ⟨le_rfl, htT⟩).1
  exact latticePolynomialMoment_mono (u := u t) (hu := hhigh) (by
    rw [iteratedHalfOrder_eq]
    push_cast
    norm_num)

end Navier.Analysis.PeriodicPressureSpatialSmoothReconstruction
