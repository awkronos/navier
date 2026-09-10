import Navier.Analysis.PeriodicPressureSpatialSmoothReconstruction

/-!
# Elliptic gain for the recovered periodic pressure

The pressure multiplier has order minus one on arbitrary vector data.  On the
actual divergence-free transport convolution, the exact triad identity moves
the transport derivative to the output frequency; the two output-frequency
factors then cancel the elliptic denominator.  Consequently pressure has the
same polynomial Fourier moment as the two velocity inputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory Set

namespace Navier.Analysis.PeriodicPressureEllipticGain

open Navier
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildHigherUniformMoments
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicPressureRecovery
open Navier.Analysis.PeriodicPressureSpatialSmoothReconstruction
open Navier.Analysis.PeriodicSpatialSmoothReconstruction
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinCoerciveTerminal

theorem norm_periodOneDerivative :
    ‖periodOneDerivative‖ = 2 * Real.pi := by
  unfold periodOneDerivative
  rw [norm_mul, Complex.norm_I, mul_one]
  norm_num [abs_of_pos Real.pi_pos]

/-- The exact pressure multiplier gains one homogeneous output derivative away
from the zero mode. -/
theorem norm_pressureCoefficient_le_div_modeSize
    {k : LatticeMode} (hk : k ≠ 0) (z : ComplexSpace) :
    ‖pressureCoefficient k z‖ ≤
      complexEuclideanNorm z / (2 * Real.pi * latticeModeSize k) := by
  have hmode : 0 < latticeModeSize k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeSize_of_ne_zero hk)
  have hnum : ‖∑ i : Fin 3, (latticeFrequency k i : ℂ) * z i‖ ≤
      latticeModeSize k * complexEuclideanNorm z := by
    rw [← inner_complexFrequency]
    exact norm_inner_le_norm _ _
  have hsq : latticeFrequency k ⬝ᵥ latticeFrequency k =
      latticeModeSize k ^ 2 := by
    symm
    exact complexFrequency_norm_sq (latticeFrequency k)
  unfold pressureCoefficient
  rw [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    hsq, abs_of_nonneg (sq_nonneg _), norm_periodOneDerivative]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    ‖∑ i : Fin 3, (latticeFrequency k i : ℂ) * z i‖ *
          (2 * Real.pi * latticeModeSize k ^ 2)⁻¹ ≤
        (latticeModeSize k * complexEuclideanNorm z) *
          (2 * Real.pi * latticeModeSize k ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (by positivity))
    _ = complexEuclideanNorm z *
        (2 * Real.pi * latticeModeSize k)⁻¹ := by
      field_simp

/-- One pressure summand on an exact output fiber, including the physical
period-one derivative phase. -/
def pressureFiberTerm (k : LatticeMode) (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) : ℂ :=
  pressureCoefficient k (periodOneDerivative •
    spectralTransport (latticeFrequency ij.1.2)
      (weightedLatticeCoefficient u ij.1.1)
      (weightedLatticeCoefficient v ij.1.2))

/-- Incompressibility makes each exact pressure triad order zero: the
transport derivative transfers to the output frequency and is cancelled by
the inverse-order pressure multiplier. -/
theorem norm_pressureFiberTerm_le
    (k : LatticeMode) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖pressureFiberTerm k u v ij‖ ≤
      complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
        complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2) := by
  by_cases hk : k = 0
  · subst k
    simp [pressureFiberTerm]
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hkSize : 0 < latticeModeSize k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeSize_of_ne_zero hk)
  have htransfer := complexEuclideanNorm_spectralTransport_output_le
    u v hu ij.1.1 ij.1.2 k (by
      change ij.1.1 + ij.1.2 = k
      have hij := ij.2
      change latticeOutputMode ij.1 ∈ ({k} : Set LatticeMode) at hij
      simpa only [Set.mem_singleton_iff, latticeOutputMode] using hij)
  have hp := norm_pressureCoefficient_le_div_modeSize (k := k) hk
    (periodOneDerivative • spectralTransport (latticeFrequency ij.1.2)
      (weightedLatticeCoefficient u ij.1.1)
      (weightedLatticeCoefficient v ij.1.2))
  unfold complexEuclideanNorm at hp
  rw [complexEuclideanPoint_smul, norm_smul,
    norm_periodOneDerivative] at hp
  unfold pressureFiberTerm
  calc
    ‖pressureCoefficient k (periodOneDerivative •
        spectralTransport (latticeFrequency ij.1.2)
          (weightedLatticeCoefficient u ij.1.1)
          (weightedLatticeCoefficient v ij.1.2))‖ ≤
      (2 * Real.pi * complexEuclideanNorm
        (spectralTransport (latticeFrequency ij.1.2)
          (weightedLatticeCoefficient u ij.1.1)
          (weightedLatticeCoefficient v ij.1.2))) /
        (2 * Real.pi * latticeModeSize k) := hp
    _ ≤ (2 * Real.pi *
          (latticeModeSize k *
            complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
            complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) /
        (2 * Real.pi * latticeModeSize k) := by
      change _ ≤ (2 * Real.pi *
        (‖complexFrequency (latticeFrequency k)‖ * _ * _)) / _
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left htransfer (by positivity)) (by positivity)
    _ = complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
        complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2) := by
      field_simp

/-- The pressure recovery applied to one encoded unprojected convolution
coefficient, as a finite-dimensional continuous linear map. -/
def pressureOutputLinearMap (k : LatticeMode) : ComplexE3 →ₗ[ℂ] ℂ where
  toFun z := pressureCoefficient k
    (periodOneDerivative • WithLp.ofLp z)
  map_add' z w := by
    change pressureCoefficient k
      (periodOneDerivative • (WithLp.ofLp z + WithLp.ofLp w)) = _
    unfold pressureCoefficient
    simp only [smul_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c z := by
    change pressureCoefficient k
      (periodOneDerivative • (c • WithLp.ofLp z)) =
      c • pressureCoefficient k (periodOneDerivative • WithLp.ofLp z)
    unfold pressureCoefficient
    simp only [smul_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc, Finset.mul_sum]
    have hsum :
        (∑ x : Fin 3, (latticeFrequency k x : ℂ) *
          (periodOneDerivative * (c * WithLp.ofLp z x))) =
        c * ∑ x : Fin 3, (latticeFrequency k x : ℂ) *
          (periodOneDerivative * WithLp.ofLp z x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    rw [hsum]
    ring

def pressureOutputCLM (k : LatticeMode) : ComplexE3 →L[ℂ] ℂ :=
  ContinuousLinearMap.mk (pressureOutputLinearMap k)
    (LinearMap.continuous_of_finiteDimensional _)

/-- Same-order output weight attached to one exact pressure triad. -/
def polynomialPressureFiberTerm (r : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) : ℂ :=
  ((latticeModeWeight k ^ r : ℝ) : ℂ) • pressureFiberTerm k u v ij

theorem norm_polynomialPressureFiberTerm_le
    (r : ℝ) (hr : 0 ≤ r) (k : LatticeMode)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖polynomialPressureFiberTerm r k u v ij‖ ≤
      polynomialMomentPairMajorant r u v ij.1 := by
  have hij : ij.1.1 + ij.1.2 = k := by
    have h := ij.2
    change latticeOutputMode ij.1 ∈ ({k} : Set LatticeMode) at h
    simpa only [Set.mem_singleton_iff, latticeOutputMode] using h
  have hw : latticeModeWeight k ≤
      latticeModeWeight ij.1.1 * latticeModeWeight ij.1.2 := by
    calc
      latticeModeWeight k = latticeModeWeight (ij.1.1 + ij.1.2) :=
        congrArg latticeModeWeight hij.symm
      _ ≤ latticeModeWeight ij.1.1 * latticeModeWeight ij.1.2 :=
        latticeModeWeight_add_le_mul _ _
  have hw0 : 0 ≤ latticeModeWeight k :=
    zero_le_one.trans (one_le_latticeModeWeight k)
  have hinputs0 : 0 ≤
      latticeModeWeight ij.1.1 * latticeModeWeight ij.1.2 :=
    mul_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight ij.1.1))
      (zero_le_one.trans (one_le_latticeModeWeight ij.1.2))
  have hpow := Real.rpow_le_rpow hw0 hw hr
  unfold polynomialPressureFiberTerm
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hw0 r)]
  calc
    latticeModeWeight k ^ r * ‖pressureFiberTerm k u v ij‖ ≤
        latticeModeWeight k ^ r *
          (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
            complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) :=
      mul_le_mul_of_nonneg_left (norm_pressureFiberTerm_le k u v hu ij)
        (Real.rpow_nonneg hw0 r)
    _ ≤ (latticeModeWeight ij.1.1 * latticeModeWeight ij.1.2) ^ r *
          (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
            complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) :=
      mul_le_mul_of_nonneg_right hpow
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = polynomialMomentPairMajorant r u v ij.1 := by
      rw [Real.mul_rpow
        (zero_le_one.trans (one_le_latticeModeWeight ij.1.1))
        (zero_le_one.trans (one_le_latticeModeWeight ij.1.2))]
      unfold polynomialMomentPairMajorant polynomialMomentAmplitude
      ring

def polynomialPressureOutputCLM (r : ℝ) (k : LatticeMode) :
    ComplexE3 →L[ℂ] ℂ :=
  ((latticeModeWeight k ^ r : ℝ) : ℂ) • pressureOutputCLM k

def polynomialPressureSpectralOutputFiber (r : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) : ℂ :=
  ((latticeModeWeight k ^ r : ℝ) : ℂ) • periodOnePressureCoefficient k u v

theorem polynomialPressureOutputCLM_apply_latticeSpectralTerm
    (r : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    polynomialPressureOutputCLM r k
        (latticeSpectralTerm k (weightedLatticeCoefficient u)
          (weightedLatticeCoefficient v) ij.1) =
      polynomialPressureFiberTerm r k u v ij := by
  have hij : ij.1.1 + ij.1.2 = k := by
    have h := ij.2
    change latticeOutputMode ij.1 ∈ ({k} : Set LatticeMode) at h
    simpa only [Set.mem_singleton_iff, latticeOutputMode] using h
  rw [latticeSpectralTerm, if_pos hij]
  simp [polynomialPressureOutputCLM, pressureOutputCLM,
    pressureOutputLinearMap, polynomialPressureFiberTerm, pressureFiberTerm,
    complexEuclideanPoint]

theorem polynomialPressureOutputCLM_map_tsum
    (r : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    polynomialPressureOutputCLM r k
        (weightedLatticeSpectralConvolution k u v) =
      ∑' ij : LatticeMode × LatticeMode,
        polynomialPressureOutputCLM r k
          (latticeSpectralTerm k (weightedLatticeCoefficient u)
            (weightedLatticeCoefficient v) ij) := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  exact ContinuousLinearMap.map_tsum _
    (summable_latticeSpectralTerm_of_weightedL1 k
      (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
      (latticeConvolutionWeightedL1_of_weightedL1 k
        (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient v)))

theorem polynomialPressureOutputCLM_convolution
    (r : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    polynomialPressureOutputCLM r k
        (weightedLatticeSpectralConvolution k u v) =
      polynomialPressureSpectralOutputFiber r k u v := by
  simp [polynomialPressureOutputCLM, pressureOutputCLM,
    pressureOutputLinearMap, polynomialPressureSpectralOutputFiber,
    periodOnePressureCoefficient, periodOneConvectionCoefficient,
    complexEuclideanPoint]

theorem tsum_polynomialPressureFiberTerm_eq
    (r : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    (∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
      polynomialPressureFiberTerm r k u v ij) =
      polynomialPressureSpectralOutputFiber r k u v := by
  let f : LatticeMode × LatticeMode → ℂ := fun ij =>
    polynomialPressureOutputCLM r k
      (latticeSpectralTerm k (weightedLatticeCoefficient u)
        (weightedLatticeCoefficient v) ij)
  calc
    (∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        polynomialPressureFiberTerm r k u v ij) =
        ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode), f ij.1 := by
      apply tsum_congr
      intro ij
      exact (polynomialPressureOutputCLM_apply_latticeSpectralTerm
        r k u v ij).symm
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
        · dsimp [f, polynomialPressureOutputCLM]
          rw [latticeSpectralTerm, if_neg hij]
          simp
        · intro hm
          apply hij
          change latticeOutputMode ij = k at hm
          simpa [latticeOutputMode] using hm
    _ = polynomialPressureOutputCLM r k
        (weightedLatticeSpectralConvolution k u v) :=
      (polynomialPressureOutputCLM_map_tsum r k u v).symm
    _ = polynomialPressureSpectralOutputFiber r k u v :=
      polynomialPressureOutputCLM_convolution r k u v

theorem norm_polynomialPressureSpectralOutputFiber_le
    (r : ℝ) (hr : 0 ≤ r) (k : LatticeMode)
    (u v : WeightedLatticeBanach) (huDiv : LatticeDivergenceFree u)
    (hu : LatticePolynomialMoment r u) (hv : LatticePolynomialMoment r v) :
    ‖polynomialPressureSpectralOutputFiber r k u v‖ ≤
      polynomialMomentFiberMajorant r u v k := by
  rw [← tsum_polynomialPressureFiberTerm_eq r k u v]
  exact tsum_of_norm_bounded
    ((summable_polynomialMomentPairMajorant r u v hu hv).subtype _).hasSum
    (norm_polynomialPressureFiberTerm_le r hr k u v huDiv)

theorem norm_polynomialPressureSpectralOutputFiber_eq
    (r : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    ‖polynomialPressureSpectralOutputFiber r k u v‖ =
      latticeModeWeight k ^ r * ‖periodOnePressureCoefficient k u v‖ := by
  unfold polynomialPressureSpectralOutputFiber
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight k)) r)]

/-- Exact same-order pressure estimate for the countable physical transport
convolution.  Only the advecting carrier needs the divergence-free constraint. -/
theorem summable_periodOnePressureCoefficient_polynomial_noLoss
    (r : ℝ) (hr : 0 ≤ r) (u v : WeightedLatticeBanach)
    (huDiv : LatticeDivergenceFree u)
    (hu : LatticePolynomialMoment r u) (hv : LatticePolynomialMoment r v) :
    Summable fun k : LatticeMode => latticeModeWeight k ^ r *
      ‖periodOnePressureCoefficient k u v‖ := by
  simpa only [← norm_polynomialPressureSpectralOutputFiber_eq] using
    (summable_polynomialMomentFiberMajorant r u v hu hv).of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun k => norm_polynomialPressureSpectralOutputFiber_le
        r hr k u v huDiv hu hv)

/-- The order-`n` spatial pressure jet is summable from the same order velocity
moment; the earlier two-moment surplus is unnecessary on divergence-free data. -/
theorem summable_pressureSpatialJetMajorant_noLoss
    (n : ℕ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hdiv : LatticeDivergenceFree (physicalCarrier (A t)))
    (hA : LatticePolynomialMoment n (physicalCarrier (A t))) :
    Summable (pressureSpatialJetMajorant n A t) := by
  have hp := summable_periodOnePressureCoefficient_polynomial_noLoss
    n (by positivity) (physicalCarrier (A t)) (physicalCarrier (A t))
    hdiv hA hA
  apply (hp.mul_left ((n.factorial : ℝ) * 8 ^ n * 3 ^ n)).congr
  intro m
  simp only [pressureSpatialJetMajorant, physicalPressureCoefficient,
    Real.rpow_natCast]

private theorem finiteOrder_le_smooth (N : ℕ) :
    (N : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl N

/-- A single order-`N` moment of a divergence-free physical carrier gives
`C^N` spatial regularity of its exact recovered pressure. -/
theorem contDiff_physicalMildPressure_at_fixedTime_of_moment
    (N : ℕ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hdiv : LatticeDivergenceFree (physicalCarrier (A t)))
    (hA : LatticePolynomialMoment N (physicalCarrier (A t))) :
    ContDiff ℝ N (physicalMildPressure A t) := by
  have hmoment : ∀ n : ℕ, (n : ℕ∞) ≤ N →
      LatticePolynomialMoment n (physicalCarrier (A t)) := by
    intro n hn
    apply latticePolynomialMoment_mono (u := physicalCarrier (A t))
      (hu := hA)
    exact_mod_cast hn
  have hcomplex : ContDiff ℝ N (fun x : Space =>
      ∑' m : LatticeMode, fixedTimePhysicalPressureModeTerm A t m x) :=
    contDiff_tsum
      (N := N)
      (fun m => (contDiff_fixedTimePhysicalPressureModeTerm A t m).of_le
        (finiteOrder_le_smooth N))
      (fun n hn => summable_pressureSpatialJetMajorant_noLoss
        n A t hdiv (hmoment n hn))
      (fun n m x _hn =>
        norm_iteratedFDeriv_fixedTimePhysicalPressureModeTerm_le n A t m x)
  change ContDiff ℝ N (fun x : Space =>
    (∑' m : LatticeMode,
      physicalSpacetimePressureModeTerm A m (t, x)).re)
  have hre : ContDiff ℝ N (fun x : Space =>
      Complex.reCLM
        ((fun y : Space => ∑' m : LatticeMode,
          fixedTimePhysicalPressureModeTerm A t m y) x)) :=
    Complex.reCLM.contDiff.comp hcomplex
  simpa only [fixedTimePhysicalPressureModeTerm,
    physicalSpacetimePressureModeTerm, Complex.reCLM_apply] using hre

/-- All same-order moments give spatial smoothness without shifting every
pressure jet by two extra velocity moments. -/
theorem contDiff_physicalMildPressure_at_fixedTime_noLoss
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hdiv : LatticeDivergenceFree (physicalCarrier (A t)))
    (hA : ∀ n : ℕ,
      LatticePolynomialMoment n (physicalCarrier (A t))) :
    ContDiff ℝ ∞ (physicalMildPressure A t) := by
  have hcomplex : ContDiff ℝ ∞ (fun x : Space =>
      ∑' m : LatticeMode, fixedTimePhysicalPressureModeTerm A t m x) :=
    contDiff_tsum
      (f := fun m => fixedTimePhysicalPressureModeTerm A t m)
      (v := fun n => pressureSpatialJetMajorant n A t)
      (fun m => contDiff_fixedTimePhysicalPressureModeTerm A t m)
      (fun n _hn => summable_pressureSpatialJetMajorant_noLoss
        n A t hdiv (hA n))
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

/-- The actual bounded critical mild trajectory feeds the lossless pressure
reconstruction at every positive time. -/
theorem contDiff_physicalMildPressure_at_positiveTime_noLoss
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
  apply contDiff_physicalMildPressure_at_fixedTime_noLoss
  · exact latticeDivergenceFree_physicalCarrier (hu t)
  · intro n
    apply latticePolynomialMoment_physicalCarrier
    have hhigh := (hall (2 * n) t ⟨le_rfl, htT⟩).1
    exact latticePolynomialMoment_mono (u := u t) (hu := hhigh) (by
      rw [iteratedHalfOrder_eq]
      push_cast
      norm_num)

end Navier.Analysis.PeriodicPressureEllipticGain
