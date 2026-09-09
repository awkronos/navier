import Navier.Analysis.CriticalMildModeDifferentiation

/-!
# Polynomial moments of the exact projected lattice convolution

For every real order `s ≥ 1`, this module proves the derivative-loss estimate

`S_(s - 1)(P div (u tensor v)) ≤ S_s(u) S_s(v)`.

Here `S_s` is the inhomogeneous Fourier `ℓ¹` moment built from the repository's
literal decoded lattice coefficients.  The output below is the exact countable
transport convolution followed by the existing complex Leray projector; no
finite truncation or auxiliary bilinear operator replaces that convolution.

The repository's raw spectral transport omits the physical period-one factor
`-2 * π * I`.  Multiplying the output by that scalar therefore multiplies the
displayed estimate by `2 * π`; the moment and derivative accounting is unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildPolynomialMomentConvolution

open MeasureTheory Set Topology
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildModeDifferentiation

/-- The order-`s` inhomogeneous Fourier moment density of one decoded mode. -/
def polynomialMomentAmplitude (s : ℝ) (u : WeightedLatticeBanach)
    (k : LatticeMode) : ℝ :=
  latticeModeWeight k ^ s *
    complexEuclideanNorm (weightedLatticeCoefficient u k)

/-- Finiteness of the exact order-`s` inhomogeneous Fourier `ℓ¹` moment. -/
def LatticePolynomialMoment (s : ℝ) (u : WeightedLatticeBanach) : Prop :=
  Summable (polynomialMomentAmplitude s u)

/-- The scalar value of the exact order-`s` Fourier moment. -/
def polynomialMoment (s : ℝ) (u : WeightedLatticeBanach) : ℝ :=
  ∑' k, polynomialMomentAmplitude s u k

theorem polynomialMomentAmplitude_nonneg (s : ℝ) (u : WeightedLatticeBanach)
    (k : LatticeMode) : 0 ≤ polynomialMomentAmplitude s u k := by
  exact mul_nonneg
    (Real.rpow_nonneg (zero_le_one.trans (one_le_latticeModeWeight k)) s)
    (norm_nonneg _)

/-- The full-pair product majorant at polynomial order `s`. -/
def polynomialMomentPairMajorant (s : ℝ) (u v : WeightedLatticeBanach)
    (ij : LatticeMode × LatticeMode) : ℝ :=
  polynomialMomentAmplitude s u ij.1 * polynomialMomentAmplitude s v ij.2

theorem summable_polynomialMomentPairMajorant (s : ℝ)
    (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    Summable (polynomialMomentPairMajorant s u v) := by
  exact hu.mul_of_nonneg hv
    (polynomialMomentAmplitude_nonneg s u)
    (polynomialMomentAmplitude_nonneg s v)

/-- Exact weight allocation on a lattice triad: an order `s - 1` output
weight and the one transport derivative fit inside two order-`s` inputs. -/
theorem outputDerivativeWeight_le_inputPolynomialWeights
    (s : ℝ) (hs : 1 ≤ s) (i j k : LatticeMode) (hijk : i + j = k) :
    latticeModeWeight k ^ (s - 1) *
        ‖complexFrequency (latticeFrequency j)‖ ≤
      latticeModeWeight i ^ s * latticeModeWeight j ^ s := by
  have hsi : 0 ≤ s - 1 := sub_nonneg.mpr hs
  have hwi : 0 ≤ latticeModeWeight i :=
    zero_le_one.trans (one_le_latticeModeWeight i)
  have hwj : 0 ≤ latticeModeWeight j :=
    zero_le_one.trans (one_le_latticeModeWeight j)
  have hwip : 0 < latticeModeWeight i := lt_of_lt_of_le zero_lt_one
    (one_le_latticeModeWeight i)
  have hwjp : 0 < latticeModeWeight j := lt_of_lt_of_le zero_lt_one
    (one_le_latticeModeWeight j)
  have hwk : latticeModeWeight k ≤ latticeModeWeight i * latticeModeWeight j := by
    rw [← hijk]
    exact latticeModeWeight_add_le_mul i j
  have hwk0 : 0 ≤ latticeModeWeight k :=
    zero_le_one.trans (one_le_latticeModeWeight k)
  have hpow : latticeModeWeight k ^ (s - 1) ≤
      (latticeModeWeight i * latticeModeWeight j) ^ (s - 1) :=
    Real.rpow_le_rpow hwk0 hwk hsi
  have hq : ‖complexFrequency (latticeFrequency j)‖ ≤ latticeModeWeight j := by
    unfold latticeModeWeight
    linarith [norm_nonneg (complexFrequency (latticeFrequency j))]
  have hi : latticeModeWeight i ^ (s - 1) ≤ latticeModeWeight i ^ s :=
    Real.rpow_le_rpow_of_exponent_le (one_le_latticeModeWeight i) (by linarith)
  have hj : latticeModeWeight j ^ (s - 1) * latticeModeWeight j =
      latticeModeWeight j ^ s := by
    simpa only [Real.rpow_one, sub_add_cancel] using
      (Real.rpow_add hwjp (s - 1) 1).symm
  calc
    latticeModeWeight k ^ (s - 1) *
        ‖complexFrequency (latticeFrequency j)‖ ≤
      (latticeModeWeight i * latticeModeWeight j) ^ (s - 1) *
        latticeModeWeight j := by
          exact mul_le_mul hpow hq (norm_nonneg _)
            (Real.rpow_nonneg (mul_nonneg hwi hwj) (s - 1))
    _ = latticeModeWeight i ^ (s - 1) * latticeModeWeight j ^ s := by
      rw [Real.mul_rpow hwi hwj]
      calc
        latticeModeWeight i ^ (s - 1) * latticeModeWeight j ^ (s - 1) *
            latticeModeWeight j = latticeModeWeight i ^ (s - 1) *
              (latticeModeWeight j ^ (s - 1) * latticeModeWeight j) := by ring
        _ = _ := by rw [hj]
    _ ≤ latticeModeWeight i ^ s * latticeModeWeight j ^ s :=
      mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg hwj s)

/-- One exact projected transport summand on the constrained output fiber,
carrying the order `s - 1` output weight. -/
def polynomialProjectedFiberTerm (s : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) : ComplexE3 :=
  latticeModeWeight k ^ (s - 1) • complexEuclideanPoint
    (complexLeray (latticeFrequency k)
      (spectralTransport (latticeFrequency ij.1.2)
        (weightedLatticeCoefficient u ij.1.1)
        (weightedLatticeCoefficient v ij.1.2)))

/-- The exact projected triad is bounded by the polynomial pair majorant. -/
theorem norm_polynomialProjectedFiberTerm_le
    (s : ℝ) (hs : 1 ≤ s) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖polynomialProjectedFiberTerm s k u v ij‖ ≤
      polynomialMomentPairMajorant s u v ij.1 := by
  have hijk : ij.1.1 + ij.1.2 = k := ij.2
  have hwk0 : 0 ≤ latticeModeWeight k :=
    zero_le_one.trans (one_le_latticeModeWeight k)
  have hweight := outputDerivativeWeight_le_inputPolynomialWeights
    s hs ij.1.1 ij.1.2 k hijk
  have htransport := complexEuclideanNorm_spectralTransport_le
    (latticeFrequency ij.1.2)
    (weightedLatticeCoefficient u ij.1.1)
    (weightedLatticeCoefficient v ij.1.2)
  have hproject := complexEuclideanNorm_complexLeray_le
    (latticeFrequency k)
    (spectralTransport (latticeFrequency ij.1.2)
      (weightedLatticeCoefficient u ij.1.1)
      (weightedLatticeCoefficient v ij.1.2))
  unfold polynomialProjectedFiberTerm
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hwk0 (s - 1))]
  change latticeModeWeight k ^ (s - 1) * complexEuclideanNorm
      (complexLeray (latticeFrequency k)
        (spectralTransport (latticeFrequency ij.1.2)
          (weightedLatticeCoefficient u ij.1.1)
          (weightedLatticeCoefficient v ij.1.2))) ≤ _
  calc
    latticeModeWeight k ^ (s - 1) * complexEuclideanNorm
        (complexLeray (latticeFrequency k)
          (spectralTransport (latticeFrequency ij.1.2)
            (weightedLatticeCoefficient u ij.1.1)
            (weightedLatticeCoefficient v ij.1.2))) ≤
      latticeModeWeight k ^ (s - 1) * complexEuclideanNorm
        (spectralTransport (latticeFrequency ij.1.2)
          (weightedLatticeCoefficient u ij.1.1)
          (weightedLatticeCoefficient v ij.1.2)) :=
      mul_le_mul_of_nonneg_left hproject (Real.rpow_nonneg hwk0 (s - 1))
    _ ≤ latticeModeWeight k ^ (s - 1) *
        (‖complexFrequency (latticeFrequency ij.1.2)‖ *
          complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
          complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) :=
      mul_le_mul_of_nonneg_left htransport (Real.rpow_nonneg hwk0 (s - 1))
    _ ≤ (latticeModeWeight ij.1.1 ^ s * latticeModeWeight ij.1.2 ^ s) *
        (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
          complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) := by
      calc
        latticeModeWeight k ^ (s - 1) *
            (‖complexFrequency (latticeFrequency ij.1.2)‖ *
              complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) =
            (latticeModeWeight k ^ (s - 1) *
              ‖complexFrequency (latticeFrequency ij.1.2)‖) *
              (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
                complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hweight
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = polynomialMomentPairMajorant s u v ij.1 := by
      unfold polynomialMomentPairMajorant polynomialMomentAmplitude
      ring

theorem summable_polynomialProjectedFiberTerm
    (s : ℝ) (hs : 1 ≤ s) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    Summable (polynomialProjectedFiberTerm s k u v) := by
  exact ((summable_polynomialMomentPairMajorant s u v hu hv).subtype
    (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))).of_norm_bounded
      (norm_polynomialProjectedFiberTerm_le s hs k u v)

/-- The projected coefficient of the repository's literal countable transport
convolution at one output mode. -/
def projectedSpectralConvolutionCoefficient (k : LatticeMode)
    (u v : WeightedLatticeBanach) : ComplexSpace :=
  complexLeray (latticeFrequency k) (spectralOutputCoefficient k u v)

/-- The order-`r` moment of the exact projected countable convolution. -/
def projectedConvolutionPolynomialMoment (r : ℝ)
    (u v : WeightedLatticeBanach) : ℝ :=
  ∑' k, latticeModeWeight k ^ r *
    complexEuclideanNorm (projectedSpectralConvolutionCoefficient k u v)

/-- The exact order-`s - 1` projected nonlinear coefficient encoded with its
moment weight: the literal countable convolution is formed first, and Leray
projection is applied at the output frequency. -/
def polynomialProjectedSpectralOutputFiber (s : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) : ComplexE3 :=
  latticeModeWeight k ^ (s - 1) • complexEuclideanPoint
    (projectedSpectralConvolutionCoefficient k u v)

/-- The finite-dimensional complex Leray projector as a continuous linear map. -/
def complexLerayCLM (k : LatticeMode) : ComplexSpace →L[ℂ] ComplexSpace :=
  ContinuousLinearMap.mk (complexLeray (latticeFrequency k))
    (LinearMap.continuous_of_finiteDimensional _)

/-- Apply Leray projection and the order-`s - 1` output weight to an encoded
literal convolution fiber. -/
def polynomialProjectionCarrierCLM (s : ℝ) (k : LatticeMode) :
    ComplexE3 →L[ℂ] ComplexE3 :=
  ((latticeModeWeight k ^ (s - 1) : ℝ) : ℂ) •
    (complexEuclideanDecodeCLM.comp
      ((complexLerayCLM k).comp complexEuclideanEncodeCLM))

theorem polynomialProjectionCarrierCLM_apply (s : ℝ) (k : LatticeMode)
    (z : ComplexE3) :
    polynomialProjectionCarrierCLM s k z =
      latticeModeWeight k ^ (s - 1) • complexEuclideanPoint
        (complexLeray (latticeFrequency k) (WithLp.ofLp z)) := by
  simp [polynomialProjectionCarrierCLM, complexLerayCLM,
    complexEuclideanDecodeCLM, complexEuclideanEncodeCLM,
    complexEuclideanPoint]

theorem polynomialProjectionCarrierCLM_apply_latticeSpectralTerm
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    polynomialProjectionCarrierCLM s k
        (latticeSpectralTerm k (weightedLatticeCoefficient u)
          (weightedLatticeCoefficient v) ij.1) =
      polynomialProjectedFiberTerm s k u v ij := by
  rw [polynomialProjectionCarrierCLM_apply]
  have hij : ij.1.1 + ij.1.2 = k := ij.2
  rw [latticeSpectralTerm, if_pos hij]
  rfl

/-- The projection/weight map commutes with the convergent literal
convolution `tsum`. -/
theorem polynomialProjectionCarrierCLM_map_tsum
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    polynomialProjectionCarrierCLM s k
        (weightedLatticeSpectralConvolution k u v) =
      ∑' ij : LatticeMode × LatticeMode,
        polynomialProjectionCarrierCLM s k
          (latticeSpectralTerm k (weightedLatticeCoefficient u)
            (weightedLatticeCoefficient v) ij) := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  exact ContinuousLinearMap.map_tsum _
    (summable_latticeSpectralTerm_of_weightedL1 k
      (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
      (latticeConvolutionWeightedL1_of_weightedL1 k
        (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient v)))

theorem polynomialProjectionCarrierCLM_weightedLatticeSpectralConvolution
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    polynomialProjectionCarrierCLM s k
        (weightedLatticeSpectralConvolution k u v) =
      polynomialProjectedSpectralOutputFiber s k u v := by
  rw [polynomialProjectionCarrierCLM_apply]
  rfl

/-- The summable constrained projected triads are exactly the existing
literal countable convolution followed by output-frequency Leray projection. -/
theorem tsum_polynomialProjectedFiberTerm_eq
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    (∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
      polynomialProjectedFiberTerm s k u v ij) =
      polynomialProjectedSpectralOutputFiber s k u v := by
  let f : LatticeMode × LatticeMode → ComplexE3 := fun ij =>
    polynomialProjectionCarrierCLM s k
      (latticeSpectralTerm k (weightedLatticeCoefficient u)
        (weightedLatticeCoefficient v) ij)
  calc
    (∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        polynomialProjectedFiberTerm s k u v ij) =
        ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode), f ij.1 := by
      apply tsum_congr
      intro ij
      exact (polynomialProjectionCarrierCLM_apply_latticeSpectralTerm
        s k u v ij).symm
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
    _ = polynomialProjectionCarrierCLM s k
        (weightedLatticeSpectralConvolution k u v) :=
      (polynomialProjectionCarrierCLM_map_tsum s k u v).symm
    _ = polynomialProjectedSpectralOutputFiber s k u v :=
      polynomialProjectionCarrierCLM_weightedLatticeSpectralConvolution s k u v

/-- The scalar majorant grouped over each exact output-mode fiber. -/
def polynomialMomentFiberMajorant (s : ℝ) (u v : WeightedLatticeBanach)
    (k : LatticeMode) : ℝ :=
  ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
    polynomialMomentPairMajorant s u v ij.1

theorem summable_polynomialMomentFiberMajorant
    (s : ℝ) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    Summable (polynomialMomentFiberMajorant s u v) := by
  have hpair := summable_polynomialMomentPairMajorant s u v hu hv
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      polynomialMomentPairMajorant s u v x.2.1) :=
    latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
  exact hsigma.sigma

theorem norm_polynomialProjectedSpectralOutputFiber_le
    (s : ℝ) (hs : 1 ≤ s) (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    ‖polynomialProjectedSpectralOutputFiber s k u v‖ ≤
      polynomialMomentFiberMajorant s u v k := by
  rw [← tsum_polynomialProjectedFiberTerm_eq s k u v]
  exact tsum_of_norm_bounded
    ((summable_polynomialMomentPairMajorant s u v hu hv).subtype _).hasSum
    (norm_polynomialProjectedFiberTerm_le s hs k u v)

theorem summable_norm_polynomialProjectedSpectralOutputFiber
    (s : ℝ) (hs : 1 ≤ s) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    Summable fun k => ‖polynomialProjectedSpectralOutputFiber s k u v‖ := by
  exact (summable_polynomialMomentFiberMajorant s u v hu hv).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun k => norm_polynomialProjectedSpectralOutputFiber_le s hs k u v hu hv)

theorem norm_polynomialProjectedSpectralOutputFiber_eq
    (s : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    ‖polynomialProjectedSpectralOutputFiber s k u v‖ =
      latticeModeWeight k ^ (s - 1) *
        complexEuclideanNorm (projectedSpectralConvolutionCoefficient k u v) := by
  unfold polynomialProjectedSpectralOutputFiber
  rw [norm_smul, Real.norm_of_nonneg
    (Real.rpow_nonneg (zero_le_one.trans (one_le_latticeModeWeight k)) (s - 1))]
  rfl

/-- The exact projected convolution has a finite order-`s - 1` moment whenever
both inputs have finite order-`s` moments. -/
theorem summable_projectedConvolutionPolynomialMoment
    (s : ℝ) (hs : 1 ≤ s) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    Summable fun k => latticeModeWeight k ^ (s - 1) *
      complexEuclideanNorm (projectedSpectralConvolutionCoefficient k u v) := by
  simpa only [← norm_polynomialProjectedSpectralOutputFiber_eq] using
    summable_norm_polynomialProjectedSpectralOutputFiber s hs u v hu hv

/-- Exact reindexing of the fiber majorants back to all ordered input pairs. -/
theorem tsum_polynomialMomentFiberMajorant_eq_pair
    (s : ℝ) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    (∑' k, polynomialMomentFiberMajorant s u v k) =
      ∑' ij : LatticeMode × LatticeMode,
        polynomialMomentPairMajorant s u v ij := by
  have hpair := summable_polynomialMomentPairMajorant s u v hu hv
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      polynomialMomentPairMajorant s u v x.2.1) :=
    latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
  change (∑' k : LatticeMode,
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        polynomialMomentPairMajorant s u v ij.1) = _
  rw [← hsigma.tsum_sigma]
  exact latticeOutputFiberSigmaEquiv.tsum_eq _

/-- The full-pair polynomial majorant factors exactly into its two moments. -/
theorem tsum_polynomialMomentPairMajorant_eq_product
    (s : ℝ) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    (∑' ij : LatticeMode × LatticeMode,
      polynomialMomentPairMajorant s u v ij) =
      polynomialMoment s u * polynomialMoment s v := by
  have hpair := summable_polynomialMomentPairMajorant s u v hu hv
  exact (hu.tsum_mul_tsum hv hpair).symm

/-- Arbitrary-real-order polynomial moment estimate for the actual projected
countable convolution.  In particular, it applies at every integer and
half-integer order `s ≥ 1`. -/
theorem tsum_norm_polynomialProjectedSpectralOutputFiber_le
    (s : ℝ) (hs : 1 ≤ s) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    (∑' k, ‖polynomialProjectedSpectralOutputFiber s k u v‖) ≤
      polynomialMoment s u * polynomialMoment s v := by
  calc
    (∑' k, ‖polynomialProjectedSpectralOutputFiber s k u v‖) ≤
        ∑' k, polynomialMomentFiberMajorant s u v k :=
      Summable.tsum_le_tsum
        (fun k => norm_polynomialProjectedSpectralOutputFiber_le
          s hs k u v hu hv)
        (summable_norm_polynomialProjectedSpectralOutputFiber s hs u v hu hv)
        (summable_polynomialMomentFiberMajorant s u v hu hv)
    _ = ∑' ij : LatticeMode × LatticeMode,
        polynomialMomentPairMajorant s u v ij :=
      tsum_polynomialMomentFiberMajorant_eq_pair s u v hu hv
    _ = polynomialMoment s u * polynomialMoment s v :=
      tsum_polynomialMomentPairMajorant_eq_product s u v hu hv

/-- Direct `S_s × S_s → S_(s-1)` estimate for the exact projected countable
convolution. -/
theorem projectedConvolutionPolynomialMoment_sub_one_le
    (s : ℝ) (hs : 1 ≤ s) (u v : WeightedLatticeBanach)
    (hu : LatticePolynomialMoment s u) (hv : LatticePolynomialMoment s v) :
    projectedConvolutionPolynomialMoment (s - 1) u v ≤
      polynomialMoment s u * polynomialMoment s v := by
  unfold projectedConvolutionPolynomialMoment
  simpa only [← norm_polynomialProjectedSpectralOutputFiber_eq] using
    tsum_norm_polynomialProjectedSpectralOutputFiber_le s hs u v hu hv

/-- Consumer form for the exact projected forcing used by the repository's
mode ODE.  This is the same literal convolution estimate, specialized to one
time slice of an evolving path. -/
theorem tsum_projectedModeForcing_polynomial_sub_one_le
    (s : ℝ) (hs : 1 ≤ s) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hA : LatticePolynomialMoment s (A t)) :
    (∑' k, latticeModeWeight k ^ (s - 1) *
      complexEuclideanNorm (projectedModeForcing A k t)) ≤
      polynomialMoment s (A t) ^ 2 := by
  have h := projectedConvolutionPolynomialMoment_sub_one_le
    s hs (A t) (A t) hA hA
  simpa [projectedConvolutionPolynomialMoment,
    projectedSpectralConvolutionCoefficient, projectedModeForcing, pow_two] using h

#check tsum_polynomialProjectedFiberTerm_eq
#check summable_projectedConvolutionPolynomialMoment
#check projectedConvolutionPolynomialMoment_sub_one_le
#check tsum_projectedModeForcing_polynomial_sub_one_le
#print axioms tsum_polynomialProjectedFiberTerm_eq
#print axioms tsum_norm_polynomialProjectedSpectralOutputFiber_le
#print axioms projectedConvolutionPolynomialMoment_sub_one_le
#print axioms tsum_projectedModeForcing_polynomial_sub_one_le

end Navier.Analysis.CriticalMildPolynomialMomentConvolution
