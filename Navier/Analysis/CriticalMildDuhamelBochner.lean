import Navier.Analysis.CriticalMildHeatCoefficientLift
import Navier.Analysis.CriticalMildWeightedBanach
import Navier.Analysis.CriticalMildDuhamel
import Navier.Analysis.CriticalMildGlobalWeightedOutput
import Navier.Analysis.CriticalMildHeatBochner

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

open MeasureTheory Set Topology
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildHeatCoefficientLift
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildHeatTimeKernel

/-- The physical Fourier divergence-free constraint on a completed weighted
carrier: every decoded mode is Hermitian-transverse to its own frequency. -/
def LatticeDivergenceFree (u : WeightedLatticeBanach) : Prop :=
  ∀ m : LatticeMode, inner ℂ (complexFrequency (latticeFrequency m))
    (complexEuclideanPoint (weightedLatticeCoefficient u m)) = 0

/-- The physical divergence-free subspace is closed under subtraction. -/
theorem LatticeDivergenceFree.sub {u v : WeightedLatticeBanach}
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v) :
    LatticeDivergenceFree (u - v) := by
  intro m
  have hcoefficient :
      weightedLatticeCoefficient (u - v) m =
        weightedLatticeCoefficient u m - weightedLatticeCoefficient v m := by
    simp [weightedLatticeCoefficient, sub_eq_add_neg, smul_add]
  rw [hcoefficient]
  have hpoint (a b : ComplexSpace) :
      complexEuclideanPoint (a - b) =
        complexEuclideanPoint a - complexEuclideanPoint b := by
    ext j
    rfl
  rw [hpoint, inner_sub_right, hu m, hv m, sub_self]

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

/-- The finite-dimensional encoding map from the Euclidean carrier to the
coefficient carrier, made continuous explicitly for use with `tsum`. -/
def complexEuclideanEncodeCLM : ComplexE3 →L[ℂ] ComplexSpace :=
  ContinuousLinearMap.mk (WithLp.linearEquiv 2 ℂ ComplexSpace).toLinearMap
    (LinearMap.continuous_of_finiteDimensional _)

/-- The finite-dimensional decoding map back to the Euclidean carrier. -/
def complexEuclideanDecodeCLM : ComplexSpace →L[ℂ] ComplexE3 :=
  ContinuousLinearMap.mk (WithLp.linearEquiv 2 ℂ ComplexSpace).symm.toLinearMap
    (LinearMap.continuous_of_finiteDimensional _)

/-- The heat--Leray multiplier, promoted to a continuous linear map on its
finite-dimensional coefficient carrier. -/
def complexFrequencyHeatLerayCLM (ν τ : ℝ) (k : LatticeMode) :
    ComplexSpace →L[ℂ] ComplexSpace :=
  ContinuousLinearMap.mk (complexFrequencyHeatLeray ν τ (latticeFrequency k))
    (LinearMap.continuous_of_finiteDimensional _)

/-- The exact output-mode operation: encode, apply the output-frequency
heat--Leray multiplier, decode, and attach the output lattice weight. -/
def outputHeatCarrierCLM (ν τ : ℝ) (k : LatticeMode) : ComplexE3 →L[ℂ] ComplexE3 :=
  (latticeModeWeight k : ℂ) •
    (complexEuclideanDecodeCLM.comp
      ((complexFrequencyHeatLerayCLM ν τ k).comp complexEuclideanEncodeCLM))

theorem outputHeatCarrierCLM_apply (ν τ : ℝ) (k : LatticeMode) (z : ComplexE3) :
    outputHeatCarrierCLM ν τ k z =
      latticeModeWeight k • complexEuclideanPoint
        (complexFrequencyHeatLeray ν τ (latticeFrequency k) (WithLp.ofLp z)) := by
  simp [outputHeatCarrierCLM, complexEuclideanDecodeCLM,
    complexFrequencyHeatLerayCLM, complexEuclideanEncodeCLM,
    complexEuclideanPoint]

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

/-- On a constrained pair, the output carrier map is exactly the displayed
heat-regularized triad summand. -/
theorem outputHeatCarrierCLM_apply_latticeSpectralTerm
    (ν τ : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    outputHeatCarrierCLM ν τ k
        (latticeSpectralTerm k (weightedLatticeCoefficient u)
          (weightedLatticeCoefficient v) ij.1) =
      constrainedHeatRegularizedFiberTerm ν τ k u v ij := by
  rw [outputHeatCarrierCLM_apply]
  have hmem := ij.2
  change latticeOutputMode ij.1 = k at hmem
  have hij : ij.1.1 + ij.1.2 = k := by
    simpa [latticeOutputMode] using hmem
  rw [latticeSpectralTerm, if_pos hij]
  rfl

/-- The continuous output carrier map commutes with the already convergent
literal convolution series. -/
theorem outputHeatCarrierCLM_map_tsum (ν τ : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) :
    outputHeatCarrierCLM ν τ k (weightedLatticeSpectralConvolution k u v) =
      ∑' ij : LatticeMode × LatticeMode,
        outputHeatCarrierCLM ν τ k
          (latticeSpectralTerm k (weightedLatticeCoefficient u)
            (weightedLatticeCoefficient v) ij) := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  exact ContinuousLinearMap.map_tsum _
    (summable_latticeSpectralTerm_of_weightedL1 k
      (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
      (latticeConvolutionWeightedL1_of_weightedL1 k
        (weightedLatticeCoefficient u) (weightedLatticeCoefficient v)
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient v)))

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

/-- Applying the carrier map after the literal convolution is definitionally
the pre-existing post-convolution heat output fiber. -/
theorem outputHeatCarrierCLM_weightedLatticeSpectralConvolution
    (ν τ : ℝ) (k : LatticeMode) (u v : WeightedLatticeBanach) :
    outputHeatCarrierCLM ν τ k (weightedLatticeSpectralConvolution k u v) =
      heatRegularizedSpectralOutputFiber ν τ k u v := by
  rw [outputHeatCarrierCLM_apply]
  rfl

/-- The absolutely summable constrained heat fiber is exactly the existing
post-convolution heat output: the carrier map commutes with the literal
convolution `tsum`, and all off-fiber terms vanish. -/
theorem constrainedHeatRegularizedFiber_eq_heatRegularizedSpectralOutputFiber
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    constrainedHeatRegularizedFiber ν τ hν hτ u v hu k =
      heatRegularizedSpectralOutputFiber ν τ k u v := by
  let f : LatticeMode × LatticeMode → ComplexE3 := fun ij =>
    outputHeatCarrierCLM ν τ k
      (latticeSpectralTerm k (weightedLatticeCoefficient u)
        (weightedLatticeCoefficient v) ij)
  calc
    constrainedHeatRegularizedFiber ν τ hν hτ u v hu k =
        ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode), f ij.1 := by
      apply tsum_congr
      intro ij
      exact (outputHeatCarrierCLM_apply_latticeSpectralTerm ν τ k u v ij).symm
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
    _ = outputHeatCarrierCLM ν τ k (weightedLatticeSpectralConvolution k u v) :=
      (outputHeatCarrierCLM_map_tsum ν τ k u v).symm
    _ = heatRegularizedSpectralOutputFiber ν τ k u v :=
      outputHeatCarrierCLM_weightedLatticeSpectralConvolution ν τ k u v

/-- The scalar majorant of one exact output heat fiber. -/
def outputHeatFiberMajorant (ν τ : ℝ) (u v : WeightedLatticeBanach)
    (k : LatticeMode) : ℝ :=
  ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
    outputHeatPairMajorant ν τ u v ij.1

/-- Reindexing through exact output fibers preserves summability of the
full-pair heat majorant. -/
theorem summable_outputHeatFiberMajorant (ν τ : ℝ)
    (u v : WeightedLatticeBanach) :
    Summable (outputHeatFiberMajorant ν τ u v) := by
  have hpair := summable_outputHeatPairMajorant ν τ u v
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      outputHeatPairMajorant ν τ u v x.2.1) := by
    exact latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
  exact hsigma.sigma

/-- The exact completed heat fiber is bounded by its reindexed scalar
majorant. -/
theorem norm_constrainedHeatRegularizedFiber_le_outputHeatFiberMajorant
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ ≤
      outputHeatFiberMajorant ν τ u v k := by
  exact tsum_of_norm_bounded
    ((summable_outputHeatPairMajorant ν τ u v).subtype _).hasSum
    (norm_constrainedHeatRegularizedFiberTerm_le ν τ hν hτ u v hu k)

/-- The norms of the actual heat fibers are summable over all output modes. -/
theorem summable_norm_constrainedHeatRegularizedFiber
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Summable fun k => ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ := by
  exact (summable_outputHeatFiberMajorant ν τ u v).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun k => norm_constrainedHeatRegularizedFiber_le_outputHeatFiberMajorant
      ν τ hν hτ u v hu k)

/-- The completed same-weight heat-regularized nonlinear output carrier. -/
def heatRegularizedSpectralOutput (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    WeightedLatticeBanach :=
  ⟨fun k => constrainedHeatRegularizedFiber ν τ hν hτ u v hu k,
    memℓp_gen (by
      simpa using summable_norm_constrainedHeatRegularizedFiber ν τ hν hτ u v hu)⟩

/-- Every coordinate of the completed carrier is the existing actual
output-frequency heat-regularized convolution fiber. -/
theorem heatRegularizedSpectralOutput_apply (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    heatRegularizedSpectralOutput ν τ hν hτ u v hu k =
      heatRegularizedSpectralOutputFiber ν τ k u v := by
  exact constrainedHeatRegularizedFiber_eq_heatRegularizedSpectralOutputFiber
    ν τ hν hτ u v hu k

/-- The completed output-heat carrier is additive in the transported input.
This is an exact identity of the actual global `ℓ¹` output, not merely a
majorant estimate. -/
theorem heatRegularizedSpectralOutput_add_right (ν τ : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ)
    (u v w : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    heatRegularizedSpectralOutput ν τ hν hτ u (v + w) hu =
      heatRegularizedSpectralOutput ν τ hν hτ u v hu +
        heatRegularizedSpectralOutput ν τ hν hτ u w hu := by
  apply Subtype.ext
  funext k
  rw [heatRegularizedSpectralOutput_apply,
    show (heatRegularizedSpectralOutput ν τ hν hτ u v hu +
        heatRegularizedSpectralOutput ν τ hν hτ u w hu) k =
      heatRegularizedSpectralOutput ν τ hν hτ u v hu k +
        heatRegularizedSpectralOutput ν τ hν hτ u w hu k by rfl,
    heatRegularizedSpectralOutput_apply, heatRegularizedSpectralOutput_apply]
  unfold heatRegularizedSpectralOutputFiber spectralOutputCoefficient
  rw [weightedLatticeSpectralConvolution_add_right]
  simp
  have hpoint (a b : ComplexSpace) :
      complexEuclideanPoint (a + b) =
        complexEuclideanPoint a + complexEuclideanPoint b := by
    ext i
    rfl
  rw [hpoint, smul_add]

/-- The completed output-heat carrier is also additive in the advecting
divergence-free input. -/
theorem heatRegularizedSpectralOutput_add_left (ν τ : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ)
    (u v w : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v)
    (huv : LatticeDivergenceFree (u + v)) :
    heatRegularizedSpectralOutput ν τ hν hτ (u + v) w huv =
      heatRegularizedSpectralOutput ν τ hν hτ u w hu +
        heatRegularizedSpectralOutput ν τ hν hτ v w hv := by
  apply Subtype.ext
  funext k
  rw [heatRegularizedSpectralOutput_apply,
    show (heatRegularizedSpectralOutput ν τ hν hτ u w hu +
        heatRegularizedSpectralOutput ν τ hν hτ v w hv) k =
      heatRegularizedSpectralOutput ν τ hν hτ u w hu k +
        heatRegularizedSpectralOutput ν τ hν hτ v w hv k by rfl,
    heatRegularizedSpectralOutput_apply, heatRegularizedSpectralOutput_apply]
  unfold heatRegularizedSpectralOutputFiber spectralOutputCoefficient
  rw [weightedLatticeSpectralConvolution_add_left]
  simp
  have hpoint (a b : ComplexSpace) :
      complexEuclideanPoint (a + b) =
        complexEuclideanPoint a + complexEuclideanPoint b := by
    ext i
    rfl
  rw [hpoint, smul_add]

/-- Summing the fiber majorants is exactly summing the original full-pair
majorant. -/
theorem tsum_outputHeatFiberMajorant_eq_pair (ν τ : ℝ)
    (u v : WeightedLatticeBanach) :
    (∑' k : LatticeMode, outputHeatFiberMajorant ν τ u v k) =
      ∑' ij : LatticeMode × LatticeMode, outputHeatPairMajorant ν τ u v ij := by
  have hpair := summable_outputHeatPairMajorant ν τ u v
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      outputHeatPairMajorant ν τ u v x.2.1) := by
    exact latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
  rw [show outputHeatFiberMajorant ν τ u v = fun k =>
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        outputHeatPairMajorant ν τ u v ij.1 by rfl]
  rw [← hsigma.tsum_sigma]
  exact latticeOutputFiberSigmaEquiv.tsum_eq _

/-- The full-pair heat majorant has the exact inverse-square-root product
budget supplied by the two completed one-weight input carriers. -/
theorem tsum_outputHeatPairMajorant_eq (ν τ : ℝ)
    (u v : WeightedLatticeBanach) :
    (∑' ij : LatticeMode × LatticeMode, outputHeatPairMajorant ν τ u v ij) =
      (Real.sqrt (ν * τ))⁻¹ * ‖u‖ * ‖v‖ := by
  let a : LatticeMode → ℝ := latticeWeightedAmplitude (weightedLatticeCoefficient u)
  let b : LatticeMode → ℝ := latticeWeightedAmplitude (weightedLatticeCoefficient v)
  have ha : Summable a := latticeWeightedL1_coefficient u
  have hb : Summable b := latticeWeightedL1_coefficient v
  have ha0 : ∀ m, 0 ≤ a m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hb0 : ∀ m, 0 ≤ b m := by
    intro m
    exact mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight m)) (norm_nonneg _)
  have hab : Summable (fun ij : LatticeMode × LatticeMode => a ij.1 * b ij.2) :=
    ha.mul_of_nonneg hb ha0 hb0
  rw [show outputHeatPairMajorant ν τ u v = fun ij =>
      (Real.sqrt (ν * τ))⁻¹ * (a ij.1 * b ij.2) by
    funext ij
    unfold outputHeatPairMajorant a b latticeWeightedAmplitude
    ring]
  rw [tsum_mul_left, ← ha.tsum_mul_tsum hb hab]
  rw [tsum_latticeWeightedAmplitude_coefficient,
    tsum_latticeWeightedAmplitude_coefficient]
  ring

/-- The `ℓ¹` norm of the completed heat output is the sum of its exact
output-coordinate norms. -/
theorem norm_heatRegularizedSpectralOutput_eq_tsum (ν τ : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu‖ =
      ∑' k, ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  change (∑' k : LatticeMode,
    ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ ^ (1 : ℝ)) ^
      (1 / (1 : ℝ)) = _
  rw [show (1 : ℝ) / 1 = 1 by norm_num, Real.rpow_one]
  apply congrArg tsum
  funext k
  exact Real.rpow_one _

/-- Global same-weight inverse-square-root estimate for the actual completed
output-frequency heat-regularized nonlinear carrier. -/
theorem norm_heatRegularizedSpectralOutput_le (ν τ : ℝ)
    (hν : 0 < ν) (hτ : 0 < τ) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu‖ ≤
      (Real.sqrt (ν * τ))⁻¹ * ‖u‖ * ‖v‖ := by
  rw [norm_heatRegularizedSpectralOutput_eq_tsum]
  calc
    (∑' k, ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖) ≤
        ∑' k, outputHeatFiberMajorant ν τ u v k := by
      exact Summable.tsum_le_tsum
        (fun k => norm_constrainedHeatRegularizedFiber_le_outputHeatFiberMajorant
          ν τ hν hτ u v hu k)
        (summable_norm_constrainedHeatRegularizedFiber ν τ hν hτ u v hu)
        (summable_outputHeatFiberMajorant ν τ u v)
    _ = ∑' ij : LatticeMode × LatticeMode, outputHeatPairMajorant ν τ u v ij :=
      tsum_outputHeatFiberMajorant_eq_pair ν τ u v
    _ = (Real.sqrt (ν * τ))⁻¹ * ‖u‖ * ‖v‖ :=
      tsum_outputHeatPairMajorant_eq ν τ u v

/-- Difference majorant for the actual output-frequency heat multiplier at
two positive lags.  This is the reusable shared-interval bound for moving
Duhamel observation times; no continuity is assumed. -/
theorem norm_heatRegularizedSpectralOutput_sub_le
    (ν τ σ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (hσ : 0 < σ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu -
        heatRegularizedSpectralOutput ν σ hν hσ u v hu‖ ≤
      ((Real.sqrt (ν * τ))⁻¹ + (Real.sqrt (ν * σ))⁻¹) * ‖u‖ * ‖v‖ := by
  calc
    ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu -
        heatRegularizedSpectralOutput ν σ hν hσ u v hu‖ ≤
        ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu‖ +
          ‖heatRegularizedSpectralOutput ν σ hν hσ u v hu‖ :=
      norm_sub_le _ _
    _ ≤ (Real.sqrt (ν * τ))⁻¹ * ‖u‖ * ‖v‖ +
        (Real.sqrt (ν * σ))⁻¹ * ‖u‖ * ‖v‖ :=
      add_le_add
        (norm_heatRegularizedSpectralOutput_le ν τ hν hτ u v hu)
        (norm_heatRegularizedSpectralOutput_le ν σ hν hσ u v hu)
    _ = ((Real.sqrt (ν * τ))⁻¹ + (Real.sqrt (ν * σ))⁻¹) * ‖u‖ * ‖v‖ := by
      ring

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

/-- The actual nonlinear heat output, made total in its elapsed-time
argument by zero extension at nonpositive lag. -/
def positiveTimeHeatRegularizedSpectralOutput (ν : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    ℝ → WeightedLatticeBanach := fun τ =>
  if hτ : 0 < τ then heatRegularizedSpectralOutput ν τ hν hτ u v hu else 0

/-- Positive elapsed time selects the actual globally completed heat output. -/
theorem positiveTimeHeatRegularizedSpectralOutput_of_pos (ν : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    {τ : ℝ} (hτ : 0 < τ) :
    positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ =
      heatRegularizedSpectralOutput ν τ hν hτ u v hu := by
  simp [positiveTimeHeatRegularizedSpectralOutput, hτ]

/-- The zero-extended positive-time nonlinear integrand remains exactly
additive in its transported input. -/
theorem positiveTimeHeatRegularizedSpectralOutput_add_right
    (ν : ℝ) (hν : 0 < ν)
    (u v w : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    positiveTimeHeatRegularizedSpectralOutput ν hν u (v + w) hu =
      positiveTimeHeatRegularizedSpectralOutput ν hν u v hu +
        positiveTimeHeatRegularizedSpectralOutput ν hν u w hu := by
  funext τ
  by_cases hτ : 0 < τ
  · simp only [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν _ _ hu hτ,
      Pi.add_apply]
    exact heatRegularizedSpectralOutput_add_right ν τ hν hτ u v w hu
  · simp [positiveTimeHeatRegularizedSpectralOutput, hτ]

/-- The zero-extended positive-time integrand is additive in its advecting
divergence-free input. -/
theorem positiveTimeHeatRegularizedSpectralOutput_add_left
    (ν : ℝ) (hν : 0 < ν)
    (u v w : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v)
    (huv : LatticeDivergenceFree (u + v)) :
    positiveTimeHeatRegularizedSpectralOutput ν hν (u + v) w huv =
      positiveTimeHeatRegularizedSpectralOutput ν hν u w hu +
        positiveTimeHeatRegularizedSpectralOutput ν hν v w hv := by
  funext τ
  by_cases hτ : 0 < τ
  · simp only [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν _ _ _ hτ,
      Pi.add_apply]
    exact heatRegularizedSpectralOutput_add_left ν τ hν hτ u v w hu hv huv
  · simp [positiveTimeHeatRegularizedSpectralOutput, hτ]

/-- The positive-time output heat gain is the viscosity-scaled inverse square
root time singularity used by the Bochner budget. -/
theorem outputHeatGain_eq_inverseSqrtTime (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    (Real.sqrt (ν * τ))⁻¹ = (Real.sqrt ν)⁻¹ * inverseSqrtTime τ := by
  have h := heatTimeMajorant_eq ν τ hν hτ
  unfold heatTimeMajorant at h
  linarith

/-- The explicit scalar majorant for the total nonlinear Duhamel integrand. -/
def duhamelHeatTimeMajorant (ν : ℝ) (u v : WeightedLatticeBanach) : ℝ → ℝ :=
  fun τ => (Real.sqrt ν)⁻¹ * inverseSqrtTime τ * ‖u‖ * ‖v‖

/-- On positive lag, the actual global output is controlled by the exact
inverse-square-root majorant. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutput_le (ν : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    {τ : ℝ} (hτ : 0 < τ) :
    ‖positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ‖ ≤
      duhamelHeatTimeMajorant ν u v τ := by
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν u v hu hτ]
  calc
    ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu‖ ≤
        (Real.sqrt (ν * τ))⁻¹ * ‖u‖ * ‖v‖ :=
      norm_heatRegularizedSpectralOutput_le ν τ hν hτ u v hu
    _ = duhamelHeatTimeMajorant ν u v τ := by
      unfold duhamelHeatTimeMajorant
      rw [outputHeatGain_eq_inverseSqrtTime ν τ hν hτ]

/-- Two-input Lipschitz estimate for the actual positive-lag nonlinear heat
output.  This is the pointwise contraction leaf consumed by the evolving-path
Bochner integral. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutput_sub_le
    (ν : ℝ) (hν : 0 < ν)
    (u u' v v' : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hu' : LatticeDivergenceFree u')
    {τ : ℝ} (hτ : 0 < τ) :
    ‖positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ -
        positiveTimeHeatRegularizedSpectralOutput ν hν u' v' hu' τ‖ ≤
      (Real.sqrt ν)⁻¹ * inverseSqrtTime τ *
        (‖u‖ * ‖v - v'‖ + ‖u - u'‖ * ‖v'‖) := by
  have hright :
      positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ -
          positiveTimeHeatRegularizedSpectralOutput ν hν u v' hu τ =
        positiveTimeHeatRegularizedSpectralOutput ν hν u (v - v') hu τ := by
    have hadd := congrFun
      (positiveTimeHeatRegularizedSpectralOutput_add_right
        ν hν u (v - v') v' hu) τ
    rw [sub_add_cancel] at hadd
    have hadd' :
        positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ =
          positiveTimeHeatRegularizedSpectralOutput ν hν u (v - v') hu τ +
            positiveTimeHeatRegularizedSpectralOutput ν hν u v' hu τ := by
      simpa only [Pi.add_apply] using hadd
    rw [hadd']
    abel
  have hleft :
      positiveTimeHeatRegularizedSpectralOutput ν hν u v' hu τ -
          positiveTimeHeatRegularizedSpectralOutput ν hν u' v' hu' τ =
        positiveTimeHeatRegularizedSpectralOutput ν hν
          (u - u') v' (hu.sub hu') τ := by
    have hsum : LatticeDivergenceFree (u - u' + u') := by
      simpa only [sub_add_cancel] using hu
    have hadd := congrFun
      (positiveTimeHeatRegularizedSpectralOutput_add_left
        ν hν (u - u') u' v' (hu.sub hu') hu' hsum) τ
    have hproof :
        positiveTimeHeatRegularizedSpectralOutput ν hν
            (u - u' + u') v' hsum τ =
          positiveTimeHeatRegularizedSpectralOutput ν hν u v' hu τ := by
      congr 2
      exact sub_add_cancel u u'
    have hadd' :
        positiveTimeHeatRegularizedSpectralOutput ν hν u v' hu τ =
          positiveTimeHeatRegularizedSpectralOutput ν hν
              (u - u') v' (hu.sub hu') τ +
            positiveTimeHeatRegularizedSpectralOutput ν hν u' v' hu' τ := by
      rw [← hproof]
      simpa only [Pi.add_apply] using hadd
    rw [hadd']
    abel
  have hdecomp :
      positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ -
          positiveTimeHeatRegularizedSpectralOutput ν hν u' v' hu' τ =
        (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ -
          positiveTimeHeatRegularizedSpectralOutput ν hν u v' hu τ) +
        (positiveTimeHeatRegularizedSpectralOutput ν hν u v' hu τ -
          positiveTimeHeatRegularizedSpectralOutput ν hν u' v' hu' τ) := by
    abel
  rw [hdecomp, hright, hleft]
  calc
    ‖positiveTimeHeatRegularizedSpectralOutput ν hν u (v - v') hu τ +
        positiveTimeHeatRegularizedSpectralOutput ν hν
          (u - u') v' (hu.sub hu') τ‖ ≤
      ‖positiveTimeHeatRegularizedSpectralOutput ν hν u (v - v') hu τ‖ +
        ‖positiveTimeHeatRegularizedSpectralOutput ν hν
          (u - u') v' (hu.sub hu') τ‖ := norm_add_le _ _
    _ ≤ duhamelHeatTimeMajorant ν u (v - v') τ +
        duhamelHeatTimeMajorant ν (u - u') v' τ :=
      add_le_add
        (norm_positiveTimeHeatRegularizedSpectralOutput_le
          ν hν u (v - v') hu hτ)
        (norm_positiveTimeHeatRegularizedSpectralOutput_le
          ν hν (u - u') v' (hu.sub hu') hτ)
    _ = (Real.sqrt ν)⁻¹ * inverseSqrtTime τ *
        (‖u‖ * ‖v - v'‖ + ‖u - u'‖ * ‖v'‖) := by
      unfold duhamelHeatTimeMajorant
      ring

/-- The nonlinear Duhamel scalar majorant is interval-integrable on every
nonnegative finite horizon. -/
theorem intervalIntegrable_duhamelHeatTimeMajorant (ν T : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach) :
    IntervalIntegrable (duhamelHeatTimeMajorant ν u v) volume 0 T := by
  unfold duhamelHeatTimeMajorant
  exact (((inverseSqrtTime_intervalIntegrable T).const_mul _).mul_const _).mul_const _

/-- Exact finite-horizon scalar budget for the nonlinear heat integrand. -/
theorem integral_duhamelHeatTimeMajorant (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : WeightedLatticeBanach) :
    (∫ τ in (0 : ℝ)..T, duhamelHeatTimeMajorant ν u v τ) =
      (2 * Real.sqrt T / Real.sqrt ν) * ‖u‖ * ‖v‖ := by
  unfold duhamelHeatTimeMajorant
  rw [show (fun τ : ℝ => (Real.sqrt ν)⁻¹ * inverseSqrtTime τ * ‖u‖ * ‖v‖) =
      fun τ => (Real.sqrt ν)⁻¹ * (inverseSqrtTime τ * (‖u‖ * ‖v‖)) by
        funext τ; ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const,
    integral_inverseSqrtTime_zero T hT]
  field_simp [ne_of_gt hν]

/-- Every output lattice coordinate of the post-convolution heat fiber is
continuous in its elapsed-time parameter. -/
theorem continuous_heatRegularizedSpectralOutputFiber_apply (ν : ℝ)
    (k : LatticeMode) (u v : WeightedLatticeBanach) :
    Continuous fun τ : ℝ => heatRegularizedSpectralOutputFiber ν τ k u v := by
  unfold heatRegularizedSpectralOutputFiber
  show Continuous
      (latticeModeWeight k •
        fun τ : ℝ => complexEuclideanPoint
          ((complexFrequencyHeatLeray ν τ (latticeFrequency k))
            (spectralOutputCoefficient k u v)))
  apply Continuous.const_smul
  apply CriticalMildHeatBochner.continuous_complexEuclideanPoint.comp
  rw [show (fun τ : ℝ => complexFrequencyHeatLeray ν τ (latticeFrequency k)
      (spectralOutputCoefficient k u v)) =
      fun τ => (complexHeatDecay ν τ (latticeFrequency k) : ℂ) •
        complexLeray (latticeFrequency k) (spectralOutputCoefficient k u v) by
    funext τ
    exact complexFrequencyHeatLeray_apply ν τ (latticeFrequency k)
      (spectralOutputCoefficient k u v)]
  unfold complexHeatDecay heatDecay
  fun_prop

/-- Each coordinate of the zero-extended actual nonlinear integrand is
strongly measurable. -/
theorem stronglyMeasurable_positiveTimeHeatRegularizedSpectralOutput_apply
    (ν : ℝ) (hν : 0 < ν) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (k : LatticeMode) :
    StronglyMeasurable (fun τ : ℝ =>
      positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ k) := by
  have hpiece : (fun τ : ℝ =>
      positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ k) =
      Set.piecewise (Ioi 0) (fun τ => heatRegularizedSpectralOutputFiber ν τ k u v)
        (fun _ => 0) := by
    funext τ
    by_cases hτ : 0 < τ
    · simp [hτ, positiveTimeHeatRegularizedSpectralOutput_of_pos,
        heatRegularizedSpectralOutput_apply]
    · simp [hτ, positiveTimeHeatRegularizedSpectralOutput]
  rw [hpiece]
  exact ((continuous_heatRegularizedSpectralOutputFiber_apply ν k u v).stronglyMeasurable).piecewise
    measurableSet_Ioi stronglyMeasurable_const

/-- Coordinate insertion into the one-weight completed output carrier. -/
def duhamelOutputSingleLinear (k : LatticeMode) : ComplexE3 →ₗ[ℂ] WeightedLatticeBanach :=
  lp.singleContinuousLinearMap ℂ (fun _ : LatticeMode => ComplexE3) 1 k

theorem continuous_duhamelOutputSingleLinear (k : LatticeMode) :
    Continuous (duhamelOutputSingleLinear k) :=
  LinearMap.continuous_of_finiteDimensional _

/-- Enumerated finite-coordinate approximants to the completed nonlinear
Duhamel integrand. -/
def positiveTimeHeatRegularizedSpectralOutputNatTruncation (n : ℕ) (ν : ℝ)
    (hν : 0 < ν) (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    ℝ → WeightedLatticeBanach := fun τ =>
  ∑ j ∈ Finset.range n,
    duhamelOutputSingleLinear (CriticalMildHeatBochner.latticeModeEquivNat.symm j)
      (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ
        (CriticalMildHeatBochner.latticeModeEquivNat.symm j))

theorem stronglyMeasurable_positiveTimeHeatRegularizedSpectralOutputNatTruncation
    (n : ℕ) (ν : ℝ) (hν : 0 < ν) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    StronglyMeasurable (positiveTimeHeatRegularizedSpectralOutputNatTruncation n ν hν u v hu) := by
  unfold positiveTimeHeatRegularizedSpectralOutputNatTruncation
  let f : ℕ → ℝ → WeightedLatticeBanach := fun j τ =>
    duhamelOutputSingleLinear (CriticalMildHeatBochner.latticeModeEquivNat.symm j)
      (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ
        (CriticalMildHeatBochner.latticeModeEquivNat.symm j))
  change StronglyMeasurable fun τ => ∑ j ∈ Finset.range n, f j τ
  have hsum : StronglyMeasurable (∑ j ∈ Finset.range n, f j) :=
    Finset.stronglyMeasurable_sum _ (fun j hj => by
      apply (continuous_duhamelOutputSingleLinear _).comp_stronglyMeasurable
      exact stronglyMeasurable_positiveTimeHeatRegularizedSpectralOutput_apply ν hν u v hu _)
  have heq : (fun τ => ∑ j ∈ Finset.range n, f j τ) = ∑ j ∈ Finset.range n, f j := by
    funext τ; simp
  rw [heq]
  exact hsum

/-- The finite-coordinate approximants converge pointwise in the completed
`lp` norm to the actual nonlinear output integrand. -/
theorem tendsto_positiveTimeHeatRegularizedSpectralOutputNatTruncation
    (ν : ℝ) (hν : 0 < ν) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (τ : ℝ) :
    Filter.Tendsto (fun n =>
      positiveTimeHeatRegularizedSpectralOutputNatTruncation n ν hν u v hu τ)
      Filter.atTop (𝓝 (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ)) := by
  let f := positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ
  have hsingle := lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
    (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤) f
  have hsum : Summable (fun n : ℕ => lp.single (E := fun _ : LatticeMode => ComplexE3)
      1 (CriticalMildHeatBochner.latticeModeEquivNat.symm n)
      (f (CriticalMildHeatBochner.latticeModeEquivNat.symm n))) := by
    exact CriticalMildHeatBochner.latticeModeEquivNat.symm.summable_iff.mpr hsingle.summable
  have hsum_eq : (∑' n : ℕ, lp.single (E := fun _ : LatticeMode => ComplexE3)
      1 (CriticalMildHeatBochner.latticeModeEquivNat.symm n)
      (f (CriticalMildHeatBochner.latticeModeEquivNat.symm n))) = f := by
    calc
      (∑' n : ℕ, lp.single (E := fun _ : LatticeMode => ComplexE3)
          1 (CriticalMildHeatBochner.latticeModeEquivNat.symm n)
          (f (CriticalMildHeatBochner.latticeModeEquivNat.symm n))) =
          ∑' i : LatticeMode, lp.single (E := fun _ : LatticeMode => ComplexE3) 1 i (f i) :=
        CriticalMildHeatBochner.latticeModeEquivNat.symm.tsum_eq
          (fun i : LatticeMode => lp.single (E := fun _ : LatticeMode => ComplexE3) 1 i (f i))
      _ = f := hsingle.tsum_eq
  have hhas := hsum.hasSum_iff.mpr hsum_eq
  exact hhas.tendsto_sum_nat

/-- The zero-extended completed nonlinear Duhamel integrand is strongly
measurable. -/
theorem stronglyMeasurable_positiveTimeHeatRegularizedSpectralOutput
    (ν : ℝ) (hν : 0 < ν) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    StronglyMeasurable (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu) := by
  apply stronglyMeasurable_of_tendsto
    (f := fun n => positiveTimeHeatRegularizedSpectralOutputNatTruncation n ν hν u v hu)
    Filter.atTop
  · intro n
    exact stronglyMeasurable_positiveTimeHeatRegularizedSpectralOutputNatTruncation n ν hν u v hu
  · rw [tendsto_pi_nhds]
    intro τ
    exact tendsto_positiveTimeHeatRegularizedSpectralOutputNatTruncation ν hν u v hu τ

/-- The completed nonlinear Duhamel integrand is Bochner-integrable on every
nonnegative finite horizon. -/
theorem integrableOn_positiveTimeHeatRegularizedSpectralOutput
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    IntegrableOn (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu) (Ioc 0 T) volume := by
  have hmajorant := intervalIntegrable_duhamelHeatTimeMajorant ν T hν u v
  have hinterval : IntervalIntegrable
      (positiveTimeHeatRegularizedSpectralOutput ν hν u v hu) volume 0 T :=
    IntervalIntegrable.mono_fun' hmajorant
      (stronglyMeasurable_positiveTimeHeatRegularizedSpectralOutput ν hν u v hu).aestronglyMeasurable (by
        rw [uIoc_of_le hT]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
        exact norm_positiveTimeHeatRegularizedSpectralOutput_le ν hν u v hu hτ.1)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hinterval

/-- The actual Bochner Duhamel integral of the completed nonlinear heat
output on the elapsed-time interval `[0,T]`. -/
def positiveTimeHeatRegularizedSpectralOutputIntegral
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    WeightedLatticeBanach :=
  ∫ τ in Ioc 0 T, positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ

/-- Bochner integration preserves the exact right-input additivity of the
completed nonlinear heat output. -/
theorem positiveTimeHeatRegularizedSpectralOutputIntegral_add_right
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v w : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    positiveTimeHeatRegularizedSpectralOutputIntegral ν T hν hT u (v + w) hu =
      positiveTimeHeatRegularizedSpectralOutputIntegral ν T hν hT u v hu +
        positiveTimeHeatRegularizedSpectralOutputIntegral ν T hν hT u w hu := by
  unfold positiveTimeHeatRegularizedSpectralOutputIntegral
  rw [positiveTimeHeatRegularizedSpectralOutput_add_right]
  exact integral_add
    (integrableOn_positiveTimeHeatRegularizedSpectralOutput ν T hν hT u v hu)
    (integrableOn_positiveTimeHeatRegularizedSpectralOutput ν T hν hT u w hu)

/-- Bochner integration preserves exact additivity in the advecting
divergence-free input. -/
theorem positiveTimeHeatRegularizedSpectralOutputIntegral_add_left
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v w : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v)
    (huv : LatticeDivergenceFree (u + v)) :
    positiveTimeHeatRegularizedSpectralOutputIntegral ν T hν hT (u + v) w huv =
      positiveTimeHeatRegularizedSpectralOutputIntegral ν T hν hT u w hu +
        positiveTimeHeatRegularizedSpectralOutputIntegral ν T hν hT v w hv := by
  unfold positiveTimeHeatRegularizedSpectralOutputIntegral
  rw [positiveTimeHeatRegularizedSpectralOutput_add_left]
  exact integral_add
    (integrableOn_positiveTimeHeatRegularizedSpectralOutput ν T hν hT u w hu)
    (integrableOn_positiveTimeHeatRegularizedSpectralOutput ν T hν hT v w hv)

/-- The genuine nonlinear Duhamel Bochner integral has the exact
inverse-square-root finite-time budget. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutputIntegral_le
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    ‖positiveTimeHeatRegularizedSpectralOutputIntegral ν T hν hT u v hu‖ ≤
      (2 * Real.sqrt T / Real.sqrt ν) * ‖u‖ * ‖v‖ := by
  have hmajorant := intervalIntegrable_duhamelHeatTimeMajorant ν T hν u v
  have hactual := integrableOn_positiveTimeHeatRegularizedSpectralOutput ν T hν hT u v hu
  have hscalar := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hmajorant
  have hmono : (fun τ => ‖positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ‖) ≤ᵐ[
      volume.restrict (Ioc 0 T)] duhamelHeatTimeMajorant ν u v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
    exact norm_positiveTimeHeatRegularizedSpectralOutput_le ν hν u v hu hτ.1
  unfold positiveTimeHeatRegularizedSpectralOutputIntegral
  calc
    ‖∫ τ in Ioc 0 T, positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ‖ ≤
        ∫ τ in Ioc 0 T, ‖positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ τ in Ioc 0 T, duhamelHeatTimeMajorant ν u v τ :=
      integral_mono_ae hactual.norm hscalar hmono
    _ = ∫ τ in (0 : ℝ)..T, duhamelHeatTimeMajorant ν u v τ := by
      rw [← intervalIntegral.integral_of_le hT]
    _ = (2 * Real.sqrt T / Real.sqrt ν) * ‖u‖ * ‖v‖ :=
      integral_duhamelHeatTimeMajorant ν T hν hT u v

/-- The actual nonlinear Duhamel integral, indexed by nonnegative elapsed
time.  This is the carrier-valued path rung; no self-map or contraction is
asserted here. -/
def positiveTimeHeatRegularizedSpectralOutputPath
    (ν : ℝ) (hν : 0 < ν) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    NNReal → WeightedLatticeBanach := fun T =>
  positiveTimeHeatRegularizedSpectralOutputIntegral
    ν T hν T.property u v hu

/-- The path construction respects equality of the advecting carrier; its
divergence-free witness is proof-irrelevant. -/
theorem positiveTimeHeatRegularizedSpectralOutputPath_congr_left
    (ν : ℝ) (hν : 0 < ν) {u v : WeightedLatticeBanach}
    (w : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (hv : LatticeDivergenceFree v) (huv : u = v) :
    positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu =
      positiveTimeHeatRegularizedSpectralOutputPath ν hν v w hv := by
  subst v
  rfl

/-- The completed nonlinear Duhamel path is additive in its transported
input at every nonnegative elapsed time. -/
theorem positiveTimeHeatRegularizedSpectralOutputPath_add_right
    (ν : ℝ) (hν : 0 < ν)
    (u v w : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    positiveTimeHeatRegularizedSpectralOutputPath ν hν u (v + w) hu =
      positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu +
        positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu := by
  funext T
  exact positiveTimeHeatRegularizedSpectralOutputIntegral_add_right
    ν T hν T.property u v w hu

/-- The completed nonlinear Duhamel path is additive in its advecting
divergence-free input. -/
theorem positiveTimeHeatRegularizedSpectralOutputPath_add_left
    (ν : ℝ) (hν : 0 < ν)
    (u v w : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v)
    (huv : LatticeDivergenceFree (u + v)) :
    positiveTimeHeatRegularizedSpectralOutputPath ν hν (u + v) w huv =
      positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu +
        positiveTimeHeatRegularizedSpectralOutputPath ν hν v w hv := by
  funext T
  exact positiveTimeHeatRegularizedSpectralOutputIntegral_add_left
    ν T hν T.property u v w hu hv huv

@[simp] theorem positiveTimeHeatRegularizedSpectralOutputPath_zero
    (ν : ℝ) (hν : 0 < ν) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu 0 = 0 := by
  simp [positiveTimeHeatRegularizedSpectralOutputPath,
    positiveTimeHeatRegularizedSpectralOutputIntegral]

/-- Every point of the nonlinear Duhamel path obeys the exact
inverse-square-root finite-time budget. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutputPath_le
    (ν : ℝ) (hν : 0 < ν) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (T : NNReal) :
    ‖positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu T‖ ≤
      (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) * ‖u‖ * ‖v‖ := by
  exact norm_positiveTimeHeatRegularizedSpectralOutputIntegral_le
    ν T hν T.property u v hu

/-- The difference of two transported-input Duhamel paths is exactly the
Duhamel path of the input difference. -/
theorem positiveTimeHeatRegularizedSpectralOutputPath_sub_right
    (ν : ℝ) (hν : 0 < ν)
    (u v w : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu -
        positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu =
      positiveTimeHeatRegularizedSpectralOutputPath ν hν u (v - w) hu := by
  have hadd := positiveTimeHeatRegularizedSpectralOutputPath_add_right
    ν hν u (v - w) w hu
  rw [sub_add_cancel] at hadd
  rw [hadd]
  abel

/-- Genuine right-input Lipschitz estimate for the completed nonlinear
Duhamel path on every finite horizon. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_right_le
    (ν : ℝ) (hν : 0 < ν)
    (u v w : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (T : NNReal) :
    ‖positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu T -
        positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu T‖ ≤
      (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) * ‖u‖ * ‖v - w‖ := by
  have hsub := congrFun
    (positiveTimeHeatRegularizedSpectralOutputPath_sub_right ν hν u v w hu) T
  change ‖(positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu -
      positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu) T‖ ≤ _
  rw [hsub]
  exact norm_positiveTimeHeatRegularizedSpectralOutputPath_le
    ν hν u (v - w) hu T

/-- The difference of two advecting-input Duhamel paths is exactly the path
of the advecting-input difference. -/
theorem positiveTimeHeatRegularizedSpectralOutputPath_sub_left
    (ν : ℝ) (hν : 0 < ν)
    (u v w : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v) :
    positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu -
      positiveTimeHeatRegularizedSpectralOutputPath ν hν v w hv =
      positiveTimeHeatRegularizedSpectralOutputPath ν hν (u - v) w (hu.sub hv) := by
  have huvfree : LatticeDivergenceFree (u - v + v) := by
    simpa only [sub_add_cancel] using hu
  have hadd := positiveTimeHeatRegularizedSpectralOutputPath_add_left
    ν hν (u - v) v w (hu.sub hv) hv huvfree
  have huv : u - v + v = u := sub_add_cancel u v
  have hadd' :
      positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu =
        positiveTimeHeatRegularizedSpectralOutputPath ν hν (u - v) w (hu.sub hv) +
          positiveTimeHeatRegularizedSpectralOutputPath ν hν v w hv := by
    rw [← positiveTimeHeatRegularizedSpectralOutputPath_congr_left
      ν hν w huvfree hu huv]
    exact hadd
  rw [hadd']
  abel

/-- Genuine left-input Lipschitz estimate for the completed nonlinear
Duhamel path on every finite horizon. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_left_le
    (ν : ℝ) (hν : 0 < ν)
    (u v w : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v)
    (T : NNReal) :
    ‖positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu T -
        positiveTimeHeatRegularizedSpectralOutputPath ν hν v w hv T‖ ≤
      (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) * ‖u - v‖ * ‖w‖ := by
  have hsub := congrFun
    (positiveTimeHeatRegularizedSpectralOutputPath_sub_left ν hν u v w hu hv) T
  change ‖(positiveTimeHeatRegularizedSpectralOutputPath ν hν u w hu -
      positiveTimeHeatRegularizedSpectralOutputPath ν hν v w hv) T‖ ≤ _
  rw [hsub]
  exact norm_positiveTimeHeatRegularizedSpectralOutputPath_le
    ν hν (u - v) w (hu.sub hv) T

/-- Two-input local Lipschitz estimate for the actual completed bilinear
Duhamel path.  This is the quantitative nonlinear estimate needed by a
fixed-point argument once a time-dependent path space is supplied. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_le
    (ν : ℝ) (hν : 0 < ν)
    (u u' v v' : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hu' : LatticeDivergenceFree u')
    (T : NNReal) :
    ‖positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu T -
        positiveTimeHeatRegularizedSpectralOutputPath ν hν u' v' hu' T‖ ≤
      (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) *
        (‖u‖ * ‖v - v'‖ + ‖u - u'‖ * ‖v'‖) := by
  have hdecomp :
      positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu T -
          positiveTimeHeatRegularizedSpectralOutputPath ν hν u' v' hu' T =
        (positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu T -
          positiveTimeHeatRegularizedSpectralOutputPath ν hν u v' hu T) +
        (positiveTimeHeatRegularizedSpectralOutputPath ν hν u v' hu T -
          positiveTimeHeatRegularizedSpectralOutputPath ν hν u' v' hu' T) := by
    abel
  rw [hdecomp]
  calc
    ‖(positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu T -
          positiveTimeHeatRegularizedSpectralOutputPath ν hν u v' hu T) +
        (positiveTimeHeatRegularizedSpectralOutputPath ν hν u v' hu T -
          positiveTimeHeatRegularizedSpectralOutputPath ν hν u' v' hu' T)‖ ≤
        ‖positiveTimeHeatRegularizedSpectralOutputPath ν hν u v hu T -
          positiveTimeHeatRegularizedSpectralOutputPath ν hν u v' hu T‖ +
        ‖positiveTimeHeatRegularizedSpectralOutputPath ν hν u v' hu T -
          positiveTimeHeatRegularizedSpectralOutputPath ν hν u' v' hu' T‖ :=
      norm_add_le _ _
    _ ≤ (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) * ‖u‖ * ‖v - v'‖ +
        (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) * ‖u - u'‖ * ‖v'‖ :=
      add_le_add
        (norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_right_le
          ν hν u v v' hu T)
        (norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_left_le
          ν hν u u' v' hu hu' T)
    _ = (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) *
        (‖u‖ * ‖v - v'‖ + ‖u - u'‖ * ‖v'‖) := by ring

/-- The actual diagonal nonlinear Duhamel map on divergence-free weighted
Fourier data. -/
def nonlinearDuhamelPath (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    NNReal → WeightedLatticeBanach :=
  positiveTimeHeatRegularizedSpectralOutputPath ν hν u u hu

@[simp]
theorem nonlinearDuhamelPath_zero (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    nonlinearDuhamelPath ν hν u hu 0 = 0 :=
  positiveTimeHeatRegularizedSpectralOutputPath_zero ν hν u u hu

/-- Quadratic finite-horizon bound for the actual diagonal nonlinear
Duhamel map. -/
theorem norm_nonlinearDuhamelPath_le
    (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (T : NNReal) :
    ‖nonlinearDuhamelPath ν hν u hu T‖ ≤
      (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) * ‖u‖ ^ 2 := by
  unfold nonlinearDuhamelPath
  calc
    ‖positiveTimeHeatRegularizedSpectralOutputPath ν hν u u hu T‖ ≤
        (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) * ‖u‖ * ‖u‖ :=
      norm_positiveTimeHeatRegularizedSpectralOutputPath_le ν hν u u hu T
    _ = (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) * ‖u‖ ^ 2 := by ring

/-- Local Lipschitz bound for the actual diagonal nonlinear Duhamel map.
On a radius-`R` ball this yields Lipschitz constant
`4 * sqrt(T) * R / sqrt(ν)`. -/
theorem norm_nonlinearDuhamelPath_sub_le
    (ν : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v)
    (T : NNReal) :
    ‖nonlinearDuhamelPath ν hν u hu T -
        nonlinearDuhamelPath ν hν v hv T‖ ≤
      (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) *
        (‖u‖ + ‖v‖) * ‖u - v‖ := by
  unfold nonlinearDuhamelPath
  calc
    ‖positiveTimeHeatRegularizedSpectralOutputPath ν hν u u hu T -
        positiveTimeHeatRegularizedSpectralOutputPath ν hν v v hv T‖ ≤
      (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) *
        (‖u‖ * ‖u - v‖ + ‖u - v‖ * ‖v‖) :=
      norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_le
        ν hν u v u v hu hv T
    _ = (2 * Real.sqrt (T : ℝ) / Real.sqrt ν) *
        (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

end Navier.Analysis.CriticalMildDuhamelBochner

#print axioms Navier.Analysis.CriticalMildDuhamelBochner.positiveTimeHeatRegularizedSpectralOutputPath_zero
#print axioms Navier.Analysis.CriticalMildDuhamelBochner.norm_positiveTimeHeatRegularizedSpectralOutputPath_le
#print axioms Navier.Analysis.CriticalMildDuhamelBochner.norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_right_le
#print axioms Navier.Analysis.CriticalMildDuhamelBochner.norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_left_le
#print axioms Navier.Analysis.CriticalMildDuhamelBochner.norm_positiveTimeHeatRegularizedSpectralOutputPath_sub_le
#print axioms Navier.Analysis.CriticalMildDuhamelBochner.norm_positiveTimeHeatRegularizedSpectralOutput_sub_le
#print axioms Navier.Analysis.CriticalMildDuhamelBochner.norm_nonlinearDuhamelPath_sub_le
