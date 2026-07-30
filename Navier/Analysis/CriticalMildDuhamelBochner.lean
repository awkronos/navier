import Navier.Analysis.CriticalMildHeatCoefficientLift
import Navier.Analysis.CriticalMildWeightedBanach
import Navier.Analysis.CriticalMildDuhamel
import Navier.Analysis.CriticalMildGlobalWeightedOutput

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

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatCoefficientLift
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildGlobalReindex

/-- The physical Fourier divergence-free constraint on a completed weighted
carrier: every decoded mode is Hermitian-transverse to its own frequency. -/
def LatticeDivergenceFree (u : WeightedLatticeBanach) : Prop :=
  ∀ m : LatticeMode, inner ℂ (complexFrequency (latticeFrequency m))
    (complexEuclideanPoint (weightedLatticeCoefficient u m)) = 0

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

end Navier.Analysis.CriticalMildDuhamelBochner
