import Navier.Analysis.PhysicalLocalEvolution

/-!
# Pointwise reconstruction of the periodic Fourier nonlinearity

This file identifies the repository's literal countable lattice convolution
with the pointwise transport term of the reconstructed period-one velocity.
All products and regroupings are justified by absolute summability from the
weighted carrier; no formal-series multiplication principle is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators

namespace Navier.Analysis.PeriodicNonlinearFourierReconstruction

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildAsymmetricPairSummable
open Navier.Analysis.CriticalMildGlobalClosure
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildSmoothBootstrap
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildHigherMomentBootstrap
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildQuantitativeRestart
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalLocalEvolution
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicPressureRecovery

theorem latticeCharacter_add (p q : LatticeMode) (x : Space) :
    latticeCharacter (p + q) x = latticeCharacter p x * latticeCharacter q x := by
  rw [latticeCharacter_eq_exp, latticeCharacter_eq_exp,
    latticeCharacter_eq_exp, ← Complex.exp_add]
  congr 1
  simp [latticeFrequency, Fin.sum_univ_three]
  ring

/-- One component of the differentiated complex Fourier velocity. -/
def complexSpatialDerivativeCoordinate (u : WeightedLatticeBanach)
    (x : Space) (i j : Fin 3) : ℂ :=
  ∑' q : LatticeMode,
    periodOneDerivative * (latticeFrequency q j : ℂ) *
      latticeCharacter q x * weightedLatticeCoefficient u q i

/-- The complex pointwise transport term built from the actual reconstructed
velocity and its termwise differentiated Fourier series. -/
def complexPointwiseConvection (u : WeightedLatticeBanach)
    (x : Space) : ComplexSpace :=
  fun i => ∑ j : Fin 3,
    complexFourierReconstruction u x j *
      complexSpatialDerivativeCoordinate u x i j

theorem complexFourierReconstruction_apply_eq
    (u : WeightedLatticeBanach) (x : Space) (j : Fin 3) :
    complexFourierReconstruction u x j =
      ∑' p : LatticeMode,
        latticeCharacter p x * weightedLatticeCoefficient u p j := by
  have hs := summable_latticeFourierTerm u x
  unfold complexFourierReconstruction
  change complexE3CoordinateCLM j
      (∑' p : LatticeMode, latticeFourierTerm u p x) = _
  rw [(complexE3CoordinateCLM j).map_tsum hs]
  apply tsum_congr
  intro p
  rfl

/-- One ordered pair contribution to a coordinate of `(u·∇)u`. -/
def pointwiseConvectionPairCoordinate (u : WeightedLatticeBanach)
    (x : Space) (i j : Fin 3)
    (pq : LatticeMode × LatticeMode) : ℂ :=
  (latticeCharacter pq.1 x * weightedLatticeCoefficient u pq.1 j) *
    (periodOneDerivative * (latticeFrequency pq.2 j : ℂ) *
      latticeCharacter pq.2 x * weightedLatticeCoefficient u pq.2 i)

theorem summable_pointwiseConvectionPairCoordinate
    (u : WeightedLatticeBanach) (x : Space) (i j : Fin 3) :
    Summable (pointwiseConvectionPairCoordinate u x i j) := by
  let f : LatticeMode → ℂ := fun p =>
    latticeCharacter p x * weightedLatticeCoefficient u p j
  let g : LatticeMode → ℂ := fun q =>
    periodOneDerivative * (latticeFrequency q j : ℂ) *
      latticeCharacter q x * weightedLatticeCoefficient u q i
  have hf : Summable f :=
    summable_complexVelocityCoordinate_term (fun _ => u) 0 x j
  have hg : Summable g :=
    summable_complexVelocityCoordinate_line_derivative (fun _ => u) 0 x i j
  have hfg : Summable (fun pq : LatticeMode × LatticeMode =>
      f pq.1 * g pq.2) :=
    summable_mul_of_summable_norm (f := f) (g := g) hf.norm hg.norm
  exact hfg.congr (fun _ => rfl)

theorem pointwiseConvection_product_eq_pair_tsum
    (u : WeightedLatticeBanach) (x : Space) (i j : Fin 3) :
    complexFourierReconstruction u x j *
        complexSpatialDerivativeCoordinate u x i j =
      ∑' pq : LatticeMode × LatticeMode,
        pointwiseConvectionPairCoordinate u x i j pq := by
  rw [complexFourierReconstruction_apply_eq]
  unfold complexSpatialDerivativeCoordinate pointwiseConvectionPairCoordinate
  exact tsum_mul_tsum_of_summable_norm
    (summable_complexVelocityCoordinate_term (fun _ => u) 0 x j).norm
    (summable_complexVelocityCoordinate_line_derivative
      (fun _ => u) 0 x i j).norm

/-- Finite coordinate summation commutes with the absolutely convergent pair
series. -/
theorem complexPointwiseConvection_eq_pair_tsum
    (u : WeightedLatticeBanach) (x : Space) (i : Fin 3) :
    complexPointwiseConvection u x i =
      ∑' pq : LatticeMode × LatticeMode,
        ∑ j : Fin 3, pointwiseConvectionPairCoordinate u x i j pq := by
  unfold complexPointwiseConvection
  rw [Finset.sum_congr rfl (fun j _ =>
    pointwiseConvection_product_eq_pair_tsum u x i j)]
  symm
  exact Summable.tsum_finsetSum (s := Finset.univ)
    (fun j _ => summable_pointwiseConvectionPairCoordinate u x i j)

/-- The finite coordinate contraction of one ordered Fourier pair. -/
def pointwiseConvectionPairSumCoordinate (u : WeightedLatticeBanach)
    (x : Space) (i : Fin 3) (pq : LatticeMode × LatticeMode) : ℂ :=
  ∑ j : Fin 3, pointwiseConvectionPairCoordinate u x i j pq

theorem summable_pointwiseConvectionPairSumCoordinate
    (u : WeightedLatticeBanach) (x : Space) (i : Fin 3) :
    Summable (pointwiseConvectionPairSumCoordinate u x i) := by
  unfold pointwiseConvectionPairSumCoordinate
  classical
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction with
  | empty => simp
  | @insert j s hj ih =>
      simpa [Finset.sum_insert hj] using
        (summable_pointwiseConvectionPairCoordinate u x i j).add ih

/-- A single pointwise pair is exactly its output character times the actual
unprojected spectral transport coefficient, including the period-one phase. -/
theorem pointwiseConvectionPairSumCoordinate_eq
    (u : WeightedLatticeBanach) (x : Space) (i : Fin 3)
    (pq : LatticeMode × LatticeMode) :
    pointwiseConvectionPairSumCoordinate u x i pq =
      latticeCharacter (pq.1 + pq.2) x * periodOneDerivative *
        spectralTransport (latticeFrequency pq.2)
          (weightedLatticeCoefficient u pq.1)
          (weightedLatticeCoefficient u pq.2) i := by
  unfold pointwiseConvectionPairSumCoordinate pointwiseConvectionPairCoordinate
  unfold spectralTransport
  rw [inner_complexFrequency, Pi.smul_apply]
  rw [latticeCharacter_add]
  rw [smul_eq_mul]
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Evaluating the repository's literal convolution at one coordinate is the
absolutely convergent sum over the exact output-mode fiber. -/
theorem weightedLatticeSpectralConvolution_apply_eq_fiber_tsum
    (u : WeightedLatticeBanach) (k : LatticeMode) (i : Fin 3) :
    WithLp.ofLp (weightedLatticeSpectralConvolution k u u) i =
      ∑' pq : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        spectralTransport (latticeFrequency pq.1.2)
          (weightedLatticeCoefficient u pq.1.1)
          (weightedLatticeCoefficient u pq.1.2) i := by
  let v := weightedLatticeCoefficient u
  have hv : LatticeWeightedL1 v := latticeWeightedL1_coefficient u
  have hterm : Summable (latticeSpectralTerm k v v) :=
    summable_latticeSpectralTerm_of_weightedL1 k v v
      (latticeConvolutionWeightedL1_of_weightedL1 k v v hv hv)
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  change complexE3CoordinateCLM i
      (∑' pq : LatticeMode × LatticeMode, latticeSpectralTerm k v v pq) = _
  rw [(complexE3CoordinateCLM i).map_tsum hterm]
  change (∑' pq : LatticeMode × LatticeMode,
      complexE3CoordinateCLM i (latticeSpectralTerm k v v pq)) =
    ∑' pq : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
      spectralTransport (latticeFrequency pq.1.2) (v pq.1.1) (v pq.1.2) i
  have hsub := tsum_subtype
    (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))
    (fun pq : LatticeMode × LatticeMode =>
      spectralTransport (latticeFrequency pq.2) (v pq.1) (v pq.2) i)
  rw [hsub]
  apply tsum_congr
  intro pq
  by_cases hpq : pq.1 + pq.2 = k
  · have hmem : pq ∈ latticeOutputMode ⁻¹' ({k} : Set LatticeMode) := by
      change latticeOutputMode pq = k
      simpa [latticeOutputMode] using hpq
    rw [Set.indicator_of_mem hmem]
    rw [latticeSpectralTerm, if_pos hpq]
    rfl
  · have hmem : pq ∉ latticeOutputMode ⁻¹' ({k} : Set LatticeMode) := by
      intro h
      apply hpq
      change latticeOutputMode pq = k at h
      simpa [latticeOutputMode] using h
    rw [Set.indicator_of_notMem hmem]
    simp [latticeSpectralTerm, hpq]

/-- The absolutely convergent pointwise pair series restricted to one exact
output mode. -/
def pointwiseConvectionFiberCoordinate (u : WeightedLatticeBanach)
    (x : Space) (i : Fin 3) (k : LatticeMode) : ℂ :=
  ∑' pq : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
    pointwiseConvectionPairSumCoordinate u x i pq.1

theorem summable_pointwiseConvectionFiberCoordinate
    (u : WeightedLatticeBanach) (x : Space) (i : Fin 3) :
    Summable (pointwiseConvectionFiberCoordinate u x i) := by
  have hpair := summable_pointwiseConvectionPairSumCoordinate u x i
  have hsigma : Summable (fun z :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
        pointwiseConvectionPairSumCoordinate u x i z.2.1) :=
    latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
  exact hsigma.sigma

theorem tsum_pointwiseConvectionFiberCoordinate_eq_pair
    (u : WeightedLatticeBanach) (x : Space) (i : Fin 3) :
    (∑' k : LatticeMode, pointwiseConvectionFiberCoordinate u x i k) =
      ∑' pq : LatticeMode × LatticeMode,
        pointwiseConvectionPairSumCoordinate u x i pq := by
  have hpair := summable_pointwiseConvectionPairSumCoordinate u x i
  have hsigma : Summable (fun z :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
        pointwiseConvectionPairSumCoordinate u x i z.2.1) :=
    latticeOutputFiberSigmaEquiv.summable_iff.mpr hpair
  unfold pointwiseConvectionFiberCoordinate
  rw [← hsigma.tsum_sigma]
  exact latticeOutputFiberSigmaEquiv.tsum_eq _

/-- Each output fiber of the pointwise product is exactly the corresponding
coefficient of the repository's literal convolution Fourier series. -/
theorem pointwiseConvectionFiberCoordinate_eq
    (u : WeightedLatticeBanach) (x : Space) (i : Fin 3) (k : LatticeMode) :
    pointwiseConvectionFiberCoordinate u x i k =
      latticeCharacter k x * periodOneConvectionCoefficient k u u i := by
  unfold pointwiseConvectionFiberCoordinate
  calc
    (∑' pq : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        pointwiseConvectionPairSumCoordinate u x i pq.1) =
        ∑' pq : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
          latticeCharacter k x * periodOneDerivative *
            spectralTransport (latticeFrequency pq.1.2)
              (weightedLatticeCoefficient u pq.1.1)
              (weightedLatticeCoefficient u pq.1.2) i := by
      apply tsum_congr
      intro pq
      rw [pointwiseConvectionPairSumCoordinate_eq]
      have hpq : pq.1.1 + pq.1.2 = k := by
        have hmem := pq.2
        change latticeOutputMode pq.1 = k at hmem
        simpa [latticeOutputMode] using hmem
      rw [hpq]
    _ = latticeCharacter k x * periodOneDerivative *
        (∑' pq : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
          spectralTransport (latticeFrequency pq.1.2)
            (weightedLatticeCoefficient u pq.1.1)
            (weightedLatticeCoefficient u pq.1.2) i) := by
      rw [tsum_mul_left]
    _ = latticeCharacter k x * periodOneConvectionCoefficient k u u i := by
      rw [← weightedLatticeSpectralConvolution_apply_eq_fiber_tsum u k i]
      unfold periodOneConvectionCoefficient
      simp [Pi.smul_apply, smul_eq_mul]
      ring

/-- The pointwise product of the reconstructed velocity and its actual
termwise spatial derivative is precisely the Fourier series of the literal
countable convection coefficients. -/
theorem complexPointwiseConvection_eq_periodOneConvectionFourierSeries
    (u : WeightedLatticeBanach) (x : Space) (i : Fin 3) :
    complexPointwiseConvection u x i =
      ∑' k : LatticeMode,
        latticeCharacter k x * periodOneConvectionCoefficient k u u i := by
  rw [complexPointwiseConvection_eq_pair_tsum]
  change (∑' pq : LatticeMode × LatticeMode,
      pointwiseConvectionPairSumCoordinate u x i pq) = _
  rw [← tsum_pointwiseConvectionFiberCoordinate_eq_pair]
  apply tsum_congr
  intro k
  exact pointwiseConvectionFiberCoordinate_eq u x i k

/-- Coordinate Fourier reconstruction for an absolutely summable family of
physical vector coefficients. -/
def complexCoefficientSeriesCoordinate (f : LatticeMode → ComplexSpace)
    (x : Space) (i : Fin 3) : ℂ :=
  ∑' k : LatticeMode, latticeCharacter k x * f k i

theorem summable_character_mul_coordinate_of_summable_norm
    (f : LatticeMode → ComplexSpace)
    (hf : Summable fun k => complexEuclideanNorm (f k))
    (x : Space) (i : Fin 3) :
    Summable fun k : LatticeMode => latticeCharacter k x * f k i := by
  apply Summable.of_norm
  apply hf.of_nonneg_of_le
  · intro k
    exact norm_nonneg _
  · intro k
    rw [norm_mul, norm_latticeCharacter, one_mul]
    simpa [complexEuclideanNorm] using
      PiLp.norm_apply_le (complexEuclideanPoint (f k)) i

theorem summable_periodOneConvectionFourierCoordinate
    (u : WeightedLatticeBanach) (x : Space) (i : Fin 3) :
    Summable fun k : LatticeMode =>
      latticeCharacter k x * periodOneConvectionCoefficient k u u i := by
  exact (summable_pointwiseConvectionFiberCoordinate u x i).congr
    (fun k => pointwiseConvectionFiberCoordinate_eq u x i k)

/-- The pressure-gradient field reconstructed from the exact zero-mean
pressure coefficients selected by the Leray decomposition. -/
def complexPressureGradientReconstruction (u : WeightedLatticeBanach)
    (x : Space) : ComplexSpace :=
  fun i => complexCoefficientSeriesCoordinate
    (fun k => periodOneGradientCoefficient k
      (periodOnePressureCoefficient k u u)) x i

theorem summable_pressureGradientFourierCoordinate
    (u : WeightedLatticeBanach)
    (hu : LatticeTwoWeightL1 (weightedLatticeCoefficient u))
    (x : Space) (i : Fin 3) :
    Summable fun k : LatticeMode => latticeCharacter k x *
      periodOneGradientCoefficient k
        (periodOnePressureCoefficient k u u) i := by
  exact summable_character_mul_coordinate_of_summable_norm _
    (summable_recoveredPressureGradient_of_twoWeight u hu) x i

/-- Summing a genuine unprojected coefficient equation produces the exact
pointwise Fourier balance.  The nonlinear series is then replaced by the
actual pointwise product proved above. -/
theorem unprojectedModeEquation_to_pointwiseFourierBalance
    (nu : ℝ) (u : WeightedLatticeBanach)
    (timeDerivative : LatticeMode → ComplexSpace)
    (htime : Summable fun k => complexEuclideanNorm (timeDerivative k))
    (huTwo : LatticeTwoWeightL1 (weightedLatticeCoefficient u))
    (hviscous : Summable fun k => complexEuclideanNorm
      (periodOneViscousCoefficient nu k (weightedLatticeCoefficient u k)))
    (heq : ∀ k,
      timeDerivative k + periodOneConvectionCoefficient k u u +
          periodOneViscousCoefficient nu k (weightedLatticeCoefficient u k) +
          periodOneGradientCoefficient k
            (periodOnePressureCoefficient k u u) = 0)
    (x : Space) (i : Fin 3) :
    complexCoefficientSeriesCoordinate timeDerivative x i +
        complexPointwiseConvection u x i +
        complexCoefficientSeriesCoordinate
          (fun k => periodOneViscousCoefficient nu k
            (weightedLatticeCoefficient u k)) x i +
        complexPressureGradientReconstruction u x i = 0 := by
  have ht := summable_character_mul_coordinate_of_summable_norm
    timeDerivative htime x i
  have hc := summable_periodOneConvectionFourierCoordinate u x i
  have hv := summable_character_mul_coordinate_of_summable_norm _ hviscous x i
  have hp := summable_pressureGradientFourierCoordinate u huTwo x i
  have hsum : Summable fun k : LatticeMode =>
      latticeCharacter k x * timeDerivative k i +
        latticeCharacter k x * periodOneConvectionCoefficient k u u i +
        latticeCharacter k x *
          periodOneViscousCoefficient nu k (weightedLatticeCoefficient u k) i +
        latticeCharacter k x * periodOneGradientCoefficient k
          (periodOnePressureCoefficient k u u) i :=
    ((ht.add hc).add hv).add hp
  have hzero : (fun k : LatticeMode =>
      latticeCharacter k x * timeDerivative k i +
        latticeCharacter k x * periodOneConvectionCoefficient k u u i +
        latticeCharacter k x *
          periodOneViscousCoefficient nu k (weightedLatticeCoefficient u k) i +
        latticeCharacter k x * periodOneGradientCoefficient k
          (periodOnePressureCoefficient k u u) i) = fun _ => 0 := by
    funext k
    have hk := congrFun (heq k) i
    simp only [Pi.add_apply, Pi.zero_apply] at hk
    linear_combination latticeCharacter k x * hk
  have htotal : (∑' k : LatticeMode,
      (latticeCharacter k x * timeDerivative k i +
        latticeCharacter k x * periodOneConvectionCoefficient k u u i +
        latticeCharacter k x *
          periodOneViscousCoefficient nu k (weightedLatticeCoefficient u k) i +
        latticeCharacter k x * periodOneGradientCoefficient k
          (periodOnePressureCoefficient k u u) i)) = 0 := by
    rw [hzero]
    simp
  rw [Summable.tsum_add ((ht.add hc).add hv) hp,
    Summable.tsum_add (ht.add hc) hv,
    Summable.tsum_add ht hc] at htotal
  rw [← complexPointwiseConvection_eq_periodOneConvectionFourierSeries u x i]
    at htotal
  exact htotal

theorem summable_twoSpatialMoments_of_twoAndQuarter
    (u : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient u k))) :
    Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient u k) := by
  apply hu.of_nonneg_of_le
  · intro k
    exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
  · intro k
    by_cases hk : k = 0
    · subst k
      have hz : latticeFrequency (0 : LatticeMode) = 0 := by
        ext j
        fin_cases j <;> simp [latticeFrequency]
      rw [hz]
      simp [officialEuclideanPoint]
    · have hq : 1 ≤ ‖complexFrequency (latticeFrequency k)‖ :=
        one_le_latticeModeSize_of_ne_zero hk
      have hquarter : 1 ≤ quarterFrequencyWeight k := by
        dsimp [quarterFrequencyWeight]
        rw [Real.one_le_sqrt, Real.one_le_sqrt]
        exact hq
      exact le_mul_of_one_le_left
        (mul_nonneg (sq_nonneg _) (norm_nonneg _)) hquarter

/-- Two summable spatial moments make the physical viscous Fourier
coefficients absolutely summable. -/
theorem summable_periodOneViscousCoefficient_of_twoSpatialMoments
    (nu : ℝ) (u : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient u k)) :
    Summable fun k : LatticeMode => complexEuclideanNorm
      (periodOneViscousCoefficient nu k (weightedLatticeCoefficient u k)) := by
  have hs := hu.mul_left |nu * (2 * Real.pi) ^ 2|
  apply hs.congr
  intro k
  have hdot : latticeFrequency k ⬝ᵥ latticeFrequency k =
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 := by
    rw [← complexFrequency_norm_sq, complexFrequency_norm_eq_official]
  unfold periodOneViscousCoefficient complexEuclideanNorm
  rw [complexEuclideanPoint_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, hdot]
  simp only [abs_mul, abs_pow, abs_norm]
  ring

theorem summable_periodOneViscousCoefficient_of_twoAndQuarter
    (nu : ℝ) (u : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient u k))) :
    Summable fun k : LatticeMode => complexEuclideanNorm
      (periodOneViscousCoefficient nu k (weightedLatticeCoefficient u k)) :=
  summable_periodOneViscousCoefficient_of_twoSpatialMoments nu u
    (summable_twoSpatialMoments_of_twoAndQuarter u hu)

/-- The completed carrier's zeroth moment together with two homogeneous
moments controls the inhomogeneous two-weight class used by pressure recovery. -/
theorem latticeTwoWeightL1_of_twoSpatialMoments
    (u : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode =>
      ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient u k)) :
    LatticeTwoWeightL1 (weightedLatticeCoefficient u) := by
  have hbase := summable_decodedCoefficientNorm u
  have hsum := hbase.add hu
  have htwo := hsum.mul_left 2
  apply htwo.of_nonneg_of_le
  · intro k
    exact mul_nonneg (sq_nonneg _) (norm_nonneg _)
  · intro k
    let r := ‖officialEuclideanPoint (latticeFrequency k)‖
    let z := complexEuclideanNorm (weightedLatticeCoefficient u k)
    have hr : 0 ≤ r := norm_nonneg _
    have hz : 0 ≤ z := norm_nonneg _
    have hw : (1 + r) ^ 2 ≤ 2 * (1 + r ^ 2) := by
      nlinarith [sq_nonneg (r - 1)]
    have hm := mul_le_mul_of_nonneg_right hw hz
    unfold latticeModeWeight
    rw [complexFrequency_norm_eq_official]
    dsimp [r, z] at hm ⊢
    nlinarith

theorem latticeTwoWeightL1_of_twoAndQuarter
    (u : WeightedLatticeBanach)
    (hu : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm (weightedLatticeCoefficient u k))) :
    LatticeTwoWeightL1 (weightedLatticeCoefficient u) :=
  latticeTwoWeightL1_of_twoSpatialMoments u
    (summable_twoSpatialMoments_of_twoAndQuarter u hu)

theorem summable_physicalTimeDerivative_of_raw
    (mu : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (ht : Summable fun k : LatticeMode =>
      complexEuclideanNorm (mildRawTimeDerivative mu A t k)) :
    Summable fun k : LatticeMode => complexEuclideanNorm
      (rawToPhysicalAmplitude •
        mildRawTimeDerivative mu A t k) := by
  have hs := ht.mul_left ‖rawToPhysicalAmplitude‖
  apply hs.congr
  intro k
  unfold complexEuclideanNorm
  rw [complexEuclideanPoint_smul, norm_smul]

/-- The exact pointwise Fourier balance carried by a physicalized raw mild
trajectory at a positive time. -/
def PhysicalPointwiseFourierBalance (nu : ℝ)
    (A : ℝ → WeightedLatticeBanach) (t : ℝ) (x : Space) (i : Fin 3) : Prop :=
  complexCoefficientSeriesCoordinate
      (fun k => rawToPhysicalAmplitude •
        mildRawTimeDerivative (rawMildViscosity nu) A t k) x i +
    complexPointwiseConvection (physicalCarrier (A t)) x i +
    complexCoefficientSeriesCoordinate
      (fun k => periodOneViscousCoefficient nu k
        (weightedLatticeCoefficient (physicalCarrier (A t)) k)) x i +
    complexPressureGradientReconstruction (physicalCarrier (A t)) x i = 0

/-- The first joint bootstrap's genuine coefficient equation reconstructs to
the pointwise nonlinear Fourier balance at the same positive time. -/
theorem physicalLocalEvolution_pointwiseFourierBalance
    (nu : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hspace : Summable fun k : LatticeMode => quarterFrequencyWeight k *
      (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
        complexEuclideanNorm
          (weightedLatticeCoefficient (physicalCarrier (A t)) k)))
    (htime : Summable fun k : LatticeMode => complexEuclideanNorm
      (mildRawTimeDerivative (rawMildViscosity nu) A t k))
    (heq : ∀ k,
      rawToPhysicalAmplitude •
            mildRawTimeDerivative (rawMildViscosity nu) A t k +
          periodOneConvectionCoefficient k
            (physicalCarrier (A t)) (physicalCarrier (A t)) +
          periodOneViscousCoefficient nu k
            (weightedLatticeCoefficient (physicalCarrier (A t)) k) +
          periodOneGradientCoefficient k
            (periodOnePressureCoefficient k
              (physicalCarrier (A t)) (physicalCarrier (A t))) = 0)
    (x : Space) (i : Fin 3) :
    PhysicalPointwiseFourierBalance nu A t x i := by
  have htwo := latticeTwoWeightL1_of_twoAndQuarter
    (physicalCarrier (A t)) hspace
  have ht := summable_physicalTimeDerivative_of_raw
    (rawMildViscosity nu) A t htime
  have hv := summable_periodOneViscousCoefficient_of_twoAndQuarter
    nu (physicalCarrier (A t)) hspace
  exact unprojectedModeEquation_to_pointwiseFourierBalance
    nu (physicalCarrier (A t))
      (fun k => rawToPhysicalAmplitude •
        mildRawTimeDerivative (rawMildViscosity nu) A t k)
      ht htwo hv heq x i

/-- Arbitrary physical solenoidal initial coefficients generate a nontrivial
time interval on which the actual mild trajectory satisfies the reconstructed
pointwise Fourier Navier--Stokes balance.  The finite interval is the local
chart supplied by the fixed-point construction. -/
theorem exists_physical_local_pointwise_fourier_balance
    (nu : ℝ) (hnu : 0 < nu) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a) (hareal : LatticeAntiHermitian a) :
    ∃ T : ℝ, 0 < T ∧ ∃ A : ℝ → WeightedLatticeBanach,
      A 0 = a ∧ Continuous A ∧ (∀ s, LatticeDivergenceFree (A s)) ∧
      (∀ s, LatticeAntiHermitian (A s)) ∧
      (∀ s, ‖A s‖ ≤ criticalMildBoundedRadius ‖a‖) ∧
      ∀ t ∈ Set.Ioo (0 : ℝ) T,
        (Summable fun k : LatticeMode => quarterFrequencyWeight k *
          (‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2 *
            complexEuclideanNorm
              (weightedLatticeCoefficient (physicalCarrier (A t)) k))) ∧
        (∀ k i, HasDerivAt (fun r => weightedLatticeCoefficient (A r) k i)
          (mildRawTimeDerivative (rawMildViscosity nu) A t k i) t) ∧
        (Summable fun k : LatticeMode => complexEuclideanNorm
          (mildRawTimeDerivative (rawMildViscosity nu) A t k)) ∧
        (∀ k,
          rawToPhysicalAmplitude •
                mildRawTimeDerivative (rawMildViscosity nu) A t k +
              periodOneConvectionCoefficient k
                (physicalCarrier (A t)) (physicalCarrier (A t)) +
              periodOneViscousCoefficient nu k
                (weightedLatticeCoefficient (physicalCarrier (A t)) k) +
              periodOneGradientCoefficient k
                (periodOnePressureCoefficient k
                  (physicalCarrier (A t)) (physicalCarrier (A t))) = 0) ∧
        ∀ x i, PhysicalPointwiseFourierBalance nu A t x i := by
  obtain ⟨T, hT, A, hA0, hAc, hdiv, hreal, hbound, hreg⟩ :=
    exists_physical_local_evolution nu hnu a ha hareal
  refine ⟨T, hT, A, hA0, hAc, hdiv, hreal, hbound, ?_⟩
  intro t ht
  have h := hreg t ht
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  intro x i
  exact physicalLocalEvolution_pointwiseFourierBalance
    nu A t h.1 h.2.2.1 h.2.2.2 x i

end Navier.Analysis.PeriodicNonlinearFourierReconstruction
