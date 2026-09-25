import Navier.Analysis.CriticalMildZeroMode

/-!
# Fourier translation phases and exact zero-mode drift removal

On the period-one torus, spatial translation by `t c` multiplies Fourier mode
`k` by `exp(2π i t k·c)`.  This module constructs that operation on the actual
completed weighted lattice carrier and proves that it preserves every scalar
amplitude used by the off-zero terminal estimates.

The literal lattice convolution is inspected at the summand level.  Its raw
transport symbol uses `k·A`; therefore physical Fourier coefficients cannot be
inserted directly.  The faithful change of variables `A_k = -2π i û_k` turns a
physical constant mean `c` into the raw zero mode `-2π i c`.  Its sole nonzero
cross interaction then cancels the derivative of the unit-modulus translation
phase exactly.  The checked identities below prove that cancellation and all
off-zero estimate invariances.  Promotion of these coefficient identities to
the complete time-integrated mild fixed-point equation is a separate Volterra
change-of-variables step.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildMeanDriftRemoval

open MeasureTheory
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.CriticalMildZeroMode

/-- The real lattice pairing `k·c` in the repository's frequency convention. -/
def latticePairing (c : Space) (k : LatticeMode) : ℝ :=
  ∑ i : Fin 3, latticeFrequency k i * c i

theorem latticePairing_add (c : Space) (i j : LatticeMode) :
    latticePairing c (i + j) = latticePairing c i + latticePairing c j := by
  simp only [latticePairing, latticeFrequency_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

/-- Infinitesimal period-one translation multiplier `2π i k·c`. -/
def physicalTranslationRate (c : Space) (k : LatticeMode) : ℂ :=
  Complex.I * ((2 * Real.pi * latticePairing c k : ℝ) : ℂ)

/-- Period-one Fourier phase for the physical translation `x ↦ x + t c`. -/
def physicalTranslationPhase (c : Space) (t : ℝ) (k : LatticeMode) : ℂ :=
  Complex.exp (physicalTranslationRate c k * (t : ℂ))

@[simp] theorem norm_physicalTranslationPhase (c : Space) (t : ℝ) (k : LatticeMode) :
    ‖physicalTranslationPhase c t k‖ = 1 := by
  rw [physicalTranslationPhase, Complex.norm_exp]
  simp [physicalTranslationRate]

@[simp] theorem physicalTranslationPhase_zero (c : Space) (t : ℝ) :
    physicalTranslationPhase c t 0 = 1 := by
  simp [physicalTranslationPhase, physicalTranslationRate, latticePairing,
    latticeFrequency_zero]

theorem physicalTranslationPhase_add (c : Space) (t : ℝ) (i j : LatticeMode) :
    physicalTranslationPhase c t (i + j) =
      physicalTranslationPhase c t i * physicalTranslationPhase c t j := by
  rw [physicalTranslationPhase, physicalTranslationPhase, physicalTranslationPhase,
    ← Complex.exp_add]
  congr 1
  simp only [physicalTranslationRate, latticePairing_add]
  push_cast
  ring

theorem hasDerivAt_physicalTranslationPhase (c : Space) (k : LatticeMode)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => physicalTranslationPhase c s k)
      (physicalTranslationPhase c t k * physicalTranslationRate c k) t := by
  have hlinear : HasDerivAt
      (fun s : ℝ => physicalTranslationRate c k * (s : ℂ))
      (physicalTranslationRate c k) t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
        (physicalTranslationRate c k))
  exact hlinear.cexp

/-- Multiply each stored weighted Fourier coefficient by the physical
translation phase. -/
def translationPhaseCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) : WeightedLatticeBanach :=
  ⟨fun k => physicalTranslationPhase c t k • u k, memℓp_gen (by
    have hu : Summable (fun k : LatticeMode => ‖u k‖) := by
      simpa using u.2.summable
    simpa [norm_smul] using hu)⟩

@[simp] theorem translationPhaseCarrier_apply (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) (k : LatticeMode) :
    translationPhaseCarrier c t u k = physicalTranslationPhase c t k • u k :=
  rfl

theorem weightedLatticeCoefficient_translationPhaseCarrier
    (c : Space) (t : ℝ) (u : WeightedLatticeBanach) (k : LatticeMode) :
    weightedLatticeCoefficient (translationPhaseCarrier c t u) k =
      physicalTranslationPhase c t k • weightedLatticeCoefficient u k := by
  ext i
  simp [weightedLatticeCoefficient, translationPhaseCarrier]
  ring

theorem translationPhaseCarrier_apply_norm (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) (k : LatticeMode) :
    ‖translationPhaseCarrier c t u k‖ = ‖u k‖ := by
  rw [translationPhaseCarrier_apply, norm_smul, norm_physicalTranslationPhase,
    one_mul]

theorem weightedAmplitude_translationPhaseCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) (k : LatticeMode) :
    weightedAmplitude (translationPhaseCarrier c t u) k = weightedAmplitude u k := by
  unfold weightedAmplitude
  rw [weightedLatticeCoefficient_translationPhaseCarrier]
  unfold complexEuclideanNorm
  rw [ComplexFrequencyHeatLeray.complexEuclideanPoint_smul, norm_smul,
    norm_physicalTranslationPhase,
    one_mul]

theorem amplitudeOffZero_translationPhaseCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) :
    amplitudeOffZero (translationPhaseCarrier c t u) = amplitudeOffZero u := by
  funext k
  simp [amplitudeOffZero, weightedAmplitude_translationPhaseCarrier]

theorem heatHalfGeneratorMoment_translationPhaseCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) :
    heatHalfGeneratorMoment (translationPhaseCarrier c t u) =
      heatHalfGeneratorMoment u := by
  unfold heatHalfGeneratorMoment
  apply tsum_congr
  intro k
  rw [translationPhaseCarrier_apply_norm]

theorem offZeroSquareEnergy_translationPhaseCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) :
    (∑' k : LatticeMode, (amplitudeOffZero (translationPhaseCarrier c t u) k) ^ 2) =
      ∑' k : LatticeMode, (amplitudeOffZero u k) ^ 2 := by
  rw [amplitudeOffZero_translationPhaseCarrier]

/-! ## Exact covariance of the literal convolution under translation phase -/

theorem spectralTransport_smul_smul (a b : ℂ) (p : Space)
    (v w : ComplexSpace) :
    spectralTransport p (a • v) (b • w) =
      (a * b) • spectralTransport p v w := by
  unfold spectralTransport
  rw [ComplexFrequencyHeatLeray.complexEuclideanPoint_smul, inner_smul_right]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem latticeSpectralTerm_translationPhase
    (c : Space) (t : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) (ij : LatticeMode × LatticeMode) :
    latticeSpectralTerm k
        (weightedLatticeCoefficient (translationPhaseCarrier c t u))
        (weightedLatticeCoefficient (translationPhaseCarrier c t v)) ij =
      physicalTranslationPhase c t k •
        latticeSpectralTerm k (weightedLatticeCoefficient u)
          (weightedLatticeCoefficient v) ij := by
  by_cases hij : ij.1 + ij.2 = k
  · simp only [latticeSpectralTerm, hij, if_pos,
      weightedLatticeCoefficient_translationPhaseCarrier]
    rw [spectralTransport_smul_smul,
      ← physicalTranslationPhase_add c t ij.1 ij.2, hij]
    exact ComplexFrequencyHeatLeray.complexEuclideanPoint_smul _ _
  · simp [latticeSpectralTerm, hij]

/-- The phase covariance is proved from each actual convolution summand and
absolute summability, rather than postulated at the completed-output level. -/
theorem weightedLatticeSpectralConvolution_translationPhase
    (c : Space) (t : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k
        (translationPhaseCarrier c t u) (translationPhaseCarrier c t v) =
      physicalTranslationPhase c t k •
        weightedLatticeSpectralConvolution k u v := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [← Summable.tsum_const_smul _
    (summable_latticeSpectralTerm_of_weightedL1 k _ _
      (latticeConvolutionWeightedL1_of_weightedL1 k _ _
        (latticeWeightedL1_coefficient u) (latticeWeightedL1_coefficient v)))]
  apply tsum_congr
  exact latticeSpectralTerm_translationPhase c t k u v

theorem spectralOutputCoefficient_translationPhase
    (c : Space) (t : ℝ) (k : LatticeMode)
    (u v : WeightedLatticeBanach) :
    spectralOutputCoefficient k
        (translationPhaseCarrier c t u) (translationPhaseCarrier c t v) =
      physicalTranslationPhase c t k • spectralOutputCoefficient k u v := by
  unfold spectralOutputCoefficient
  rw [weightedLatticeSpectralConvolution_translationPhase]
  rfl

/-- The output-frequency heat--Leray semigroup commutes with the physical
translation phase at every mode. -/
theorem weightedLatticeCoefficient_weightedHeatFlow_translationPhase
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (c : Space) (t : ℝ) (u : WeightedLatticeBanach) (k : LatticeMode) :
    weightedLatticeCoefficient
        (CriticalMildHeatFlow.weightedHeatFlow ν τ hν hτ
          (translationPhaseCarrier c t u)) k =
      physicalTranslationPhase c t k •
        weightedLatticeCoefficient
          (CriticalMildHeatFlow.weightedHeatFlow ν τ hν hτ u) k := by
  rw [CriticalMildHeatFlow.weightedLatticeCoefficient_weightedHeatFlow,
    CriticalMildHeatFlow.weightedLatticeCoefficient_weightedHeatFlow,
    weightedLatticeCoefficient_translationPhaseCarrier]
  exact (ComplexFrequencyHeatLeray.complexFrequencyHeatLeray
    ν τ (latticeFrequency k)).map_smul
      (physicalTranslationPhase c t k) (weightedLatticeCoefficient u k)

/-! ## Faithful normalization between physical and raw mild coefficients -/

/-- Physical period-one coefficients are embedded in the repository's raw
mild equation by `A_k = -2π i û_k`. -/
def rawFourierScale : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)

def rawCarrierOfPhysical (u : WeightedLatticeBanach) : WeightedLatticeBanach :=
  rawFourierScale • u

@[simp] theorem rawCarrierOfPhysical_apply (u : WeightedLatticeBanach)
    (k : LatticeMode) :
    rawCarrierOfPhysical u k = rawFourierScale • u k := rfl

theorem spectralOutputCoefficient_rawCarrierOfPhysical
    (k : LatticeMode) (u v : WeightedLatticeBanach) :
    spectralOutputCoefficient k (rawCarrierOfPhysical u)
        (rawCarrierOfPhysical v) =
      rawFourierScale ^ 2 • spectralOutputCoefficient k u v := by
  unfold spectralOutputCoefficient rawCarrierOfPhysical
  rw [weightedLatticeSpectralConvolution_smul_left,
    weightedLatticeSpectralConvolution_smul_right, smul_smul]
  rw [WithLp.ofLp_smul]
  congr 1
  ring

theorem rawFourierScale_sq :
    rawFourierScale ^ 2 = -((2 * Real.pi) ^ 2 : ℝ) := by
  simp only [rawFourierScale, neg_sq, mul_pow, Complex.I_sq]
  push_cast
  ring

theorem rawFourierScale_mul_pairing_eq_neg_translationRate
    (c : Space) (k : LatticeMode) :
    rawFourierScale * latticePairing c k = -physicalTranslationRate c k := by
  simp only [rawFourierScale, physicalTranslationRate]
  push_cast
  ring

theorem hasDerivAt_physicalTranslationPhase_smul
    (c : Space) (k : LatticeMode) (z : ComplexSpace) (t : ℝ) :
    HasDerivAt (fun s : ℝ => physicalTranslationPhase c s k • z)
      ((physicalTranslationPhase c t k * physicalTranslationRate c k) • z) t :=
  (hasDerivAt_physicalTranslationPhase c k t).smul_const z

/-- The time derivative of the physical translation phase cancels exactly
against the raw constant-mean transport multiplier. -/
theorem translationRate_add_rawMeanDrift
    (c : Space) (t : ℝ) (k : LatticeMode) (z : ComplexSpace) :
    (physicalTranslationPhase c t k * physicalTranslationRate c k) • z +
      (rawFourierScale * latticePairing c k) •
        (physicalTranslationPhase c t k • z) = 0 := by
  rw [rawFourierScale_mul_pairing_eq_neg_translationRate]
  rw [smul_smul, ← add_smul]
  have hscalar :
      physicalTranslationPhase c t k * physicalTranslationRate c k +
        -physicalTranslationRate c k * physicalTranslationPhase c t k = 0 := by
    ring
  rw [hscalar, zero_smul]

theorem spectralOutputCoefficient_rawCarrierOfPhysical_eq
    (k : LatticeMode) (u v : WeightedLatticeBanach) :
    spectralOutputCoefficient k (rawCarrierOfPhysical u)
        (rawCarrierOfPhysical v) =
      (-((2 * Real.pi) ^ 2 : ℝ) : ℂ) • spectralOutputCoefficient k u v := by
  rw [spectralOutputCoefficient_rawCarrierOfPhysical, rawFourierScale_sq]

/-! ## The correctly normalized constant mean inside the raw carrier -/

/-- A constant physical velocity `c` is the zero raw Fourier mode
`-2π i c`.  The inhomogeneous lattice weight equals one at mode zero. -/
def rawMeanCarrier (c : Space) : WeightedLatticeBanach :=
  lp.single 1 (0 : LatticeMode)
    (complexEuclideanPoint (rawFourierScale • complexOfReal c))

theorem weightedLatticeCoefficient_rawMeanCarrier (c : Space) (k : LatticeMode) :
    weightedLatticeCoefficient (rawMeanCarrier c) k =
      if k = 0 then rawFourierScale • complexOfReal c else 0 := by
  by_cases hk : k = 0
  · subst k
    ext i
    simp [rawMeanCarrier, weightedLatticeCoefficient, latticeModeWeight,
      latticeFrequency_zero]
  · ext i
    simp [rawMeanCarrier, weightedLatticeCoefficient, hk]

theorem rawMeanCarrier_apply_zero (c : Space) :
    rawMeanCarrier c 0 =
      complexEuclideanPoint (rawFourierScale • complexOfReal c) := by
  simp [rawMeanCarrier]

theorem rawMeanCarrier_apply_ne_zero (c : Space) {k : LatticeMode} (hk : k ≠ 0) :
    rawMeanCarrier c k = 0 := by
  simp [rawMeanCarrier, hk]

/-- Remove the correctly normalized raw mean after applying the physical
translation phase. -/
def meanRemovedCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) : WeightedLatticeBanach :=
  translationPhaseCarrier c t u - rawMeanCarrier c

theorem meanRemovedCarrier_apply_ne_zero (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) {k : LatticeMode} (hk : k ≠ 0) :
    meanRemovedCarrier c t u k = translationPhaseCarrier c t u k := by
  simp [meanRemovedCarrier, rawMeanCarrier_apply_ne_zero c hk]

theorem amplitudeOffZero_meanRemovedCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) :
    amplitudeOffZero (meanRemovedCarrier c t u) = amplitudeOffZero u := by
  funext k
  by_cases hk : k = 0
  · simp [amplitudeOffZero, hk]
  · rw [amplitudeOffZero, if_neg hk, amplitudeOffZero, if_neg hk]
    unfold weightedAmplitude
    have hc : weightedLatticeCoefficient (meanRemovedCarrier c t u) k =
        weightedLatticeCoefficient (translationPhaseCarrier c t u) k := by
      unfold weightedLatticeCoefficient
      rw [meanRemovedCarrier_apply_ne_zero c t u hk]
    rw [hc]
    exact weightedAmplitude_translationPhaseCarrier c t u k

theorem offZeroSquareEnergy_meanRemovedCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) :
    (∑' k : LatticeMode, (amplitudeOffZero (meanRemovedCarrier c t u) k) ^ 2) =
      ∑' k : LatticeMode, (amplitudeOffZero u k) ^ 2 := by
  rw [amplitudeOffZero_meanRemovedCarrier]

theorem heatHalfGeneratorMoment_meanRemovedCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) :
    heatHalfGeneratorMoment (meanRemovedCarrier c t u) =
      heatHalfGeneratorMoment u := by
  unfold heatHalfGeneratorMoment
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k
    simp [latticeFrequency_zero]
  · rw [meanRemovedCarrier_apply_ne_zero c t u hk,
      translationPhaseCarrier_apply_norm]

theorem translationPhaseCarrier_divergenceFree
    (c : Space) (t : ℝ) {u : WeightedLatticeBanach}
    (hu : LatticeDivergenceFree u) :
    LatticeDivergenceFree (translationPhaseCarrier c t u) := by
  intro k
  rw [weightedLatticeCoefficient_translationPhaseCarrier,
    ComplexFrequencyHeatLeray.complexEuclideanPoint_smul, inner_smul_right,
    hu k, mul_zero]

theorem rawMeanCarrier_divergenceFree (c : Space) :
    LatticeDivergenceFree (rawMeanCarrier c) := by
  intro k
  by_cases hk : k = 0
  · subst k
    rw [latticeFrequency_zero, complexFrequency_zero, inner_zero_left]
  · rw [weightedLatticeCoefficient_rawMeanCarrier, if_neg hk]
    have hp : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
      ext i
      rfl
    rw [hp, inner_zero_right]

theorem meanRemovedCarrier_divergenceFree
    (c : Space) (t : ℝ) {u : WeightedLatticeBanach}
    (hu : LatticeDivergenceFree u) :
    LatticeDivergenceFree (meanRemovedCarrier c t u) :=
  LatticeDivergenceFree.sub
    (translationPhaseCarrier_divergenceFree c t hu)
    (rawMeanCarrier_divergenceFree c)

/-- If `c` is the physical mean encoded by the raw zero mode, the transformed
carrier is exactly mean-zero. -/
theorem meanRemovedCarrier_zero_mode
    (c : Space) (t : ℝ) (u : WeightedLatticeBanach)
    (hmean : u 0 = rawMeanCarrier c 0) :
    meanRemovedCarrier c t u 0 = 0 := by
  simp [meanRemovedCarrier, hmean]

theorem latticePairing_as_complex_inner (c : Space) (k : LatticeMode) :
    inner ℂ (complexFrequency (latticeFrequency k))
      (complexEuclideanPoint (complexOfReal c)) = (latticePairing c k : ℂ) := by
  rw [inner_complexFrequency]
  simp [latticePairing, complexOfReal, complexOfParts]

theorem spectralTransport_rawMean (c : Space) (k : LatticeMode)
    (w : ComplexSpace) :
    spectralTransport (latticeFrequency k)
        (rawFourierScale • complexOfReal c) w =
      (rawFourierScale * latticePairing c k) • w := by
  unfold spectralTransport
  rw [ComplexFrequencyHeatLeray.complexEuclideanPoint_smul,
    inner_smul_right, latticePairing_as_complex_inner]

theorem latticeSpectralTerm_rawMean_eq_single
    (c : Space) (k : LatticeMode) (u : WeightedLatticeBanach)
    (ij : LatticeMode × LatticeMode) :
    latticeSpectralTerm k (weightedLatticeCoefficient (rawMeanCarrier c))
        (weightedLatticeCoefficient u) ij =
      if ij = (0, k) then
        complexEuclideanPoint
          ((rawFourierScale * latticePairing c k) •
            weightedLatticeCoefficient u k)
      else 0 := by
  by_cases hpair : ij = (0, k)
  · subst ij
    rw [if_pos rfl, latticeSpectralTerm, if_pos (zero_add k),
      weightedLatticeCoefficient_rawMeanCarrier, if_pos rfl,
      spectralTransport_rawMean]
  · rw [if_neg hpair]
    by_cases hi : ij.1 = 0
    · have hj : ij.2 ≠ k := by
        intro hj
        apply hpair
        exact Prod.ext hi hj
      have hsum : ij.1 + ij.2 ≠ k := by simpa [hi] using hj
      rw [latticeSpectralTerm, if_neg hsum]
    · rw [latticeSpectralTerm]
      split_ifs
      · rw [weightedLatticeCoefficient_rawMeanCarrier, if_neg hi]
        unfold spectralTransport
        have hp : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
          ext i
          rfl
        rw [hp, inner_zero_right, zero_smul]
        exact hp
      · rfl

/-- The actual countable convolution with a constant physical mean in its
advecting slot is exactly the raw drift multiplier. -/
theorem weightedLatticeSpectralConvolution_rawMean_left
    (c : Space) (k : LatticeMode) (u : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k (rawMeanCarrier c) u =
      complexEuclideanPoint
        ((rawFourierScale * latticePairing c k) •
          weightedLatticeCoefficient u k) := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [show (fun ij => latticeSpectralTerm k
      (weightedLatticeCoefficient (rawMeanCarrier c))
      (weightedLatticeCoefficient u) ij) =
      fun ij => if ij = (0, k) then
        complexEuclideanPoint
          ((rawFourierScale * latticePairing c k) •
            weightedLatticeCoefficient u k) else 0 by
    funext ij
    exact latticeSpectralTerm_rawMean_eq_single c k u ij]
  rw [tsum_eq_single (0, k)]
  · simp
  · intro b hb
    simp [hb]

theorem latticeSpectralTerm_rawMean_right_zero
    (c : Space) (k : LatticeMode) (u : WeightedLatticeBanach)
    (ij : LatticeMode × LatticeMode) :
    latticeSpectralTerm k (weightedLatticeCoefficient u)
      (weightedLatticeCoefficient (rawMeanCarrier c)) ij = 0 := by
  rcases ij with ⟨i, j⟩
  by_cases hij : i + j = k
  · rw [latticeSpectralTerm, if_pos hij,
      weightedLatticeCoefficient_rawMeanCarrier]
    by_cases hj : j = 0
    · rw [if_pos hj]
      subst j
      unfold spectralTransport
      rw [latticeFrequency_zero, complexFrequency_zero, inner_zero_left,
        zero_smul]
      have hp : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
        ext i
        rfl
      exact hp
    · rw [if_neg hj]
      unfold spectralTransport
      have hp : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
        ext i
        rfl
      rw [smul_zero]
      exact hp
  · simp [latticeSpectralTerm, hij]

/-- The differentiated input is the second convolution slot, so a constant
mode there contributes exactly zero. -/
theorem weightedLatticeSpectralConvolution_rawMean_right
    (c : Space) (k : LatticeMode) (u : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k u (rawMeanCarrier c) = 0 := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [show (fun ij => latticeSpectralTerm k (weightedLatticeCoefficient u)
      (weightedLatticeCoefficient (rawMeanCarrier c)) ij) = fun _ => 0 by
    funext ij
    exact latticeSpectralTerm_rawMean_right_zero c k u ij]
  simp

theorem weightedLatticeSpectralConvolution_sub_left
    (k : LatticeMode) (u v z : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k (u - v) z =
      weightedLatticeSpectralConvolution k u z -
        weightedLatticeSpectralConvolution k v z := by
  exact (weightedLatticeSpectralCLM k z).map_sub u v

theorem weightedLatticeSpectralConvolution_sub_right
    (k : LatticeMode) (u v z : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k u (v - z) =
      weightedLatticeSpectralConvolution k u v -
        weightedLatticeSpectralConvolution k u z := by
  exact (weightedLatticeSpectralBilinear k u).map_sub v z

/-- Exact nonlinear identity for the mean-removed, translated carrier.  The
only surviving cross term is the raw drift multiplier supplied by the
zero-mode coefficient `-2π i c`. -/
theorem weightedLatticeSpectralConvolution_meanRemoved
    (c : Space) (t : ℝ) (k : LatticeMode) (u : WeightedLatticeBanach) :
    weightedLatticeSpectralConvolution k
        (meanRemovedCarrier c t u) (meanRemovedCarrier c t u) =
      physicalTranslationPhase c t k •
          weightedLatticeSpectralConvolution k u u -
        complexEuclideanPoint
          ((rawFourierScale * latticePairing c k) •
            weightedLatticeCoefficient (translationPhaseCarrier c t u) k) := by
  unfold meanRemovedCarrier
  rw [weightedLatticeSpectralConvolution_sub_left,
    weightedLatticeSpectralConvolution_sub_right,
    weightedLatticeSpectralConvolution_sub_right,
    weightedLatticeSpectralConvolution_translationPhase,
    weightedLatticeSpectralConvolution_rawMean_right,
    weightedLatticeSpectralConvolution_rawMean_left,
    weightedLatticeSpectralConvolution_rawMean_right]
  abel

theorem spectralOutputCoefficient_meanRemoved
    (c : Space) (t : ℝ) (k : LatticeMode) (u : WeightedLatticeBanach) :
    spectralOutputCoefficient k
        (meanRemovedCarrier c t u) (meanRemovedCarrier c t u) =
      physicalTranslationPhase c t k • spectralOutputCoefficient k u u -
        (rawFourierScale * latticePairing c k) •
          weightedLatticeCoefficient (translationPhaseCarrier c t u) k := by
  unfold spectralOutputCoefficient
  rw [weightedLatticeSpectralConvolution_meanRemoved,
    WithLp.ofLp_sub, WithLp.ofLp_smul]
  congr 1

end Navier.Analysis.CriticalMildMeanDriftRemoval

#check Navier.Analysis.CriticalMildMeanDriftRemoval.spectralOutputCoefficient_rawCarrierOfPhysical_eq
#check Navier.Analysis.CriticalMildMeanDriftRemoval.amplitudeOffZero_meanRemovedCarrier
#check Navier.Analysis.CriticalMildMeanDriftRemoval.offZeroSquareEnergy_meanRemovedCarrier
#check Navier.Analysis.CriticalMildMeanDriftRemoval.heatHalfGeneratorMoment_meanRemovedCarrier
#check Navier.Analysis.CriticalMildMeanDriftRemoval.weightedLatticeSpectralConvolution_meanRemoved
#check Navier.Analysis.CriticalMildMeanDriftRemoval.spectralOutputCoefficient_meanRemoved
#check Navier.Analysis.CriticalMildMeanDriftRemoval.translationRate_add_rawMeanDrift
#print axioms Navier.Analysis.CriticalMildMeanDriftRemoval.spectralOutputCoefficient_rawCarrierOfPhysical_eq
#print axioms Navier.Analysis.CriticalMildMeanDriftRemoval.amplitudeOffZero_meanRemovedCarrier
#print axioms Navier.Analysis.CriticalMildMeanDriftRemoval.offZeroSquareEnergy_meanRemovedCarrier
#print axioms Navier.Analysis.CriticalMildMeanDriftRemoval.heatHalfGeneratorMoment_meanRemovedCarrier
#print axioms Navier.Analysis.CriticalMildMeanDriftRemoval.weightedLatticeSpectralConvolution_meanRemoved
#print axioms Navier.Analysis.CriticalMildMeanDriftRemoval.spectralOutputCoefficient_meanRemoved
#print axioms Navier.Analysis.CriticalMildMeanDriftRemoval.translationRate_add_rawMeanDrift
