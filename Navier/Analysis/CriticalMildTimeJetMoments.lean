import Navier.Analysis.CriticalMildSecondTimeDerivative

/-!
# Polynomial moments for time-jet carriers

The first time derivative is already a genuine element of the completed
critical carrier.  This module transports arbitrary spatial moments through
that encoding and proves the reusable two-slot moment estimate for the
differentiated quadratic forcing.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal

namespace Navier.Analysis.CriticalMildTimeJetMoments

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.CriticalMildTimeJetInterchange
open Navier.Analysis.CriticalMildSecondTimeDerivative

/-- The weighted carrier encoding preserves every polynomial spatial moment
of the decoded derivative family exactly. -/
theorem polynomialMomentAmplitude_weightedTimeDerivativeCarrier
    (p : ℝ) (D : LatticeMode → ComplexSpace)
    (hD : TimeDerivativePolynomialMoment 1 D) (k : LatticeMode) :
    polynomialMomentAmplitude p (weightedTimeDerivativeCarrier D hD) k =
      timeDerivativeMomentAmplitude p D k := by
  unfold polynomialMomentAmplitude timeDerivativeMomentAmplitude
  rw [weightedLatticeCoefficient_weightedTimeDerivativeCarrier]

/-- Any finite derivative moment therefore becomes the identical spatial
moment of its completed carrier. -/
theorem latticePolynomialMoment_weightedTimeDerivativeCarrier
    (p : ℝ) (D : LatticeMode → ComplexSpace)
    (hD : TimeDerivativePolynomialMoment 1 D)
    (hp : TimeDerivativePolynomialMoment p D) :
    LatticePolynomialMoment p (weightedTimeDerivativeCarrier D hD) := by
  apply hp.congr
  intro k
  exact (polynomialMomentAmplitude_weightedTimeDerivativeCarrier p D hD k).symm

/-- Quantitative form of the moment-preserving carrier transport. -/
theorem polynomialMoment_weightedTimeDerivativeCarrier
    (p : ℝ) (D : LatticeMode → ComplexSpace)
    (hD : TimeDerivativePolynomialMoment 1 D) :
    polynomialMoment p (weightedTimeDerivativeCarrier D hD) =
      timeDerivativePolynomialMoment p D := by
  unfold polynomialMoment timeDerivativePolynomialMoment
  apply tsum_congr
  intro k
  exact polynomialMomentAmplitude_weightedTimeDerivativeCarrier p D hD k

/-- The differentiated projected forcing is exactly the sum of the two
ordered projected convolution coefficients. -/
theorem projectedModeForcingCarrierDerivative_eq
    (A V : WeightedLatticeBanach) (k : LatticeMode) :
    projectedModeForcingCarrierDerivative A V k =
      projectedSpectralConvolutionCoefficient k V A +
        projectedSpectralConvolutionCoefficient k A V := by
  apply complexEuclideanPoint_injective
  unfold projectedModeForcingCarrierDerivative
  change complexEuclideanLeray (latticeFrequency k)
      (weightedLatticeSpectralBilinear k V A +
        weightedLatticeSpectralBilinear k A V) =
    complexEuclideanPoint
      (projectedSpectralConvolutionCoefficient k V A +
        projectedSpectralConvolutionCoefficient k A V)
  rw [map_add]
  unfold projectedSpectralConvolutionCoefficient spectralOutputCoefficient
  change complexEuclideanLeray (latticeFrequency k)
        (weightedLatticeSpectralBilinear k V A) +
      complexEuclideanLeray (latticeFrequency k)
        (weightedLatticeSpectralBilinear k A V) =
    complexEuclideanPoint
        (complexLeray (latticeFrequency k)
          (WithLp.ofLp (weightedLatticeSpectralBilinear k V A))) +
      complexEuclideanPoint
        (complexLeray (latticeFrequency k)
          (WithLp.ofLp (weightedLatticeSpectralBilinear k A V)))
  rw [complexEuclideanPoint_complexLeray,
    complexEuclideanPoint_complexLeray]
  rfl

/-- Order-`p` density of the differentiated quadratic forcing. -/
def forcingDerivativeMomentAmplitude
    (p : ℝ) (A V : WeightedLatticeBanach) (k : LatticeMode) : ℝ :=
  latticeModeWeight k ^ p *
    complexEuclideanNorm (projectedModeForcingCarrierDerivative A V k)

def ForcingDerivativePolynomialMoment
    (p : ℝ) (A V : WeightedLatticeBanach) : Prop :=
  Summable (forcingDerivativeMomentAmplitude p A V)

def forcingDerivativePolynomialMoment
    (p : ℝ) (A V : WeightedLatticeBanach) : ℝ :=
  ∑' k, forcingDerivativeMomentAmplitude p A V k

/-- Pointwise two-slot majorization before summing output modes. -/
theorem forcingDerivativeMomentAmplitude_le
    (p : ℝ) (A V : WeightedLatticeBanach) (k : LatticeMode) :
    forcingDerivativeMomentAmplitude p A V k ≤
      latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedSpectralConvolutionCoefficient k V A) +
        latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedSpectralConvolutionCoefficient k A V) := by
  unfold forcingDerivativeMomentAmplitude
  rw [projectedModeForcingCarrierDerivative_eq]
  have hn : complexEuclideanNorm
      (projectedSpectralConvolutionCoefficient k V A +
        projectedSpectralConvolutionCoefficient k A V) ≤
      complexEuclideanNorm (projectedSpectralConvolutionCoefficient k V A) +
        complexEuclideanNorm (projectedSpectralConvolutionCoefficient k A V) := by
    unfold complexEuclideanNorm
    change ‖complexEuclideanPoint (projectedSpectralConvolutionCoefficient k V A) +
        complexEuclideanPoint (projectedSpectralConvolutionCoefficient k A V)‖ ≤ _
    exact norm_add_le _ _
  calc
    latticeModeWeight k ^ p * complexEuclideanNorm
        (projectedSpectralConvolutionCoefficient k V A +
          projectedSpectralConvolutionCoefficient k A V) ≤
      latticeModeWeight k ^ p *
        (complexEuclideanNorm (projectedSpectralConvolutionCoefficient k V A) +
          complexEuclideanNorm (projectedSpectralConvolutionCoefficient k A V)) :=
      mul_le_mul_of_nonneg_left hn
        (Real.rpow_nonneg
          (zero_le_one.trans (one_le_latticeModeWeight k)) p)
    _ = _ := by ring

/-- Both inputs at order `s` give the differentiated forcing order `s-1`.
This is the reusable summability recurrence for higher time jets. -/
theorem summable_forcingDerivativePolynomialMoment_sub_one
    (s : ℝ) (hs : 1 ≤ s) (A V : WeightedLatticeBanach)
    (hA : LatticePolynomialMoment s A)
    (hV : LatticePolynomialMoment s V) :
    ForcingDerivativePolynomialMoment (s - 1) A V := by
  have hVA := summable_projectedConvolutionPolynomialMoment
    s hs V A hV hA
  have hAV := summable_projectedConvolutionPolynomialMoment
    s hs A V hA hV
  exact (hVA.add hAV).of_nonneg_of_le
    (fun k => mul_nonneg
      (Real.rpow_nonneg
        (zero_le_one.trans (one_le_latticeModeWeight k)) (s - 1))
      (norm_nonneg _))
    (forcingDerivativeMomentAmplitude_le (s - 1) A V)

/-- Quantitative `S_s × S_s → S_(s-1)` bound for the two differentiated
convolution slots. -/
theorem forcingDerivativePolynomialMoment_sub_one_le
    (s : ℝ) (hs : 1 ≤ s) (A V : WeightedLatticeBanach)
    (hA : LatticePolynomialMoment s A)
    (hV : LatticePolynomialMoment s V) :
    forcingDerivativePolynomialMoment (s - 1) A V ≤
      polynomialMoment s V * polynomialMoment s A +
        polynomialMoment s A * polynomialMoment s V := by
  have hVA := summable_projectedConvolutionPolynomialMoment
    s hs V A hV hA
  have hAV := summable_projectedConvolutionPolynomialMoment
    s hs A V hA hV
  have hsum := hVA.add hAV
  unfold forcingDerivativePolynomialMoment
  calc
    (∑' k, forcingDerivativeMomentAmplitude (s - 1) A V k) ≤
        ∑' k, (latticeModeWeight k ^ (s - 1) *
          complexEuclideanNorm (projectedSpectralConvolutionCoefficient k V A) +
          latticeModeWeight k ^ (s - 1) *
          complexEuclideanNorm (projectedSpectralConvolutionCoefficient k A V)) :=
      (summable_forcingDerivativePolynomialMoment_sub_one
        s hs A V hA hV).tsum_le_tsum
          (forcingDerivativeMomentAmplitude_le (s - 1) A V) hsum
    _ = projectedConvolutionPolynomialMoment (s - 1) V A +
        projectedConvolutionPolynomialMoment (s - 1) A V := by
      rw [hVA.tsum_add hAV]
      rfl
    _ ≤ polynomialMoment s V * polynomialMoment s A +
        polynomialMoment s A * polynomialMoment s V :=
      add_le_add
        (projectedConvolutionPolynomialMoment_sub_one_le s hs V A hV hA)
        (projectedConvolutionPolynomialMoment_sub_one_le s hs A V hA hV)

/-- Order-`p` density of the second raw time derivative. -/
def secondTimeDerivativeMomentAmplitude
    (p μ : ℝ) (A : ℝ → WeightedLatticeBanach)
    (V : WeightedLatticeBanach) (t : ℝ) (k : LatticeMode) : ℝ :=
  latticeModeWeight k ^ p *
    complexEuclideanNorm (mildRawSecondTimeDerivative μ A V t k)

def SecondTimeDerivativePolynomialMoment
    (p μ : ℝ) (A : ℝ → WeightedLatticeBanach)
    (V : WeightedLatticeBanach) (t : ℝ) : Prop :=
  Summable (secondTimeDerivativeMomentAmplitude p μ A V t)

def secondTimeDerivativePolynomialMoment
    (p μ : ℝ) (A : ℝ → WeightedLatticeBanach)
    (V : WeightedLatticeBanach) (t : ℝ) : ℝ :=
  ∑' k, secondTimeDerivativeMomentAmplitude p μ A V t k

theorem secondTimeDerivativeMomentAmplitude_nonneg
    (p μ : ℝ) (A : ℝ → WeightedLatticeBanach)
    (V : WeightedLatticeBanach) (t : ℝ) (k : LatticeMode) :
    0 ≤ secondTimeDerivativeMomentAmplitude p μ A V t k :=
  mul_nonneg (Real.rpow_nonneg
    (zero_le_one.trans (one_le_latticeModeWeight k)) p) (norm_nonneg _)

/-- Pointwise recurrence bound: one convolution weight or two generator
weights are lost in taking the next time derivative. -/
theorem secondTimeDerivativeMomentAmplitude_le
    (p μ : ℝ) (A : ℝ → WeightedLatticeBanach)
    (V : WeightedLatticeBanach) (t : ℝ) (k : LatticeMode) :
    secondTimeDerivativeMomentAmplitude p μ A V t k ≤
      forcingDerivativeMomentAmplitude p (A t) V k +
        |μ| * timeDerivativeMomentAmplitude (p + 2)
          (mildRawTimeDerivative μ A t) k := by
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hdecay := abs_rawModeDecayRate_le_weight_sq μ k
  unfold secondTimeDerivativeMomentAmplitude mildRawSecondTimeDerivative
  unfold forcingDerivativeMomentAmplitude
  calc
    latticeModeWeight k ^ p * complexEuclideanNorm
        (projectedModeForcingCarrierDerivative (A t) V k -
          (rawModeDecayRate μ k : ℂ) • mildRawTimeDerivative μ A t k) ≤
      latticeModeWeight k ^ p *
        (complexEuclideanNorm (projectedModeForcingCarrierDerivative (A t) V k) +
          |rawModeDecayRate μ k| *
            complexEuclideanNorm (mildRawTimeDerivative μ A t k)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hw.le p)
      unfold complexEuclideanNorm
      change ‖complexEuclideanPoint
          (projectedModeForcingCarrierDerivative (A t) V k) -
        (rawModeDecayRate μ k : ℂ) •
          complexEuclideanPoint (mildRawTimeDerivative μ A t k)‖ ≤ _
      calc
        _ ≤ ‖complexEuclideanPoint
              (projectedModeForcingCarrierDerivative (A t) V k)‖ +
            ‖(rawModeDecayRate μ k : ℂ) •
              complexEuclideanPoint (mildRawTimeDerivative μ A t k)‖ :=
          norm_sub_le _ _
        _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedModeForcingCarrierDerivative (A t) V k) +
        latticeModeWeight k ^ p *
          ((|μ| * latticeModeWeight k ^ 2) *
            complexEuclideanNorm (mildRawTimeDerivative μ A t k)) := by
      rw [mul_add]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdecay (norm_nonneg _))
          (Real.rpow_nonneg hw.le p))
    _ = latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedModeForcingCarrierDerivative (A t) V k) +
        |μ| * timeDerivativeMomentAmplitude (p + 2)
          (mildRawTimeDerivative μ A t) k := by
      unfold timeDerivativeMomentAmplitude
      rw [Real.rpow_add hw, Real.rpow_two]
      ring

/-- Reusable summability recurrence for the second derivative. -/
theorem summable_secondTimeDerivativePolynomialMoment
    (p μ : ℝ) (hp : 0 ≤ p)
    (A : ℝ → WeightedLatticeBanach) (V : WeightedLatticeBanach) (t : ℝ)
    (hA : LatticePolynomialMoment (p + 1) (A t))
    (hV : LatticePolynomialMoment (p + 1) V)
    (hD : TimeDerivativePolynomialMoment (p + 2)
      (mildRawTimeDerivative μ A t)) :
    SecondTimeDerivativePolynomialMoment p μ A V t := by
  have hforcing : ForcingDerivativePolynomialMoment p (A t) V := by
    have h := summable_forcingDerivativePolynomialMoment_sub_one
      (p + 1) (by linarith) (A t) V hA hV
    simpa only [show p + 1 - 1 = p by ring] using h
  have hvisc : Summable fun k => |μ| *
      timeDerivativeMomentAmplitude (p + 2)
        (mildRawTimeDerivative μ A t) k := hD.mul_left |μ|
  exact (hforcing.add hvisc).of_nonneg_of_le
    (secondTimeDerivativeMomentAmplitude_nonneg p μ A V t)
    (secondTimeDerivativeMomentAmplitude_le p μ A V t)

/-- Quantitative second-derivative recurrence used for locally uniform jet
majorants. -/
theorem secondTimeDerivativePolynomialMoment_le
    (p μ : ℝ) (hp : 0 ≤ p)
    (A : ℝ → WeightedLatticeBanach) (V : WeightedLatticeBanach) (t : ℝ)
    (hA : LatticePolynomialMoment (p + 1) (A t))
    (hV : LatticePolynomialMoment (p + 1) V)
    (hD : TimeDerivativePolynomialMoment (p + 2)
      (mildRawTimeDerivative μ A t)) :
    secondTimeDerivativePolynomialMoment p μ A V t ≤
      polynomialMoment (p + 1) V * polynomialMoment (p + 1) (A t) +
        polynomialMoment (p + 1) (A t) * polynomialMoment (p + 1) V +
        |μ| * timeDerivativePolynomialMoment (p + 2)
          (mildRawTimeDerivative μ A t) := by
  have hforcing : ForcingDerivativePolynomialMoment p (A t) V := by
    have h := summable_forcingDerivativePolynomialMoment_sub_one
      (p + 1) (by linarith) (A t) V hA hV
    simpa only [show p + 1 - 1 = p by ring] using h
  have hvisc : Summable fun k => |μ| *
      timeDerivativeMomentAmplitude (p + 2)
        (mildRawTimeDerivative μ A t) k := hD.mul_left |μ|
  unfold secondTimeDerivativePolynomialMoment
  calc
    (∑' k, secondTimeDerivativeMomentAmplitude p μ A V t k) ≤
        ∑' k, (forcingDerivativeMomentAmplitude p (A t) V k +
          |μ| * timeDerivativeMomentAmplitude (p + 2)
            (mildRawTimeDerivative μ A t) k) :=
      (summable_secondTimeDerivativePolynomialMoment
        p μ hp A V t hA hV hD).tsum_le_tsum
          (secondTimeDerivativeMomentAmplitude_le p μ A V t)
          (hforcing.add hvisc)
    _ = forcingDerivativePolynomialMoment p (A t) V +
        |μ| * timeDerivativePolynomialMoment (p + 2)
          (mildRawTimeDerivative μ A t) := by
      rw [hforcing.tsum_add hvisc, tsum_mul_left]
      rfl
    _ ≤ polynomialMoment (p + 1) V * polynomialMoment (p + 1) (A t) +
        polynomialMoment (p + 1) (A t) * polynomialMoment (p + 1) V +
        |μ| * timeDerivativePolynomialMoment (p + 2)
          (mildRawTimeDerivative μ A t) := by
      gcongr
      simpa only [show p + 1 - 1 = p by ring] using
        forcingDerivativePolynomialMoment_sub_one_le
          (p + 1) (by linarith) (A t) V hA hV

end Navier.Analysis.CriticalMildTimeJetMoments

#print axioms Navier.Analysis.CriticalMildTimeJetMoments.latticePolynomialMoment_weightedTimeDerivativeCarrier
#print axioms Navier.Analysis.CriticalMildTimeJetMoments.polynomialMoment_weightedTimeDerivativeCarrier
#print axioms Navier.Analysis.CriticalMildTimeJetMoments.projectedModeForcingCarrierDerivative_eq
#print axioms Navier.Analysis.CriticalMildTimeJetMoments.forcingDerivativePolynomialMoment_sub_one_le
#print axioms Navier.Analysis.CriticalMildTimeJetMoments.summable_secondTimeDerivativePolynomialMoment
#print axioms Navier.Analysis.CriticalMildTimeJetMoments.secondTimeDerivativePolynomialMoment_le
