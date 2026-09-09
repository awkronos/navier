import Navier.Analysis.CriticalMildTimeJetMoments

/-!
# Second strong time derivative of the actual critical mild trajectory

The first derivative path is defined proof-independently as the sum of its
encoded lattice modes.  Positive-time spatial smoothing identifies it with
the completed derivative carrier and supplies uniform moments.  A second
smooth-series interchange then constructs the genuine second derivative in
the same Banach space.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped BigOperators ENNReal
open Set

namespace Navier.Analysis.CriticalMildSecondStrongDerivative

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildHigherUniformMoments
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.CriticalMildTimeJetInterchange
open Navier.Analysis.CriticalMildSecondTimeDerivative
open Navier.Analysis.CriticalMildTimeJetMoments

/-- Proof-independent completed first-derivative path obtained by summing the
actual mode ODE derivatives with the critical one-weight encoding. -/
def mildFirstDerivativePath
    (μ : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ) :
    WeightedLatticeBanach :=
  ∑' k : LatticeMode,
    lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
      (latticeModeWeight k • complexEuclideanPoint
        (mildRawTimeDerivative μ A t k))

/-- Whenever the order-one derivative moment is finite, the proof-independent
series is exactly the completed derivative carrier. -/
theorem mildFirstDerivativePath_eq_weightedTimeDerivativeCarrier
    (μ : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hD : TimeDerivativePolynomialMoment 1
      (mildRawTimeDerivative μ A t)) :
    mildFirstDerivativePath μ A t =
      weightedTimeDerivativeCarrier (mildRawTimeDerivative μ A t) hD := by
  exact tsum_single_weightedTimeDerivativeCarrier
    (mildRawTimeDerivative μ A t) hD

/-- The proof-independent first derivative path decodes to the literal mode
ODE derivative. -/
theorem weightedLatticeCoefficient_mildFirstDerivativePath
    (μ : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hD : TimeDerivativePolynomialMoment 1
      (mildRawTimeDerivative μ A t)) (k : LatticeMode) :
    weightedLatticeCoefficient (mildFirstDerivativePath μ A t) k =
      mildRawTimeDerivative μ A t k := by
  rw [mildFirstDerivativePath_eq_weightedTimeDerivativeCarrier μ A t hD,
    weightedLatticeCoefficient_weightedTimeDerivativeCarrier]

/-- The first derivative furnished by the actual positive-time mild equation
is the proof-independent path above. -/
theorem hasDerivAt_mildPath_eq_mildFirstDerivativePath
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R a T t : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a < T)
    (ht : t ∈ Ioo a T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1) :
    HasDerivAt A (mildFirstDerivativePath μ A t) t := by
  obtain ⟨hD, hderiv⟩ :=
    exists_hasDerivAt_mildPath_in_weightedCarrier
      μ hμ u₀ hu₀ A hAc hdiv hR ha haT hbound hmild t ht
  rw [mildFirstDerivativePath_eq_weightedTimeDerivativeCarrier μ A t hD]
  exact hderiv

private def complexEuclideanPointCLMReal :
    ComplexSpace →L[ℝ] ComplexE3 :=
  (ContinuousLinearEquiv.toContinuousLinearMap
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm).restrictScalars ℝ

/-- Every encoded first-derivative mode differentiates to its encoded second
mode derivative. -/
theorem hasDerivAt_single_mildRawTimeDerivative
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1)
    (V : WeightedLatticeBanach) (hA : HasDerivAt A V t)
    (k : LatticeMode) :
    HasDerivAt
      (fun r => lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
        (latticeModeWeight k • complexEuclideanPoint
          (mildRawTimeDerivative μ A r k)))
      (lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
        (latticeModeWeight k • complexEuclideanPoint
          (mildRawSecondTimeDerivative μ A V t k))) t := by
  have hmode := hasDerivAt_mildRawTimeDerivative
    μ hμ u₀ A hAc hdiv hR ht hbound hmild V hA k
  have hpoint : HasDerivAt
      (fun r => complexEuclideanPoint (mildRawTimeDerivative μ A r k))
      (complexEuclideanPoint (mildRawSecondTimeDerivative μ A V t k)) t := by
    change HasDerivAt
      (fun r => complexEuclideanPointCLMReal (mildRawTimeDerivative μ A r k))
      (complexEuclideanPointCLMReal
        (mildRawSecondTimeDerivative μ A V t k)) t
    exact complexEuclideanPointCLMReal.hasFDerivAt.comp_hasDerivAt t hmode
  have hweighted := hpoint.const_smul (latticeModeWeight k)
  let L := (lp.singleContinuousLinearMap ℂ
    (fun _ : LatticeMode => ComplexE3) 1 k).restrictScalars ℝ
  change HasDerivAt
    (fun r => L (latticeModeWeight k • complexEuclideanPoint
      (mildRawTimeDerivative μ A r k)))
    (L (latticeModeWeight k • complexEuclideanPoint
      (mildRawSecondTimeDerivative μ A V t k))) t
  exact L.hasFDerivAt.comp_hasDerivAt t hweighted

/-- Six extra second-derivative weights convert a total moment bound into a
single summable envelope, exactly as at the first time rung. -/
theorem secondTimeDerivativeMomentAmplitude_le_uniform_invSix
    (p μ M : ℝ) (A : ℝ → WeightedLatticeBanach)
    (V : WeightedLatticeBanach) (t : ℝ)
    (hhigh : SecondTimeDerivativePolynomialMoment (p + 6) μ A V t)
    (hM : secondTimeDerivativePolynomialMoment (p + 6) μ A V t ≤ M)
    (k : LatticeMode) :
    secondTimeDerivativeMomentAmplitude p μ A V t k ≤
      M * (latticeModeWeight k ^ 6)⁻¹ := by
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hterm : secondTimeDerivativeMomentAmplitude (p + 6) μ A V t k ≤
      secondTimeDerivativePolynomialMoment (p + 6) μ A V t := by
    unfold secondTimeDerivativePolynomialMoment
    have hs := hhigh.sum_le_tsum ({k} : Finset LatticeMode)
      (fun j _ => secondTimeDerivativeMomentAmplitude_nonneg
        (p + 6) μ A V t j)
    simpa using hs
  have heq : secondTimeDerivativeMomentAmplitude p μ A V t k =
      (latticeModeWeight k ^ 6)⁻¹ *
        secondTimeDerivativeMomentAmplitude (p + 6) μ A V t k := by
    unfold secondTimeDerivativeMomentAmplitude
    rw [Real.rpow_add hw]
    norm_num
    field_simp
  rw [heq]
  calc
    (latticeModeWeight k ^ 6)⁻¹ *
        secondTimeDerivativeMomentAmplitude (p + 6) μ A V t k ≤
      (latticeModeWeight k ^ 6)⁻¹ * M :=
        mul_le_mul_of_nonneg_left (hterm.trans hM)
          (inv_nonneg.mpr (pow_nonneg hw.le 6))
    _ = M * (latticeModeWeight k ^ 6)⁻¹ := by ring

/-- Budget obtained from a common high spatial-moment bound at the second
time rung. -/
def secondStrongDerivativeBudget (μ M : ℝ) : ℝ :=
  let C₁ := M ^ 2 + |μ| * M
  C₁ * M + M * C₁ + |μ| * C₁

/-- A uniform order-eleven spatial bound controls the order-seven second time
derivative, uniformly on the same interval. -/
theorem uniform_secondTimeDerivativeMoment_seven
    (μ M : ℝ) (A : ℝ → WeightedLatticeBanach) {S : Set ℝ}
    (hhigh : ∀ t ∈ S,
      LatticePolynomialMoment 11 (A t) ∧
        polynomialMoment 11 (A t) ≤ M) :
    ∀ t, t ∈ S →
      SecondTimeDerivativePolynomialMoment 7 μ A
          (mildFirstDerivativePath μ A t) t ∧
        secondTimeDerivativePolynomialMoment 7 μ A
          (mildFirstDerivativePath μ A t) t ≤
            secondStrongDerivativeBudget μ M := by
  intro t ht
  have hA11 := (hhigh t ht).1
  have hA10 : LatticePolynomialMoment 10 (A t) :=
    latticePolynomialMoment_mono (by norm_num) (A t) hA11
  have hA9 : LatticePolynomialMoment 9 (A t) :=
    latticePolynomialMoment_mono (by norm_num) (A t) hA11
  have hA8 : LatticePolynomialMoment 8 (A t) :=
    latticePolynomialMoment_mono (by norm_num) (A t) hA11
  have hA3 : LatticePolynomialMoment 3 (A t) :=
    latticePolynomialMoment_mono (by norm_num) (A t) hA11
  have hM10 : polynomialMoment 10 (A t) ≤ M :=
    (polynomialMoment_mono (by norm_num) (A t) hA11).trans (hhigh t ht).2
  have hM9 : polynomialMoment 9 (A t) ≤ M :=
    (polynomialMoment_mono (by norm_num) (A t) hA11).trans (hhigh t ht).2
  have hM8 : polynomialMoment 8 (A t) ≤ M :=
    (polynomialMoment_mono (by norm_num) (A t) hA11).trans (hhigh t ht).2
  have hA3' : LatticePolynomialMoment ((1 : ℝ) + 2) (A t) := by
    simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using hA3
  have hA10' : LatticePolynomialMoment ((8 : ℝ) + 2) (A t) := by
    simpa only [show (8 : ℝ) + 2 = 10 by norm_num] using hA10
  have hA11' : LatticePolynomialMoment ((9 : ℝ) + 2) (A t) := by
    simpa only [show (9 : ℝ) + 2 = 11 by norm_num] using hA11
  have hD1 : TimeDerivativePolynomialMoment 1
      (mildRawTimeDerivative μ A t) :=
    timeDerivativePolynomialMoment_mildRaw 1 μ (by norm_num) A t hA3'
  have hD8 : TimeDerivativePolynomialMoment 8
      (mildRawTimeDerivative μ A t) :=
    timeDerivativePolynomialMoment_mildRaw 8 μ (by norm_num) A t hA10'
  have hD9 : TimeDerivativePolynomialMoment 9
      (mildRawTimeDerivative μ A t) :=
    timeDerivativePolynomialMoment_mildRaw 9 μ (by norm_num) A t hA11'
  let C₁ : ℝ := M ^ 2 + |μ| * M
  have hD8bound : timeDerivativePolynomialMoment 8
      (mildRawTimeDerivative μ A t) ≤ C₁ := by
    refine (timeDerivativePolynomialMoment_mildRaw_le
      8 μ (by norm_num) A t hA10').trans ?_
    dsimp only [C₁]
    have hM9' : polynomialMoment ((8 : ℝ) + 1) (A t) ≤ M := by
      simpa only [show (8 : ℝ) + 1 = 9 by norm_num] using hM9
    have hM10' : polynomialMoment ((8 : ℝ) + 2) (A t) ≤ M := by
      simpa only [show (8 : ℝ) + 2 = 10 by norm_num] using hM10
    exact add_le_add
      (pow_le_pow_left₀
        (polynomialMoment_nonneg ((8 : ℝ) + 1) (A t)) hM9' 2)
      (mul_le_mul_of_nonneg_left hM10' (abs_nonneg μ))
  have hD9bound : timeDerivativePolynomialMoment 9
      (mildRawTimeDerivative μ A t) ≤ C₁ := by
    refine (timeDerivativePolynomialMoment_mildRaw_le
      9 μ (by norm_num) A t hA11').trans ?_
    dsimp only [C₁]
    have hM10' : polynomialMoment ((9 : ℝ) + 1) (A t) ≤ M := by
      simpa only [show (9 : ℝ) + 1 = 10 by norm_num] using hM10
    have hM11' : polynomialMoment ((9 : ℝ) + 2) (A t) ≤ M := by
      simpa only [show (9 : ℝ) + 2 = 11 by norm_num] using (hhigh t ht).2
    exact add_le_add
      (pow_le_pow_left₀
        (polynomialMoment_nonneg ((9 : ℝ) + 1) (A t)) hM10' 2)
      (mul_le_mul_of_nonneg_left hM11' (abs_nonneg μ))
  have hV8 : LatticePolynomialMoment 8 (mildFirstDerivativePath μ A t) := by
    rw [mildFirstDerivativePath_eq_weightedTimeDerivativeCarrier μ A t hD1]
    exact latticePolynomialMoment_weightedTimeDerivativeCarrier 8
      (mildRawTimeDerivative μ A t) hD1 hD8
  have hV8bound : polynomialMoment 8 (mildFirstDerivativePath μ A t) ≤ C₁ := by
    rw [mildFirstDerivativePath_eq_weightedTimeDerivativeCarrier μ A t hD1,
      polynomialMoment_weightedTimeDerivativeCarrier]
    exact hD8bound
  have hA8' : LatticePolynomialMoment ((7 : ℝ) + 1) (A t) := by
    simpa only [show (7 : ℝ) + 1 = 8 by norm_num] using hA8
  have hV8' : LatticePolynomialMoment ((7 : ℝ) + 1)
      (mildFirstDerivativePath μ A t) := by
    simpa only [show (7 : ℝ) + 1 = 8 by norm_num] using hV8
  have hD9' : TimeDerivativePolynomialMoment ((7 : ℝ) + 2)
      (mildRawTimeDerivative μ A t) := by
    simpa only [show (7 : ℝ) + 2 = 9 by norm_num] using hD9
  have hsecond := summable_secondTimeDerivativePolynomialMoment
    7 μ (by norm_num) A (mildFirstDerivativePath μ A t) t hA8' hV8' hD9'
  refine ⟨hsecond, (secondTimeDerivativePolynomialMoment_le
    7 μ (by norm_num) A (mildFirstDerivativePath μ A t) t
      hA8' hV8' hD9').trans ?_⟩
  unfold secondStrongDerivativeBudget
  dsimp only
  have hV8bound' : polynomialMoment ((7 : ℝ) + 1)
      (mildFirstDerivativePath μ A t) ≤ M ^ 2 + |μ| * M := by
    simpa only [C₁, show (7 : ℝ) + 1 = 8 by norm_num] using hV8bound
  have hM8' : polynomialMoment ((7 : ℝ) + 1) (A t) ≤ M := by
    simpa only [show (7 : ℝ) + 1 = 8 by norm_num] using hM8
  have hD9bound' : timeDerivativePolynomialMoment ((7 : ℝ) + 2)
      (mildRawTimeDerivative μ A t) ≤ M ^ 2 + |μ| * M := by
    simpa only [C₁, show (7 : ℝ) + 2 = 9 by norm_num] using hD9bound
  have hC₁nonneg : 0 ≤ M ^ 2 + |μ| * M :=
    (polynomialMoment_nonneg ((7 : ℝ) + 1)
      (mildFirstDerivativePath μ A t)).trans hV8bound'
  have hMnonneg : 0 ≤ M :=
    (polynomialMoment_nonneg ((7 : ℝ) + 1) (A t)).trans hM8'
  exact add_le_add
    (add_le_add
      (mul_le_mul hV8bound' hM8'
        (polynomialMoment_nonneg ((7 : ℝ) + 1) (A t))
        hC₁nonneg)
      (mul_le_mul hM8' hV8bound'
        (polynomialMoment_nonneg ((7 : ℝ) + 1)
          (mildFirstDerivativePath μ A t))
        hMnonneg))
    (mul_le_mul_of_nonneg_left hD9bound' (abs_nonneg μ))

theorem secondTimeDerivativeMomentAmplitude_mono
    {p q : ℝ} (hpq : p ≤ q) (μ : ℝ)
    (A : ℝ → WeightedLatticeBanach) (V : WeightedLatticeBanach)
    (t : ℝ) (k : LatticeMode) :
    secondTimeDerivativeMomentAmplitude p μ A V t k ≤
      secondTimeDerivativeMomentAmplitude q μ A V t k := by
  unfold secondTimeDerivativeMomentAmplitude
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (one_le_latticeModeWeight k) hpq)
    (norm_nonneg _)

theorem secondTimeDerivativePolynomialMoment_mono
    {p q : ℝ} (hpq : p ≤ q) (μ : ℝ)
    (A : ℝ → WeightedLatticeBanach) (V : WeightedLatticeBanach)
    (t : ℝ) (hV : SecondTimeDerivativePolynomialMoment q μ A V t) :
    SecondTimeDerivativePolynomialMoment p μ A V t :=
  hV.of_nonneg_of_le
    (secondTimeDerivativeMomentAmplitude_nonneg p μ A V t)
    (secondTimeDerivativeMomentAmplitude_mono hpq μ A V t)

/-- Uniform summable single-mode envelope for the second derivative series. -/
theorem uniform_secondTimeDerivative_envelope_one
    (μ M : ℝ) (A : ℝ → WeightedLatticeBanach) {S : Set ℝ}
    (hhigh : ∀ t ∈ S,
      LatticePolynomialMoment 11 (A t) ∧
        polynomialMoment 11 (A t) ≤ M) :
    ∀ k t, t ∈ S →
      secondTimeDerivativeMomentAmplitude 1 μ A
          (mildFirstDerivativePath μ A t) t k ≤
        secondStrongDerivativeBudget μ M *
          (latticeModeWeight k ^ 6)⁻¹ := by
  intro k t ht
  have hseven := uniform_secondTimeDerivativeMoment_seven μ M A hhigh t ht
  exact secondTimeDerivativeMomentAmplitude_le_uniform_invSix
    1 μ (secondStrongDerivativeBudget μ M) A
      (mildFirstDerivativePath μ A t) t (by
        simpa only [show (1 : ℝ) + 6 = 7 by norm_num] using hseven.1) (by
        simpa only [show (1 : ℝ) + 6 = 7 by norm_num] using hseven.2) k

/-- A uniform order-eleven bound performs the second infinite-series
interchange and constructs a genuine second derivative in the completed
critical carrier. -/
theorem exists_hasDerivAt_mildFirstDerivativePath_of_uniform_eleven
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R a T M t : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a < T)
    (ht : t ∈ Ioo a T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1)
    (hhigh : ∀ s ∈ Ioo a T,
      LatticePolynomialMoment 11 (A s) ∧
        polynomialMoment 11 (A s) ≤ M) :
    ∃ hD₂ : TimeDerivativePolynomialMoment 1
        (mildRawSecondTimeDerivative μ A
          (mildFirstDerivativePath μ A t) t),
      HasDerivAt (mildFirstDerivativePath μ A)
        (weightedTimeDerivativeCarrier
          (mildRawSecondTimeDerivative μ A
            (mildFirstDerivativePath μ A t) t) hD₂) t := by
  have hseven := uniform_secondTimeDerivativeMoment_seven μ M A hhigh t ht
  have hsecondOne : SecondTimeDerivativePolynomialMoment 1 μ A
      (mildFirstDerivativePath μ A t) t :=
    secondTimeDerivativePolynomialMoment_mono (by norm_num) μ A
      (mildFirstDerivativePath μ A t) t hseven.1
  have hD₂ : TimeDerivativePolynomialMoment 1
      (mildRawSecondTimeDerivative μ A
        (mildFirstDerivativePath μ A t) t) := by
    change Summable (timeDerivativeMomentAmplitude 1
      (mildRawSecondTimeDerivative μ A
        (mildFirstDerivativePath μ A t) t))
    change Summable (secondTimeDerivativeMomentAmplitude 1 μ A
      (mildFirstDerivativePath μ A t) t) at hsecondOne
    apply hsecondOne.congr
    intro k
    rfl
  refine ⟨hD₂, ?_⟩
  let majorant : LatticeMode → ℝ := fun k =>
    secondStrongDerivativeBudget μ M * (latticeModeWeight k ^ 6)⁻¹
  have hmajorant : Summable majorant :=
    summable_uniform_invSixEnvelope (secondStrongDerivativeBudget μ M)
  let g : LatticeMode → ℝ → WeightedLatticeBanach := fun k r =>
    lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
      (latticeModeWeight k • complexEuclideanPoint
        (mildRawTimeDerivative μ A r k))
  let g' : LatticeMode → ℝ → WeightedLatticeBanach := fun k r =>
    lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
      (latticeModeWeight k • complexEuclideanPoint
        (mildRawSecondTimeDerivative μ A
          (mildFirstDerivativePath μ A r) r k))
  have hg : ∀ k r, r ∈ Ioo a T → HasDerivAt (g k) (g' k r) r := by
    intro k r hr
    have hAr := hasDerivAt_mildPath_eq_mildFirstDerivativePath
      μ hμ u₀ hu₀ A hAc hdiv hR ha haT hr hbound hmild
    exact hasDerivAt_single_mildRawTimeDerivative
      μ hμ u₀ A hAc hdiv hR ⟨ha.trans hr.1, hr.2⟩
        hbound hmild (mildFirstDerivativePath μ A r) hAr k
  have hg' : ∀ k r, r ∈ Ioo a T → ‖g' k r‖ ≤ majorant k := by
    intro k r hr
    have henv := uniform_secondTimeDerivative_envelope_one
      μ M A hhigh k r hr
    dsimp only [g', majorant]
    rw [lp.norm_single (by norm_num : 0 < (1 : ENNReal)),
      norm_smul,
      Real.norm_of_nonneg
        (zero_le_one.trans (one_le_latticeModeWeight k))]
    simpa only [secondTimeDerivativeMomentAmplitude, Real.rpow_one,
      complexEuclideanNorm] using henv
  have hA3 : LatticePolynomialMoment ((1 : ℝ) + 2) (A t) :=
    latticePolynomialMoment_mono (by norm_num) (A t) (hhigh t ht).1
  have hD1 : TimeDerivativePolynomialMoment 1
      (mildRawTimeDerivative μ A t) :=
    timeDerivativePolynomialMoment_mildRaw 1 μ (by norm_num) A t hA3
  have hg0 : Summable fun k => g k t := by
    have hs := (lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
      (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤)
      (weightedTimeDerivativeCarrier (mildRawTimeDerivative μ A t) hD1)).summable
    apply hs.congr
    intro k
    rfl
  have hseries := hasDerivAt_tsum_of_isPreconnected
    hmajorant isOpen_Ioo ordConnected_Ioo.isPreconnected hg hg' ht hg0 ht
  have hsumD₂ : (∑' k, g' k t) =
      weightedTimeDerivativeCarrier
        (mildRawSecondTimeDerivative μ A
          (mildFirstDerivativePath μ A t) t) hD₂ := by
    exact tsum_single_weightedTimeDerivativeCarrier
      (mildRawSecondTimeDerivative μ A
        (mildFirstDerivativePath μ A t) t) hD₂
  change HasDerivAt (mildFirstDerivativePath μ A)
    (weightedTimeDerivativeCarrier
      (mildRawSecondTimeDerivative μ A
        (mildFirstDerivativePath μ A t) t) hD₂) t
  rw [← hsumD₂]
  exact hseries

/-- **Actual second strong time derivative on every compact positive-time
interior.** The order-eleven hypothesis of the interchange theorem is
constructed here from the native all-order spatial bootstrap, starting only
from the bounded mild trajectory. -/
theorem exists_hasDerivAt_mildFirstDerivativePath
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R a T : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a < T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1) :
    ∀ t ∈ Ioo a T,
      ∃ hD₂ : TimeDerivativePolynomialMoment 1
          (mildRawSecondTimeDerivative μ A
            (mildFirstDerivativePath μ A t) t),
        HasDerivAt (mildFirstDerivativePath μ A)
          (weightedTimeDerivativeCarrier
            (mildRawSecondTimeDerivative μ A
              (mildFirstDerivativePath μ A t) t) hD₂) t := by
  obtain ⟨B, hBnonneg, hB⟩ :=
    exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval
      μ hμ u₀ hu₀ A hAc hdiv hR ha haT.le hbound hmild
  have hhigh : ∀ s ∈ Ioo a T,
      LatticePolynomialMoment 11 (A s) ∧
        polynomialMoment 11 (A s) ≤ B 18 := by
    intro s hs
    have h := hB 18 s ⟨hs.1.le, hs.2.le⟩
    norm_num [iteratedHalfOrder] at h ⊢
    exact h
  intro t ht
  exact exists_hasDerivAt_mildFirstDerivativePath_of_uniform_eleven
    μ hμ u₀ hu₀ A hAc hdiv hR ha haT ht hbound hmild hhigh

end Navier.Analysis.CriticalMildSecondStrongDerivative
