import Navier.Analysis.CriticalMildHigherUniformMoments
import Navier.Analysis.PeriodicDatumFourierBridge

/-!
# Time-jet interchange for the actual periodic mild trajectory

This module builds the summable, time-independent lattice envelopes required
to turn modewise mild derivatives into derivatives in the completed carrier.
The six-weight reserve is harmless because positive-time smoothing now gives
uniform moments of every finite order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators ENNReal
open Set Filter

namespace Navier.Analysis.CriticalMildTimeJetInterchange

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildHigherUniformMoments
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.PeriodicDatumFourierBridge

/-- Each integer coordinate factor is controlled by the inhomogeneous
Euclidean lattice weight. -/
theorem one_add_abs_first_le_latticeModeWeight (k : LatticeMode) :
    1 + |(k.1 : ℝ)| ≤ latticeModeWeight k := by
  unfold latticeModeWeight
  have h := PiLp.norm_apply_le
    (complexFrequency (latticeFrequency k)) (0 : Fin 3)
  have h' : |(k.1 : ℝ)| ≤ ‖complexFrequency (latticeFrequency k)‖ := by
    simpa [complexFrequency, latticeFrequency,
      Navier.Analysis.ComplexLerayProjection.complexOfReal,
      Navier.Analysis.ComplexLerayProjection.complexOfParts] using h
  simpa [add_comm] using add_le_add_left h' 1

theorem torusWeight_le_two_mul_latticeModeWeight (k : LatticeMode) :
    Navier.Construction.TorusInverse.weight k.2 ≤ 2 * latticeModeWeight k := by
  have hy := PiLp.norm_apply_le
    (complexFrequency (latticeFrequency k)) (1 : Fin 3)
  have hz := PiLp.norm_apply_le
    (complexFrequency (latticeFrequency k)) (2 : Fin 3)
  unfold Navier.Construction.TorusInverse.weight latticeModeWeight
  have hy' : |(k.2.1 : ℝ)| ≤ ‖complexFrequency (latticeFrequency k)‖ := by
    simpa [complexFrequency, latticeFrequency, complexEuclideanNorm,
      complexEuclideanPoint,
      Navier.Analysis.ComplexLerayProjection.complexOfReal,
      Navier.Analysis.ComplexLerayProjection.complexOfParts] using hy
  have hz' : |(k.2.2 : ℝ)| ≤ ‖complexFrequency (latticeFrequency k)‖ := by
    simpa [complexFrequency, latticeFrequency, complexEuclideanNorm,
      complexEuclideanPoint,
      Navier.Analysis.ComplexLerayProjection.complexOfReal,
      Navier.Analysis.ComplexLerayProjection.complexOfParts] using hz
  linarith [norm_nonneg (complexFrequency (latticeFrequency k))]

/-- Six inverse powers of the native radial lattice weight form a summable
family on `ℤ³`. -/
theorem summable_latticeModeWeight_inv_pow_six :
    Summable fun k : LatticeMode => (latticeModeWeight k ^ 6)⁻¹ := by
  let g : LatticeMode → ℝ := fun k =>
    16 * (((1 + |(k.1 : ℝ)|) ^ 2)⁻¹ *
      (Navier.Construction.TorusInverse.weight k.2 ^ 4)⁻¹)
  have hg : Summable g := by
    simpa only [g] using summable_productWeightTail.mul_left 16
  apply hg.of_nonneg_of_le
  · intro k
    exact inv_nonneg.mpr (pow_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight k)) 6)
  · intro k
    have hw : 0 < latticeModeWeight k :=
      lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
    have hx : 0 < 1 + |(k.1 : ℝ)| := by positivity
    have hyz : 0 < Navier.Construction.TorusInverse.weight k.2 :=
      Navier.Construction.TorusInverse.weight_pos _
    have hxle := one_add_abs_first_le_latticeModeWeight k
    have hyzle := torusWeight_le_two_mul_latticeModeWeight k
    have hden : (1 + |(k.1 : ℝ)|) ^ 2 *
        Navier.Construction.TorusInverse.weight k.2 ^ 4 ≤
          16 * latticeModeWeight k ^ 6 := by
      calc
        (1 + |(k.1 : ℝ)|) ^ 2 *
            Navier.Construction.TorusInverse.weight k.2 ^ 4 ≤
            latticeModeWeight k ^ 2 * (2 * latticeModeWeight k) ^ 4 := by
          gcongr
        _ = 16 * latticeModeWeight k ^ 6 := by ring
    have hinv := one_div_le_one_div_of_le
      (mul_pos (pow_pos hx 2) (pow_pos hyz 4)) hden
    dsimp [g]
    simp only [one_div] at hinv ⊢
    calc
      (latticeModeWeight k ^ 6)⁻¹ =
          16 * (16 * latticeModeWeight k ^ 6)⁻¹ := by
        field_simp
      _ ≤ 16 * (((1 + |(k.1 : ℝ)|) ^ 2 *
          Navier.Construction.TorusInverse.weight k.2 ^ 4)⁻¹) := by gcongr
      _ = 16 * (((1 + |(k.1 : ℝ)|) ^ 2)⁻¹ *
          (Navier.Construction.TorusInverse.weight k.2 ^ 4)⁻¹) := by
        rw [mul_inv_rev]
        ring

/-- Six additional spatial weights convert a uniform moment-mass bound into
a single summable modewise envelope. -/
theorem polynomialMomentAmplitude_le_uniform_invSix
    (p M : ℝ) (A : WeightedLatticeBanach)
    (hhigh : LatticePolynomialMoment (p + 6) A)
    (hM : polynomialMoment (p + 6) A ≤ M)
    (k : LatticeMode) :
    polynomialMomentAmplitude p A k ≤
      M * (latticeModeWeight k ^ 6)⁻¹ := by
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hterm : polynomialMomentAmplitude (p + 6) A k ≤
      polynomialMoment (p + 6) A := by
    unfold polynomialMoment
    have hs := hhigh.sum_le_tsum ({k} : Finset LatticeMode)
      (fun j _ => polynomialMomentAmplitude_nonneg (p + 6) A j)
    simpa using hs
  have heq : polynomialMomentAmplitude p A k =
      (latticeModeWeight k ^ 6)⁻¹ *
        polynomialMomentAmplitude (p + 6) A k := by
    unfold polynomialMomentAmplitude
    rw [Real.rpow_add hw]
    norm_num
    field_simp
  rw [heq]
  calc
    (latticeModeWeight k ^ 6)⁻¹ *
        polynomialMomentAmplitude (p + 6) A k ≤
      (latticeModeWeight k ^ 6)⁻¹ * M :=
        mul_le_mul_of_nonneg_left (hterm.trans hM)
          (inv_nonneg.mpr (pow_nonneg hw.le 6))
    _ = M * (latticeModeWeight k ^ 6)⁻¹ := by ring

/-- The envelope furnished by a six-weight reserve is summable. -/
theorem summable_uniform_invSixEnvelope (M : ℝ) :
    Summable fun k : LatticeMode => M * (latticeModeWeight k ^ 6)⁻¹ :=
  summable_latticeModeWeight_inv_pow_six.mul_left M

/-- Uniform-in-time form used by the smooth-series differentiation theorem. -/
theorem polynomialMomentAmplitude_uniform_envelope
    (p M : ℝ) (A : ℝ → WeightedLatticeBanach) {S : Set ℝ}
    (hhigh : ∀ t ∈ S, LatticePolynomialMoment (p + 6) (A t) ∧
      polynomialMoment (p + 6) (A t) ≤ M) :
    ∀ k t, t ∈ S → polynomialMomentAmplitude p (A t) k ≤
      M * (latticeModeWeight k ^ 6)⁻¹ := by
  intro k t ht
  exact polynomialMomentAmplitude_le_uniform_invSix
    p M (A t) (hhigh t ht).1 (hhigh t ht).2 k

/-- Order-`p` mass density for a decoded time-derivative family. -/
def timeDerivativeMomentAmplitude (p : ℝ)
    (D : LatticeMode → ComplexSpace) (k : LatticeMode) : ℝ :=
  latticeModeWeight k ^ p * complexEuclideanNorm (D k)

def TimeDerivativePolynomialMoment (p : ℝ)
    (D : LatticeMode → ComplexSpace) : Prop :=
  Summable (timeDerivativeMomentAmplitude p D)

def timeDerivativePolynomialMoment (p : ℝ)
    (D : LatticeMode → ComplexSpace) : ℝ :=
  ∑' k, timeDerivativeMomentAmplitude p D k

theorem timeDerivativeMomentAmplitude_nonneg
    (p : ℝ) (D : LatticeMode → ComplexSpace) (k : LatticeMode) :
    0 ≤ timeDerivativeMomentAmplitude p D k :=
  mul_nonneg (Real.rpow_nonneg
    (zero_le_one.trans (one_le_latticeModeWeight k)) p) (norm_nonneg _)

theorem abs_rawModeDecayRate_le_weight_sq
    (μ : ℝ) (k : LatticeMode) :
    |rawModeDecayRate μ k| ≤ |μ| * latticeModeWeight k ^ 2 := by
  have hq : ‖complexFrequency (latticeFrequency k)‖ ≤ latticeModeWeight k := by
    unfold latticeModeWeight
    linarith [norm_nonneg (complexFrequency (latticeFrequency k))]
  unfold rawModeDecayRate
  rw [abs_mul, abs_sq, ← complexFrequency_norm_eq_official]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq 2)
    (abs_nonneg μ)

private theorem complexEuclideanPoint_sub_local (z w : ComplexSpace) :
    complexEuclideanPoint (z - w) =
      complexEuclideanPoint z - complexEuclideanPoint w := by
  ext i
  rfl

private theorem complexEuclideanPoint_smul_local (c : ℂ) (z : ComplexSpace) :
    complexEuclideanPoint (c • z) = c • complexEuclideanPoint z := by
  ext i
  rfl

/-- The actual mode ODE loses exactly two spatial weights. -/
theorem timeDerivativeMomentAmplitude_mildRaw_le
    (p μ : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (k : LatticeMode) :
    timeDerivativeMomentAmplitude p (mildRawTimeDerivative μ A t) k ≤
      latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedModeForcing A k t) +
        |μ| * polynomialMomentAmplitude (p + 2) (A t) k := by
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hdecay := abs_rawModeDecayRate_le_weight_sq μ k
  unfold timeDerivativeMomentAmplitude mildRawTimeDerivative
  calc
    latticeModeWeight k ^ p * complexEuclideanNorm
        (projectedModeForcing A k t -
          (rawModeDecayRate μ k : ℂ) • weightedLatticeCoefficient (A t) k) ≤
      latticeModeWeight k ^ p *
        (complexEuclideanNorm (projectedModeForcing A k t) +
          |rawModeDecayRate μ k| *
            complexEuclideanNorm (weightedLatticeCoefficient (A t) k)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hw.le p)
      unfold complexEuclideanNorm
      rw [complexEuclideanPoint_sub_local, complexEuclideanPoint_smul_local]
      calc
        ‖complexEuclideanPoint (projectedModeForcing A k t) -
            (rawModeDecayRate μ k : ℂ) •
              complexEuclideanPoint (weightedLatticeCoefficient (A t) k)‖ ≤
            ‖complexEuclideanPoint (projectedModeForcing A k t)‖ +
              ‖(rawModeDecayRate μ k : ℂ) •
                complexEuclideanPoint (weightedLatticeCoefficient (A t) k)‖ :=
          norm_sub_le _ _
        _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedModeForcing A k t) +
        latticeModeWeight k ^ p *
          ((|μ| * latticeModeWeight k ^ 2) *
            complexEuclideanNorm (weightedLatticeCoefficient (A t) k)) := by
      rw [mul_add]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdecay (norm_nonneg _))
          (Real.rpow_nonneg hw.le p))
    _ = latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedModeForcing A k t) +
        |μ| * polynomialMomentAmplitude (p + 2) (A t) k := by
      unfold polynomialMomentAmplitude
      rw [Real.rpow_add hw, Real.rpow_two]
      ring

/-- Summable all-mode derivative mass follows from the actual ODE and an
order-`p+2` spatial moment of the trajectory. -/
theorem timeDerivativePolynomialMoment_mildRaw
    (p μ : ℝ) (hp : 0 ≤ p)
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hA : LatticePolynomialMoment (p + 2) (A t)) :
    TimeDerivativePolynomialMoment p (mildRawTimeDerivative μ A t) := by
  have hAone : LatticePolynomialMoment (p + 1) (A t) :=
    latticePolynomialMoment_mono (by linarith) (A t) hA
  have hforce : Summable fun k => latticeModeWeight k ^ p *
      complexEuclideanNorm (projectedModeForcing A k t) := by
    have h := summable_projectedConvolutionPolynomialMoment
      (p + 1) (by linarith) (A t) (A t) hAone hAone
    simpa only [show p + 1 - 1 = p by ring,
      projectedSpectralConvolutionCoefficient, projectedModeForcing] using h
  have hvisc : Summable fun k =>
      |μ| * polynomialMomentAmplitude (p + 2) (A t) k := hA.mul_left |μ|
  exact (hforce.add hvisc).of_nonneg_of_le
    (timeDerivativeMomentAmplitude_nonneg p _)
    (timeDerivativeMomentAmplitude_mildRaw_le p μ A t)

/-- Quantitative all-mode derivative estimate used at every time-jet rung. -/
theorem timeDerivativePolynomialMoment_mildRaw_le
    (p μ : ℝ) (hp : 0 ≤ p)
    (A : ℝ → WeightedLatticeBanach) (t : ℝ)
    (hA : LatticePolynomialMoment (p + 2) (A t)) :
    timeDerivativePolynomialMoment p (mildRawTimeDerivative μ A t) ≤
      polynomialMoment (p + 1) (A t) ^ 2 +
        |μ| * polynomialMoment (p + 2) (A t) := by
  have hAone : LatticePolynomialMoment (p + 1) (A t) :=
    latticePolynomialMoment_mono (by linarith) (A t) hA
  have hD := timeDerivativePolynomialMoment_mildRaw p μ hp A t hA
  have hforce := summable_projectedConvolutionPolynomialMoment
    (p + 1) (by linarith) (A t) (A t) hAone hAone
  have hforce' : Summable fun k => latticeModeWeight k ^ p *
      complexEuclideanNorm (projectedModeForcing A k t) := by
    simpa only [show p + 1 - 1 = p by ring,
      projectedSpectralConvolutionCoefficient, projectedModeForcing] using hforce
  have hvisc : Summable fun k =>
      |μ| * polynomialMomentAmplitude (p + 2) (A t) k := hA.mul_left |μ|
  have hright := hforce'.add hvisc
  unfold timeDerivativePolynomialMoment
  calc
    (∑' k, timeDerivativeMomentAmplitude p (mildRawTimeDerivative μ A t) k) ≤
        ∑' k, (latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedModeForcing A k t) +
          |μ| * polynomialMomentAmplitude (p + 2) (A t) k) :=
      hD.tsum_le_tsum (timeDerivativeMomentAmplitude_mildRaw_le p μ A t) hright
    _ = (∑' k, latticeModeWeight k ^ p *
          complexEuclideanNorm (projectedModeForcing A k t)) +
        |μ| * polynomialMoment (p + 2) (A t) := by
      rw [hforce'.tsum_add hvisc, tsum_mul_left]
      rfl
    _ ≤ polynomialMoment (p + 1) (A t) ^ 2 +
        |μ| * polynomialMoment (p + 2) (A t) := by
      gcongr
      simpa only [show p + 1 - 1 = p by ring] using
        (tsum_projectedModeForcing_polynomial_sub_one_le
          (p + 1) (by linarith) A t hAone)

/-- One decoded spatial weight encodes a derivative family in the repository's
completed critical carrier. -/
def weightedTimeDerivativeCarrier
    (D : LatticeMode → ComplexSpace)
    (hD : TimeDerivativePolynomialMoment 1 D) : WeightedLatticeBanach :=
  ⟨fun k => latticeModeWeight k • complexEuclideanPoint (D k),
    memℓp_gen (by
      change Summable (timeDerivativeMomentAmplitude 1 D) at hD
      have hs : Summable fun k : LatticeMode =>
          ‖latticeModeWeight k • complexEuclideanPoint (D k)‖ := by
        apply hD.congr
        intro k
        unfold timeDerivativeMomentAmplitude complexEuclideanNorm
        rw [Real.rpow_one, norm_smul,
          Real.norm_of_nonneg
            (zero_le_one.trans (one_le_latticeModeWeight k))]
      simpa using hs)⟩

@[simp] theorem weightedTimeDerivativeCarrier_apply
    (D : LatticeMode → ComplexSpace)
    (hD : TimeDerivativePolynomialMoment 1 D) (k : LatticeMode) :
    weightedTimeDerivativeCarrier D hD k =
      latticeModeWeight k • complexEuclideanPoint (D k) := rfl

/-- Decoding the completed derivative carrier recovers the original vector
mode derivative exactly. -/
theorem weightedLatticeCoefficient_weightedTimeDerivativeCarrier
    (D : LatticeMode → ComplexSpace)
    (hD : TimeDerivativePolynomialMoment 1 D) (k : LatticeMode) :
    weightedLatticeCoefficient (weightedTimeDerivativeCarrier D hD) k = D k := by
  unfold weightedLatticeCoefficient weightedTimeDerivativeCarrier
  rw [smul_smul]
  have hw : latticeModeWeight k ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k))
  rw [inv_mul_cancel₀ hw, one_smul]
  exact WithLp.ofLp_toLp _ _

/-- The completed derivative carrier is the sum of its genuine coordinate
terms. -/
theorem tsum_single_weightedTimeDerivativeCarrier
    (D : LatticeMode → ComplexSpace)
    (hD : TimeDerivativePolynomialMoment 1 D) :
    (∑' k : LatticeMode,
      lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
        (latticeModeWeight k • complexEuclideanPoint (D k))) =
      weightedTimeDerivativeCarrier D hD := by
  exact (lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
    (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤)
    (weightedTimeDerivativeCarrier D hD)).tsum_eq

private def complexEuclideanPointCLMReal :
    ComplexSpace →L[ℝ] ComplexE3 :=
  (ContinuousLinearEquiv.toContinuousLinearMap
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm).restrictScalars ℝ

@[simp] private theorem complexEuclideanPointCLMReal_apply (z : ComplexSpace) :
    complexEuclideanPointCLMReal z = complexEuclideanPoint z := rfl

/-- The coordinatewise mild ODE differentiates each actual weighted `lp`
coordinate, with the one-weight encoding of the decoded mode derivative. -/
theorem hasDerivAt_weightedLattice_apply_eq_mildRaw
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1)
    (k : LatticeMode) :
    HasDerivAt (fun r => A r k)
      (latticeModeWeight k • complexEuclideanPoint
        (mildRawTimeDerivative μ A t k)) t := by
  have hdecoded : HasDerivAt
      (fun r => weightedLatticeCoefficient (A r) k)
      (mildRawTimeDerivative μ A t k) t := by
    rw [hasDerivAt_pi]
    intro i
    exact hasDerivAt_mildPath_coefficient_eq_mildRawTimeDerivative
      μ hμ u₀ A hAc hdiv hR ht hbound hmild k i
  have hpoint : HasDerivAt
      (fun r => complexEuclideanPoint
        (weightedLatticeCoefficient (A r) k))
      (complexEuclideanPoint (mildRawTimeDerivative μ A t k)) t := by
    change HasDerivAt
      (fun r => complexEuclideanPointCLMReal
        (weightedLatticeCoefficient (A r) k))
      (complexEuclideanPointCLMReal (mildRawTimeDerivative μ A t k)) t
    exact complexEuclideanPointCLMReal.hasFDerivAt.comp_hasDerivAt t hdecoded
  have heq : (fun r => A r k) =
      fun r => latticeModeWeight k • complexEuclideanPoint
        (weightedLatticeCoefficient (A r) k) := by
    funext r
    exact (latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient
      (A r) k).symm
  rw [heq]
  exact hpoint.const_smul (latticeModeWeight k)

/-- The coordinate summands of the actual path have the corresponding
completed-carrier derivatives. -/
theorem hasDerivAt_single_weightedLattice_eq_mildRaw
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1)
    (k : LatticeMode) :
    HasDerivAt
      (fun r => lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k (A r k))
      (lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
        (latticeModeWeight k • complexEuclideanPoint
          (mildRawTimeDerivative μ A t k))) t := by
  have hcoordinate := hasDerivAt_weightedLattice_apply_eq_mildRaw
    μ hμ u₀ A hAc hdiv hR ht hbound hmild k
  let L := (lp.singleContinuousLinearMap ℂ
    (fun _ : LatticeMode => ComplexE3) 1 k).restrictScalars ℝ
  change HasDerivAt (fun r => L (A r k))
    (L (latticeModeWeight k • complexEuclideanPoint
      (mildRawTimeDerivative μ A t k))) t
  exact L.hasFDerivAt.comp_hasDerivAt t hcoordinate

/-- Six additional derivative weights convert a total derivative-moment
bound into a single summable lattice envelope. -/
theorem timeDerivativeMomentAmplitude_le_uniform_invSix
    (p M : ℝ) (D : LatticeMode → ComplexSpace)
    (hhigh : TimeDerivativePolynomialMoment (p + 6) D)
    (hM : timeDerivativePolynomialMoment (p + 6) D ≤ M)
    (k : LatticeMode) :
    timeDerivativeMomentAmplitude p D k ≤
      M * (latticeModeWeight k ^ 6)⁻¹ := by
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hterm : timeDerivativeMomentAmplitude (p + 6) D k ≤
      timeDerivativePolynomialMoment (p + 6) D := by
    unfold timeDerivativePolynomialMoment
    have hs := hhigh.sum_le_tsum ({k} : Finset LatticeMode)
      (fun j _ => timeDerivativeMomentAmplitude_nonneg (p + 6) D j)
    simpa using hs
  have heq : timeDerivativeMomentAmplitude p D k =
      (latticeModeWeight k ^ 6)⁻¹ *
        timeDerivativeMomentAmplitude (p + 6) D k := by
    unfold timeDerivativeMomentAmplitude
    rw [Real.rpow_add hw]
    norm_num
    field_simp
  rw [heq]
  calc
    (latticeModeWeight k ^ 6)⁻¹ *
        timeDerivativeMomentAmplitude (p + 6) D k ≤
      (latticeModeWeight k ^ 6)⁻¹ * M :=
        mul_le_mul_of_nonneg_left (hterm.trans hM)
          (inv_nonneg.mpr (pow_nonneg hw.le 6))
    _ = M * (latticeModeWeight k ^ 6)⁻¹ := by ring

/-- The actual mode ODE and a uniform order-`p+8` spatial bound furnish a
time-independent, summable envelope for its order-`p` derivative terms. -/
theorem mildRawTimeDerivative_uniform_envelope
    (p μ M : ℝ) (hp : 0 ≤ p)
    (A : ℝ → WeightedLatticeBanach) {S : Set ℝ}
    (hhigh : ∀ t ∈ S,
      LatticePolynomialMoment (p + 8) (A t) ∧
        polynomialMoment (p + 8) (A t) ≤ M) :
    ∀ k t, t ∈ S →
      timeDerivativeMomentAmplitude p (mildRawTimeDerivative μ A t) k ≤
        (M ^ 2 + |μ| * M) * (latticeModeWeight k ^ 6)⁻¹ := by
  intro k t ht
  have hA8 := (hhigh t ht).1
  have hA7 : LatticePolynomialMoment (p + 7) (A t) :=
    latticePolynomialMoment_mono (by linarith) (A t) hA8
  have hM7 : polynomialMoment (p + 7) (A t) ≤ M :=
    (polynomialMoment_mono (by linarith) (A t) hA8).trans (hhigh t ht).2
  have hA8' : LatticePolynomialMoment ((p + 6) + 2) (A t) := by
    simpa only [show (p + 6) + 2 = p + 8 by ring] using hA8
  have hM7' : polynomialMoment ((p + 6) + 1) (A t) ≤ M := by
    simpa only [show (p + 6) + 1 = p + 7 by ring] using hM7
  have hM8' : polynomialMoment ((p + 6) + 2) (A t) ≤ M := by
    simpa only [show (p + 6) + 2 = p + 8 by ring] using (hhigh t ht).2
  have hD : TimeDerivativePolynomialMoment (p + 6)
      (mildRawTimeDerivative μ A t) :=
    timeDerivativePolynomialMoment_mildRaw (p + 6) μ (by linarith) A t hA8'
  have hDbound : timeDerivativePolynomialMoment (p + 6)
      (mildRawTimeDerivative μ A t) ≤ M ^ 2 + |μ| * M := by
    refine (timeDerivativePolynomialMoment_mildRaw_le
      (p + 6) μ (by linarith) A t hA8').trans ?_
    exact add_le_add
      (pow_le_pow_left₀
        (polynomialMoment_nonneg ((p + 6) + 1) (A t)) hM7' 2)
      (mul_le_mul_of_nonneg_left hM8' (abs_nonneg μ))
  exact timeDerivativeMomentAmplitude_le_uniform_invSix
    p (M ^ 2 + |μ| * M) (mildRawTimeDerivative μ A t) hD hDbound k

/-- A uniform order-nine spatial moment turns the modewise mild equation into
the genuine derivative of the trajectory in the completed weighted carrier.
The proof is the actual infinite-series interchange: every `lp.single` mode
is differentiated and the six-weight reserve supplies one common summable
majorant on the whole open time interval. -/
theorem exists_hasDerivAt_mildPath_in_weightedCarrier_of_uniform_nine
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R a T M t : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (ht : t ∈ Ioo a T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1)
    (hhigh : ∀ s ∈ Ioo a T,
      LatticePolynomialMoment 9 (A s) ∧ polynomialMoment 9 (A s) ≤ M) :
    ∃ hD : TimeDerivativePolynomialMoment 1
        (mildRawTimeDerivative μ A t),
      HasDerivAt A
        (weightedTimeDerivativeCarrier (mildRawTimeDerivative μ A t) hD) t := by
  have ht0T : t ∈ Ioo (0 : ℝ) T := ⟨ha.trans ht.1, ht.2⟩
  have hAt9 : LatticePolynomialMoment ((1 : ℝ) + 2) (A t) := by
    exact latticePolynomialMoment_mono (by norm_num) (A t) (hhigh t ht).1
  let hD : TimeDerivativePolynomialMoment 1
      (mildRawTimeDerivative μ A t) :=
    timeDerivativePolynomialMoment_mildRaw 1 μ (by norm_num) A t hAt9
  refine ⟨hD, ?_⟩
  let majorant : LatticeMode → ℝ := fun k =>
    (M ^ 2 + |μ| * M) * (latticeModeWeight k ^ 6)⁻¹
  have hmajorant : Summable majorant :=
    summable_uniform_invSixEnvelope (M ^ 2 + |μ| * M)
  let g : LatticeMode → ℝ → WeightedLatticeBanach := fun k r =>
    lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k (A r k)
  let g' : LatticeMode → ℝ → WeightedLatticeBanach := fun k r =>
    lp.single (E := fun _ : LatticeMode => ComplexE3) 1 k
      (latticeModeWeight k • complexEuclideanPoint
        (mildRawTimeDerivative μ A r k))
  have hg : ∀ k r, r ∈ Ioo a T → HasDerivAt (g k) (g' k r) r := by
    intro k r hr
    exact hasDerivAt_single_weightedLattice_eq_mildRaw
      μ hμ u₀ A hAc hdiv hR ⟨ha.trans hr.1, hr.2⟩ hbound hmild k
  have hg' : ∀ k r, r ∈ Ioo a T → ‖g' k r‖ ≤ majorant k := by
    intro k r hr
    have henv := mildRawTimeDerivative_uniform_envelope
      1 μ M (by norm_num) A
      (fun s hs => by
        have h := hhigh s hs
        simpa only [show (1 : ℝ) + 8 = 9 by norm_num] using h)
      k r hr
    dsimp only [g', majorant]
    rw [lp.norm_single (by norm_num : 0 < (1 : ENNReal)),
      norm_smul,
      Real.norm_of_nonneg
        (zero_le_one.trans (one_le_latticeModeWeight k))]
    simpa only [timeDerivativeMomentAmplitude, Real.rpow_one,
      complexEuclideanNorm] using henv
  have hg0 : Summable fun k => g k t := by
    exact (lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
      (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤) (A t)).summable
  have hseries := hasDerivAt_tsum_of_isPreconnected
    hmajorant isOpen_Ioo ordConnected_Ioo.isPreconnected hg hg' ht hg0 ht
  have hsumA : (fun r => ∑' k, g k r) = A := by
    funext r
    exact (lp.hasSum_single (E := fun _ : LatticeMode => ComplexE3)
      (p := 1) (by norm_num : (1 : ENNReal) ≠ ⊤) (A r)).tsum_eq
  have hsumD : (∑' k, g' k t) =
      weightedTimeDerivativeCarrier (mildRawTimeDerivative μ A t) hD := by
    exact tsum_single_weightedTimeDerivativeCarrier
      (mildRawTimeDerivative μ A t) hD
  rw [hsumA, hsumD] at hseries
  exact hseries

/-- **Actual strong time derivative on every compact positive-time
interior.** No time differentiability or rapid-decay hypothesis is assumed:
the all-order spatial smoothing theorem constructs the uniform order-nine
bound, and the preceding series argument upgrades the genuine mode ODE to a
derivative in the completed critical carrier. -/
theorem exists_hasDerivAt_mildPath_in_weightedCarrier
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (hu₀ : LatticeDivergenceFree u₀)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R a T : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (haT : a < T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1) :
    ∀ t ∈ Ioo a T,
      ∃ hD : TimeDerivativePolynomialMoment 1
          (mildRawTimeDerivative μ A t),
        HasDerivAt A
          (weightedTimeDerivativeCarrier (mildRawTimeDerivative μ A t) hD) t := by
  obtain ⟨B, hBnonneg, hB⟩ :=
    exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval
      μ hμ u₀ hu₀ A hAc hdiv hR ha haT.le hbound hmild
  have hhigh : ∀ s ∈ Ioo a T,
      LatticePolynomialMoment 9 (A s) ∧
        polynomialMoment 9 (A s) ≤ B 14 := by
    intro s hs
    have h := hB 14 s ⟨hs.1.le, hs.2.le⟩
    norm_num [iteratedHalfOrder] at h ⊢
    exact h
  intro t ht
  exact exists_hasDerivAt_mildPath_in_weightedCarrier_of_uniform_nine
    μ hμ u₀ A hAc hdiv hR ha ht hbound hmild hhigh

end Navier.Analysis.CriticalMildTimeJetInterchange

#print axioms Navier.Analysis.CriticalMildTimeJetInterchange.timeDerivativePolynomialMoment_mildRaw_le
#print axioms Navier.Analysis.CriticalMildTimeJetInterchange.weightedLatticeCoefficient_weightedTimeDerivativeCarrier
#print axioms Navier.Analysis.CriticalMildTimeJetInterchange.hasDerivAt_single_weightedLattice_eq_mildRaw
#print axioms Navier.Analysis.CriticalMildTimeJetInterchange.mildRawTimeDerivative_uniform_envelope
#print axioms Navier.Analysis.CriticalMildTimeJetInterchange.exists_hasDerivAt_mildPath_in_weightedCarrier
