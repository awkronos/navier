import Navier.Analysis.CriticalMildHeatCarrierAlgebra
import Navier.Analysis.CriticalMildPathIntegrand

/-!
# Bounded linear completed critical heat flow
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatFlowLinear

open MeasureTheory
open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatCarrierAlgebra
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildHeatTimeKernel
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildSeries

/-- Re-encoding a decoded coefficient recovers the completed carrier
coordinate exactly. -/
theorem latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient
    (u : WeightedLatticeBanach) (m : LatticeMode) :
    latticeModeWeight m • complexEuclideanPoint (weightedLatticeCoefficient u m) =
      u m := by
  unfold weightedLatticeCoefficient complexEuclideanPoint
  rw [WithLp.toLp_ofLp]
  rw [smul_smul]
  have hm : latticeModeWeight m ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight m))
  field_simp
  simp

/-- At each nonnegative time, completed heat--Leray evolution is a bounded
complex-linear operator on the weighted carrier. -/
def weightedHeatFlowCLM
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) :
    WeightedLatticeBanach →L[ℂ] WeightedLatticeBanach :=
  LinearMap.mkContinuous
    { toFun := weightedHeatFlow ν τ hν hτ
      map_add' := by
        intro u v
        ext m i
        change weightedHeatFlowCoordinate ν τ (u + v) m i =
          weightedHeatFlowCoordinate ν τ u m i + weightedHeatFlowCoordinate ν τ v m i
        unfold weightedHeatFlowCoordinate
        rw [weightedLatticeCoefficient_add]
        change (latticeModeWeight m • complexEuclideanPoint
          (ComplexFrequencyHeatLeray.complexFrequencyHeatLeray ν τ
            (latticeFrequency m)
            (weightedLatticeCoefficient u m + weightedLatticeCoefficient v m))) i = _
        rw [map_add]
        have hpoint (a b : ComplexSpace) :
            complexEuclideanPoint (a + b) =
              complexEuclideanPoint a + complexEuclideanPoint b := by
          ext j
          rfl
        rw [hpoint, smul_add]
        rfl
      map_smul' := by
        intro c u
        ext m i
        change weightedHeatFlowCoordinate ν τ (c • u) m i =
          c • weightedHeatFlowCoordinate ν τ u m i
        unfold weightedHeatFlowCoordinate
        rw [weightedLatticeCoefficient_smul]
        change (latticeModeWeight m • complexEuclideanPoint
          (ComplexFrequencyHeatLeray.complexFrequencyHeatLeray ν τ
            (latticeFrequency m) (c • weightedLatticeCoefficient u m))) i = _
        rw [map_smul]
        rw [ComplexFrequencyHeatLeray.complexEuclideanPoint_smul, smul_comm]
        rfl }
    1
    (fun u => by
      simpa using norm_weightedHeatFlow_le ν τ hν hτ u)

@[simp] theorem weightedHeatFlowCLM_apply
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (u : WeightedLatticeBanach) :
    weightedHeatFlowCLM ν τ hν hτ u = weightedHeatFlow ν τ hν hτ u :=
  rfl

/-- Bounded heat flow commutes with every Bochner integral in the completed
carrier. -/
theorem weightedHeatFlow_integral_comm
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    {f : X → WeightedLatticeBanach} (hf : Integrable f μ) :
    weightedHeatFlow ν τ hν hτ (∫ x, f x ∂μ) =
      ∫ x, weightedHeatFlow ν τ hν hτ (f x) ∂μ := by
  symm
  exact (weightedHeatFlowCLM ν τ hν hτ).integral_comp_comm hf

/-- The complex Leray projection fixes a Hermitian-transverse Fourier
coefficient. -/
theorem complexLeray_eq_self_of_hermitian_transverse
    (q : Space) (z : ComplexSpace)
    (hz : inner ℂ (complexFrequency q) (complexEuclideanPoint z) = 0) :
    ComplexLerayProjection.complexLeray q z = z := by
  ext i
  rw [ComplexLerayNorm.complexLeray_formula,
    ← ComplexLerayNorm.inner_complexFrequency, hz]
  simp

/-- At time zero the completed heat flow is the identity on divergence-free
weighted carrier data. -/
theorem weightedHeatFlow_zero_of_divergenceFree
    (ν : ℝ) (hν : 0 ≤ ν) (u : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) :
    weightedHeatFlow ν 0 hν le_rfl u = u := by
  ext m i
  rw [weightedHeatFlow_apply]
  unfold weightedHeatFlowCoordinate
  rw [ComplexFrequencyHeatLeray.complexFrequencyHeatLeray_zero_time]
  rw [complexLeray_eq_self_of_hermitian_transverse
    (latticeFrequency m) (weightedLatticeCoefficient u m) (hu m)]
  exact congrArg (fun z : ComplexE3 => z i)
    (latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient u m)

/-! ## Half-generator heat increment -/

/-- Elementary sharp scalar estimate behind the half-generator bound:
`1 - exp(-x) ≤ √x` for `x ≥ 0`. -/
theorem one_sub_exp_neg_le_sqrt {x : ℝ} (hx : 0 ≤ x) :
    1 - Real.exp (-x) ≤ Real.sqrt x := by
  by_cases hx1 : x ≤ 1
  · have hlin : 1 - Real.exp (-x) ≤ x := by
      linarith [Real.one_sub_le_exp_neg x]
    have hxsqrt : x ≤ Real.sqrt x := by
      have hs := Real.sq_sqrt hx
      have hs0 := Real.sqrt_nonneg x
      nlinarith
    exact hlin.trans hxsqrt
  · have h1sqrt : 1 ≤ Real.sqrt x := by
      have hs := Real.sq_sqrt hx
      have hs0 := Real.sqrt_nonneg x
      nlinarith
    linarith [Real.exp_pos (-x)]

/-- The one-extra-mode moment, i.e. the domain norm of the square root of the
heat generator on the completed weighted carrier.  Finiteness is stated
separately as summability when the bound is used. -/
def heatHalfGeneratorMoment (u : WeightedLatticeBanach) : ℝ :=
  ∑' m : LatticeMode,
    ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖

theorem heatHalfGeneratorMoment_nonneg (u : WeightedLatticeBanach) :
    0 ≤ heatHalfGeneratorMoment u := by
  unfold heatHalfGeneratorMoment
  exact tsum_nonneg fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- On divergence-free data, the completed heat flow is literal scalar heat
decay on every encoded carrier coordinate. -/
theorem weightedHeatFlow_apply_of_divergenceFree
    (ν r : ℝ) (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (m : LatticeMode) :
    weightedHeatFlow ν r hν hr u m =
      (complexHeatDecay ν r (latticeFrequency m) : ℂ) • u m := by
  rw [weightedHeatFlow_apply]
  unfold weightedHeatFlowCoordinate
  rw [complexFrequencyHeatLeray_apply,
    complexLeray_eq_self_of_hermitian_transverse
      (latticeFrequency m) (weightedLatticeCoefficient u m) (hu m),
    complexEuclideanPoint_smul]
  calc
    latticeModeWeight m •
        ((complexHeatDecay ν r (latticeFrequency m) : ℂ) •
          complexEuclideanPoint (weightedLatticeCoefficient u m)) =
      (complexHeatDecay ν r (latticeFrequency m) : ℂ) •
        (latticeModeWeight m •
          complexEuclideanPoint (weightedLatticeCoefficient u m)) := by
            rw [smul_comm]
    _ = (complexHeatDecay ν r (latticeFrequency m) : ℂ) • u m := by
      rw [latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient]

/-- **Sharp half-generator heat increment.**  If the single extra mode moment
is summable, then the same-weight completed heat flow satisfies

`‖e^{rΔ}u - u‖ ≤ √ν · (∑ |k| ‖u_k‖) · √r`.

The constant is one.  The divergence-free assumption is necessary here to
remove the time-zero Leray projection from the increment. -/
theorem norm_weightedHeatFlow_sub_le_sqrt_mul_halfGeneratorMoment
    (ν r : ℝ) (hν : 0 ≤ ν) (hr : 0 ≤ r)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (hhalf : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) :
    ‖weightedHeatFlow ν r hν hr u - u‖ ≤
      Real.sqrt ν * heatHalfGeneratorMoment u * Real.sqrt r := by
  have hpoint : ∀ m : LatticeMode,
      ‖(weightedHeatFlow ν r hν hr u - u) m‖ ≤
        (Real.sqrt ν * Real.sqrt r) *
          (‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) := by
    intro m
    change ‖weightedHeatFlow ν r hν hr u m - u m‖ ≤ _
    rw [weightedHeatFlow_apply_of_divergenceFree ν r hν hr u hu m]
    let q : ℝ := ‖complexFrequency (latticeFrequency m)‖
    let x : ℝ := ν * r * q ^ 2
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hdecay : complexHeatDecay ν r (latticeFrequency m) = Real.exp (-x) := by
      unfold complexHeatDecay FrequencyHeatLeray.heatDecay
      rw [← complexFrequency_norm_eq_official (latticeFrequency m)]
      congr 1
      dsimp [x, q]
      ring
    have hscalar : ‖(complexHeatDecay ν r (latticeFrequency m) : ℂ) - 1‖ ≤
        (Real.sqrt ν * Real.sqrt r) * q := by
      rw [show (complexHeatDecay ν r (latticeFrequency m) : ℂ) - 1 =
        ((complexHeatDecay ν r (latticeFrequency m) - 1 : ℝ) : ℂ) by norm_num]
      rw [Complex.norm_real, Real.norm_eq_abs, hdecay]
      have hexp0 := Real.exp_pos (-x)
      have hexp1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      rw [abs_of_nonpos (by linarith)]
      have hsqrt := one_sub_exp_neg_le_sqrt hx
      have hsqrt_eq : Real.sqrt x = (Real.sqrt ν * Real.sqrt r) * q := by
        dsimp [x, q]
        rw [mul_assoc, Real.sqrt_mul hν,
          Real.sqrt_mul hr, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
        ring
      simpa [hsqrt_eq] using hsqrt
    calc
      ‖(complexHeatDecay ν r (latticeFrequency m) : ℂ) • u m - u m‖ =
          ‖((complexHeatDecay ν r (latticeFrequency m) : ℂ) - 1) • u m‖ := by
        rw [sub_smul, one_smul]
      _ = ‖(complexHeatDecay ν r (latticeFrequency m) : ℂ) - 1‖ * ‖u m‖ :=
        norm_smul _ _
      _ ≤ ((Real.sqrt ν * Real.sqrt r) * q) * ‖u m‖ :=
        mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
      _ = (Real.sqrt ν * Real.sqrt r) * (q * ‖u m‖) := by ring
  have hdom : Summable fun m : LatticeMode =>
      (Real.sqrt ν * Real.sqrt r) *
        (‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) :=
    hhalf.mul_left _
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one]
  calc
    (∑' m : LatticeMode, ‖(weightedHeatFlow ν r hν hr u - u) m‖) ≤
        ∑' m : LatticeMode, (Real.sqrt ν * Real.sqrt r) *
          (‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) :=
      Summable.tsum_le_tsum hpoint
        (by simpa using (weightedHeatFlow ν r hν hr u - u).2.summable) hdom
    _ = (Real.sqrt ν * Real.sqrt r) * heatHalfGeneratorMoment u := by
      rw [tsum_mul_left]
      rfl
    _ = Real.sqrt ν * heatHalfGeneratorMoment u * Real.sqrt r := by ring

/-! ## Positive-time half-generator smoothing -/

/-- Positive heat time creates one extra homogeneous mode moment with the
parabolic `1 / √(ντ)` cost. -/
theorem summable_halfGeneratorMoment_weightedHeatFlow
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖weightedHeatFlow ν τ hν.le hτ.le u m‖ := by
  have hpoint : ∀ m : LatticeMode,
      ‖complexFrequency (latticeFrequency m)‖ *
          ‖weightedHeatFlow ν τ hν.le hτ.le u m‖ ≤
        (Real.sqrt (ν * τ))⁻¹ * ‖u m‖ := by
    intro m
    rw [weightedHeatFlow_apply_of_divergenceFree ν τ hν.le hτ.le u hu m,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (complexHeatDecay_nonneg ν τ (latticeFrequency m))]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right
      (latticeHeat_frequency_gain ν τ (mul_pos hν hτ) m) (norm_nonneg (u m))
  exact ((by simpa using u.2.summable : Summable fun m : LatticeMode => ‖u m‖).mul_left
    (Real.sqrt (ν * τ))⁻¹).of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpoint

/-- Quantitative positive-time version of the preceding summability result. -/
theorem heatHalfGeneratorMoment_weightedHeatFlow_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    heatHalfGeneratorMoment (weightedHeatFlow ν τ hν.le hτ.le u) ≤
      (Real.sqrt (ν * τ))⁻¹ * ‖u‖ := by
  have hpoint : ∀ m : LatticeMode,
      ‖complexFrequency (latticeFrequency m)‖ *
          ‖weightedHeatFlow ν τ hν.le hτ.le u m‖ ≤
        (Real.sqrt (ν * τ))⁻¹ * ‖u m‖ := by
    intro m
    rw [weightedHeatFlow_apply_of_divergenceFree ν τ hν.le hτ.le u hu m,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (complexHeatDecay_nonneg ν τ (latticeFrequency m))]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right
      (latticeHeat_frequency_gain ν τ (mul_pos hν hτ) m) (norm_nonneg (u m))
  have hdom : Summable fun m : LatticeMode =>
      (Real.sqrt (ν * τ))⁻¹ * ‖u m‖ :=
    (by simpa using u.2.summable : Summable fun m : LatticeMode => ‖u m‖).mul_left _
  unfold heatHalfGeneratorMoment
  calc
    (∑' m : LatticeMode,
        ‖complexFrequency (latticeFrequency m)‖ *
          ‖weightedHeatFlow ν τ hν.le hτ.le u m‖) ≤
        ∑' m : LatticeMode, (Real.sqrt (ν * τ))⁻¹ * ‖u m‖ :=
      (summable_halfGeneratorMoment_weightedHeatFlow ν τ hν hτ u hu).tsum_le_tsum
        hpoint hdom
    _ = (Real.sqrt (ν * τ))⁻¹ * ‖u‖ := by
      rw [tsum_mul_left]
      simp [lp.norm_eq_tsum_rpow]

/-- Applying an additional heat interval to the completed nonlinear output
only adds that interval to its existing output-frequency heat lag. -/
theorem weightedHeatFlow_heatRegularizedSpectralOutput
    (ν r τ : ℝ) (hν : 0 < ν) (hr : 0 < r) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    weightedHeatFlow ν r hν.le hr.le
        (heatRegularizedSpectralOutput ν τ hν hτ u v hu) =
      heatRegularizedSpectralOutput ν (r + τ) hν (add_pos hr hτ) u v hu := by
  ext m i
  rw [weightedHeatFlow_apply]
  unfold weightedHeatFlowCoordinate
  rw [weightedLatticeCoefficient_heatRegularizedSpectralOutput,
    heatRegularizedSpectralOutput_apply]
  unfold heatRegularizedSpectralOutputFiber
  rw [ComplexFrequencyHeatLeray.complexFrequencyHeatLeray_semigroup]

/-- The actual positive-lag Duhamel integrand has one extra mode moment, with
the sharp parabolic order `1 / (ντ)`.  Its nonintegrable endpoint order is the
precise obstruction to deriving a Duhamel moment from a radius bound alone. -/
theorem heatHalfGeneratorMoment_heatRegularizedSpectralOutput_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    heatHalfGeneratorMoment
        (heatRegularizedSpectralOutput ν τ hν hτ u v hu) ≤
      (2 / (ν * τ)) * ‖u‖ * ‖v‖ := by
  let a : ℝ := τ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let z := heatRegularizedSpectralOutput ν a hν ha u v hu
  have hz : LatticeDivergenceFree z :=
    heatRegularizedSpectralOutput_divergenceFree ν a hν ha u v hu
  have hsemigroup := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha u v hu
  have haa : a + a = τ := by dsimp [a]; ring
  have hsemigroup' : weightedHeatFlow ν a hν.le ha.le z =
      heatRegularizedSpectralOutput ν τ hν hτ u v hu := by
    dsimp [z]
    simpa only [haa] using hsemigroup
  have hmoment := heatHalfGeneratorMoment_weightedHeatFlow_le ν a hν ha z hz
  rw [hsemigroup'] at hmoment
  have hnorm : ‖z‖ ≤ (Real.sqrt (ν * a))⁻¹ * ‖u‖ * ‖v‖ := by
    dsimp [z]
    exact norm_heatRegularizedSpectralOutput_le ν a hν ha u v hu
  refine hmoment.trans ?_
  calc
    (Real.sqrt (ν * a))⁻¹ * ‖z‖ ≤
        (Real.sqrt (ν * a))⁻¹ *
          ((Real.sqrt (ν * a))⁻¹ * ‖u‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (2 / (ν * τ)) * ‖u‖ * ‖v‖ := by
      have hνα : 0 < ν * a := mul_pos hν ha
      have hs : Real.sqrt (ν * a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hνα)
      rw [show (Real.sqrt (ν * a))⁻¹ *
          ((Real.sqrt (ν * a))⁻¹ * ‖u‖ * ‖v‖) =
        ((Real.sqrt (ν * a)) ^ 2)⁻¹ * ‖u‖ * ‖v‖ by field_simp]
      rw [Real.sq_sqrt hνα.le]
      dsimp [a]
      field_simp

/-! ## Integrable half-generator estimate for the nonlinear heat output -/

/-- Pair majorant which assigns the extra output frequency to either input
instead of spending a second heat derivative. -/
def outputHeatHalfMomentPairMajorant (ν τ : ℝ)
    (u v : WeightedLatticeBanach) (ij : LatticeMode × LatticeMode) : ℝ :=
  (Real.sqrt (ν * τ))⁻¹ *
    ((‖complexFrequency (latticeFrequency ij.1)‖ * ‖u ij.1‖) * ‖v ij.2‖ +
      ‖u ij.1‖ *
        (‖complexFrequency (latticeFrequency ij.2)‖ * ‖v ij.2‖))

theorem summable_outputHeatHalfMomentPairMajorant
    (ν τ : ℝ) (u v : WeightedLatticeBanach)
    (hu : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖)
    (hv : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖v m‖) :
    Summable (outputHeatHalfMomentPairMajorant ν τ u v) := by
  have hu0 : Summable fun m : LatticeMode => ‖u m‖ := by simpa using u.2.summable
  have hv0 : Summable fun m : LatticeMode => ‖v m‖ := by simpa using v.2.summable
  have hleft : Summable fun ij : LatticeMode × LatticeMode =>
      (‖complexFrequency (latticeFrequency ij.1)‖ * ‖u ij.1‖) * ‖v ij.2‖ :=
    hu.mul_of_nonneg hv0
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _ => norm_nonneg _)
  have hright : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u ij.1‖ *
        (‖complexFrequency (latticeFrequency ij.2)‖ * ‖v ij.2‖) :=
    hu0.mul_of_nonneg hv (fun _ => norm_nonneg _)
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (hleft.add hright).mul_left _

/-- The exact base pair majorant gains its extra output frequency by assigning
it to either input. -/
theorem frequency_mul_outputHeatPairMajorant_le
    (ν τ : ℝ) (u v : WeightedLatticeBanach)
    (k : LatticeMode) (ij : LatticeMode × LatticeMode)
    (hijk : ij.1 + ij.2 = k) :
    ‖complexFrequency (latticeFrequency k)‖ *
        outputHeatPairMajorant ν τ u v ij ≤
      outputHeatHalfMomentPairMajorant ν τ u v ij := by
  have hfreq : ‖complexFrequency (latticeFrequency k)‖ ≤
      ‖complexFrequency (latticeFrequency ij.1)‖ +
        ‖complexFrequency (latticeFrequency ij.2)‖ := by
    rw [← hijk, complexFrequency_latticeFrequency_add]
    exact norm_add_le _ _
  have hc : 0 ≤ (Real.sqrt (ν * τ))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc
    ‖complexFrequency (latticeFrequency k)‖ *
        outputHeatPairMajorant ν τ u v ij =
      (Real.sqrt (ν * τ))⁻¹ *
        (‖complexFrequency (latticeFrequency k)‖ *
          (‖u ij.1‖ * ‖v ij.2‖)) := by
      simp only [outputHeatPairMajorant, latticeWeightedAmplitude_coefficient]
      ring
    _ ≤ (Real.sqrt (ν * τ))⁻¹ *
        ((‖complexFrequency (latticeFrequency ij.1)‖ +
            ‖complexFrequency (latticeFrequency ij.2)‖) *
          (‖u ij.1‖ * ‖v ij.2‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfreq
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))) hc
    _ = outputHeatHalfMomentPairMajorant ν τ u v ij := by
      unfold outputHeatHalfMomentPairMajorant
      ring

/-- One exact nonlinear heat summand obeys the split-input half-moment
majorant. -/
theorem frequency_mul_norm_constrainedHeatRegularizedFiberTerm_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖complexFrequency (latticeFrequency k)‖ *
        ‖constrainedHeatRegularizedFiberTerm ν τ k u v ij‖ ≤
      outputHeatHalfMomentPairMajorant ν τ u v ij.1 := by
  exact (mul_le_mul_of_nonneg_left
      (norm_constrainedHeatRegularizedFiberTerm_le ν τ hν hτ u v hu k ij)
      (norm_nonneg _)).trans
    (frequency_mul_outputHeatPairMajorant_le ν τ u v k ij.1 ij.2)

/-- Fiberwise version of the split-input majorant. -/
def outputHeatHalfMomentFiberMajorant (ν τ : ℝ)
    (u v : WeightedLatticeBanach) (k : LatticeMode) : ℝ :=
  ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
    outputHeatHalfMomentPairMajorant ν τ u v ij.1

theorem summable_outputHeatHalfMomentFiberMajorant
    (ν τ : ℝ) (u v : WeightedLatticeBanach)
    (hu : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖)
    (hv : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖v m‖) :
    Summable (outputHeatHalfMomentFiberMajorant ν τ u v) := by
  have hp := summable_outputHeatHalfMomentPairMajorant ν τ u v hu hv
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      outputHeatHalfMomentPairMajorant ν τ u v x.2.1) :=
    latticeOutputFiberSigmaEquiv.summable_iff.mpr hp
  exact hsigma.sigma

theorem frequency_mul_norm_constrainedHeatRegularizedFiber_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (huM : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖)
    (hvM : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖v m‖)
    (k : LatticeMode) :
    ‖complexFrequency (latticeFrequency k)‖ *
        ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ ≤
      outputHeatHalfMomentFiberMajorant ν τ u v k := by
  have hbase := norm_constrainedHeatRegularizedFiber_le_outputHeatFiberMajorant
    ν τ hν hτ u v hu k
  have hbaseSum := (summable_outputHeatPairMajorant ν τ u v).subtype
    (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))
  have hhalfSum := (summable_outputHeatHalfMomentPairMajorant ν τ u v huM hvM).subtype
    (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))
  calc
    ‖complexFrequency (latticeFrequency k)‖ *
        ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ ≤
      ‖complexFrequency (latticeFrequency k)‖ *
        outputHeatFiberMajorant ν τ u v k :=
      mul_le_mul_of_nonneg_left hbase (norm_nonneg _)
    _ = ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        ‖complexFrequency (latticeFrequency k)‖ *
          outputHeatPairMajorant ν τ u v ij.1 := by
      unfold outputHeatFiberMajorant
      rw [tsum_mul_left]
    _ ≤ ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        outputHeatHalfMomentPairMajorant ν τ u v ij.1 :=
      (hbaseSum.mul_left _).tsum_le_tsum
        (fun ij => frequency_mul_outputHeatPairMajorant_le
          ν τ u v k ij.1 ij.2)
        hhalfSum
    _ = outputHeatHalfMomentFiberMajorant ν τ u v k := rfl

set_option maxHeartbeats 800000 in
/-- **Integrable nonlinear half-moment estimate.**  Assigning the extra output
frequency to the two inputs replaces the nonintegrable `1/(ντ)` radius bound
by the integrable `1/√(ντ)` Volterra kernel. -/
theorem heatHalfGeneratorMoment_heatRegularizedSpectralOutput_le_split
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (huM : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖)
    (hvM : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖v m‖) :
    heatHalfGeneratorMoment
        (heatRegularizedSpectralOutput ν τ hν hτ u v hu) ≤
      (Real.sqrt (ν * τ))⁻¹ *
        (heatHalfGeneratorMoment u * ‖v‖ + ‖u‖ * heatHalfGeneratorMoment v) := by
  unfold heatHalfGeneratorMoment
  have hout := summable_outputHeatHalfMomentFiberMajorant ν τ u v huM hvM
  have hpoint : ∀ k : LatticeMode,
      ‖complexFrequency (latticeFrequency k)‖ *
          ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu k‖ ≤
        outputHeatHalfMomentFiberMajorant ν τ u v k := by
    intro k
    rw [heatRegularizedSpectralOutput_apply]
    rw [← constrainedHeatRegularizedFiber_eq_heatRegularizedSpectralOutputFiber
      ν τ hν hτ u v hu k]
    exact frequency_mul_norm_constrainedHeatRegularizedFiber_le
      ν τ hν hτ u v hu huM hvM k
  calc
    (∑' k : LatticeMode, ‖complexFrequency (latticeFrequency k)‖ *
        ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu k‖) ≤
      ∑' k : LatticeMode, outputHeatHalfMomentFiberMajorant ν τ u v k := by
        exact Summable.tsum_le_tsum hpoint
          (hout.of_nonneg_of_le
            (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpoint) hout
    _ = ∑' ij : LatticeMode × LatticeMode,
        outputHeatHalfMomentPairMajorant ν τ u v ij := by
      have hp := summable_outputHeatHalfMomentPairMajorant ν τ u v huM hvM
      have hsigma : Summable (fun x :
          Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
          outputHeatHalfMomentPairMajorant ν τ u v x.2.1) :=
        latticeOutputFiberSigmaEquiv.summable_iff.mpr hp
      rw [show outputHeatHalfMomentFiberMajorant ν τ u v = fun k =>
          ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
            outputHeatHalfMomentPairMajorant ν τ u v ij.1 by rfl,
        ← hsigma.tsum_sigma]
      exact latticeOutputFiberSigmaEquiv.tsum_eq _
    _ = (Real.sqrt (ν * τ))⁻¹ *
        (heatHalfGeneratorMoment u * ‖v‖ + ‖u‖ * heatHalfGeneratorMoment v) := by
      unfold outputHeatHalfMomentPairMajorant heatHalfGeneratorMoment
      rw [tsum_mul_left]
      have hu0 : Summable fun m : LatticeMode => ‖u m‖ := by simpa using u.2.summable
      have hv0 : Summable fun m : LatticeMode => ‖v m‖ := by simpa using v.2.summable
      have hleft : Summable fun ij : LatticeMode × LatticeMode =>
          (‖complexFrequency (latticeFrequency ij.1)‖ * ‖u ij.1‖) * ‖v ij.2‖ :=
        huM.mul_of_nonneg hv0
          (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _ => norm_nonneg _)
      have hright : Summable fun ij : LatticeMode × LatticeMode =>
          ‖u ij.1‖ *
            (‖complexFrequency (latticeFrequency ij.2)‖ * ‖v ij.2‖) :=
        hu0.mul_of_nonneg hvM (fun _ => norm_nonneg _)
          (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      rw [Summable.tsum_add
        hleft hright,
        (huM.tsum_mul_tsum hv0 hleft).symm,
        (hu0.tsum_mul_tsum hvM hright).symm]
      simp [lp.norm_eq_tsum_rpow]

/-- The evolving-path Duhamel integrand inherits the integrable split-input
kernel.  For a self-interaction the two allocations coincide, giving the
factor `2`. -/
theorem heatHalfGeneratorMoment_criticalMildPathIntegrand_le_split
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s < t)
    (hM : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖) :
    heatHalfGeneratorMoment (criticalMildPathIntegrand ν hν u hu t s) ≤
      2 * (Real.sqrt ν)⁻¹ * inverseSqrtTime (t - s) *
        ‖u s‖ * heatHalfGeneratorMoment (u s) := by
  have hlag : 0 < t - s := sub_pos.mpr hst
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν _ _ (hu s) hlag]
  have hsplit := heatHalfGeneratorMoment_heatRegularizedSpectralOutput_le_split
    ν (t - s) hν hlag (u s) (u s) (hu s) hM hM
  refine hsplit.trans_eq ?_
  rw [outputHeatGain_eq_inverseSqrtTime ν (t - s) hν hlag]
  ring

/-- The exact weighted-time hypothesis exposed by the split estimate is
sufficient for integrability of the nonlinear half-generator moment.  This is
strictly stronger than unweighted `L¹` control of the input half moment: the
backward square-root kernel must remain in the hypothesis. -/
theorem intervalIntegrable_heatHalfGeneratorMoment_criticalMildPathIntegrand_of_weighted
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {a t : ℝ} (hat : a ≤ t)
    (hM : ∀ s ∈ Set.Ioc a t, Summable fun m : LatticeMode ↦
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖)
    (hweighted : IntervalIntegrable
      (fun s ↦ inverseSqrtTime (t - s) * ‖u s‖ *
        heatHalfGeneratorMoment (u s)) volume a t) :
    IntervalIntegrable
      (fun s ↦ heatHalfGeneratorMoment
        (criticalMildPathIntegrand ν hν u hu t s)) volume a t := by
  have hmeas : Measurable (fun s ↦ heatHalfGeneratorMoment
      (criticalMildPathIntegrand ν hν u hu t s)) := by
    unfold heatHalfGeneratorMoment
    exact Measurable.tsum fun k ↦
      measurable_const.mul
        (stronglyMeasurable_criticalMildPathIntegrand_apply
          ν hν u huc hu t k).norm.measurable
  apply IntervalIntegrable.mono_fun'
    (hweighted.const_mul (2 * (Real.sqrt ν)⁻¹)) hmeas.aestronglyMeasurable
  rw [Set.uIoc_of_le hat]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hnonneg : 0 ≤ heatHalfGeneratorMoment
      (criticalMildPathIntegrand ν hν u hu t s) := by
    unfold heatHalfGeneratorMoment
    exact tsum_nonneg fun _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  by_cases hst : s < t
  · simpa only [mul_assoc] using
      heatHalfGeneratorMoment_criticalMildPathIntegrand_le_split
        ν hν u hu hst (hM s hs)
  · have hst' : s = t := le_antisymm hs.2 (not_lt.mp hst)
    subst s
    simp [criticalMildPathIntegrand, positiveTimeHeatRegularizedSpectralOutput,
      heatHalfGeneratorMoment, inverseSqrtTime]

end Navier.Analysis.CriticalMildHeatFlowLinear

#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlowCLM
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlow_integral_comm
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlow_zero_of_divergenceFree
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.one_sub_exp_neg_le_sqrt
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlow_apply_of_divergenceFree
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.norm_weightedHeatFlow_sub_le_sqrt_mul_halfGeneratorMoment
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.summable_halfGeneratorMoment_weightedHeatFlow
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.heatHalfGeneratorMoment_weightedHeatFlow_le
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.weightedHeatFlow_heatRegularizedSpectralOutput
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.heatHalfGeneratorMoment_heatRegularizedSpectralOutput_le
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.heatHalfGeneratorMoment_heatRegularizedSpectralOutput_le_split
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.heatHalfGeneratorMoment_criticalMildPathIntegrand_le_split
#print axioms Navier.Analysis.CriticalMildHeatFlowLinear.intervalIntegrable_heatHalfGeneratorMoment_criticalMildPathIntegrand_of_weighted
