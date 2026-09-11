import Navier.Analysis.CriticalMildPathFixedPoint
import Navier.Analysis.CriticalMildZeroMode
import Navier.Analysis.CriticalMildHeatSmoothing
import Navier.Analysis.CriticalMildHeatCoefficientLift
import Navier.Analysis.CriticalMildHigherUniformMoments
import Navier.Analysis.PeriodicMildOfficialEquation

/-!
# Unconditional small-data global mild continuation on the periodic lattice carrier

On the periodic Fourier-lattice carrier `WeightedLatticeBanach` the heat
semigroup decays exponentially on every nonzero lattice mode: the spectral gap
`1 ≤ ‖complexFrequency (latticeFrequency m)‖` for `m ≠ 0` is verified directly
from the coordinate definition of `latticeFrequency` in this file.  Because the
exact zero-mode cancellation of `CriticalMildZeroMode` removes the only gapless
output mode from the Duhamel integrand, the two-branch heat gain

* `(√(ν·τ))⁻¹` for `ν·τ ≤ 1` (the checked existing inverse-square-root leaf), and
* `Real.exp (-(ν·τ))` for `ν·τ > 1` (gap-driven exponential decay),

is integrable over `[0, ∞)` with total budget `3/ν`, uniformly in the
horizon.  Feeding this into the completed Bochner Duhamel term
`criticalMildDuhamel` (integrability reused from `CriticalMildDuhamelBochner`,
never rebuilt) gives a horizon-free self-map and strict contraction of the
radius-`2‖a‖` ball in `C(Set.Ici 0, WeightedLatticeBanach)` for
`‖a‖ ≤ ν/16`.

The main theorem `smallDataGlobalMild` is an unconditional small-data global
mild continuation on the periodic lattice carrier with explicit threshold
`ε(ν) = ν/16 > 0`: a continuous zero-mean divergence-free mild solution on
`[0, ∞)` with decay and uniqueness in its ball.  This strictly surpasses the
horizon-limited local charts of `CriticalMildPathFixedPoint`, whose coefficients
grow like `√T`.  The remaining named OPEN obligations are unchanged: closure on
the official `Navier.Problem` carrier `B` for arbitrary data, and the classical
spacetime reconstruction, which is the same named consumer obligation already
recorded for the finite charts (`PeriodicNonlinearFourierReconstruction`,
`PeriodicSpatialSmoothReconstruction`).  The raw terminal-horizon bounds that
block a naive global estimate are documented in
`Navier.Analysis.PeriodicGlobalCriticalControl`,
`Navier.Analysis.PhysicalPeriodicGlobalControl`, and
`GlobalRegularityCrownCore.not_restart_scalar_budget_le_fixed_radius`.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildSmallDataGlobal

open Set Topology MeasureTheory
open scoped BigOperators ENNReal
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatTimeKernel
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildZeroMode
open Navier.Analysis.CriticalMildHeatCoefficientLift
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildPolynomialMomentConvolution
open Navier.Analysis.CriticalMildHigherUniformMoments
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicMildOfficialEquation

/-! ### 1. The spectral gap read off the actual definitions -/

/-- One real coordinate of a lattice frequency is bounded by its complex
Euclidean norm. -/
theorem abs_latticeFrequency_apply_le_norm (m : LatticeMode) (i : Fin 3) :
    |(latticeFrequency m) i| ≤ ‖complexFrequency (latticeFrequency m)‖ := by
  have h : (‖complexFrequency (latticeFrequency m)‖ : ℝ) =
      officialEuclideanNorm (latticeFrequency m) := by
    rw [Navier.Analysis.CriticalMildHeatSmoothing.complexFrequency_norm_eq_official,
      officialEuclideanNorm]
  have h1 : |(latticeFrequency m) i| ≤
      officialEuclideanNorm (latticeFrequency m) := by
    rw [officialEuclideanNorm_eq_sqrt_sum_sq]
    exact (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
      (Finset.single_le_sum (f := fun j : Fin 3 => |(latticeFrequency m) j| ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  exact h1.trans (le_of_eq h.symm)

/-- A nonzero lattice mode carries the exact gap `1`: every coordinate of
`latticeFrequency m` is an integer, and an integer strictly below one in
absolute value is zero. -/
theorem latticeFrequency_gap {m : LatticeMode} (hm : ¬ (m = 0)) :
    1 ≤ ‖complexFrequency (latticeFrequency m)‖ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, b, c⟩ := m
  have key (z : ℤ) (hz : |(z : ℝ)| < 1) : z = 0 := by
    obtain ⟨h1, h2⟩ := abs_lt.mp hz
    norm_cast at h1 h2
    omega
  have ha : a = 0 :=
    key a (lt_of_le_of_lt (abs_latticeFrequency_apply_le_norm ⟨a, (b, c)⟩ 0) hlt)
  have hb : b = 0 :=
    key b (lt_of_le_of_lt (abs_latticeFrequency_apply_le_norm ⟨a, (b, c)⟩ 1) hlt)
  have hc : c = 0 :=
    key c (lt_of_le_of_lt (abs_latticeFrequency_apply_le_norm ⟨a, (b, c)⟩ 2) hlt)
  exact hm (by rw [ha, hb, hc]; rfl)

/-- The exact gap decay form of one nonzero lattice mode. -/
theorem complexHeatDecay_latticeFrequency_eq (ν τ : ℝ) (k : LatticeMode) :
    complexHeatDecay ν τ (latticeFrequency k) =
      Real.exp (-ν * τ * ‖complexFrequency (latticeFrequency k)‖ ^ 2) := by
  unfold complexHeatDecay heatDecay
  rw [Navier.Analysis.CriticalMildHeatSmoothing.complexFrequency_norm_eq_official]

/-- On nonzero modes the heat decay is bounded by the gap exponential. -/
theorem complexHeatDecay_latticeFrequency_le_gap_exp
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) {k : LatticeMode} (hk : ¬ (k = 0)) :
    complexHeatDecay ν τ (latticeFrequency k) ≤ Real.exp (-ν * τ) := by
  rw [complexHeatDecay_latticeFrequency_eq]
  refine Real.exp_le_exp.mpr ?_
  have hw : 1 ≤ ‖complexFrequency (latticeFrequency k)‖ ^ 2 := by
    nlinarith [latticeFrequency_gap hk, sq_nonneg
      (‖complexFrequency (latticeFrequency k)‖ - 1)]
  have hmul : 0 ≤ ν * τ := mul_nonneg hν hτ
  nlinarith

/-! ### 2. The two-branch gap gain and its global integrability -/

/-- The gap-aware heat gain: the checked inverse-square-root leaf at small
scaled lag `ν·τ ≤ 1`, and pure gap-driven exponential decay at large scaled
lag.  At `ν·τ = 0` this is `0`, matching the zero extension of the completed
positive-time nonlinear integrand. -/
def gapTimeGain (ν τ : ℝ) : ℝ :=
  if ν * τ ≤ 1 then (Real.sqrt (ν * τ))⁻¹ else Real.exp (-(ν * τ))

theorem gapTimeGain_nonneg (ν τ : ℝ) : 0 ≤ gapTimeGain ν τ := by
  unfold gapTimeGain
  split_ifs
  · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  · exact Real.exp_pos _ |>.le

/-- The gap gain is dominated by the existing integrable inverse-square-root
kernel at every nonnegative lag. -/
theorem gapTimeGain_le_inverseSqrtTime (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    gapTimeGain ν τ ≤ (Real.sqrt ν)⁻¹ * inverseSqrtTime τ := by
  unfold gapTimeGain
  split_ifs with hs
  · rw [outputHeatGain_eq_inverseSqrtTime ν τ hν hτ]
  · have hx : 1 < ν * τ := lt_of_not_ge hs
    have hp : 0 < ν * τ := by linarith
    have hsqrt_le : Real.sqrt (ν * τ) ≤ Real.exp (ν * τ) := by
      have hl : Real.log (Real.sqrt (ν * τ)) ≤ Real.log (Real.exp (ν * τ)) := by
        rw [Real.log_sqrt hp.le, Real.log_exp]
        have := Real.log_le_sub_one_of_pos hp
        linarith
      exact (Real.log_le_log_iff (Real.sqrt_pos.mpr hp) (Real.exp_pos _)).mp hl
    have h1 : Real.exp (-(ν * τ)) ≤ (Real.sqrt (ν * τ))⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) (Real.sqrt_pos.mpr hp)).mpr hsqrt_le
    exact h1.trans (le_of_eq (outputHeatGain_eq_inverseSqrtTime ν τ hν hτ))

/-- At large scaled lag the transported triad output decays exponentially:
`ω · exp (-ν·τ·ω²) ≤ exp (-(ν·τ))` for `1 ≤ ω` and `1 ≤ ν·τ`.  The statement
is written in the exact definitional shape of `heatDecay`. -/
theorem omega_decay_le_gap_exp {x : ℝ} (ν τ : ℝ) (hx : 1 ≤ x) (hr : 1 ≤ ν * τ) :
    x * Real.exp (-ν * τ * x ^ 2) ≤ Real.exp (-(ν * τ)) := by
  have hpos : 0 < x := by linarith
  have hlog : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hpos
  have hxr : Real.log x ≤ ν * τ * (x ^ 2 - 1) := by
    have h0 : 0 ≤ x ^ 2 - 1 := by nlinarith
    nlinarith
  have hexp : x ≤ Real.exp (ν * τ * (x ^ 2 - 1)) :=
    calc x = Real.exp (Real.log x) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (ν * τ * (x ^ 2 - 1)) := Real.exp_le_exp.mpr hxr
  calc x * Real.exp (-ν * τ * x ^ 2)
      ≤ Real.exp (ν * τ * (x ^ 2 - 1)) * Real.exp (-ν * τ * x ^ 2) :=
        mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
    _ = Real.exp (ν * τ * (x ^ 2 - 1) + -ν * τ * x ^ 2) :=
        (Real.exp_add _ _).symm
    _ = Real.exp (-(ν * τ)) := by congr 1; ring

/-- Nonnegativity of the complex Euclidean amplitude norm. -/
theorem complexEuclideanNorm_nonneg (z : ComplexSpace) :
    0 ≤ complexEuclideanNorm z := by
  unfold complexEuclideanNorm
  exact norm_nonneg _

/-- A nonzero factor cancels its inverse inside a three-term product. -/
theorem sqrt_inv_prod_cancel {S P Q : ℝ} (hS : S ≠ 0) :
    S * (S⁻¹ * P * Q) = P * Q := by
  rw [mul_assoc, ← mul_assoc, mul_inv_cancel₀ hS, one_mul]

/-- The gain prefactor cancels the inverse square root inside the weighted
pair product. -/
theorem exp_prod_inv_cancel {E S P Q : ℝ} (hS : S ≠ 0) :
    E * (P * Q) = (E * S) * (S⁻¹ * P * Q) := by
  rw [mul_assoc, sqrt_inv_prod_cancel hS]

/-! ### 3. The gap-driven large-lag gain on the completed output carrier -/

/-- The exponential branch of the heat gain: at scaled lag `ν·τ > 1` the exact
zero-mode cancellation removes every gapless output mode, so each transported
triad through output mode `k` carries `ω_k · exp (-ν·τ·ω_k²) ≤ exp (-ν·τ)`
after the submultiplicative weight absorbs the output weight. -/
theorem norm_heatRegularizedSpectralOutput_le_gap_exp
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (hrs : 1 < ν * τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu‖ ≤
      Real.exp (-(ν * τ)) * ‖u‖ * ‖v‖ := by
  set c := Real.exp (-(ν * τ)) * Real.sqrt (ν * τ) with hcdef
  have hsqrt : Real.sqrt (ν * τ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hdecay (k : LatticeMode) :
      complexHeatDecay ν τ (latticeFrequency k) *
        ‖complexFrequency (latticeFrequency k)‖ ≤ Real.exp (-(ν * τ)) := by
    by_cases hk0 : k = 0
    · rw [hk0, latticeFrequency_zero, complexFrequency_zero, norm_zero, mul_zero]
      exact (Real.exp_pos _).le
    · have hgap := latticeFrequency_gap hk0
      have hcomm : complexHeatDecay ν τ (latticeFrequency k) *
            ‖complexFrequency (latticeFrequency k)‖ =
          ‖complexFrequency (latticeFrequency k)‖ *
            complexHeatDecay ν τ (latticeFrequency k) := by ring
      rw [hcomm, complexHeatDecay_latticeFrequency_eq]
      exact omega_decay_le_gap_exp ν τ hgap (by linarith)
  have hterm (k : LatticeMode)
      (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
      ‖constrainedHeatRegularizedFiberTerm ν τ k u v ij‖ ≤
        c * outputHeatPairMajorant ν τ u v ij.1 := by
    have hk : ij.1.1 + ij.1.2 = k := ij.2
    have hwk : latticeModeWeight k = latticeModeWeight (ij.1.1 + ij.1.2) :=
      congrArg latticeModeWeight hk.symm
    have hnorm : ‖constrainedHeatRegularizedFiberTerm ν τ k u v ij‖ =
        latticeModeWeight k * complexEuclideanNorm
          (complexFrequencyHeatLeray ν τ (latticeFrequency k)
            (spectralTransport (latticeFrequency ij.1.2)
              (weightedLatticeCoefficient u ij.1.1)
              (weightedLatticeCoefficient v ij.1.2))) := by
      unfold constrainedHeatRegularizedFiberTerm
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (zero_le_one.trans (one_le_latticeModeWeight k))]
      rfl
    rw [hnorm]
    have htr : spectralTransport (latticeFrequency ij.1.2)
        (weightedLatticeCoefficient u ij.1.1)
        (weightedLatticeCoefficient v ij.1.2) =
        spectralTransport (latticeFrequency k)
          (weightedLatticeCoefficient u ij.1.1)
          (weightedLatticeCoefficient v ij.1.2) :=
      spectralTransport_frequency_transfer u v hu ij.1.1 ij.1.2 k hk
    have hle : complexEuclideanNorm
          (complexFrequencyHeatLeray ν τ (latticeFrequency k)
            (spectralTransport (latticeFrequency ij.1.2)
              (weightedLatticeCoefficient u ij.1.1)
              (weightedLatticeCoefficient v ij.1.2))) ≤
        complexHeatDecay ν τ (latticeFrequency k) *
          complexEuclideanNorm (spectralTransport (latticeFrequency k)
            (weightedLatticeCoefficient u ij.1.1)
            (weightedLatticeCoefficient v ij.1.2)) := by
      refine (complexEuclideanNorm_heatLeray_le_decay ν τ k
          (spectralTransport (latticeFrequency ij.1.2)
            (weightedLatticeCoefficient u ij.1.1)
            (weightedLatticeCoefficient v ij.1.2))).trans ?_
      rw [htr]
    have hzero : 0 ≤ complexHeatDecay ν τ (latticeFrequency k) :=
      complexHeatDecay_nonneg ν τ (latticeFrequency k)
    have hw : 0 ≤ latticeModeWeight k :=
      zero_le_one.trans (one_le_latticeModeWeight k)
    have htransp : complexEuclideanNorm
          (spectralTransport (latticeFrequency k)
            (weightedLatticeCoefficient u ij.1.1)
            (weightedLatticeCoefficient v ij.1.2)) ≤
        ‖complexFrequency (latticeFrequency k)‖ *
          complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
          complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2) :=
      complexEuclideanNorm_spectralTransport_le _ _ _
    have hsub : latticeModeWeight k *
          complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
          complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2) ≤
        latticeModeWeight ij.1.1 *
          complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
          (latticeModeWeight ij.1.2 *
            complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) := by
      have hU : 0 ≤ complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) :=
        complexEuclideanNorm_nonneg _
      have hV : 0 ≤ complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2) :=
        complexEuclideanNorm_nonneg _
      calc latticeModeWeight k *
              complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)
          = latticeModeWeight k *
              (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
                complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) :=
              by ring
        _ = latticeModeWeight (ij.1.1 + ij.1.2) *
              (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
                complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) :=
              by rw [hwk]
        _ ≤ (latticeModeWeight ij.1.1 * latticeModeWeight ij.1.2) *
              (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
                complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) :=
              mul_le_mul_of_nonneg_right
                (latticeModeWeight_add_le_mul ij.1.1 ij.1.2)
                (mul_nonneg hU hV)
        _ = latticeModeWeight ij.1.1 *
              complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
              (latticeModeWeight ij.1.2 *
                complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2)) :=
              by ring
    calc latticeModeWeight k *
          complexEuclideanNorm
            (complexFrequencyHeatLeray ν τ (latticeFrequency k)
              (spectralTransport (latticeFrequency ij.1.2)
                (weightedLatticeCoefficient u ij.1.1)
                (weightedLatticeCoefficient v ij.1.2))) ≤
        latticeModeWeight k * (complexHeatDecay ν τ (latticeFrequency k) *
            complexEuclideanNorm (spectralTransport (latticeFrequency k)
              (weightedLatticeCoefficient u ij.1.1)
              (weightedLatticeCoefficient v ij.1.2))) :=
          mul_le_mul_of_nonneg_left hle hw
      _ ≤ latticeModeWeight k * (complexHeatDecay ν τ (latticeFrequency k) *
            (‖complexFrequency (latticeFrequency k)‖ *
              complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left htransp hzero) hw
      _ = (complexHeatDecay ν τ (latticeFrequency k) *
            ‖complexFrequency (latticeFrequency k)‖) *
          (latticeModeWeight k *
            (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) := by ring
      _ ≤ Real.exp (-(ν * τ)) * (latticeModeWeight k *
            (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) :=
          mul_le_mul_of_nonneg_right (hdecay k)
            (mul_nonneg hw
              (mul_nonneg (complexEuclideanNorm_nonneg _)
                (complexEuclideanNorm_nonneg _)))
      _ ≤ Real.exp (-(ν * τ)) * (latticeModeWeight ij.1.1 *
            complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
            (latticeModeWeight ij.1.2 *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) := by
          refine mul_le_mul_of_nonneg_left ?_ ((Real.exp_pos _).le)
          conv_lhs => rw [← mul_assoc]
          exact hsub
      _ = c * outputHeatPairMajorant ν τ u v ij.1 := by
        unfold c outputHeatPairMajorant latticeWeightedAmplitude
        exact exp_prod_inv_cancel hsqrt
  have hfiber (k : LatticeMode) :
      ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ ≤
        c * outputHeatFiberMajorant ν τ u v k := by
    have hsum : Summable (fun ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
        c * outputHeatPairMajorant ν τ u v ij.1) :=
      ((summable_outputHeatPairMajorant ν τ u v).subtype
        (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))).mul_left c
    exact (tsum_of_norm_bounded hsum.hasSum (fun ij => hterm k ij)).trans
      (le_of_eq tsum_mul_left)
  have hFmaj : Summable (fun k => c * outputHeatFiberMajorant ν τ u v k) :=
    (summable_outputHeatFiberMajorant ν τ u v).mul_left c
  rw [norm_heatRegularizedSpectralOutput_eq_tsum ν τ hν hτ u v hu]
  calc (∑' k, ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖) ≤
      ∑' k, c * outputHeatFiberMajorant ν τ u v k :=
        Summable.tsum_le_tsum hfiber
          (summable_norm_constrainedHeatRegularizedFiber ν τ hν hτ u v hu) hFmaj
    _ = c * ∑' k, outputHeatFiberMajorant ν τ u v k := tsum_mul_left
    _ = c * ∑' ij : LatticeMode × LatticeMode,
        outputHeatPairMajorant ν τ u v ij := by
        congr 1; exact tsum_outputHeatFiberMajorant_eq_pair ν τ u v
    _ = c * ((Real.sqrt (ν * τ))⁻¹ * ‖u‖ * ‖v‖) := by
        congr 1; exact tsum_outputHeatPairMajorant_eq ν τ u v
    _ = Real.exp (-(ν * τ)) * ‖u‖ * ‖v‖ := by
        unfold c
        exact (exp_prod_inv_cancel hsqrt).symm.trans (mul_assoc _ _ _).symm

/-! ### 4. The two-branch gain for the completed positive-time integrand -/

/-- Branch-selected horizon-free gain for the actual positive-time nonlinear
heat output.  This strengthens the repo leaf
`norm_positiveTimeHeatRegularizedSpectralOutput_le` by replacing the
inverse-square-root kernel with `gapTimeGain` — equal at small scaled lag,
exponentially decaying at large scaled lag. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutput_le_gapTimeGain
    (ν : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (τ : ℝ) :
    ‖positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ‖ ≤
      gapTimeGain ν τ * ‖u‖ * ‖v‖ := by
  by_cases hτ : 0 < τ
  · by_cases hsmall : ν * τ ≤ 1
    · unfold gapTimeGain
      rw [if_pos hsmall]
      rw [outputHeatGain_eq_inverseSqrtTime ν τ hν hτ]
      exact norm_positiveTimeHeatRegularizedSpectralOutput_le ν hν u v hu hτ
    · unfold gapTimeGain
      rw [if_neg hsmall]
      rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν u v hu hτ]
      exact norm_heatRegularizedSpectralOutput_le_gap_exp ν τ hν hτ
        (lt_of_not_ge hsmall) u v hu
  · have hz : positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ = 0 := by
      simp [positiveTimeHeatRegularizedSpectralOutput, hτ]
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg (gapTimeGain_nonneg ν τ) (norm_nonneg _))
      (norm_nonneg _)

/-- Difference form of the branch-selected gain for the actual positive-time
nonlinear heat output. -/
theorem norm_positiveTimeHeatRegularizedSpectralOutput_gap_sub_le
    (ν : ℝ) (hν : 0 < ν)
    (u u' v v' : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hu' : LatticeDivergenceFree u')
    (τ : ℝ) :
    ‖positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ -
        positiveTimeHeatRegularizedSpectralOutput ν hν u' v' hu' τ‖ ≤
      gapTimeGain ν τ * (‖u‖ * ‖v - v'‖ + ‖u - u'‖ * ‖v'‖) := by
  have hright : positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ -
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
  have hleft : positiveTimeHeatRegularizedSpectralOutput ν hν u v' hu τ -
      positiveTimeHeatRegularizedSpectralOutput ν hν u' v' hu' τ =
      positiveTimeHeatRegularizedSpectralOutput ν hν (u - u') v' (hu.sub hu') τ := by
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
  have hdecomp : positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ -
      positiveTimeHeatRegularizedSpectralOutput ν hν u' v' hu' τ =
      positiveTimeHeatRegularizedSpectralOutput ν hν u (v - v') hu τ +
        positiveTimeHeatRegularizedSpectralOutput ν hν (u - u') v' (hu.sub hu') τ := by
    rw [← hright, ← hleft]
    abel
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  have ha := norm_positiveTimeHeatRegularizedSpectralOutput_le_gapTimeGain
    ν hν u (v - v') hu τ
  have hb := norm_positiveTimeHeatRegularizedSpectralOutput_le_gapTimeGain
    ν hν (u - u') v' (hu.sub hu') τ
  have hca : ‖positiveTimeHeatRegularizedSpectralOutput ν hν u (v - v') hu τ‖ ≤
      gapTimeGain ν τ * (‖u‖ * ‖v - v'‖) := by
    rw [← mul_assoc]
    exact ha
  have hcb : ‖positiveTimeHeatRegularizedSpectralOutput ν hν (u - u') v'
      (hu.sub hu') τ‖ ≤ gapTimeGain ν τ * (‖u - u'‖ * ‖v'‖) := by
    rw [← mul_assoc]
    exact hb
  calc ‖positiveTimeHeatRegularizedSpectralOutput ν hν u (v - v') hu τ‖ +
        ‖positiveTimeHeatRegularizedSpectralOutput ν hν (u - u') v'
          (hu.sub hu') τ‖ ≤
      gapTimeGain ν τ * (‖u‖ * ‖v - v'‖) +
        gapTimeGain ν τ * (‖u - u'‖ * ‖v'‖) := add_le_add hca hcb
    _ = gapTimeGain ν τ * (‖u‖ * ‖v - v'‖ + ‖u - u'‖ * ‖v'‖) := by ring

/-! ### 5. The horizon-free gap budget for the actual lag integral

The branch-selected kernel `gapTimeGain` is dominated on nonnegative lags by
the repo's inverse-square-root kernel (hence interval-integrable through the
existing `inverseSqrtTime_intervalIntegrable`), equals that kernel at small
scaled lag, and equals the pure exponential at large scaled lag.  Both branch
integrals are computed exactly, giving the horizon-free budget
`∫ u in (0)..t, gapTimeGain ν u ≤ 3 / ν` uniformly in the horizon `t`. -/

/-- Nonnegativity of the repo's inverse-square-root time kernel on
nonnegative time. -/
theorem inverseSqrtTime_nonneg_of_nonneg {τ : ℝ} (h : 0 ≤ τ) :
    0 ≤ inverseSqrtTime τ := by
  show 0 ≤ τ ^ (-(1 / 2 : ℝ))
  exact Real.rpow_nonneg h _

/-- The gap kernel vanishes at zero lag, matching the degenerate output at
zero heat time. -/
theorem gapTimeGain_zero (ν : ℝ) : gapTimeGain ν 0 = 0 := by
  unfold gapTimeGain
  rw [if_pos (by linarith)]
  simp

/-- Small scaled lag: the gap kernel equals the rescaled inverse-square-root
kernel. -/
theorem gapTimeGain_eq_small_branch (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (h : ν * τ ≤ 1) :
    gapTimeGain ν τ = (Real.sqrt ν)⁻¹ * inverseSqrtTime τ := by
  unfold gapTimeGain
  rw [if_pos h, outputHeatGain_eq_inverseSqrtTime ν τ hν hτ]

/-- Large scaled lag: the gap kernel is exactly the spectral-gap exponential. -/
theorem gapTimeGain_eq_exp_branch (ν τ : ℝ) (h : 1 < ν * τ) :
    gapTimeGain ν τ = Real.exp (-ν * τ) := by
  unfold gapTimeGain
  rw [if_neg (by linarith)]
  congr 1
  ring

/-- The gap kernel is dominated pointwise on nonnegative lags by the repo's
inverse-square-root kernel. -/
theorem gapTimeGain_le_kernel (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 ≤ τ) :
    gapTimeGain ν τ ≤ (Real.sqrt ν)⁻¹ * inverseSqrtTime τ := by
  rcases eq_or_lt_of_le hτ with h | h
  · rw [← h, gapTimeGain_zero]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg ν))
      (inverseSqrtTime_nonneg_of_nonneg (le_refl 0))
  · exact gapTimeGain_le_inverseSqrtTime ν τ hν h

private theorem gap_kernel_small_measurable (ν : ℝ) :
    Measurable (fun τ : ℝ => (Real.sqrt (ν * τ))⁻¹) :=
  Measurable.inv
    (Real.continuous_sqrt.measurable.comp (measurable_const.mul measurable_id))

private theorem gap_kernel_exp_measurable (ν : ℝ) :
    AEMeasurable (fun τ : ℝ => Real.exp (-ν * τ)) volume :=
  ((Real.continuous_exp : Continuous Real.exp).measurable.comp
      ((measurable_const : Measurable (fun _ : ℝ => (-ν))).mul
        measurable_id)).aemeasurable

private theorem gap_kernel_branch_measurable (ν : ℝ) :
    MeasurableSet {τ : ℝ | ν * τ ≤ 1} := by
  have h : {τ : ℝ | ν * τ ≤ 1} = (fun τ : ℝ => ν * τ) ⁻¹' Iic (1 : ℝ) := rfl
  rw [h]
  exact isClosed_Iic.measurableSet.preimage (measurable_const.mul measurable_id)

private theorem gap_kernel_branch_compl_measurable (ν : ℝ) :
    MeasurableSet {τ : ℝ | ¬(ν * τ ≤ 1)} :=
  (gap_kernel_branch_measurable ν).compl

private theorem gap_kernel_eq_indicators (ν : ℝ) :
    (fun τ : ℝ => gapTimeGain ν τ) =
      ({x : ℝ | ν * x ≤ 1}).indicator (fun τ => (Real.sqrt (ν * τ))⁻¹) +
        ({x : ℝ | ¬(ν * x ≤ 1)}).indicator (fun τ => Real.exp (-ν * τ)) := by
  refine funext (fun τ => ?_)
  unfold gapTimeGain
  by_cases h : ν * τ ≤ 1
  · show (if ν * τ ≤ 1 then (Real.sqrt (ν * τ))⁻¹ else Real.exp (-(ν * τ))) =
      ({x : ℝ | ν * x ≤ 1}).indicator (fun y => (Real.sqrt (ν * y))⁻¹) τ +
        ({x : ℝ | ¬(ν * x ≤ 1)}).indicator (fun y => Real.exp (-ν * y)) τ
    simp [h]
  · show (if ν * τ ≤ 1 then (Real.sqrt (ν * τ))⁻¹ else Real.exp (-(ν * τ))) =
      ({x : ℝ | ν * x ≤ 1}).indicator (fun y => (Real.sqrt (ν * y))⁻¹) τ +
        ({x : ℝ | ¬(ν * x ≤ 1)}).indicator (fun y => Real.exp (-ν * y)) τ
    simp [h]
    exact (indicator_of_mem
      (show τ ∈ {x : ℝ | 1 < ν * x} from not_le.mp h)
      (fun y : ℝ => Real.exp (-(ν * y)))).symm

/-- The gap kernel is almost-everywhere measurable. -/
theorem gap_kernel_aemeasurable (ν : ℝ) :
    AEMeasurable (fun τ : ℝ => gapTimeGain ν τ) volume := by
  rw [gap_kernel_eq_indicators ν]
  refine AEMeasurable.add ?_ ?_
  · exact AEMeasurable.indicator
      (gap_kernel_small_measurable ν).aemeasurable (gap_kernel_branch_measurable ν)
  · exact AEMeasurable.indicator (gap_kernel_exp_measurable ν)
      (gap_kernel_branch_compl_measurable ν)

/-- The gap kernel is interval-integrable on every nonnegative interval. -/
theorem intervalIntegrable_gapTimeGain (ν : ℝ) (hν : 0 < ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => gapTimeGain ν u) volume a b := by
  have hmaj : IntervalIntegrable
      (fun u : ℝ => (Real.sqrt ν)⁻¹ * inverseSqrtTime u) volume a b := by
    refine IntervalIntegrable.const_mul ?_ _
    by_cases h0 : a = 0
    · subst h0
      exact inverseSqrtTime_intervalIntegrable b
    · refine intervalIntegral.intervalIntegrable_rpow (Or.inr ?_)
      intro hmem
      rcases mem_uIcc.mp hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h0 (le_antisymm h1 ha)
      · exact h0 (le_antisymm (le_trans hab h1) ha)
  refine hmaj.mono_fun'
    ((gap_kernel_aemeasurable ν).aestronglyMeasurable.mono_measure
      (Measure.restrict_le_self (μ := volume) (s := uIoc a b)))
    ?_
  filter_upwards [ae_restrict_mem (measurableSet_uIoc)] with u hu
  rcases mem_uIoc.mp hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · have hge : 0 ≤ u := le_trans ha (le_of_lt hl)
    have hle := gapTimeGain_le_kernel ν u hν hge
    simpa [abs_of_nonneg (gapTimeGain_nonneg ν u),
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg ν))
        (inverseSqrtTime_nonneg_of_nonneg hge))] using hle
  · linarith

/-- Change of variables for the gap kernel across the lag map. -/
theorem gapTimeGain_integral_comp_sub (ν t : ℝ) :
    (∫ s in (0 : ℝ)..t, gapTimeGain ν (t - s)) =
      ∫ u in (0 : ℝ)..t, gapTimeGain ν u := by
  have he : (∫ s in (0 : ℝ)..t, gapTimeGain ν (t - s)) =
      ∫ u in t - t..t - (0 : ℝ), gapTimeGain ν u :=
    intervalIntegral.integral_comp_sub_left (fun x => gapTimeGain ν x) t
  rw [he, sub_self, sub_zero]

private theorem gapTimeGain_integral_small (ν t : ℝ) (hν : 0 < ν)
    (ht : 0 ≤ t) (hle : t ≤ ν⁻¹) :
    (∫ u in (0 : ℝ)..t, gapTimeGain ν u) ≤ 2 * ν⁻¹ := by
  have hinv : ν * ν⁻¹ = 1 := by field_simp
  have hae : ∀ᵐ (u : ℝ) ∂volume, u ∈ uIoc 0 t →
      gapTimeGain ν u = (Real.sqrt ν)⁻¹ * inverseSqrtTime u := by
    refine ae_of_all volume (fun u hu => ?_)
    rcases mem_uIoc.mp hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · refine gapTimeGain_eq_small_branch ν u hν hl ?_
      exact (mul_le_mul_of_nonneg_left (le_trans hr hle) hν.le).trans
        (le_of_eq hinv)
    · linarith
  have h1 : (∫ u in (0 : ℝ)..t, gapTimeGain ν u) =
      ∫ u in (0 : ℝ)..t, (Real.sqrt ν)⁻¹ * inverseSqrtTime u :=
    intervalIntegral.integral_congr_ae hae
  rw [h1, intervalIntegral.integral_const_mul,
    integral_inverseSqrtTime_zero t ht]
  have hs : Real.sqrt t ≤ (Real.sqrt ν)⁻¹ := by
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt hle
  have hsq : Real.sqrt ν ≠ 0 := Real.sqrt_ne_zero'.mpr hν
  have hsq2 : (Real.sqrt ν)⁻¹ * (Real.sqrt ν)⁻¹ = ν⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt hν.le]
  calc (Real.sqrt ν)⁻¹ * (2 * Real.sqrt t) ≤
      (Real.sqrt ν)⁻¹ * (2 * (Real.sqrt ν)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 2 by norm_num))
          (inv_nonneg.mpr (Real.sqrt_nonneg ν))
    _ = 2 * ((Real.sqrt ν)⁻¹ * (Real.sqrt ν)⁻¹) := by ring
    _ = 2 * ν⁻¹ := by rw [hsq2]

private theorem integral_exp_neg_mul (ν A B : ℝ) (hν : 0 < ν) :
    (∫ u in A..B, Real.exp (-ν * u)) =
      (Real.exp (-ν * A) - Real.exp (-ν * B)) * ν⁻¹ := by
  have hc : (-ν : ℝ) ≠ 0 := by linarith
  rw [intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp]
  simp only [smul_eq_mul]
  ring

private theorem integral_exp_neg_le (ν A B : ℝ) (hν : 0 < ν) (hA : 0 ≤ A) :
    (∫ u in A..B, Real.exp (-ν * u)) ≤ ν⁻¹ := by
  rw [integral_exp_neg_mul ν A B hν]
  have h1 : Real.exp (-ν * B) ≥ 0 := (Real.exp_pos _).le
  have h2 : Real.exp (-ν * A) ≤ 1 :=
    (Real.exp_le_exp.mpr (show -ν * A ≤ 0 by nlinarith)).trans
      (le_of_eq Real.exp_zero)
  calc (Real.exp (-ν * A) - Real.exp (-ν * B)) * ν⁻¹ ≤
      (1 - 0) * ν⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hν.le)
        linarith
    _ = ν⁻¹ := by ring

private theorem gapTimeGain_integral_large (ν t : ℝ) (hν : 0 < ν)
    (hgt : ν⁻¹ < t) :
    (∫ u in (0 : ℝ)..t, gapTimeGain ν u) ≤ 3 * ν⁻¹ := by
  have h1 : IntervalIntegrable (fun u => gapTimeGain ν u) volume 0 ν⁻¹ :=
    intervalIntegrable_gapTimeGain ν hν (le_refl 0) (inv_nonneg.mpr hν.le)
  have h2 : IntervalIntegrable (fun u => gapTimeGain ν u) volume ν⁻¹ t :=
    intervalIntegrable_gapTimeGain ν hν (inv_nonneg.mpr hν.le) (le_of_lt hgt)
  have hsplit : (∫ u in (0 : ℝ)..t, gapTimeGain ν u) =
      (∫ u in (0 : ℝ)..ν⁻¹, gapTimeGain ν u) +
        ∫ u in ν⁻¹..t, gapTimeGain ν u :=
    (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hsmall := gapTimeGain_integral_small ν ν⁻¹ hν (inv_nonneg.mpr hν.le)
    (le_refl _)
  have hinv : ν * ν⁻¹ = 1 := by field_simp
  have hae : ∀ᵐ (u : ℝ) ∂volume, u ∈ uIoc ν⁻¹ t →
      gapTimeGain ν u = Real.exp (-ν * u) := by
    refine ae_of_all volume (fun u hu => ?_)
    rcases mem_uIoc.mp hu with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · refine gapTimeGain_eq_exp_branch ν u ?_
      have hlt : ν * ν⁻¹ < ν * u := mul_lt_mul_of_pos_left hl hν
      rw [hinv] at hlt
      exact hlt
    · linarith
  have heq : (∫ u in ν⁻¹..t, gapTimeGain ν u) =
      ∫ u in ν⁻¹..t, Real.exp (-ν * u) :=
    intervalIntegral.integral_congr_ae hae
  rw [hsplit, heq]
  have hb := integral_exp_neg_le ν ν⁻¹ t hν (inv_nonneg.mpr hν.le)
  linarith

/-- Horizon-free gap budget: for every nonnegative horizon the gap kernel's
integral is at most `3 / ν`. -/
theorem gapTimeGain_integral_budget (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, gapTimeGain ν u) ≤ 3 * ν⁻¹ := by
  by_cases hle : t ≤ ν⁻¹
  · exact (gapTimeGain_integral_small ν t hν ht hle).trans (by linarith)
  · exact gapTimeGain_integral_large ν t hν (by linarith)

/-! ### 6. Gap-budget estimates for the genuine Duhamel term -/

/-- Pointwise gap gain for the genuine evolving-path nonlinear integrand
before the observation time. -/
theorem norm_criticalMildPathIntegrand_le_gap
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t s : ℝ) :
    ‖criticalMildPathIntegrand ν hν u hu t s‖ ≤
      gapTimeGain ν (t - s) * ‖u s‖ ^ 2 := by
  unfold criticalMildPathIntegrand
  calc
      ‖positiveTimeHeatRegularizedSpectralOutput ν hν (u s) (u s) (hu s)
          (t - s)‖ ≤
        gapTimeGain ν (t - s) * ‖u s‖ * ‖u s‖ :=
      norm_positiveTimeHeatRegularizedSpectralOutput_le_gapTimeGain ν hν
        (u s) (u s) (hu s) (t - s)
    _ = gapTimeGain ν (t - s) * ‖u s‖ ^ 2 := by ring

/-- Radius form of the pointwise gap gain: at the degenerate endpoint
`s = t` both sides vanish through the zero-lag branches. -/
theorem norm_criticalMildPathIntegrand_le_gap_of_norm_le
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t s : ℝ} (hR : 0 ≤ R) (hst : s ≤ t) (huR : ‖u s‖ ≤ R) :
    ‖criticalMildPathIntegrand ν hν u hu t s‖ ≤
      gapTimeGain ν (t - s) * R ^ 2 := by
  rcases hst.eq_or_lt with hst | hst
  · subst hst
    simp [criticalMildPathIntegrand, positiveTimeHeatRegularizedSpectralOutput,
      gapTimeGain]
  · refine (norm_criticalMildPathIntegrand_le_gap ν hν u hu t s).trans
      (mul_le_mul_of_nonneg_left ?_ (gapTimeGain_nonneg ν (t - s)))
    exact (sq_le_sq₀ (norm_nonneg _) hR).2 huR

/-- Horizon-free gap budget for the genuine evolving-path Duhamel integral:
the small-lag gain singularity is absorbed together with the spectral gap,
replacing the repo's horizon-growing constant `2 sqrt t / sqrt ν` by the
uniform `3 / ν`.  Derivation of the small-data constants: at radius
`R = 2 ‖a‖` and `‖a‖ ≤ ν / 16`, this bound is `(3/ν) · 4 ‖a‖² ≤ 3 ‖a‖ / 4`,
so the image stays in the `2 ‖a‖` ball. -/
theorem norm_criticalMildDuhamel_le_gap
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    ‖criticalMildDuhamel ν hν u hu t‖ ≤ (3 * ν⁻¹) * R ^ 2 := by
  have hactual :=
    integrableOn_criticalMildPathIntegrand ν hν u huc hu hR ht huR
  have hkmaj : IntervalIntegrable
      (fun s : ℝ => gapTimeGain ν (t - s) * R ^ 2) volume 0 t := by
    have hlag : IntervalIntegrable
        (fun s => gapTimeGain ν (t - s)) volume t 0 := by
      simpa using
        (intervalIntegrable_gapTimeGain ν hν (le_refl 0) ht).comp_sub_left t
    exact hlag.symm.mul_const (R ^ 2)
  have hscalar :
      IntegrableOn (fun s : ℝ => gapTimeGain ν (t - s) * R ^ 2)
        (Ioc 0 t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hkmaj
  have hmono :
      (fun s => ‖criticalMildPathIntegrand ν hν u hu t s‖) ≤ᵐ[
        volume.restrict (Ioc 0 t)] fun s => gapTimeGain ν (t - s) * R ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact norm_criticalMildPathIntegrand_le_gap_of_norm_le ν hν u hu hR hs.2
      (huR s hs)
  unfold criticalMildDuhamel
  calc
    ‖∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hu t s‖ ≤
        ∫ s in Ioc 0 t, ‖criticalMildPathIntegrand ν hν u hu t s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc 0 t, (fun s => gapTimeGain ν (t - s) * R ^ 2) s :=
      integral_mono_ae hactual.norm hscalar hmono
    _ = ∫ s in (0 : ℝ)..t, gapTimeGain ν (t - s) * R ^ 2 := by
      rw [← intervalIntegral.integral_of_le ht]
    _ = (∫ s in (0 : ℝ)..t, gapTimeGain ν (t - s)) * R ^ 2 := by
      rw [intervalIntegral.integral_mul_const]
    _ = (∫ u in (0 : ℝ)..t, gapTimeGain ν u) * R ^ 2 := by
      rw [gapTimeGain_integral_comp_sub]
    _ ≤ (3 * ν⁻¹) * R ^ 2 :=
      mul_le_mul_of_nonneg_right (gapTimeGain_integral_budget ν t hν ht)
        (sq_nonneg R)

/-- Pointwise gap gain for the difference of two genuine path integrands. -/
theorem norm_criticalMildPathIntegrand_sub_le_gap
    (ν : ℝ) (hν : 0 < ν)
    (u v : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (hv : ∀ s, LatticeDivergenceFree (v s))
    {t s : ℝ} (hst : s ≤ t) :
    ‖criticalMildPathIntegrand ν hν u hu t s -
        criticalMildPathIntegrand ν hν v hv t s‖ ≤
      gapTimeGain ν (t - s) * (‖u s‖ * ‖u s - v s‖ + ‖u s - v s‖ * ‖v s‖) := by
  rcases hst.eq_or_lt with hst | hst
  · subst hst
    simp [criticalMildPathIntegrand, positiveTimeHeatRegularizedSpectralOutput,
      gapTimeGain]
  · unfold criticalMildPathIntegrand
    exact norm_positiveTimeHeatRegularizedSpectralOutput_gap_sub_le ν hν
      (u s) (v s) (u s) (v s) (hu s) (hv s) (t - s)

theorem norm_criticalMildPathIntegrand_sub_le_gap_of_norm_bounds
    (ν : ℝ) (hν : 0 < ν)
    (u v : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (hv : ∀ s, LatticeDivergenceFree (v s))
    {R D t s : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) (hst : s ≤ t)
    (huR : ‖u s‖ ≤ R) (hvR : ‖v s‖ ≤ R) (hsub : ‖u s - v s‖ ≤ D) :
    ‖criticalMildPathIntegrand ν hν u hu t s -
        criticalMildPathIntegrand ν hν v hv t s‖ ≤
      gapTimeGain ν (t - s) * (2 * R * D) := by
  refine (norm_criticalMildPathIntegrand_sub_le_gap ν hν u v hu hv hst).trans
    (mul_le_mul_of_nonneg_left ?_ (gapTimeGain_nonneg ν (t - s)))
  have h1 : ‖u s‖ * ‖u s - v s‖ ≤ R * D :=
    mul_le_mul huR hsub (norm_nonneg _) hR
  have h2 : ‖u s - v s‖ * ‖v s‖ ≤ D * R :=
    mul_le_mul hsub hvR (norm_nonneg _) hD
  calc ‖u s‖ * ‖u s - v s‖ + ‖u s - v s‖ * ‖v s‖ ≤ R * D + D * R :=
      add_le_add h1 h2
    _ = 2 * R * D := by ring

/-- Horizon-free Lipschitz estimate for the genuine Duhamel operator on a
radius-`R` ball with separation `D`: at `R = 2 ‖a‖`, `D = ‖v − w‖∞` and
`‖a‖ ≤ ν / 16` the coefficient `6 ‖a‖ / ν ≤ 3/4 < 1`, the contraction
factor of the global self-map. -/
theorem norm_criticalMildDuhamel_sub_le_gap
    (ν : ℝ) (hν : 0 < ν)
    (u v : ℝ → WeightedLatticeBanach)
    (huc : Continuous u) (hvc : Continuous v)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (hv : ∀ s, LatticeDivergenceFree (v s))
    {R D t : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hvR : ∀ s ∈ Ioc (0 : ℝ) t, ‖v s‖ ≤ R)
    (huvD : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s - v s‖ ≤ D) :
    ‖criticalMildDuhamel ν hν u hu t -
        criticalMildDuhamel ν hν v hv t‖ ≤
      (3 * ν⁻¹) * (2 * R) * D := by
  have hintu :=
    integrableOn_criticalMildPathIntegrand ν hν u huc hu hR ht huR
  have hintv :=
    integrableOn_criticalMildPathIntegrand ν hν v hvc hv hR ht hvR
  have hkmaj : IntervalIntegrable
      (fun s : ℝ => gapTimeGain ν (t - s) * (2 * R * D)) volume 0 t := by
    have hlag : IntervalIntegrable
        (fun s => gapTimeGain ν (t - s)) volume t 0 := by
      simpa using
        (intervalIntegrable_gapTimeGain ν hν (le_refl 0) ht).comp_sub_left t
    exact hlag.symm.mul_const (2 * R * D)
  have hscalar :
      IntegrableOn (fun s : ℝ => gapTimeGain ν (t - s) * (2 * R * D))
        (Ioc 0 t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hkmaj
  have hmono :
      (fun s => ‖criticalMildPathIntegrand ν hν u hu t s -
        criticalMildPathIntegrand ν hν v hv t s‖) ≤ᵐ[
          volume.restrict (Ioc 0 t)]
        fun s => gapTimeGain ν (t - s) * (2 * R * D) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact norm_criticalMildPathIntegrand_sub_le_gap_of_norm_bounds ν hν u v
      hu hv hR hD hs.2 (huR s hs) (hvR s hs) (huvD s hs)
  unfold criticalMildDuhamel
  rw [← integral_sub hintu hintv]
  calc
    ‖∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hu t s -
          criticalMildPathIntegrand ν hν v hv t s‖ ≤
        ∫ s in Ioc 0 t, ‖criticalMildPathIntegrand ν hν u hu t s -
            criticalMildPathIntegrand ν hν v hv t s‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioc 0 t,
          (fun s => gapTimeGain ν (t - s) * (2 * R * D)) s :=
      integral_mono_ae (hintu.sub hintv).norm hscalar hmono
    _ = ∫ s in (0 : ℝ)..t, gapTimeGain ν (t - s) * (2 * R * D) := by
      rw [← intervalIntegral.integral_of_le ht]
    _ = (∫ s in (0 : ℝ)..t, gapTimeGain ν (t - s)) * (2 * R * D) := by
      rw [intervalIntegral.integral_mul_const]
    _ = (∫ u in (0 : ℝ)..t, gapTimeGain ν u) * (2 * R * D) := by
      rw [gapTimeGain_integral_comp_sub]
    _ ≤ (3 * ν⁻¹) * (2 * R * D) :=
      mul_le_mul_of_nonneg_right (gapTimeGain_integral_budget ν t hν ht)
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR) hD)
    _ = (3 * ν⁻¹) * (2 * R) * D := by ring

/-! ### 7. Spectral-gap decay of the completed heat flow -/

/-- Per-coordinate gap decay of the same-weight heat flow: a mode whose
coefficient vanishes (the zero mode, under the exact zero-mode predicate
`a 0 = 0`) contributes nothing, and every nonzero lattice frequency carries
the gap `1 ≤ ‖complexFrequency (latticeFrequency m)‖`, so its scalar heat
factor is at most `Real.exp (-ν * τ)`. -/
theorem norm_weightedHeatFlowCoordinate_le_gap_exp
    (ν τ : ℝ) (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (a : WeightedLatticeBanach) {m : LatticeMode}
    (hz : m = 0 → a 0 = 0) :
    ‖weightedHeatFlowCoordinate ν τ a m‖ ≤
      Real.exp (-ν * τ) * ‖a m‖ := by
  by_cases hm : m = 0
  · subst hm
    have hc : weightedHeatFlowCoordinate ν τ a 0 = a 0 := by
      unfold weightedHeatFlowCoordinate
      rw [Navier.Analysis.CriticalMildZeroMode.latticeFrequency_zero,
        complexFrequencyHeatLeray_zero_frequency]
      exact Navier.Analysis.CriticalMildHeatFlowLinear.latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient a 0
    rw [hc, hz (rfl (a := (0 : LatticeMode)))]
    simp
  · unfold weightedHeatFlowCoordinate
    rw [norm_smul, Real.norm_of_nonneg
      (zero_le_one.trans (one_le_latticeModeWeight m))]
    change latticeModeWeight m *
        complexEuclideanNorm
          (complexFrequencyHeatLeray ν τ (latticeFrequency m)
            (weightedLatticeCoefficient a m)) ≤
      Real.exp (-ν * τ) * ‖a m‖
    calc
      latticeModeWeight m *
          complexEuclideanNorm
            (complexFrequencyHeatLeray ν τ (latticeFrequency m)
              (weightedLatticeCoefficient a m)) ≤
        latticeModeWeight m *
          (complexHeatDecay ν τ (latticeFrequency m) *
            complexEuclideanNorm (weightedLatticeCoefficient a m)) := by
        refine mul_le_mul_of_nonneg_left
          (complexEuclideanNorm_heatLeray_le_decay ν τ m
            (weightedLatticeCoefficient a m)) ?_
        exact zero_le_one.trans (one_le_latticeModeWeight m)
      _ = complexHeatDecay ν τ (latticeFrequency m) *
          (latticeModeWeight m *
            complexEuclideanNorm (weightedLatticeCoefficient a m)) := by ring
      _ = complexHeatDecay ν τ (latticeFrequency m) * ‖a m‖ := by
        rw [show latticeModeWeight m *
              complexEuclideanNorm (weightedLatticeCoefficient a m) = ‖a m‖
            from latticeWeightedAmplitude_coefficient a m]
      _ ≤ Real.exp (-ν * τ) * ‖a m‖ := by
        refine mul_le_mul_of_nonneg_right
          (complexHeatDecay_latticeFrequency_le_gap_exp ν τ hν hτ hm) ?_
        exact norm_nonneg _

/-- Zero-mode-vanishing initial data decays under the completed heat flow at
the full gap rate: `‖weightedHeatFlow ν τ _ _ a‖ ≤ exp (-ν τ) · ‖a‖`. -/
theorem norm_weightedHeatFlow_le_gap_exp
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 ≤ τ)
    (a : WeightedLatticeBanach) (ha : a 0 = 0) :
    ‖weightedHeatFlow ν τ hν.le hτ a‖ ≤
      Real.exp (-ν * τ) * ‖a‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  change (∑' m : LatticeMode, ‖weightedHeatFlowCoordinate ν τ a m‖ ^ (1 : ℝ)) ^
      (1 / (1 : ℝ)) ≤ Real.exp (-ν * τ) * ‖a‖
  rw [show (1 : ℝ) / 1 = 1 by norm_num, Real.rpow_one]
  have hflow : Summable
      (fun m : LatticeMode => ‖weightedHeatFlowCoordinate ν τ a m‖) := by
    simpa [weightedHeatFlow] using
      (weightedHeatFlow ν τ hν.le hτ a).2.summable
  have hu : Summable (fun m : LatticeMode => ‖a m‖) := by
    simpa using a.2.summable
  have hgd : Summable
      (fun m : LatticeMode => Real.exp (-ν * τ) * ‖a m‖) :=
    hu.mul_left _
  calc
    (∑' m : LatticeMode, ‖weightedHeatFlowCoordinate ν τ a m‖ ^ (1 : ℝ)) =
        ∑' m : LatticeMode, ‖weightedHeatFlowCoordinate ν τ a m‖ := by
      apply congrArg tsum
      funext m
      exact Real.rpow_one _
    _ ≤ ∑' m : LatticeMode, Real.exp (-ν * τ) * ‖a m‖ :=
      Summable.tsum_le_tsum
        (fun m => norm_weightedHeatFlowCoordinate_le_gap_exp ν τ hν.le hτ a
          (fun _ => ha)) hflow hgd
    _ = Real.exp (-ν * τ) * ∑' m : LatticeMode, ‖a m‖ :=
      tsum_mul_left
    _ = Real.exp (-ν * τ) * ‖a‖ := by
      rw [show (∑' m : LatticeMode, ‖a m‖) = ‖a‖ from
        by simp [lp.norm_eq_tsum_rpow]]

/-! ### 8. Horizon-free estimates for the assembled mild image -/

/-- Gap estimate for the assembled critical mild image: gap decay of the
zero-mode-vanishing datum plus the horizon-free `3 / ν` Duhamel budget. -/
theorem norm_criticalMildImage_gap_le
    (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    ‖criticalMildImage ν hν a u hu t ht‖ ≤
      Real.exp (-ν * t) * ‖a‖ + (3 * ν⁻¹) * R ^ 2 := by
  unfold criticalMildImage
  calc
      ‖weightedHeatFlow ν t hν.le ht a + criticalMildDuhamel ν hν u hu t‖ ≤
        ‖weightedHeatFlow ν t hν.le ht a‖ +
          ‖criticalMildDuhamel ν hν u hu t‖ := norm_add_le _ _
    _ ≤ Real.exp (-ν * t) * ‖a‖ + (3 * ν⁻¹) * R ^ 2 :=
      add_le_add
        (norm_weightedHeatFlow_le_gap_exp ν t hν ht a ha)
        (norm_criticalMildDuhamel_le_gap ν hν u huc hu hR ht huR)

/-- Horizon-free Lipschitz estimate for the assembled mild image at a fixed
initial datum: the linear parts cancel exactly. -/
theorem norm_criticalMildImage_sub_le_gap
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (u v : ℝ → WeightedLatticeBanach)
    (huc : Continuous u) (hvc : Continuous v)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (hv : ∀ s, LatticeDivergenceFree (v s))
    {R D t : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hvR : ∀ s ∈ Ioc (0 : ℝ) t, ‖v s‖ ≤ R)
    (huvD : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s - v s‖ ≤ D) :
    ‖criticalMildImage ν hν a u hu t ht -
        criticalMildImage ν hν a v hv t ht‖ ≤
      (3 * ν⁻¹) * (2 * R) * D := by
  unfold criticalMildImage
  rw [add_sub_add_left_eq_sub]
  exact norm_criticalMildDuhamel_sub_le_gap ν hν u v huc hvc hu hv hR hD ht
    huR hvR huvD

/-! ### 9a. Horizon-free gap endomap on the repo local ball -/

/-- The small-data gap budget: with `R = 2 ‖a‖` and `‖a‖ ≤ ν / 16`, the
horizon-free image budget closes at the ball radius.  Derivation:
`(3/ν) · R² = (3/ν) · 4‖a‖² = (12‖a‖/ν)·‖a‖ ≤ (3/4)‖a‖ ≤ ‖a‖`, so
`‖a‖ + (3/ν)·R² ≤ 2‖a‖ = R`. -/
theorem smallData_gap_budget_le
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (ha16 : ‖a‖ ≤ ν / 16) :
    ‖a‖ + (3 * ν⁻¹) * (2 * ‖a‖) ^ 2 ≤ 2 * ‖a‖ := by
  have h1 : (3 * ν⁻¹) * (2 * ‖a‖) ^ 2 ≤ (3 / 4 : ℝ) * ‖a‖ := by
    have hq : (2 * ‖a‖) ^ 2 = 4 * ‖a‖ ^ 2 := by ring
    rw [hq]
    have h2 : (3 * ν⁻¹) * (4 * ‖a‖ ^ 2) = 12 * (‖a‖ / ν) * ‖a‖ := by
      field_simp [ne_of_gt hν]
      ring
    rw [h2]
    have h3 : ‖a‖ / ν ≤ (1 / 16 : ℝ) := by
      refine (div_le_iff₀ (by positivity)).mpr ?_
      linarith
    nlinarith [norm_nonneg a, h3]
  nlinarith [norm_nonneg a]

/-- The horizon-free gap contraction factor stays strictly below one. -/
theorem smallData_gap_contraction_lt_one
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (ha16 : ‖a‖ ≤ ν / 16) :
    (3 * ν⁻¹) * (2 * (2 * ‖a‖)) < 1 := by
  have h1 : (3 * ν⁻¹) * (2 * (2 * ‖a‖)) = 12 * ‖a‖ / ν := by
    field_simp [ne_of_gt hν]
    ring
  rw [h1]
  refine div_lt_one (by linarith) |>.mpr ?_
  have h2 : 12 * ‖a‖ ≤ 12 * (ν / 16) :=
    mul_le_mul_of_nonneg_left ha16 (by norm_num)
  linarith

/-! ### 9b. The horizon-free gap endomap on the repo local ball -/

/-- Horizon-free gap endomap on the repo local ball: the mild image of the
`IccExtend` clamp of a ball path, carried by the horizon-free budget
`‖a‖ + (3 / ν) · R² ≤ R` (no horizon factor, unlike the repo budget
`‖u₀‖ + (2√T/√ν)·R² ≤ R`). -/
def gapBallImage
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖a‖ + (3 * ν⁻¹) * R ^ 2 ≤ R)
    (u : CriticalMildPathBall T R) : CriticalMildPathBall T R := by
  let p : CriticalMildPath T := u.1
  let ext : ℝ → WeightedLatticeBanach := criticalMildPathExtension T hT p
  have hextc : Continuous ext := continuous_criticalMildPathExtension T hT p
  have hextdf : ∀ s, LatticeDivergenceFree (ext s) := by
    intro s
    exact criticalMildPathBallExtension_divergenceFree hT u s
  have hextR : ∀ s, ‖ext s‖ ≤ R := by
    intro s
    exact criticalMildPathBallExtension_norm_le hT u s
  refine ⟨⟨fun τ => criticalMildImage ν hν a ext hextdf τ.1 τ.2.1, ?_⟩, ?_⟩
  · exact continuous_criticalMildImage_on_Icc ν hν a ext hextc hextdf hR hT hextR
  · intro τ
    constructor
    · exact criticalMildImage_divergenceFree ν hν a ext hextc hextdf hR τ.2.1
        (fun s hs => hextR s)
    · have hτ0 : 0 ≤ (τ : ℝ) := τ.2.1
      have hexp : Real.exp (-ν * τ.1) ≤ 1 :=
        (Real.exp_le_exp.mpr (show -ν * τ.1 ≤ 0 by nlinarith)).trans
          (le_of_eq Real.exp_zero)
      have hdecay : Real.exp (-ν * τ.1) * ‖a‖ ≤ ‖a‖ :=
        (mul_le_mul_of_nonneg_right hexp (norm_nonneg a)).trans (one_mul _).le
      calc
        ‖criticalMildImage ν hν a ext hextdf τ.1 τ.2.1‖ ≤
            Real.exp (-ν * τ.1) * ‖a‖ + (3 * ν⁻¹) * R ^ 2 :=
          norm_criticalMildImage_gap_le ν hν a ha ext hextc hextdf hR τ.2.1
            (fun s hs => hextR s)
        _ ≤ ‖a‖ + (3 * ν⁻¹) * R ^ 2 := add_le_add hdecay le_rfl
        _ ≤ R := hbudget

/-- Uniform path-norm gap Lipschitz estimate for the ball endomap: the
horizon-free coefficient `(3 / ν) · (2R)`. -/
theorem norm_gapBallImage_sub_le
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖a‖ + (3 * ν⁻¹) * R ^ 2 ≤ R)
    (u v : CriticalMildPathBall T R) :
    ‖(gapBallImage ν hν a ha hT hR hbudget u).1 -
        (gapBallImage ν hν a ha hT hR hbudget v).1‖ ≤
      (3 * ν⁻¹) * (2 * R) * ‖u.1 - v.1‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro τ
  let pu : CriticalMildPath T := u.1
  let pv : CriticalMildPath T := v.1
  let eu : ℝ → WeightedLatticeBanach := criticalMildPathExtension T hT pu
  let ev : ℝ → WeightedLatticeBanach := criticalMildPathExtension T hT pv
  have heuc : Continuous eu := continuous_criticalMildPathExtension T hT pu
  have hevc : Continuous ev := continuous_criticalMildPathExtension T hT pv
  have heudf : ∀ s, LatticeDivergenceFree (eu s) := by
    intro s
    exact criticalMildPathBallExtension_divergenceFree hT u s
  have hevdf : ∀ s, LatticeDivergenceFree (ev s) := by
    intro s
    exact criticalMildPathBallExtension_divergenceFree hT v s
  have heuR : ∀ s, ‖eu s‖ ≤ R := by
    intro s
    exact criticalMildPathBallExtension_norm_le hT u s
  have hevR : ∀ s, ‖ev s‖ ≤ R := by
    intro s
    exact criticalMildPathBallExtension_norm_le hT v s
  have hD : ∀ s, ‖eu s - ev s‖ ≤ ‖u.1 - v.1‖ := by
    intro s
    exact norm_criticalMildPathExtension_sub_le T hT pu pv s
  change ‖criticalMildImage ν hν a eu heudf τ.1 τ.2.1 -
      criticalMildImage ν hν a ev hevdf τ.1 τ.2.1‖ ≤ _
  exact norm_criticalMildImage_sub_le_gap ν hν a eu ev heuc hevc heudf hevdf
    hR (norm_nonneg _) τ.2.1 (fun s hs => heuR s) (fun s hs => hevR s)
    (fun s hs => hD s)

/-- Under the horizon-free gap contraction condition the ball endomap is a
strict contraction in the inherited uniform path metric. -/
theorem gapBallImage_contractingWith
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖a‖ + (3 * ν⁻¹) * R ^ 2 ≤ R)
    (hcontr : (3 * ν⁻¹) * (2 * R) < 1) :
    ContractingWith
      ⟨(3 * ν⁻¹) * (2 * R), by positivity⟩
      (gapBallImage ν hν a ha hT hR hbudget) := by
  constructor
  · exact hcontr
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm_sub, dist_eq_norm_sub]
    exact norm_gapBallImage_sub_le ν hν a ha hT hR hbudget u v

/-- Banach fixed-point existence for the horizon-free gap ball endomap. -/
theorem exists_gapBallPathBall_fixedPoint
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖a‖ + (3 * ν⁻¹) * R ^ 2 ≤ R)
    (hcontr : (3 * ν⁻¹) * (2 * R) < 1) :
    ∃ u : CriticalMildPathBall T R,
      Function.IsFixedPt (gapBallImage ν hν a ha hT hR hbudget) u := by
  let z : CriticalMildPathBall T R :=
    ⟨0, zero_mem_criticalMildPathBall T R hR⟩
  have hc := gapBallImage_contractingWith ν hν a ha hT hR hbudget hcontr
  obtain ⟨u, hu, -, -⟩ := ContractingWith.exists_fixedPoint hc z (edist_ne_top _ _)
  exact ⟨u, hu⟩

/-- Uniqueness of the gap fixed point inside the local ball. -/
theorem gapBallImage_fixedPoint_unique
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖a‖ + (3 * ν⁻¹) * R ^ 2 ≤ R)
    (hcontr : (3 * ν⁻¹) * (2 * R) < 1)
    {u v : CriticalMildPathBall T R}
    (hu : Function.IsFixedPt (gapBallImage ν hν a ha hT hR hbudget) u)
    (hv : Function.IsFixedPt (gapBallImage ν hν a ha hT hR hbudget) v) :
    u = v := by
  letI : Nonempty (CriticalMildPathBall T R) :=
    ⟨⟨0, zero_mem_criticalMildPathBall T R hR⟩⟩
  have hc := gapBallImage_contractingWith ν hν a ha hT hR hbudget hcontr
  exact (hc.fixedPoint_unique hu).trans (hc.fixedPoint_unique hv).symm

/-- The gap fixed point is an actual continuous local mild trajectory on the
closed horizon. -/
theorem exists_gapBall_trajectory
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hbudget : ‖a‖ + (3 * ν⁻¹) * R ^ 2 ≤ R)
    (hcontr : (3 * ν⁻¹) * (2 * R) < 1) :
    ∃ u : CriticalMildPathBall T R,
      (∀ τ : Icc (0 : ℝ) T,
        u.1 τ = criticalMildImage ν hν a
          (criticalMildPathExtension T hT u.1)
          (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) := by
  obtain ⟨u, hu⟩ := exists_gapBallPathBall_fixedPoint
    ν hν a ha hT hR hbudget hcontr
  refine ⟨u, ?_⟩
  intro τ
  have hτ := congrArg (fun w : CriticalMildPathBall T R => w.1 τ) hu
  simpa [Function.IsFixedPt, gapBallImage] using hτ.symm

/-! ### 9c. Horizon coherence and the glued global path -/

/-- The mild image depends on its path argument only through the values on
`Ioc 0 t`: the flow term is path-free and the Duhamel integral sees
`Ioc 0 t`. -/
theorem criticalMildImage_congr_of_Ioc
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (f g : ℝ → WeightedLatticeBanach)
    (hf : ∀ s, LatticeDivergenceFree (f s))
    (hg : ∀ s, LatticeDivergenceFree (g s))
    {t : ℝ} (ht : 0 ≤ t)
    (hag : ∀ s ∈ Ioc (0 : ℝ) t, f s = g s) :
    criticalMildImage ν hν a f hf t ht =
      criticalMildImage ν hν a g hg t ht := by
  have key : ∀ (x y : WeightedLatticeBanach) (hx : LatticeDivergenceFree x)
      (hy : LatticeDivergenceFree y) (hxy : x = y) (l : ℝ),
      positiveTimeHeatRegularizedSpectralOutput ν hν x x hx l =
        positiveTimeHeatRegularizedSpectralOutput ν hν y y hy l := by
    intro x y hx hy rfl l
    exact congrArg
      (fun h => positiveTimeHeatRegularizedSpectralOutput ν hν x x h l)
      (Subsingleton.elim hx hy)
  have hpint : ∀ s ∈ Ioc (0 : ℝ) t,
      criticalMildPathIntegrand ν hν f hf t s =
        criticalMildPathIntegrand ν hν g hg t s := by
    intro s hs
    unfold criticalMildPathIntegrand
    exact key (f s) (g s) (hf s) (hg s) (hag s hs) (t - s)
  have hI : ∫ s in Ioc (0 : ℝ) t, criticalMildPathIntegrand ν hν f hf t s =
      ∫ s in Ioc (0 : ℝ) t, criticalMildPathIntegrand ν hν g hg t s := by
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all volume fun s hs => hpint s hs))
  unfold criticalMildImage criticalMildDuhamel
  rw [hI]

/-- Restrict a local ball path from horizon `n` down to horizon `m ≤ n`. -/
def ballRestriction {m n R : ℝ} (hmn : m ≤ n) :
    CriticalMildPathBall n R → CriticalMildPathBall m R := by
  intro u
  refine ⟨u.1.comp ⟨fun τ => ⟨τ.1, τ.2.1, le_trans τ.2.2 hmn⟩, by fun_prop⟩, ?_⟩
  intro τ
  exact ⟨criticalMildPathBall_divergenceFree u _,
    criticalMildPathBall_norm_le u _⟩

/-- The fixed-point property for the gap endomap restricts to smaller
horizons: the `IccExtend` clamps agree on the integration window. -/
theorem ballRestriction_isFixedPt
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    {m n R : ℝ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m ≤ n) (hR : 0 ≤ R)
    (hbudget : ‖a‖ + (3 * ν⁻¹) * R ^ 2 ≤ R)
    {u : CriticalMildPathBall n R}
    (hu : Function.IsFixedPt (gapBallImage ν hν a ha hn hR hbudget) u) :
    Function.IsFixedPt (gapBallImage ν hν a ha hm hR hbudget)
      (ballRestriction hmn u) := by
  rw [Function.IsFixedPt] at hu ⊢
  apply Subtype.ext
  apply ContinuousMap.ext
  intro τ
  have hagree : ∀ s ∈ Ioc (0 : ℝ) τ.1,
      criticalMildPathExtension m hm (ballRestriction hmn u).1 s =
        criticalMildPathExtension n hn u.1 s := by
    intro s hs
    have hsm : s ∈ Icc (0 : ℝ) m := ⟨hs.1.le, hs.2.trans τ.2.2⟩
    have hsn : s ∈ Icc (0 : ℝ) n := ⟨hs.1.le, hs.2.trans (τ.2.2.trans hmn)⟩
    rw [criticalMildPathExtension_apply m hm (ballRestriction hmn u).1 hsm,
      criticalMildPathExtension_apply n hn u.1 hsn]
    rfl
  have hun : criticalMildImage ν hν a (criticalMildPathExtension n hn u.1)
      (criticalMildPathBallExtension_divergenceFree hn u) τ.1 τ.2.1 =
      u.1 ⟨τ.1, τ.2.1, le_trans τ.2.2 hmn⟩ := by
    have huσ := congrArg (fun w : CriticalMildPathBall n R =>
      w.1 ⟨τ.1, τ.2.1, le_trans τ.2.2 hmn⟩) hu
    simpa [gapBallImage] using huσ
  calc (gapBallImage ν hν a ha hm hR hbudget (ballRestriction hmn u)).1 τ
      = criticalMildImage ν hν a
          (criticalMildPathExtension m hm (ballRestriction hmn u).1)
          (criticalMildPathBallExtension_divergenceFree hm (ballRestriction hmn u))
          τ.1 τ.2.1 := rfl
    _ = criticalMildImage ν hν a (criticalMildPathExtension n hn u.1)
          (criticalMildPathBallExtension_divergenceFree hn u) τ.1 τ.2.1 :=
        criticalMildImage_congr_of_Ioc ν hν a
          (criticalMildPathExtension m hm (ballRestriction hmn u).1)
          (criticalMildPathExtension n hn u.1)
          (criticalMildPathBallExtension_divergenceFree hm (ballRestriction hmn u))
          (criticalMildPathBallExtension_divergenceFree hn u) τ.2.1 hagree
    _ = (ballRestriction hmn u).1 τ := hun

theorem smallData_hR2 (a : WeightedLatticeBanach) : (0 : ℝ) ≤ 2 * ‖a‖ :=
  mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg a)

/-- The small-data gap endomap at natural horizon `n`: the gap ball map with
radius `2 ‖a‖` and the two small-data budget instances, packaged as one
constant so downstream statements share a syntactic head. -/
def gapBallImageNat
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (n : ℕ) :
    CriticalMildPathBall (↑n) (2 * ‖a‖) →
      CriticalMildPathBall (↑n) (2 * ‖a‖) :=
  gapBallImage ν hν a ha (Nat.cast_nonneg n) (smallData_hR2 a)
    (smallData_gap_budget_le ν hν a ha16)

theorem gapBallImageNat_hasFixedPoint
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (n : ℕ) :
    ∃ u : CriticalMildPathBall (↑n) (2 * ‖a‖),
      Function.IsFixedPt (gapBallImageNat ν hν a ha ha16 n) u :=
  exists_gapBallPathBall_fixedPoint ν hν a ha (Nat.cast_nonneg n)
    (smallData_hR2 a) (smallData_gap_budget_le ν hν a ha16)
    (smallData_gap_contraction_lt_one ν hν a ha16)

theorem gapBallImageNat_fixedPoint_unique
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (n : ℕ)
    {u v : CriticalMildPathBall (↑n) (2 * ‖a‖)}
    (hu : Function.IsFixedPt (gapBallImageNat ν hν a ha ha16 n) u)
    (hv : Function.IsFixedPt (gapBallImageNat ν hν a ha ha16 n) v) :
    u = v :=
  gapBallImage_fixedPoint_unique ν hν a ha (Nat.cast_nonneg n)
    (smallData_hR2 a) (smallData_gap_budget_le ν hν a ha16)
    (smallData_gap_contraction_lt_one ν hν a ha16) hu hv

/-- The small-data gap path on horizon `n` (radius `2 ‖a‖`), produced by the
horizon-free gap contraction at every horizon. -/
noncomputable def localGapPath
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (n : ℕ) :
    CriticalMildPathBall (↑n) (2 * ‖a‖) :=
  Classical.choose (gapBallImageNat_hasFixedPoint ν hν a ha ha16 n)

theorem localGapPath_isFixedPt
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (n : ℕ) :
    Function.IsFixedPt (gapBallImageNat ν hν a ha ha16 n)
      (localGapPath ν hν a ha ha16 n) :=
  Classical.choose_spec _

/-- Coherence: restricting the horizon-`n` gap path to `m ≤ n` gives the
horizon-`m` gap path. -/
theorem ballRestriction_localGapPath
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) {m n : ℕ} (hmn : (↑m : ℝ) ≤ ↑n) :
    ballRestriction hmn (localGapPath ν hν a ha ha16 n) =
      localGapPath ν hν a ha ha16 m := by
  refine ((gapBallImageNat_fixedPoint_unique ν hν a ha ha16 m ?hufix ?hvfix).symm :
    ballRestriction hmn (localGapPath ν hν a ha ha16 n) =
      localGapPath ν hν a ha ha16 m)
  · exact localGapPath_isFixedPt ν hν a ha ha16 m
  · refine ballRestriction_isFixedPt ν hν a ha (Nat.cast_nonneg m) (Nat.cast_nonneg n)
      hmn (smallData_hR2 a) (smallData_gap_budget_le ν hν a ha16)
      (localGapPath_isFixedPt ν hν a ha ha16 n)

/-- The glued global small-data gap path over all nonnegative times: at time
`t` it evaluates the coherent local fixed point at horizon `⌈t⌉₊`. -/
noncomputable def globalGapPath
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) : NNReal → WeightedLatticeBanach :=
  fun t => (localGapPath ν hν a ha ha16 ⌈(t : ℝ)⌉₊).1
    ⟨t, ⟨t.2, Nat.le_ceil (t : ℝ)⟩⟩

/-- Evaluation of the glued path against any admissible horizon bound. -/
theorem globalGapPath_apply_le
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) {n : ℕ} {t : NNReal} (ht : (t : ℝ) ≤ ↑n) :
    globalGapPath ν hν a ha ha16 t =
      (localGapPath ν hν a ha ha16 n).1 ⟨t, ⟨t.2, ht⟩⟩ := by
  unfold globalGapPath
  have hm : (⌈(t : ℝ)⌉₊ : ℝ) ≤ ↑n :=
    Nat.cast_le.mpr (Nat.ceil_le.mpr ht)
  rw [← ballRestriction_localGapPath ν hν a ha ha16 hm]
  rfl

/-- The glued global path is pointwise divergence-free. -/
theorem globalGapPath_divergenceFree
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (t : NNReal) :
    LatticeDivergenceFree (globalGapPath ν hν a ha ha16 t) :=
  criticalMildPathBall_divergenceFree
    (localGapPath ν hν a ha ha16 ⌈(t : ℝ)⌉₊) _

/-- The glued global path stays in the small-data ball `2 ‖a‖`. -/
theorem globalGapPath_norm_le
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (t : NNReal) :
    ‖globalGapPath ν hν a ha ha16 t‖ ≤ 2 * ‖a‖ :=
  criticalMildPathBall_norm_le (localGapPath ν hν a ha ha16 ⌈(t : ℝ)⌉₊) _

/-- The glued global path is continuous on `ℝ≥0`: at each time it agrees on
a neighborhood `Iio ⌈t₀⌉₊ + 1` with one fixed local ball path composed with
the inclusion of that neighborhood. -/
theorem continuous_globalGapPath
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) : Continuous (globalGapPath ν hν a ha ha16) := by
  refine continuous_iff_continuousAt.mpr ?_
  intro t₀
  let N₀ : ℕ := ⌈(t₀ : ℝ)⌉₊ + 1
  have hlt : t₀ < (N₀ : NNReal) := by
    have h₁ : (t₀ : ℝ) < ((⌈(t₀ : ℝ)⌉₊ + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
    exact_mod_cast h₁
  let incl : C(Iio (N₀ : NNReal), Icc (0 : ℝ) (N₀ : ℝ)) :=
    ⟨fun τ => ⟨(τ : NNReal), NNReal.coe_nonneg _,
        by exact_mod_cast le_of_lt τ.2⟩, by fun_prop⟩
  have hceil_le : ∀ τ : Iio (N₀ : NNReal), ⌈((τ : NNReal) : ℝ)⌉₊ ≤ N₀ := by
    intro τ
    refine Nat.ceil_le.mpr ?_
    exact_mod_cast le_of_lt τ.2
  have heq : ∀ τ : Iio (N₀ : NNReal),
      globalGapPath ν hν a ha ha16 (τ : NNReal) =
        (localGapPath ν hν a ha ha16 N₀).1 (incl τ) := by
    intro τ
    have hm : (↑⌈((τ : NNReal) : ℝ)⌉₊ : ℝ) ≤ (N₀ : ℝ) :=
      Nat.cast_le.mpr (hceil_le τ)
    calc globalGapPath ν hν a ha ha16 (τ : NNReal)
        = (localGapPath ν hν a ha ha16 ⌈((τ : NNReal) : ℝ)⌉₊).1
            ⟨(τ : NNReal), ⟨(τ : NNReal).2, Nat.le_ceil ((τ : NNReal) : ℝ)⟩⟩ :=
          globalGapPath_apply_le ν hν a ha ha16 (Nat.le_ceil _)
      _ = (ballRestriction hm
            (localGapPath ν hν a ha ha16 N₀)).1
            ⟨(τ : NNReal), ⟨(τ : NNReal).2, Nat.le_ceil ((τ : NNReal) : ℝ)⟩⟩ :=
          congrArg
            (fun w : CriticalMildPathBall (↑⌈((τ : NNReal) : ℝ)⌉₊) (2 * ‖a‖) =>
              w.1 ⟨(τ : NNReal), ⟨(τ : NNReal).2,
                Nat.le_ceil ((τ : NNReal) : ℝ)⟩⟩)
            ((ballRestriction_localGapPath ν hν a ha ha16 hm).symm)
      _ = (localGapPath ν hν a ha ha16 N₀).1 (incl τ) := rfl
  have hcon : ContinuousOn (globalGapPath ν hν a ha ha16)
      (Iio (N₀ : NNReal)) := by
    refine continuousOn_iff_continuous_restrict.mpr ?_
    have hfun : (Iio (N₀ : NNReal)).restrict (globalGapPath ν hν a ha ha16) =
        (localGapPath ν hν a ha ha16 N₀).1.comp incl := by
      refine funext (fun τ => ?_)
      exact heq τ
    rw [hfun]
    exact ((localGapPath ν hν a ha ha16 N₀).1.comp incl).continuous
  exact ContinuousOn.continuousAt hcon (isOpen_Iio.mem_nhds hlt)

/-- The glued global path solves the mild equation at every time: the local
fixed-point trajectory equality on `Icc 0 ⌈t⌉₊` plus the `Ioc`-congruence of
the mild image convert it into the equation driven by the global path. -/
theorem globalGapPath_mild
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (t : NNReal) :
    globalGapPath ν hν a ha ha16 t =
      criticalMildImage ν hν a
        (fun s : ℝ => globalGapPath ν hν a ha ha16 s.toNNReal)
        (fun s => globalGapPath_divergenceFree ν hν a ha ha16 s.toNNReal)
        (t : ℝ) t.2 := by
  let n : ℕ := ⌈(t : ℝ)⌉₊
  have ht : (t : ℝ) ≤ ↑n := Nat.le_ceil _
  have hagree : ∀ s ∈ Ioc (0 : ℝ) (t : ℝ),
      criticalMildPathExtension (↑n) (Nat.cast_nonneg n)
          (localGapPath ν hν a ha ha16 n).1 s =
        globalGapPath ν hν a ha ha16 s.toNNReal := by
    intro s hs
    have hsm : s ∈ Icc (0 : ℝ) (↑n) := ⟨hs.1.le, hs.2.trans ht⟩
    have hb : (s.toNNReal : ℝ) ≤ ↑n := by
      rw [Real.coe_toNNReal s hs.1.le]
      exact hs.2.trans ht
    have h1 : (localGapPath ν hν a ha ha16 n).1 ⟨s, hsm⟩ =
        (localGapPath ν hν a ha ha16 n).1
          ⟨s.toNNReal, ⟨(s.toNNReal).2, hb⟩⟩ :=
      congrArg (fun p : Icc (0 : ℝ) (↑n) =>
          (localGapPath ν hν a ha ha16 n).1 p)
        (Subtype.ext (Real.coe_toNNReal s hs.1.le).symm)
    calc criticalMildPathExtension (↑n) (Nat.cast_nonneg n)
          (localGapPath ν hν a ha ha16 n).1 s
        = (localGapPath ν hν a ha ha16 n).1 ⟨s, hsm⟩ :=
          criticalMildPathExtension_apply (↑n) (Nat.cast_nonneg n)
            (localGapPath ν hν a ha ha16 n).1 hsm
      _ = (localGapPath ν hν a ha ha16 n).1
            ⟨s.toNNReal, ⟨(s.toNNReal).2, hb⟩⟩ := h1
      _ = globalGapPath ν hν a ha ha16 s.toNNReal :=
          (globalGapPath_apply_le ν hν a ha ha16 hb).symm
  have htraj : (localGapPath ν hν a ha ha16 n).1 ⟨(t : ℝ), ⟨t.2, ht⟩⟩ =
      criticalMildImage ν hν a
        (criticalMildPathExtension (↑n) (Nat.cast_nonneg n)
          (localGapPath ν hν a ha ha16 n).1)
        (criticalMildPathBallExtension_divergenceFree (Nat.cast_nonneg n)
          (localGapPath ν hν a ha ha16 n))
        (t : ℝ) t.2 := by
    have hσ := congrArg
        (fun w : CriticalMildPathBall (↑n) (2 * ‖a‖) =>
          w.1 ⟨(t : ℝ), ⟨t.2, ht⟩⟩)
        (localGapPath_isFixedPt ν hν a ha ha16 n)
    simpa [Function.IsFixedPt, gapBallImageNat, gapBallImage] using hσ.symm
  have himg : criticalMildImage ν hν a
      (criticalMildPathExtension (↑n) (Nat.cast_nonneg n)
        (localGapPath ν hν a ha ha16 n).1)
      (criticalMildPathBallExtension_divergenceFree (Nat.cast_nonneg n)
        (localGapPath ν hν a ha ha16 n))
      (t : ℝ) t.2 =
      criticalMildImage ν hν a
        (fun s : ℝ => globalGapPath ν hν a ha ha16 s.toNNReal)
        (fun s => globalGapPath_divergenceFree ν hν a ha ha16 s.toNNReal)
        (t : ℝ) t.2 :=
    criticalMildImage_congr_of_Ioc ν hν a _ _ _ _ t.2 hagree
  rw [globalGapPath_apply_le ν hν a ha ha16 ht, htraj, himg]

/-! ### 10. The small-data global mild continuation theorem -/

/-- Small-data global mild continuation on the periodic Fourier-lattice
carrier: unconditional, with explicit threshold `ε(ν) = ν / 16 > 0`. If the
zero mode of the datum `a` vanishes and `‖a‖ ≤ ν / 16`, there is a continuous
divergence-free path `v : ℝ≥0 → WeightedLatticeBanach` solving the mild
equation at every time, staying in the ball `‖v t‖ ≤ 2 ‖a‖` with the uniform
decay bound `‖v t‖ ≤ e^{-ν t} ‖a‖ + (3 / ν) (2 ‖a‖)²`, unique among all
continuous divergence-free ball-bounded drivers solving the same equation.
Constants close in one line: the budget inequality
`‖a‖ + (3 / ν) (2 ‖a‖)² ≤ 2 ‖a‖` is `6 ‖a‖² ≤ ν ‖a‖`, i.e. `‖a‖ ≤ ν / 12`,
and `ν / 16 ≤ ν / 12`. -/
theorem smallDataGlobalMild
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) :
    ∃ (v : C(NNReal, WeightedLatticeBanach))
        (hvdf : ∀ t, LatticeDivergenceFree (v t)),
      (∀ t : NNReal,
          v t = criticalMildImage ν hν a (fun s : ℝ => v (Real.toNNReal s))
            (fun s => hvdf (Real.toNNReal s)) (t : ℝ) t.2) ∧
        (∀ t : NNReal, ‖v t‖ ≤ 2 * ‖a‖) ∧
        (∀ t : NNReal,
          ‖v t‖ ≤
            Real.exp (-ν * (t : ℝ)) * ‖a‖ + (3 * ν⁻¹) * (2 * ‖a‖) ^ 2) ∧
        (∀ (w : ℝ → WeightedLatticeBanach) (_ : Continuous w)
            (hwd : ∀ t, LatticeDivergenceFree (w t))
            (_ : ∀ t : NNReal,
              w (t : ℝ) = criticalMildImage ν hν a
                (fun s : ℝ => w s.toNNReal) (fun s => hwd s.toNNReal)
                (t : ℝ) t.2)
            (_ : ∀ t : NNReal, ‖w (t : ℝ)‖ ≤ 2 * ‖a‖),
          ∀ t : NNReal, v t = w (t : ℝ)) := by
  refine ⟨⟨globalGapPath ν hν a ha ha16,
      continuous_globalGapPath ν hν a ha ha16⟩,
    fun t => globalGapPath_divergenceFree ν hν a ha ha16 t,
    fun t => globalGapPath_mild ν hν a ha ha16 t,
    fun t => globalGapPath_norm_le ν hν a ha ha16 t, ?_, ?_⟩
  · intro t
    show ‖globalGapPath ν hν a ha ha16 t‖ ≤
      Real.exp (-ν * (t : ℝ)) * ‖a‖ + (3 * ν⁻¹) * (2 * ‖a‖) ^ 2
    have hcomp : Continuous
        (fun s : ℝ => globalGapPath ν hν a ha ha16 s.toNNReal) :=
      (continuous_globalGapPath ν hν a ha ha16).comp
        (by fun_prop : Continuous Real.toNNReal)
    rw [globalGapPath_mild ν hν a ha ha16 t]
    exact norm_criticalMildImage_gap_le ν hν a ha _ hcomp _
      (smallData_hR2 a) t.2
      (fun s _ => globalGapPath_norm_le ν hν a ha ha16 s.toNNReal)
  · intro w hw hwd heq hbound t
    let n : ℕ := ⌈(t : ℝ)⌉₊
    have hn : (t : ℝ) ≤ ↑n := Nat.le_ceil _
    let wn : CriticalMildPathBall (↑n) (2 * ‖a‖) :=
      ⟨⟨fun τ : Icc (0 : ℝ) (↑n) => w τ.1, hw.comp continuous_subtype_val⟩,
        fun τ => ⟨hwd τ.1, hbound ⟨τ.1, τ.2.1⟩⟩⟩
    have hfix : Function.IsFixedPt (gapBallImageNat ν hν a ha ha16 n) wn := by
      rw [Function.IsFixedPt]
      apply Subtype.ext
      apply ContinuousMap.ext
      intro τ
      have hagree : ∀ s ∈ Ioc (0 : ℝ) τ.1,
          criticalMildPathExtension (↑n) (Nat.cast_nonneg n) wn.1 s =
            (fun x : ℝ => w x.toNNReal) s := by
        intro s hs
        have hsm : s ∈ Icc (0 : ℝ) (↑n) := ⟨hs.1.le, hs.2.trans τ.2.2⟩
        calc criticalMildPathExtension (↑n) (Nat.cast_nonneg n) wn.1 s
            = wn.1 ⟨s, hsm⟩ :=
              criticalMildPathExtension_apply (↑n) (Nat.cast_nonneg n)
                wn.1 hsm
          _ = w s := rfl
          _ = (fun x : ℝ => w x.toNNReal) s :=
              congrArg w (Real.coe_toNNReal s hs.1.le).symm
      have himgw : criticalMildImage ν hν a
          (criticalMildPathExtension (↑n) (Nat.cast_nonneg n) wn.1)
          (criticalMildPathBallExtension_divergenceFree
            (Nat.cast_nonneg n) wn)
          τ.1 τ.2.1 =
          criticalMildImage ν hν a (fun s : ℝ => w s.toNNReal)
            (fun s => hwd s.toNNReal) τ.1 τ.2.1 :=
        criticalMildImage_congr_of_Ioc ν hν a _ _ _ _ τ.2.1 hagree
      calc (gapBallImageNat ν hν a ha ha16 n wn).1 τ =
          criticalMildImage ν hν a
            (criticalMildPathExtension (↑n) (Nat.cast_nonneg n) wn.1)
            (criticalMildPathBallExtension_divergenceFree
              (Nat.cast_nonneg n) wn)
            τ.1 τ.2.1 := rfl
        _ = criticalMildImage ν hν a (fun s : ℝ => w s.toNNReal)
              (fun s => hwd s.toNNReal) τ.1 τ.2.1 := himgw
        _ = w τ.1 := (heq ⟨τ.1, τ.2.1⟩).symm
        _ = wn.1 τ := rfl
    have huniq : localGapPath ν hν a ha ha16 n = wn :=
      gapBallImageNat_fixedPoint_unique ν hν a ha ha16 n
        (localGapPath_isFixedPt ν hν a ha ha16 n) hfix
    show globalGapPath ν hν a ha ha16 t = w (t : ℝ)
    calc globalGapPath ν hν a ha ha16 t
        = (localGapPath ν hν a ha ha16 n).1 ⟨t, ⟨t.2, hn⟩⟩ :=
          globalGapPath_apply_le ν hν a ha ha16 hn
      _ = wn.1 ⟨t, ⟨t.2, hn⟩⟩ :=
          congrArg (fun p : CriticalMildPathBall (↑n) (2 * ‖a‖) =>
            p.1 ⟨t, ⟨t.2, hn⟩⟩) huniq
      _ = w (t : ℝ) := rfl

/-! ### 11. Non-vacuity guards -/

/-- The small-data threshold is a positive number. -/
theorem smallData_epsilon_pos (ν : ℝ) (hν : 0 < ν) : 0 < ν / 16 :=
  div_pos hν (by norm_num : (0 : ℝ) < 16)

/-- The norm of a single-mode datum is its fiber norm. -/
theorem smallData_norm_single (x : ComplexE3) :
    ‖(lp.single (1 : ℝ≥0∞) (1, (0, 0)) x : WeightedLatticeBanach)‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp), ENNReal.toReal_one]
  simp only [div_one, Real.rpow_one]
  rw [tsum_eq_single (1, (0, 0))]
  · rw [lp.single_apply_self]
  · intro b' hb'
    rw [norm_eq_zero, lp.single_apply _ _ _ b']
    rw [Pi.single_apply, if_neg hb']

/-- A single-mode datum has vanishing zero mode: the support point
`(1, (0, 0))` differs from `(0, (0, 0))`. -/
theorem smallData_zeroMode_single (x : ComplexE3) :
    (lp.single (1 : ℝ≥0∞) (1, (0, 0)) x : WeightedLatticeBanach) 0 = 0 := by
  have hne : (0 : LatticeMode) ≠ (1, (0, 0)) := by decide
  rw [lp.single_apply _ _ _ (0 : LatticeMode), Pi.single_apply, if_neg hne]

/-- A single-mode datum with nonzero fiber value is nonzero. -/
theorem smallData_nonzero_single (x : ComplexE3) (hx : x ≠ 0) :
    (lp.single (1 : ℝ≥0∞) (1, (0, 0)) x : WeightedLatticeBanach) ≠ 0 := by
  intro h
  have := congrArg (fun u : WeightedLatticeBanach => u (1, (0, 0))) h
  rw [lp.single_apply_self] at this
  exact hx this

/-- The small-data class is inhabited at every nonzero polarization: for
every `x ≠ 0` there is a nonzero zero-mode-free datum with `‖a‖ ≤ ν / 16`. -/
theorem smallData_modeGuard
    (ν : ℝ) (hν : 0 < ν) (x : ComplexE3) (hx : x ≠ 0) :
    ∃ a : WeightedLatticeBanach, a 0 = 0 ∧ a ≠ 0 ∧ ‖a‖ ≤ ν / 16 := by
  let c : ℝ := ν / 32 / (1 + ‖x‖)
  have hc : 0 < c := div_pos (by linarith) (by linarith [norm_nonneg x])
  let y : ComplexE3 := ((c : ℝ) : ℂ) • x
  have hy0 : y ≠ 0 := by
    intro h
    exact (smul_eq_zero.mp h).elim (fun hc0 => hc.ne' (by exact_mod_cast hc0)) hx
  refine ⟨(lp.single (1 : ℝ≥0∞) (1, (0, 0)) y : WeightedLatticeBanach),
    smallData_zeroMode_single y, smallData_nonzero_single y hy0, ?_⟩
  calc ‖(lp.single (1 : ℝ≥0∞) (1, (0, 0)) y : WeightedLatticeBanach)‖ = ‖y‖ :=
      smallData_norm_single y
    _ ≤ ‖((c : ℝ) : ℂ)‖ * ‖x‖ := norm_smul_le _ _
    _ = c * ‖x‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
    _ ≤ ν / 16 := by
      have h2 : c * ‖x‖ ≤ c * (1 + ‖x‖) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) hc.le
      have h3 : c * (1 + ‖x‖) = ν / 32 := by
        show ν / 32 / (1 + ‖x‖) * (1 + ‖x‖) = _
        rw [div_mul_cancel₀ _ (by linarith [norm_nonneg x])]
      linarith

/-! ### 12. Goal L: feeding the global path into the official consumers -/

/-- The all-time continuous driver of the global small-data mild solution:
the glued path extended to every real time through `Real.toNNReal`. -/
noncomputable def smallDataGlobalDriver
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) : ℝ → WeightedLatticeBanach :=
  fun s : ℝ => globalGapPath ν hν a ha ha16 s.toNNReal

theorem continuous_smallDataGlobalDriver
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) :
    Continuous (smallDataGlobalDriver ν hν a ha ha16) :=
  (continuous_globalGapPath ν hν a ha ha16).comp
    (by fun_prop : Continuous Real.toNNReal)

theorem smallDataGlobalDriver_divergenceFree
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (s : ℝ) :
    LatticeDivergenceFree (smallDataGlobalDriver ν hν a ha ha16 s) :=
  globalGapPath_divergenceFree ν hν a ha ha16 s.toNNReal

theorem smallDataGlobalDriver_norm_le
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (s : ℝ) :
    ‖smallDataGlobalDriver ν hν a ha ha16 s‖ ≤ 2 * ‖a‖ :=
  globalGapPath_norm_le ν hν a ha ha16 s.toNNReal

/-- The mild image is invariant under a propositional change of its time
argument: only the value of the real time and the irrelevance of the
nonnegativity proof matter. -/
theorem criticalMildImage_congr_time
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (h : t₁ = t₂) :
    criticalMildImage ν hν a u hu t₁ ht₁ =
      criticalMildImage ν hν a u hu t₂ ht₂ := by
  cases h
  rfl

/-- The global driver solves the mild equation on every finite horizon:
the glued-path equation at `x.toNNReal` plus the time-congruence of the
mild image. -/
theorem smallDataGlobalDriver_mild
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) {T x : ℝ} (hx : x ∈ Icc (0 : ℝ) T) :
    smallDataGlobalDriver ν hν a ha ha16 x =
      criticalMildImage ν hν a (smallDataGlobalDriver ν hν a ha ha16)
        (smallDataGlobalDriver_divergenceFree ν hν a ha ha16) x hx.1 :=
  (globalGapPath_mild ν hν a ha ha16 x.toNNReal).trans
    (criticalMildImage_congr_time ν hν a _ _ _ _
      (Real.coe_toNNReal x hx.1))

/-- **Goal L, lattice part: CLOSED.** The global small-data mild solution
has every iterated half-order lattice polynomial moment uniformly bounded on
every compact positive time interval: the repository consumer
`exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval` instantiates
at the global driver with driving radius `2 ‖a‖`, the same radius at every
horizon `T ≥ a₀ > 0` — chart radius does not deteriorate. -/
theorem smallDataGlobal_uniformAllHalfOrderMoments
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ ν / 16) (hadf : LatticeDivergenceFree a)
    {a₀ T : ℝ} (ha₀ : 0 < a₀) (haT : a₀ ≤ T) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n t, t ∈ Icc a₀ T →
      LatticePolynomialMoment (iteratedHalfOrder 2 n)
        (smallDataGlobalDriver ν hν a ha ha16 t) ∧
        polynomialMoment (iteratedHalfOrder 2 n)
          (smallDataGlobalDriver ν hν a ha ha16 t) ≤ B n :=
  exists_uniform_all_iteratedHalfOrder_on_compactPositiveInterval
    ν hν a hadf (smallDataGlobalDriver ν hν a ha ha16)
    (continuous_smallDataGlobalDriver ν hν a ha ha16)
    (smallDataGlobalDriver_divergenceFree ν hν a ha ha16)
    (smallData_hR2 a) ha₀ haT
    (fun s _ => smallDataGlobalDriver_norm_le ν hν a ha ha16 s)
    (fun _ hx => smallDataGlobalDriver_mild ν hν a ha ha16 hx)

/-- **Goal L, official equation: exact conditional.** The carrier convention
of `rawMildViscosity ν₀ = ν₀ · (2π)²` rescales the lattice viscosity against
the physical one. The only premise not discharged by this lane is the reality
(anti-Hermitian) transport of the global driver, the symmetry-equivariance of
`criticalMildImage`. Under it, the small-data global solution satisfies the
official momentum identity on the `Navier.Problem` carrier at every positive
time of every finite horizon, with driving radius `2 ‖a‖` and threshold
`ε(ν₀) = rawMildViscosity ν₀ / 16`, uniform in the horizon. -/
theorem smallDataGlobal_navierStokesBody_on_positiveTime
    (ν₀ : ℝ) (hν₀ : 0 < ν₀) (a : WeightedLatticeBanach) (ha : a 0 = 0)
    (ha16 : ‖a‖ ≤ rawMildViscosity ν₀ / 16) (hadf : LatticeDivergenceFree a)
    (hah : ∀ s : ℝ, LatticeAntiHermitian
        (smallDataGlobalDriver (rawMildViscosity ν₀)
          (by unfold rawMildViscosity; positivity) a ha ha16 s))
    {T t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ∀ x : Space, timeDerivative
        (physicalMildVelocity (smallDataGlobalDriver (rawMildViscosity ν₀)
          (by unfold rawMildViscosity; positivity) a ha ha16)) t x +
        convection
          (physicalMildVelocity (smallDataGlobalDriver (rawMildViscosity ν₀)
            (by unfold rawMildViscosity; positivity) a ha ha16)) t x =
      ν₀ • laplacian
          (physicalMildVelocity (smallDataGlobalDriver (rawMildViscosity ν₀)
            (by unfold rawMildViscosity; positivity) a ha ha16)) t x -
        pressureGradient
          (physicalMildPressure (smallDataGlobalDriver (rawMildViscosity ν₀)
            (by unfold rawMildViscosity; positivity) a ha ha16)) t x +
        zeroForce t x :=
  mildFixedPoint_navierStokesBody_on_positiveTime ν₀ hν₀ a hadf
    (smallDataGlobalDriver (rawMildViscosity ν₀)
      (by unfold rawMildViscosity; positivity) a ha ha16)
    (continuous_smallDataGlobalDriver (rawMildViscosity ν₀)
      (by unfold rawMildViscosity; positivity) a ha ha16)
    (smallDataGlobalDriver_divergenceFree (rawMildViscosity ν₀)
      (by unfold rawMildViscosity; positivity) a ha ha16) hah
    (smallData_hR2 a)
    (fun s _ => smallDataGlobalDriver_norm_le (rawMildViscosity ν₀)
      (by unfold rawMildViscosity; positivity) a ha ha16 s)
    (fun _ hx => smallDataGlobalDriver_mild (rawMildViscosity ν₀)
      (by unfold rawMildViscosity; positivity) a ha ha16 hx) ht

#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.abs_latticeFrequency_apply_le_norm
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.latticeFrequency_gap
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.complexHeatDecay_latticeFrequency_eq
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.complexHeatDecay_latticeFrequency_le_gap_exp
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain_nonneg
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain_le_inverseSqrtTime
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.omega_decay_le_gap_exp
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.complexEuclideanNorm_nonneg
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.sqrt_inv_prod_cancel
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.exp_prod_inv_cancel
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_heatRegularizedSpectralOutput_le_gap_exp
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_positiveTimeHeatRegularizedSpectralOutput_le_gapTimeGain
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_positiveTimeHeatRegularizedSpectralOutput_gap_sub_le
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.inverseSqrtTime_nonneg_of_nonneg
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain_zero
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain_eq_small_branch
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain_eq_exp_branch
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain_le_kernel
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gap_kernel_aemeasurable
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.intervalIntegrable_gapTimeGain
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain_integral_comp_sub
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapTimeGain_integral_budget
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_criticalMildPathIntegrand_le_gap
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_criticalMildPathIntegrand_le_gap_of_norm_le
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_criticalMildDuhamel_le_gap
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_criticalMildPathIntegrand_sub_le_gap
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_criticalMildPathIntegrand_sub_le_gap_of_norm_bounds
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_criticalMildDuhamel_sub_le_gap
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_weightedHeatFlowCoordinate_le_gap_exp
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_weightedHeatFlow_le_gap_exp
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_criticalMildImage_gap_le
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_criticalMildImage_sub_le_gap
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallData_gap_budget_le
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallData_gap_contraction_lt_one
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapBallImage
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.norm_gapBallImage_sub_le
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapBallImage_contractingWith
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.exists_gapBallPathBall_fixedPoint
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapBallImage_fixedPoint_unique
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.exists_gapBall_trajectory
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.criticalMildImage_congr_of_Ioc
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.ballRestriction
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.ballRestriction_isFixedPt
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallData_hR2
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapBallImageNat
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapBallImageNat_hasFixedPoint
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.gapBallImageNat_fixedPoint_unique
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.localGapPath
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.localGapPath_isFixedPt
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.ballRestriction_localGapPath
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.globalGapPath
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.globalGapPath_apply_le
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.globalGapPath_divergenceFree
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.globalGapPath_norm_le
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.continuous_globalGapPath
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.globalGapPath_mild
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallDataGlobalMild
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallData_epsilon_pos
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallData_norm_single
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallData_zeroMode_single
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallData_nonzero_single
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallData_modeGuard
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallDataGlobalDriver
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.continuous_smallDataGlobalDriver
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallDataGlobalDriver_divergenceFree
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallDataGlobalDriver_norm_le
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.criticalMildImage_congr_time
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallDataGlobalDriver_mild
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallDataGlobal_uniformAllHalfOrderMoments
#print axioms Navier.Analysis.CriticalMildSmallDataGlobal.smallDataGlobal_navierStokesBody_on_positiveTime
end Navier.Analysis.CriticalMildSmallDataGlobal
