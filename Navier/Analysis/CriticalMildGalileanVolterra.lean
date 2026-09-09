import Navier.Analysis.CriticalMildMeanDriftRemoval
import Navier.Analysis.CriticalMildSelfMap

/-!
# Galilean phase transport through the critical mild Volterra equation

This module lifts the period-one phase and constant-mode algebra to the
time-dependent Bochner Duhamel equation.  The scalar lemma below is the
integrating-factor identity used mode by mode; it does not assume the
transformed fixed-point conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildGalileanVolterra

open MeasureTheory Set Topology
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildMeanDriftRemoval
open Navier.Analysis.CriticalMildZeroMode

/-- A complex exponential evaluated along real time. -/
def exponentialPhase (r : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (r * (t : ℂ))

@[simp] theorem exponentialPhase_zero (r : ℂ) : exponentialPhase r 0 = 1 := by
  simp [exponentialPhase]

theorem exponentialPhase_add (r : ℂ) (t s : ℝ) :
    exponentialPhase r (t + s) = exponentialPhase r t * exponentialPhase r s := by
  rw [exponentialPhase, exponentialPhase, exponentialPhase, ← Complex.exp_add]
  push_cast
  congr 1
  ring

theorem exponentialPhase_sub (r : ℂ) (t s : ℝ) :
    exponentialPhase r (t - s) = exponentialPhase r t * exponentialPhase (-r) s := by
  rw [show t - s = t + -s by ring, exponentialPhase_add]
  congr 1
  simp [exponentialPhase]

theorem hasDerivAt_exponentialPhase (r : ℂ) (t : ℝ) :
    HasDerivAt (exponentialPhase r) (exponentialPhase r t * r) t := by
  have hlinear : HasDerivAt (fun s : ℝ => r * (s : ℂ)) r t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul r)
  exact hlinear.cexp

/-- Scalar heat Volterra evolution in a complex Banach space. -/
def scalarHeatVolterra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℝ) (x₀ : E) (f : ℝ → E) (t : ℝ) : E :=
  exponentialPhase (-a) t • x₀ +
    ∫ s in (0 : ℝ)..t, exponentialPhase (-a) (t - s) • f s

theorem scalarHeatVolterra_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (a : ℝ) (x₀ : E) (f : ℝ → E) :
    scalarHeatVolterra a x₀ f 0 = x₀ := by
  simp [scalarHeatVolterra]

/-- Pull the terminal heat factor out of the scalar Volterra formula. -/
theorem scalarHeatVolterra_factor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (a : ℝ) (x₀ : E) (f : ℝ → E) (t : ℝ) :
    scalarHeatVolterra a x₀ f t =
      exponentialPhase (-a) t •
        (x₀ + ∫ s in (0 : ℝ)..t, exponentialPhase a s • f s) := by
  unfold scalarHeatVolterra
  rw [smul_add, ← intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp
  rw [smul_smul]
  congr 1
  simpa using exponentialPhase_sub (-a) t s

/-- The scalar heat Volterra formula has the expected inhomogeneous ODE. -/
theorem hasDerivAt_scalarHeatVolterra {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (a : ℝ) (x₀ : E) (f : ℝ → E) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (scalarHeatVolterra a x₀ f)
      ((-a : ℂ) • scalarHeatVolterra a x₀ f t + f t) t := by
  let g : ℝ → E := fun s => exponentialPhase a s • f s
  have hphase : Continuous (exponentialPhase a) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hasDerivAt_exponentialPhase a s).continuousAt
  have hg : Continuous g := by
    dsimp [g]
    exact hphase.smul hf
  have hint : IntervalIntegrable g volume 0 t := hg.intervalIntegrable 0 t
  have hprimitive : HasDerivAt (fun q => x₀ + ∫ s in (0 : ℝ)..q, g s)
      (g t) t := by
    have h := (hasDerivAt_const t x₀).add
      (intervalIntegral.integral_hasDerivAt_right hint
        hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt)
    convert h using 1
    · funext q
      rfl
    · simp
  have hproduct := (hasDerivAt_exponentialPhase (-a) t).smul hprimitive
  have heq : scalarHeatVolterra a x₀ f = fun q =>
      exponentialPhase (-a) q • (x₀ + ∫ s in (0 : ℝ)..q, g s) := by
    funext q
    exact scalarHeatVolterra_factor a x₀ f q
  have hp : HasDerivAt (fun q =>
      exponentialPhase (-a) q • (x₀ + ∫ s in (0 : ℝ)..q, g s))
      (exponentialPhase (-a) t • g t +
        (exponentialPhase (-a) t * (-a : ℂ)) •
          (x₀ + ∫ s in (0 : ℝ)..t, g s)) t := by
    convert hproduct using 1
    funext q
    rfl
  rw [heq]
  convert hp using 1
  dsimp [g]
  have hinv : exponentialPhase (-a) t * exponentialPhase a t = 1 := by
    unfold exponentialPhase
    rw [← Complex.exp_add]
    convert Complex.exp_zero
    ring
  simp only [smul_smul]
  rw [hinv, one_smul]
  have hcomm : -(a : ℂ) * exponentialPhase (-a) t =
      exponentialPhase (-a) t * (-a : ℂ) := by ring
  rw [hcomm]
  abel

/-- A differentiable solution of the scalar heat equation equals its literal
Bochner Volterra formula. -/
theorem eq_scalarHeatVolterra_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a : ℝ) (x₀ : E) (g y : ℝ → E) (hg : Continuous g)
    (hy : ∀ s, HasDerivAt y ((-a : ℂ) • y s + g s) s)
    (hy₀ : y 0 = x₀) (t : ℝ) :
    y t = scalarHeatVolterra a x₀ g t := by
  let z : ℝ → E := fun s => exponentialPhase a s • y s
  let z' : ℝ → E := fun s => exponentialPhase a s • g s
  have hz : ∀ s, HasDerivAt z (z' s) s := by
    intro s
    have hproduct := (hasDerivAt_exponentialPhase a s).smul (hy s)
    change HasDerivAt (fun q => exponentialPhase a q • y q)
      (exponentialPhase a s • g s) s
    have hp : HasDerivAt (fun q => exponentialPhase a q • y q)
        (exponentialPhase a s • ((-a : ℂ) • y s + g s) +
          (exponentialPhase a s * (a : ℂ)) • y s) s := by
      convert hproduct using 1
      funext q
      rfl
    convert hp using 1
    simp only [smul_add, smul_smul]
    module
  have hz' : Continuous z' := by
    dsimp [z']
    have hphase : Continuous (exponentialPhase a) := by
      rw [continuous_iff_continuousAt]
      intro s
      exact (hasDerivAt_exponentialPhase a s).continuousAt
    exact hphase.smul hg
  have hftc : (∫ s in (0 : ℝ)..t, z' s) = z t - z 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hz s) (hz'.intervalIntegrable 0 t)
  rw [scalarHeatVolterra_factor]
  rw [show (∫ s in (0 : ℝ)..t, exponentialPhase a s • g s) =
      ∫ s in (0 : ℝ)..t, z' s by rfl, hftc]
  dsimp [z]
  rw [exponentialPhase_zero, one_smul, hy₀]
  have hcancel : x₀ + (exponentialPhase a t • y t - x₀) =
      exponentialPhase a t • y t := by abel
  rw [hcancel]
  rw [smul_smul]
  have hinv : exponentialPhase (-a) t * exponentialPhase a t = 1 := by
    unfold exponentialPhase
    rw [← Complex.exp_add]
    convert Complex.exp_zero
    ring
  rw [hinv, one_smul]

/-- Multiplying a scalar heat Volterra solution by a time-dependent complex
phase adds exactly the phase generator to its forcing. -/
theorem exponentialPhase_smul_scalarHeatVolterra
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a : ℝ) (r : ℂ) (x₀ : E) (f : ℝ → E) (hf : Continuous f) (t : ℝ) :
    exponentialPhase r t • scalarHeatVolterra a x₀ f t =
      scalarHeatVolterra a x₀
        (fun s => exponentialPhase r s • f s +
          r • (exponentialPhase r s • scalarHeatVolterra a x₀ f s)) t := by
  let x : ℝ → E := scalarHeatVolterra a x₀ f
  let y : ℝ → E := fun s => exponentialPhase r s • x s
  let g : ℝ → E := fun s => exponentialPhase r s • f s + r • y s
  have hx : ∀ s, HasDerivAt x ((-a : ℂ) • x s + f s) s :=
    fun s => hasDerivAt_scalarHeatVolterra a x₀ f hf s
  have hy : ∀ s, HasDerivAt y ((-a : ℂ) • y s + g s) s := by
    intro s
    have hproduct := (hasDerivAt_exponentialPhase r s).smul (hx s)
    change HasDerivAt (fun q => exponentialPhase r q • x q)
      ((-a : ℂ) • (exponentialPhase r s • x s) +
        (exponentialPhase r s • f s +
          r • (exponentialPhase r s • x s))) s
    have hp : HasDerivAt (fun q => exponentialPhase r q • x q)
        (exponentialPhase r s • ((-a : ℂ) • x s + f s) +
          (exponentialPhase r s * r) • x s) s := by
      convert hproduct using 1
      funext q
      rfl
    convert hp using 1
    simp only [smul_add, smul_smul]
    module
  have hxcont : Continuous x := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hx s).continuousAt
  have hphase : Continuous (exponentialPhase r) := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hasDerivAt_exponentialPhase r s).continuousAt
  have hycont : Continuous y := hphase.smul hxcont
  have hg : Continuous g := (hphase.smul hf).add (hycont.const_smul r)
  have hy₀ : y 0 = x₀ := by
    simp [y, x, scalarHeatVolterra_zero]
  exact eq_scalarHeatVolterra_of_hasDerivAt a x₀ g y hg hy hy₀ t

/-! ## Modewise realization of the actual critical mild equation -/

/-- The scalar heat generator on one stored lattice mode. -/
def modeHeatRate (ν : ℝ) (k : LatticeMode) : ℝ :=
  ν * ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2

theorem complexHeatDecay_eq_exponentialPhase (ν τ : ℝ) (k : LatticeMode) :
    (complexHeatDecay ν τ (latticeFrequency k) : ℂ) =
      exponentialPhase (-modeHeatRate ν k) τ := by
  simp [complexHeatDecay, FrequencyHeatLeray.heatDecay, modeHeatRate,
    exponentialPhase]
  ring_nf

theorem physicalTranslationPhase_eq_exponentialPhase
    (c : Space) (t : ℝ) (k : LatticeMode) :
    physicalTranslationPhase c t k =
      exponentialPhase (physicalTranslationRate c k) t := rfl

/-- Translation phase is an isometry of the completed weighted carrier. -/
theorem norm_translationPhaseCarrier (c : Space) (t : ℝ)
    (u : WeightedLatticeBanach) :
    ‖translationPhaseCarrier c t u‖ = ‖u‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one]
  apply congrArg tsum
  funext k
  exact translationPhaseCarrier_apply_norm c t u k

/-- For a fixed completed carrier, the period-one translation phase is
strongly continuous in real time. -/
theorem continuous_translationPhaseCarrier (c : Space)
    (u : WeightedLatticeBanach) :
    Continuous fun t : ℝ => translationPhaseCarrier c t u := by
  rw [continuous_iff_continuousAt]
  intro t₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hcoordinate (k : LatticeMode) :
      Continuous fun t : ℝ => translationPhaseCarrier c t u k := by
    rw [show (fun t : ℝ => translationPhaseCarrier c t u k) =
        fun t => physicalTranslationPhase c t k • u k by rfl]
    have hphase : Continuous fun t => physicalTranslationPhase c t k := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (hasDerivAt_physicalTranslationPhase c k t).continuousAt
    exact hphase.smul continuous_const
  have hpointwise (k : LatticeMode) :
      Filter.Tendsto
        (fun t : ℝ => ‖translationPhaseCarrier c t u k -
          translationPhaseCarrier c t₀ u k‖)
        (𝓝 t₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hcoordinate k).continuousAt
  have hdominated : ∀ᶠ t : ℝ in 𝓝 t₀, ∀ k : LatticeMode,
      ‖(‖translationPhaseCarrier c t u k -
        translationPhaseCarrier c t₀ u k‖ : ℝ)‖ ≤ 2 * ‖u k‖ := by
    refine Filter.Eventually.of_forall ?_
    intro t k
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖translationPhaseCarrier c t u k -
          translationPhaseCarrier c t₀ u k‖ ≤
        ‖translationPhaseCarrier c t u k‖ +
          ‖translationPhaseCarrier c t₀ u k‖ := norm_sub_le _ _
      _ = 2 * ‖u k‖ := by
        rw [translationPhaseCarrier_apply_norm,
          translationPhaseCarrier_apply_norm]
        ring
  have hsum : Summable (fun k : LatticeMode => 2 * ‖u k‖) := by
    have huSum : Summable (fun k : LatticeMode => ‖u k‖) := by
      simpa using u.2.summable
    exact huSum.mul_left 2
  have htannery : Filter.Tendsto
      (fun t : ℝ => ∑' k : LatticeMode,
        ‖translationPhaseCarrier c t u k - translationPhaseCarrier c t₀ u k‖)
      (𝓝 t₀) (𝓝 0) := by
    simpa using tendsto_tsum_of_dominated_convergence
      hsum hpointwise hdominated
  convert htannery using 1
  funext t
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
  simp only [ENNReal.toReal_one, one_div, inv_one, Real.rpow_one]
  apply congrArg tsum
  funext k
  rfl

theorem translationPhaseCarrier_sub (c : Space) (t : ℝ)
    (u v : WeightedLatticeBanach) :
    translationPhaseCarrier c t (u - v) =
      translationPhaseCarrier c t u - translationPhaseCarrier c t v := by
  apply Subtype.ext
  funext k
  change physicalTranslationPhase c t k • (u k - v k) =
    physicalTranslationPhase c t k • u k -
      physicalTranslationPhase c t k • v k
  exact smul_sub _ _ _

/-- The phase action remains continuous when both time and the completed
carrier path vary continuously. -/
theorem continuous_translationPhaseCarrier_path (c : Space)
    (u : ℝ → WeightedLatticeBanach) (hu : Continuous u) :
    Continuous fun t => translationPhaseCarrier c t (u t) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  change Filter.Tendsto (fun t => translationPhaseCarrier c t (u t))
    (𝓝 t₀) (𝓝 (translationPhaseCarrier c t₀ (u t₀)))
  have hvary : Filter.Tendsto
      (fun t => translationPhaseCarrier c t (u t - u t₀))
      (𝓝 t₀) (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hu_at : Filter.Tendsto u (𝓝 t₀) (𝓝 (u t₀)) := hu.continuousAt
    have hu0 := tendsto_iff_norm_sub_tendsto_zero.mp hu_at
    convert hu0 using 1
    funext t
    rw [sub_zero, norm_translationPhaseCarrier]
  have hfixed : Filter.Tendsto
      (fun t => translationPhaseCarrier c t (u t₀))
      (𝓝 t₀) (𝓝 (translationPhaseCarrier c t₀ (u t₀))) :=
    (continuous_translationPhaseCarrier c (u t₀)).continuousAt
  rw [show (fun t => translationPhaseCarrier c t (u t)) = fun t =>
      translationPhaseCarrier c t (u t - u t₀) +
        translationPhaseCarrier c t (u t₀) by
    funext t
    rw [translationPhaseCarrier_sub]
    abel]
  convert hvary.add hfixed using 1
  simp [translationPhaseCarrier]

/-- The unheated projected nonlinear coefficient encoded in the completed
one-weight carrier coordinate. -/
def criticalMildForcingMode (k : LatticeMode)
    (u : WeightedLatticeBanach) : ComplexE3 :=
  latticeModeWeight k • complexEuclideanPoint
    (complexLeray (latticeFrequency k) (spectralOutputCoefficient k u u))

theorem continuous_criticalMildForcingMode_path (k : LatticeMode)
    (u : ℝ → WeightedLatticeBanach) (hu : Continuous u) :
    Continuous fun s => criticalMildForcingMode k (u s) := by
  unfold criticalMildForcingMode spectralOutputCoefficient
  change Continuous fun s => latticeModeWeight k • complexEuclideanPoint
    (complexLeray (latticeFrequency k)
      (WithLp.ofLp (weightedLatticeSpectralBilinear k (u s) (u s))))
  have hspectral : Continuous fun s =>
      WithLp.ofLp (weightedLatticeSpectralBilinear k (u s) (u s)) := by
    fun_prop
  apply Continuous.const_smul
  apply CriticalMildHeatBochner.continuous_complexEuclideanPoint.comp
  apply (LinearMap.continuous_of_finiteDimensional
    (complexLeray (latticeFrequency k))).comp
  exact hspectral

/-- Every positive-lag coordinate of the actual Duhamel integrand is the
scalar heat Volterra kernel applied to the unheated projected forcing mode. -/
theorem criticalMildPathIntegrand_apply_eq_scalarKernel
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t s : ℝ} (hst : s < t) (k : LatticeMode) :
    criticalMildPathIntegrand ν hν u hu t s k =
      exponentialPhase (-modeHeatRate ν k) (t - s) •
        criticalMildForcingMode k (u s) := by
  have hlag : 0 < t - s := sub_pos.mpr hst
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν _ _ (hu s) hlag,
    heatRegularizedSpectralOutput_apply]
  unfold heatRegularizedSpectralOutputFiber criticalMildForcingMode
  rw [complexFrequencyHeatLeray_apply,
    ComplexFrequencyHeatLeray.complexEuclideanPoint_smul]
  rw [complexHeatDecay_eq_exponentialPhase]
  module

/-- Each completed-carrier coordinate of the literal critical mild image is
exactly the scalar heat Volterra formula with the actual projected nonlinear
forcing. -/
theorem criticalMildImage_apply_eq_scalarHeatVolterra
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (k : LatticeMode) :
    criticalMildImage ν hν u₀ u hu t ht k =
      scalarHeatVolterra (modeHeatRate ν k) (u₀ k)
        (fun s => criticalMildForcingMode k (u s)) t := by
  have hint := integrableOn_criticalMildPathIntegrand
    ν hν u huc hu hR ht huR
  have heval :
      (∫ s in Ioc (0 : ℝ) t, criticalMildPathIntegrand ν hν u hu t s) k =
        ∫ s in Ioc (0 : ℝ) t, criticalMildPathIntegrand ν hν u hu t s k := by
    change (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k)
        (∫ s in Ioc (0 : ℝ) t, criticalMildPathIntegrand ν hν u hu t s) = _
    exact (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integral_comp_comm
      hint |>.symm
  have hintegral :
      (∫ s in Ioc (0 : ℝ) t, criticalMildPathIntegrand ν hν u hu t s k) =
        ∫ s in Ioc (0 : ℝ) t,
          exponentialPhase (-modeHeatRate ν k) (t - s) •
            criticalMildForcingMode k (u s) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (0 : ℝ) t)).ae_ne t] with s hs hne
    exact criticalMildPathIntegrand_apply_eq_scalarKernel ν hν u hu
      (lt_of_le_of_ne hs.2 hne) k
  unfold criticalMildImage criticalMildDuhamel scalarHeatVolterra
  change (weightedHeatFlow ν t hν.le ht u₀) k +
      (∫ s in Ioc (0 : ℝ) t, criticalMildPathIntegrand ν hν u hu t s) k = _
  rw [show (weightedHeatFlow ν t hν.le ht u₀) k =
      (complexHeatDecay ν t (latticeFrequency k) : ℂ) • u₀ k by
        exact weightedHeatFlow_apply_of_divergenceFree ν t hν.le ht u₀ hu₀ k,
    complexHeatDecay_eq_exponentialPhase, heval, hintegral,
    ← intervalIntegral.integral_of_le ht]

/-! ## Phase covariance with the normalized constant mean -/

/-- At the unheated projected forcing level, removing the normalized raw
mean produces exactly the phase-transported nonlinearity plus the Galilean
phase generator acting on the translated carrier coordinate. -/
theorem criticalMildForcingMode_meanRemoved
    (c : Space) (s : ℝ) (k : LatticeMode)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    criticalMildForcingMode k (meanRemovedCarrier c s u) =
      physicalTranslationPhase c s k • criticalMildForcingMode k u +
        physicalTranslationRate c k • translationPhaseCarrier c s u k := by
  have htrans := translationPhaseCarrier_divergenceFree c s hu
  have hleray : complexLeray (latticeFrequency k)
      (weightedLatticeCoefficient (translationPhaseCarrier c s u) k) =
        weightedLatticeCoefficient (translationPhaseCarrier c s u) k :=
    complexLeray_eq_self_of_hermitian_transverse _ _ (htrans k)
  have hpoint_sub (a b : ComplexSpace) :
      complexEuclideanPoint (a - b) =
        complexEuclideanPoint a - complexEuclideanPoint b := by
    ext i
    rfl
  have hcoordinate :=
    latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient
      (translationPhaseCarrier c s u) k
  unfold criticalMildForcingMode
  rw [spectralOutputCoefficient_meanRemoved, map_sub, map_smul, map_smul, hleray,
    hpoint_sub, ComplexFrequencyHeatLeray.complexEuclideanPoint_smul,
    ComplexFrequencyHeatLeray.complexEuclideanPoint_smul,
    rawFourierScale_mul_pairing_eq_neg_translationRate, ← hcoordinate]
  module

/-- Time-dependent Galilean translation followed by subtraction of the
normalized raw constant mode. -/
def galileanMeanRemovedPath (c : Space)
    (u : ℝ → WeightedLatticeBanach) : ℝ → WeightedLatticeBanach :=
  fun s => meanRemovedCarrier c s (u s)

theorem continuous_galileanMeanRemovedPath (c : Space)
    (u : ℝ → WeightedLatticeBanach) (hu : Continuous u) :
    Continuous (galileanMeanRemovedPath c u) := by
  unfold galileanMeanRemovedPath meanRemovedCarrier
  exact (continuous_translationPhaseCarrier_path c u hu).sub continuous_const

theorem norm_galileanMeanRemovedPath_le (c : Space)
    (u : ℝ → WeightedLatticeBanach) (s : ℝ) :
    ‖galileanMeanRemovedPath c u s‖ ≤ ‖u s‖ + ‖rawMeanCarrier c‖ := by
  unfold galileanMeanRemovedPath meanRemovedCarrier
  exact (norm_sub_le _ _).trans_eq
    (congrArg (fun r : ℝ => r + ‖rawMeanCarrier c‖)
      (norm_translationPhaseCarrier c s (u s)))

/-- Removing the actual constant mode contracts the completed critical norm.
The estimate uses the unchanged nonzero-mode amplitudes, with no mean penalty. -/
theorem norm_meanRemovedCarrier_le (c : Space) (s : ℝ)
    (u : WeightedLatticeBanach) (hmean : u 0 = rawMeanCarrier c 0) :
    ‖meanRemovedCarrier c s u‖ ≤ ‖u‖ := by
  apply lp.norm_mono one_ne_zero
  intro k
  by_cases hk : k = 0
  · subst k
    rw [meanRemovedCarrier_zero_mode c s u hmean, norm_zero]
    exact norm_nonneg _
  · rw [meanRemovedCarrier_apply_ne_zero c s u hk,
      translationPhaseCarrier_apply_norm]

theorem galileanMeanRemovedPath_divergenceFree
    (c : Space) (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s)) :
    ∀ s, LatticeDivergenceFree (galileanMeanRemovedPath c u s) := by
  intro s
  exact meanRemovedCarrier_divergenceFree c s (hu s)

/-- The actual critical mild fixed-point identity is preserved by the
period-one Galilean phase after the correctly normalized raw mean is removed.

The hypotheses are the native finite-horizon carrier conditions used by the
Bochner map.  No transformed fixed-point equation is assumed. -/
theorem galileanMeanRemovedPath_fixedPoint_on_horizon
    (ν : ℝ) (hν : 0 < ν) (c : Space)
    (u₀ : WeightedLatticeBanach) (hu₀ : LatticeDivergenceFree u₀)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {T Ru : ℝ} (hRu : 0 ≤ Ru)
    (huR : ∀ s ∈ Ioc (0 : ℝ) T, ‖u s‖ ≤ Ru)
    (hmean : u₀ 0 = rawMeanCarrier c 0)
    (hmild : ∀ τ : Icc (0 : ℝ) T,
      u τ.1 = criticalMildImage ν hν u₀ u hu τ.1 τ.2.1) :
    ∀ τ : Icc (0 : ℝ) T,
      galileanMeanRemovedPath c u τ.1 =
        criticalMildImage ν hν (meanRemovedCarrier c 0 u₀)
          (galileanMeanRemovedPath c u)
          (galileanMeanRemovedPath_divergenceFree c u hu)
          τ.1 τ.2.1 := by
  intro τ
  let y : ℝ → WeightedLatticeBanach := galileanMeanRemovedPath c u
  have hy : ∀ s, LatticeDivergenceFree (y s) :=
    galileanMeanRemovedPath_divergenceFree c u hu
  have hyc : Continuous y := continuous_galileanMeanRemovedPath c u huc
  let Ry : ℝ := Ru
  have hRy : 0 ≤ Ry := hRu
  have hyR : ∀ s ∈ Ioc (0 : ℝ) T, ‖y s‖ ≤ Ry := by
    intro s hs
    have hfixed := congrArg (fun w : WeightedLatticeBanach => w 0)
      (hmild ⟨s, hs.1.le, hs.2⟩)
    have hzero : u s 0 = rawMeanCarrier c 0 :=
      hfixed.trans ((criticalMildImage_zero_mode ν hν u₀ u huc hu hRu hs.1.le
        (fun q hq => huR q ⟨hq.1, hq.2.trans hs.2⟩)).trans hmean)
    exact (norm_meanRemovedCarrier_le c s (u s) hzero).trans (huR s hs)
  apply Subtype.ext
  funext k
  by_cases hk : k = 0
  · subst k
    have hut0 : u τ.1 0 = u₀ 0 := by
      have hfixed := congrArg (fun w : WeightedLatticeBanach => w 0) (hmild τ)
      exact hfixed.trans (criticalMildImage_zero_mode ν hν u₀ u huc hu
        hRu τ.2.1 (fun s hs => huR s ⟨hs.1, hs.2.trans τ.2.2⟩))
    have hyt0 : y τ.1 0 = 0 := by
      exact meanRemovedCarrier_zero_mode c τ.1 (u τ.1) (hut0.trans hmean)
    have hy00 : meanRemovedCarrier c 0 u₀ 0 = 0 :=
      meanRemovedCarrier_zero_mode c 0 u₀ hmean
    have himage0 := criticalMildImage_zero_mode ν hν
      (meanRemovedCarrier c 0 u₀) y hyc hy hRy τ.2.1
      (fun s hs => hyR s ⟨hs.1, hs.2.trans τ.2.2⟩)
    exact hyt0.trans (himage0.trans hy00).symm
  · have hy₀free : LatticeDivergenceFree (meanRemovedCarrier c 0 u₀) :=
      meanRemovedCarrier_divergenceFree c 0 hu₀
    let f : ℝ → ComplexE3 := fun s => criticalMildForcingMode k (u s)
    let xv : ℝ → ComplexE3 :=
      scalarHeatVolterra (modeHeatRate ν k) (u₀ k) f
    let g : ℝ → ComplexE3 := fun s =>
      exponentialPhase (physicalTranslationRate c k) s • f s +
        physicalTranslationRate c k •
          (exponentialPhase (physicalTranslationRate c k) s • xv s)
    have hf : Continuous f :=
      continuous_criticalMildForcingMode_path k u huc
    have hut : u τ.1 k = xv τ.1 := by
      have hfixed := congrArg (fun w : WeightedLatticeBanach => w k) (hmild τ)
      exact hfixed.trans (criticalMildImage_apply_eq_scalarHeatVolterra
        ν hν u₀ hu₀ u huc hu hRu τ.2.1
        (fun s hs => huR s ⟨hs.1, hs.2.trans τ.2.2⟩) k)
    have hphaseVolterra :
        exponentialPhase (physicalTranslationRate c k) τ.1 • xv τ.1 =
          scalarHeatVolterra (modeHeatRate ν k) (u₀ k) g τ.1 := by
      exact exponentialPhase_smul_scalarHeatVolterra
        (modeHeatRate ν k) (physicalTranslationRate c k) (u₀ k) f hf τ.1
    have hy0k : meanRemovedCarrier c 0 u₀ k = u₀ k := by
      rw [meanRemovedCarrier_apply_ne_zero c 0 u₀ hk,
        translationPhaseCarrier_apply]
      simp [physicalTranslationPhase]
    have hforcing : ∀ s ∈ uIcc (0 : ℝ) τ.1,
        criticalMildForcingMode k (y s) = g s := by
      intro s hs
      have hs0 : 0 ≤ s := by
        rw [uIcc_of_le τ.2.1] at hs
        exact hs.1
      have hsT : s ≤ T := by
        rw [uIcc_of_le τ.2.1] at hs
        exact hs.2.trans τ.2.2
      let σ : Icc (0 : ℝ) T := ⟨s, hs0, hsT⟩
      have hus : u s k = xv s := by
        have hfixed := congrArg (fun w : WeightedLatticeBanach => w k) (hmild σ)
        exact hfixed.trans (criticalMildImage_apply_eq_scalarHeatVolterra
          ν hν u₀ hu₀ u huc hu hRu hs0
          (fun q hq => huR q ⟨hq.1, hq.2.trans hsT⟩) k)
      rw [show y s = meanRemovedCarrier c s (u s) by rfl,
        criticalMildForcingMode_meanRemoved c s k (u s) (hu s)]
      rw [translationPhaseCarrier_apply,
        physicalTranslationPhase_eq_exponentialPhase, hus]
    have hscalar :
        scalarHeatVolterra (modeHeatRate ν k)
            (meanRemovedCarrier c 0 u₀ k)
            (fun s => criticalMildForcingMode k (y s)) τ.1 =
          scalarHeatVolterra (modeHeatRate ν k) (u₀ k) g τ.1 := by
      unfold scalarHeatVolterra
      rw [hy0k]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp
      rw [hforcing s hs]
    have himage := criticalMildImage_apply_eq_scalarHeatVolterra
      ν hν (meanRemovedCarrier c 0 u₀) hy₀free y hyc hy hRy τ.2.1
      (fun s hs => hyR s ⟨hs.1, hs.2.trans τ.2.2⟩) k
    rw [himage, hscalar, ← hphaseVolterra]
    rw [show y τ.1 k = translationPhaseCarrier c τ.1 (u τ.1) k by
      exact meanRemovedCarrier_apply_ne_zero c τ.1 (u τ.1) hk]
    rw [translationPhaseCarrier_apply,
      physicalTranslationPhase_eq_exponentialPhase, hut]

#check Navier.Analysis.CriticalMildGalileanVolterra.galileanMeanRemovedPath_fixedPoint_on_horizon
#print axioms Navier.Analysis.CriticalMildGalileanVolterra.norm_meanRemovedCarrier_le
#print axioms Navier.Analysis.CriticalMildGalileanVolterra.exponentialPhase_smul_scalarHeatVolterra
#print axioms Navier.Analysis.CriticalMildGalileanVolterra.criticalMildForcingMode_meanRemoved
#print axioms Navier.Analysis.CriticalMildGalileanVolterra.galileanMeanRemovedPath_fixedPoint_on_horizon

end Navier.Analysis.CriticalMildGalileanVolterra
