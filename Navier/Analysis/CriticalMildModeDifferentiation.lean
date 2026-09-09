import Navier.Analysis.PeriodicMildClassicalRealization
import Navier.Analysis.CriticalMildFullPositiveTimeRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Differentiating the actual critical mild equation mode by mode

At a fixed lattice mode the heat multiplier is a scalar exponential.  This
removes the endpoint singularity of the carrier-level estimate: the decoded
mode is an ordinary finite-dimensional variation-of-constants integral.  The
lemmas below first establish its exact derivative from continuity of the
literal projected convolution, then connect the resulting raw Fourier ODE to
the period-one physical coefficient equation and recovered pressure.

The derivative at time zero is kept separate because the official evolution
uses within derivatives on the closed half-line.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Set

namespace Navier.Analysis.CriticalMildModeDifferentiation

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.LerayProjection
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.PeriodicFourierReconstruction
open Navier.Analysis.PeriodicMildClassicalRealization
open Navier.Analysis.PeriodicPressureRecovery

/-- Scalar heat decay at one fixed Fourier mode. -/
def modeDecay (a t : ℝ) : ℂ :=
  Complex.exp (-(a : ℂ) * (t : ℂ))

def scalarModeDuhamel (a : ℝ) (b : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, modeDecay a (t - s) * b s

def scalarModePrimitive (a : ℝ) (b : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, Complex.exp ((a : ℂ) * (s : ℂ)) * b s

theorem scalarModeDuhamel_eq_decay_mul_primitive
    (a : ℝ) (b : ℝ → ℂ) (t : ℝ) :
    scalarModeDuhamel a b t = modeDecay a t * scalarModePrimitive a b t := by
  unfold scalarModeDuhamel scalarModePrimitive
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _hs
  unfold modeDecay
  change Complex.exp (-(a : ℂ) * ((t - s : ℝ) : ℂ)) * b s =
    Complex.exp (-(a : ℂ) * (t : ℂ)) *
      (Complex.exp ((a : ℂ) * (s : ℂ)) * b s)
  rw [← mul_assoc]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem hasDerivAt_modeDecay (a t : ℝ) :
    HasDerivAt (modeDecay a) (-(a : ℂ) * modeDecay a t) t := by
  unfold modeDecay
  have hlinear : HasDerivAt (fun s : ℝ => -(a : ℂ) * (s : ℂ))
      (-(a : ℂ)) t := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(a : ℂ)))
  simpa [mul_comm] using hlinear.cexp

theorem hasDerivAt_scalarModePrimitive
    (a : ℝ) {b : ℝ → ℂ} (hb : Continuous b) (t : ℝ) :
    HasDerivAt (scalarModePrimitive a b)
      (Complex.exp ((a : ℂ) * (t : ℂ)) * b t) t := by
  unfold scalarModePrimitive
  let g : ℝ → ℂ := fun s => Complex.exp ((a : ℂ) * (s : ℂ)) * b s
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  simpa [g] using intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable 0 t)
    (hg.stronglyMeasurableAtFilter volume (𝓝 t)) hg.continuousAt

theorem hasDerivAt_scalarModeDuhamel
    (a : ℝ) {b : ℝ → ℂ} (hb : Continuous b) (t : ℝ) :
    HasDerivAt (scalarModeDuhamel a b)
      (b t - (a : ℂ) * scalarModeDuhamel a b t) t := by
  have hfun : scalarModeDuhamel a b =
      fun s => modeDecay a s * scalarModePrimitive a b s := by
    funext s
    exact scalarModeDuhamel_eq_decay_mul_primitive a b s
  rw [hfun]
  have h := (hasDerivAt_modeDecay a t).mul
    (hasDerivAt_scalarModePrimitive a hb t)
  convert h using 1 <;> try rfl
  unfold modeDecay
  dsimp only
  have hcancel : Complex.exp (-(a : ℂ) * (t : ℂ)) *
      Complex.exp ((a : ℂ) * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [show Complex.exp (-(a : ℂ) * (t : ℂ)) *
      (Complex.exp ((a : ℂ) * (t : ℂ)) * b t) = b t by
        rw [← mul_assoc, hcancel, one_mul]]
  ring

/-- Raw heat-generator eigenvalue at one lattice mode. -/
def rawModeDecayRate (ν : ℝ) (k : LatticeMode) : ℝ :=
  ν * ‖officialEuclideanPoint (latticeFrequency k)‖ ^ 2

/-- Literal projected countable convolution at one evolving raw mode. -/
def projectedModeForcing (A : ℝ → WeightedLatticeBanach)
    (k : LatticeMode) (t : ℝ) : ComplexSpace :=
  complexLeray (latticeFrequency k)
    (spectralOutputCoefficient k (A t) (A t))

theorem continuous_projectedModeForcing
    {A : ℝ → WeightedLatticeBanach} (hA : Continuous A)
    (k : LatticeMode) : Continuous (projectedModeForcing A k) := by
  unfold projectedModeForcing spectralOutputCoefficient
  change Continuous fun t => complexLeray (latticeFrequency k)
    (WithLp.ofLp (weightedLatticeSpectralBilinear k (A t) (A t)))
  fun_prop

/-- Scalar coordinate evaluation of the completed weighted carrier. -/
def weightedLatticeScalarCoordinateCLM (k : LatticeMode) (i : Fin 3) :
    WeightedLatticeBanach →L[ℂ] ℂ :=
  (complexE3CoordinateCLM i).comp (weightedLatticePointCLM k)

@[simp] theorem weightedLatticeScalarCoordinateCLM_apply
    (k : LatticeMode) (i : Fin 3) (A : WeightedLatticeBanach) :
    weightedLatticeScalarCoordinateCLM k i A =
      weightedLatticeCoefficient A k i := rfl

theorem complexHeatDecay_lattice_eq_modeDecay
    (ν τ : ℝ) (k : LatticeMode) :
    (complexHeatDecay ν τ (latticeFrequency k) : ℂ) =
      modeDecay (rawModeDecayRate ν k) τ := by
  unfold complexHeatDecay heatDecay modeDecay rawModeDecayRate
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Coordinate evaluation commutes with the actual carrier Bochner integral,
and the decoded mode is exactly the ordinary scalar heat convolution. -/
theorem criticalMildDuhamel_coefficient_eq_scalarModeDuhamel
    (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖A s‖ ≤ R)
    (k : LatticeMode) (i : Fin 3) :
    weightedLatticeCoefficient (criticalMildDuhamel ν hν A hdiv t) k i =
      scalarModeDuhamel (rawModeDecayRate ν k)
        (fun s => projectedModeForcing A k s i) t := by
  have hint := integrableOn_criticalMildPathIntegrand
    ν hν A hAc hdiv hR ht hbound
  change weightedLatticeScalarCoordinateCLM k i
      (∫ s in Set.Ioc 0 t, criticalMildPathIntegrand ν hν A hdiv t s) = _
  rw [← (weightedLatticeScalarCoordinateCLM k i).integral_comp_comm hint]
  unfold scalarModeDuhamel
  rw [intervalIntegral.integral_of_le ht]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne t)] with s hs hne
  unfold criticalMildPathIntegrand
  have hlag : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs.2 hne)
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
    ν hν (A s) (A s) (hdiv s) hlag]
  rw [weightedLatticeScalarCoordinateCLM_apply,
    weightedLatticeCoefficient_heatRegularizedSpectralOutput
      ν (t - s) hν hlag (A s) (A s) (hdiv s) k,
    complexFrequencyHeatLeray_apply_coordinate,
    complexHeatDecay_lattice_eq_modeDecay]
  rfl

/-- On the interior of a bounded mild chart, every decoded nonlinear mode is
classically differentiable.  The derivative is the current projected
convolution minus the heat-generator eigenvalue times the Duhamel mode. -/
theorem hasDerivAt_criticalMildDuhamel_coefficient
    (ν : ℝ) (hν : 0 < ν)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (k : LatticeMode) (i : Fin 3) :
    HasDerivAt
      (fun r => weightedLatticeCoefficient
        (criticalMildDuhamel ν hν A hdiv r) k i)
      (projectedModeForcing A k t i -
        (rawModeDecayRate ν k : ℂ) *
          weightedLatticeCoefficient
            (criticalMildDuhamel ν hν A hdiv t) k i) t := by
  have hb : Continuous (fun s => projectedModeForcing A k s i) := by
    exact (continuous_apply i).comp (continuous_projectedModeForcing hAc k)
  have hscalar := hasDerivAt_scalarModeDuhamel
    (rawModeDecayRate ν k) hb t
  have heq : (fun r => weightedLatticeCoefficient
      (criticalMildDuhamel ν hν A hdiv r) k i) =ᶠ[𝓝 t]
      scalarModeDuhamel (rawModeDecayRate ν k)
        (fun s => projectedModeForcing A k s i) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact criticalMildDuhamel_coefficient_eq_scalarModeDuhamel
      ν hν A hAc hdiv hR hr.1.le
      (fun s hs => hbound s ⟨hs.1, hs.2.trans hr.2.le⟩) k i
  have hvalue := criticalMildDuhamel_coefficient_eq_scalarModeDuhamel
    ν hν A hAc hdiv hR ht.1.le
    (fun s hs => hbound s ⟨hs.1, hs.2.trans ht.2.le⟩) k i
  rw [hvalue]
  exact hscalar.congr_of_eventuallyEq heq

/-- Proof-independent decoded linear heat coefficient. -/
def linearHeatModeCoordinate (ν : ℝ) (u₀ : WeightedLatticeBanach)
    (k : LatticeMode) (i : Fin 3) (t : ℝ) : ℂ :=
  modeDecay (rawModeDecayRate ν k) t *
    complexLeray (latticeFrequency k)
      (weightedLatticeCoefficient u₀ k) i

theorem linearHeatModeCoordinate_eq_complexFrequencyHeatLeray
    (ν : ℝ) (u₀ : WeightedLatticeBanach)
    (k : LatticeMode) (i : Fin 3) (t : ℝ) :
    linearHeatModeCoordinate ν u₀ k i t =
      complexFrequencyHeatLeray ν t (latticeFrequency k)
        (weightedLatticeCoefficient u₀ k) i := by
  unfold linearHeatModeCoordinate
  rw [complexFrequencyHeatLeray_apply_coordinate,
    complexHeatDecay_lattice_eq_modeDecay]

theorem hasDerivAt_linearHeatModeCoordinate
    (ν : ℝ) (u₀ : WeightedLatticeBanach)
    (k : LatticeMode) (i : Fin 3) (t : ℝ) :
    HasDerivAt (linearHeatModeCoordinate ν u₀ k i)
      (-(rawModeDecayRate ν k : ℂ) *
        linearHeatModeCoordinate ν u₀ k i t) t := by
  unfold linearHeatModeCoordinate
  convert (hasDerivAt_modeDecay (rawModeDecayRate ν k) t).mul_const
    (complexLeray (latticeFrequency k)
      (weightedLatticeCoefficient u₀ k) i) using 1 <;> try rfl
  ring

/-- The fixed-mode mild right-hand side after exact scalar decoding. -/
def rawMildModeCoordinate (ν : ℝ) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (k : LatticeMode) (i : Fin 3)
    (t : ℝ) : ℂ :=
  linearHeatModeCoordinate ν u₀ k i t +
    scalarModeDuhamel (rawModeDecayRate ν k)
      (fun s => projectedModeForcing A k s i) t

theorem hasDerivAt_rawMildModeCoordinate
    (ν : ℝ) (u₀ : WeightedLatticeBanach)
    {A : ℝ → WeightedLatticeBanach} (hAc : Continuous A)
    (k : LatticeMode) (i : Fin 3) (t : ℝ) :
    HasDerivAt (rawMildModeCoordinate ν u₀ A k i)
      (projectedModeForcing A k t i -
        (rawModeDecayRate ν k : ℂ) *
          rawMildModeCoordinate ν u₀ A k i t) t := by
  have hb : Continuous (fun s => projectedModeForcing A k s i) :=
    (continuous_apply i).comp (continuous_projectedModeForcing hAc k)
  have h := (hasDerivAt_linearHeatModeCoordinate ν u₀ k i t).add
    (hasDerivAt_scalarModeDuhamel (rawModeDecayRate ν k) hb t)
  unfold rawMildModeCoordinate
  convert h using 1 <;> try rfl
  ring

/-- The actual mild fixed-point identity decodes at every positive interior
time to the proof-independent scalar variation-of-constants expression. -/
theorem mildPath_coefficient_eq_rawMildModeCoordinate
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht0 : 0 ≤ t) (htT : t < T)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) T),
      A s = criticalMildImage ν hν u₀ A hdiv s hs.1)
    (k : LatticeMode) (i : Fin 3) :
    weightedLatticeCoefficient (A t) k i =
      rawMildModeCoordinate ν u₀ A k i t := by
  rw [hmild t ⟨ht0, htT.le⟩]
  unfold criticalMildImage rawMildModeCoordinate
  rw [congrFun (weightedLatticeCoefficient_add
    (weightedHeatFlow ν t hν.le ht0 u₀)
    (criticalMildDuhamel ν hν A hdiv t)) k]
  change weightedLatticeCoefficient
      (weightedHeatFlow ν t hν.le ht0 u₀) k i +
      weightedLatticeCoefficient (criticalMildDuhamel ν hν A hdiv t) k i = _
  rw [weightedLatticeCoefficient_weightedHeatFlow,
    ← linearHeatModeCoordinate_eq_complexFrequencyHeatLeray,
    criticalMildDuhamel_coefficient_eq_scalarModeDuhamel
      ν hν A hAc hdiv hR ht0
      (fun s hs => hbound s ⟨hs.1, hs.2.trans htT.le⟩)]

/-- The actual mild path is classically differentiable at every positive
interior time, mode by mode, with the strong projected Fourier derivative. -/
theorem hasDerivAt_mildPath_coefficient
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) T),
      A s = criticalMildImage ν hν u₀ A hdiv s hs.1)
    (k : LatticeMode) (i : Fin 3) :
    HasDerivAt (fun r => weightedLatticeCoefficient (A r) k i)
      (projectedModeForcing A k t i -
        (rawModeDecayRate ν k : ℂ) *
          weightedLatticeCoefficient (A t) k i) t := by
  have hmodel := hasDerivAt_rawMildModeCoordinate ν u₀ hAc k i t
  have heq : (fun r => weightedLatticeCoefficient (A r) k i) =ᶠ[𝓝 t]
      rawMildModeCoordinate ν u₀ A k i := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact mildPath_coefficient_eq_rawMildModeCoordinate
      ν hν u₀ A hAc hdiv hR hr.1.le hr.2 hbound hmild k i
  have hvalue := mildPath_coefficient_eq_rawMildModeCoordinate
    ν hν u₀ A hAc hdiv hR ht.1.le ht.2 hbound hmild k i
  rw [hvalue]
  exact hmodel.congr_of_eventuallyEq heq

/-- Exact right derivative at the initial boundary.  This is a within
derivative on `[0,∞)` and therefore does not assume or manufacture a
negative-time mild evolution. -/
theorem hasDerivWithinAt_zero_mildPath_coefficient
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T : ℝ} (hR : 0 ≤ R) (hT : 0 < T)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) T),
      A s = criticalMildImage ν hν u₀ A hdiv s hs.1)
    (k : LatticeMode) (i : Fin 3) :
    HasDerivWithinAt (fun r => weightedLatticeCoefficient (A r) k i)
      (projectedModeForcing A k 0 i -
        (rawModeDecayRate ν k : ℂ) *
          weightedLatticeCoefficient (A 0) k i)
      (Set.Ici (0 : ℝ)) 0 := by
  have hmodel := hasDerivAt_rawMildModeCoordinate ν u₀ hAc k i 0
  have heq : (fun r => weightedLatticeCoefficient (A r) k i) =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0]
      rawMildModeCoordinate ν u₀ A k i := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with r hr0 hrT
    exact mildPath_coefficient_eq_rawMildModeCoordinate
      ν hν u₀ A hAc hdiv hR hr0 hrT hbound hmild k i
  have hvalue := mildPath_coefficient_eq_rawMildModeCoordinate
    ν hν u₀ A hAc hdiv hR (le_refl 0) hT hbound hmild k i
  have hactual := hmodel.hasDerivWithinAt.congr_of_eventuallyEq heq hvalue
  rw [hvalue]
  exact hactual

/-- The actual vector coefficient derivative supplied by the modewise mild
calculation. -/
def mildRawTimeDerivative (μ : ℝ)
    (A : ℝ → WeightedLatticeBanach)
    (t : ℝ) (k : LatticeMode) : ComplexSpace :=
  projectedModeForcing A k t -
    (rawModeDecayRate μ k : ℂ) • weightedLatticeCoefficient (A t) k

theorem hasDerivAt_mildPath_coefficient_eq_mildRawTimeDerivative
    (μ : ℝ) (hμ : 0 < μ) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ u₀ A hdiv s hs.1)
    (k : LatticeMode) (i : Fin 3) :
    HasDerivAt (fun r => weightedLatticeCoefficient (A r) k i)
      (mildRawTimeDerivative μ A t k i) t := by
  simpa [mildRawTimeDerivative, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
    hasDerivAt_mildPath_coefficient
      μ hμ u₀ A hAc hdiv hR ht hbound hmild k i

/-- Pointwise-in-time form of the raw projected coefficient equation. -/
def RawProjectedModeEquationAt (ν : ℝ)
    (A : WeightedLatticeBanach)
    (rawTimeDerivative : LatticeMode → ComplexSpace) : Prop :=
  ∀ k,
    rawTimeDerivative k -
        complexLeray (latticeFrequency k)
          (spectralOutputCoefficient k A A) +
        (((rawMildViscosity ν) *
          (latticeFrequency k ⬝ᵥ latticeFrequency k) : ℝ) : ℂ) •
          weightedLatticeCoefficient A k = 0

/-- The actual mode derivative satisfies the raw projected equation at every
positive interior time. -/
theorem mildRawTimeDerivative_projectedModeEquationAt
    (ν : ℝ) (A : ℝ → WeightedLatticeBanach) (t : ℝ) :
    RawProjectedModeEquationAt ν (A t)
      (mildRawTimeDerivative (rawMildViscosity ν) A t) := by
  intro k
  unfold mildRawTimeDerivative projectedModeForcing
  unfold rawModeDecayRate
  rw [officialPoint_norm_sq_eq_dotProduct]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
    smul_eq_mul]
  push_cast
  ring

/-- The pointwise raw projected equation feeds the already checked physical
normalization and pressure recovery, without requiring a global-in-time raw
equation premise. -/
theorem rawProjectedModeEquationAt_to_physicalUnprojected
    (ν : ℝ) (A : WeightedLatticeBanach)
    (rawTimeDerivative : LatticeMode → ComplexSpace)
    (hraw : RawProjectedModeEquationAt ν A rawTimeDerivative)
    (k : LatticeMode) :
    rawToPhysicalAmplitude • rawTimeDerivative k +
        periodOneConvectionCoefficient k
          (physicalCarrier A) (physicalCarrier A) +
        periodOneViscousCoefficient ν k
          (weightedLatticeCoefficient (physicalCarrier A) k) +
        periodOneGradientCoefficient k
          (periodOnePressureCoefficient k
            (physicalCarrier A) (physicalCarrier A)) = 0 := by
  have hr := hraw k
  rw [sub_eq_add_neg] at hr
  have hs := congrArg (fun z : ComplexSpace => rawToPhysicalAmplitude • z) hr
  simp only [smul_add, smul_zero] at hs
  rw [rawNonlinearity_to_periodOneConvection,
    rawViscosity_to_periodOneViscosity] at hs
  exact projected_mode_equation_to_unprojected ν k
    (rawToPhysicalAmplitude • rawTimeDerivative k)
    (weightedLatticeCoefficient (physicalCarrier A) k)
    (physicalCarrier A) (physicalCarrier A) hs

/-- Main positive-time consumer: an actual local mild fixed point, evolved at
the correctly scaled raw viscosity, has differentiable Fourier coefficients
and satisfies the exact unprojected physical period-one coefficient equation
with recovered pressure. -/
theorem mildFixedPoint_physicalUnprojected_at
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) T),
      A s = criticalMildImage (rawMildViscosity ν)
        (by unfold rawMildViscosity; positivity) u₀ A hdiv s hs.1) :
    (∀ k i, HasDerivAt (fun r => weightedLatticeCoefficient (A r) k i)
      (mildRawTimeDerivative (rawMildViscosity ν) A t k i) t) ∧
    ∀ k,
      rawToPhysicalAmplitude •
            mildRawTimeDerivative (rawMildViscosity ν) A t k +
          periodOneConvectionCoefficient k
            (physicalCarrier (A t)) (physicalCarrier (A t)) +
          periodOneViscousCoefficient ν k
            (weightedLatticeCoefficient (physicalCarrier (A t)) k) +
          periodOneGradientCoefficient k
            (periodOnePressureCoefficient k
              (physicalCarrier (A t)) (physicalCarrier (A t))) = 0 := by
  have hμ : 0 < rawMildViscosity ν := by
    unfold rawMildViscosity
    positivity
  constructor
  · intro k i
    exact hasDerivAt_mildPath_coefficient_eq_mildRawTimeDerivative
      (rawMildViscosity ν) hμ u₀ A hAc hdiv hR ht hbound hmild k i
  · intro k
    exact rawProjectedModeEquationAt_to_physicalUnprojected ν (A t)
      (mildRawTimeDerivative (rawMildViscosity ν) A t)
      (mildRawTimeDerivative_projectedModeEquationAt ν A t) k

end Navier.Analysis.CriticalMildModeDifferentiation
