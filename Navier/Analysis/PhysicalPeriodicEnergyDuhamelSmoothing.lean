import Navier.Analysis.PhysicalPeriodicDissipationHeatRestart
import Navier.Analysis.PhysicalPeriodicTotalEnergyControl

/-!
# Energy control of a heat-separated periodic Duhamel output

For one fixed output frequency, incompressibility transfers the derivative
from an input frequency to the output frequency.  Cauchy--Schwarz on that
exact convolution fiber then replaces the two critical carrier norms by the
square roots of the two raw spectral energies.  The remaining output heat
kernel is summable at every positive lag.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicEnergyDuhamelSmoothing

open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildHeatCoefficientLift
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildTimeJetInterchange
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicDissipationHeatRestart
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicTotalEnergyControl
open Navier.Analysis.CriticalMildSelfMap

/-- Decoded amplitude product on one exact output fiber. -/
def energyFiberPairMass (k : LatticeMode)
    (u v : WeightedLatticeBanach)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) : ℝ :=
  weightedAmplitude u ij.1.1 * weightedAmplitude v ij.1.2

private theorem fiber_fst_injective (k : LatticeMode) :
    Function.Injective
      (fun ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode) => ij.1.1) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext hxy
  have hx : x.1.1 + x.1.2 = k := x.2
  have hy : y.1.1 + y.1.2 = k := y.2
  have hxy' : x.1.1 = y.1.1 := by simpa using hxy
  rw [hxy'] at hx
  exact add_left_cancel (hx.trans hy.symm)

private theorem fiber_snd_injective (k : LatticeMode) :
    Function.Injective
      (fun ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode) => ij.1.2) := by
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · have hx : x.1.1 + x.1.2 = k := x.2
    have hy : y.1.1 + y.1.2 = k := y.2
    have hxy' : x.1.2 = y.1.2 := by simpa using hxy
    rw [hxy'] at hx
    exact add_right_cancel (hx.trans hy.symm)
  · exact hxy

/-- Cauchy--Schwarz on the exact convolution fiber. -/
theorem tsum_energyFiberPairMass_le
    (k : LatticeMode) (u v : WeightedLatticeBanach) :
    (∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        energyFiberPairMass k u v ij) ≤
      Real.sqrt (rawHighSpectralEnergy 0 u) *
        Real.sqrt (rawHighSpectralEnergy 0 v) := by
  let eu : LatticeMode → ℝ := fun i => weightedAmplitude u i ^ 2
  let ev : LatticeMode → ℝ := fun i => weightedAmplitude v i ^ 2
  have heu : Summable eu := summable_rawSpectralEnergyDensity u
  have hev : Summable ev := summable_rawSpectralEnergyDensity v
  have hEu : (∑' i, eu i) = rawHighSpectralEnergy 0 u := by
    unfold rawHighSpectralEnergy eu rawSpectralEnergyDensity
    apply tsum_congr
    intro i
    rw [if_pos (latticeModeSize_nonneg i)]
  have hEv : (∑' i, ev i) = rawHighSpectralEnergy 0 v := by
    unfold rawHighSpectralEnergy ev rawSpectralEnergyDensity
    apply tsum_congr
    intro i
    rw [if_pos (latticeModeSize_nonneg i)]
  apply Real.tsum_le_of_sum_le
  · intro ij
    exact mul_nonneg (weightedAmplitude_nonneg u _) (weightedAmplitude_nonneg v _)
  · intro S
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt S
      (fun ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode) => weightedAmplitude u ij.1.1)
      (fun ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode) => weightedAmplitude v ij.1.2)
    let pf : latticeOutputMode ⁻¹' ({k} : Set LatticeMode) → LatticeMode := fun ij => ij.1.1
    let ps : latticeOutputMode ⁻¹' ({k} : Set LatticeMode) → LatticeMode := fun ij => ij.1.2
    have huS : (∑ ij ∈ S, eu ij.1.1) ≤ ∑' i, eu i := by
      rw [← Finset.sum_image (fiber_fst_injective k).injOn]
      exact heu.sum_le_tsum (S.image pf) (fun _ _ => sq_nonneg _)
    have hvS : (∑ ij ∈ S, ev ij.1.2) ≤ ∑' i, ev i := by
      rw [← Finset.sum_image (fiber_snd_injective k).injOn]
      exact hev.sum_le_tsum (S.image ps) (fun _ _ => sq_nonneg _)
    calc
      ∑ ij ∈ S, energyFiberPairMass k u v ij ≤
          Real.sqrt (∑ ij ∈ S, eu ij.1.1) *
            Real.sqrt (∑ ij ∈ S, ev ij.1.2) := by
        simpa [energyFiberPairMass, eu, ev] using hcs
      _ ≤ Real.sqrt (∑' i, eu i) * Real.sqrt (∑' i, ev i) := by
        exact mul_le_mul (Real.sqrt_le_sqrt huS) (Real.sqrt_le_sqrt hvS)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [hEu, hEv]


/-- The decoded energy pair mass is summable on each output fiber. -/
theorem summable_energyFiberPairMass
    (k : LatticeMode) (u v : WeightedLatticeBanach) :
    Summable (energyFiberPairMass k u v) := by
  have hu : Summable fun i : LatticeMode => weightedAmplitude u i := by
    simpa only [abs_of_nonneg (weightedAmplitude_nonneg u _)] using
      summable_amplitude u
  have hv : Summable fun i : LatticeMode => weightedAmplitude v i := by
    simpa only [abs_of_nonneg (weightedAmplitude_nonneg v _)] using
      summable_amplitude v
  have hp : Summable fun ij : LatticeMode × LatticeMode =>
      weightedAmplitude u ij.1 * weightedAmplitude v ij.2 :=
    hu.mul_of_nonneg hv (fun _ => weightedAmplitude_nonneg u _)
      (fun _ => weightedAmplitude_nonneg v _)
  change Summable ((fun ij : LatticeMode × LatticeMode =>
    weightedAmplitude u ij.1 * weightedAmplitude v ij.2) ∘
      (Subtype.val : (latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) → _))
  exact hp.subtype (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))

/-- Output-frequency scalar left after the fixed-fiber energy estimate. -/
def energyOutputHeatKernel (ν τ : ℝ) (k : LatticeMode) : ℝ :=
  latticeModeWeight k * latticeModeSize k *
    complexHeatDecay ν τ (latticeFrequency k)

/-- The exact heat-regularized transport term is bounded by the output heat
kernel times the decoded energy pair mass. -/
theorem norm_constrainedHeatRegularizedFiberTerm_le_energy
    (ν τ : ℝ) (_hν : 0 < ν) (_hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖constrainedHeatRegularizedFiberTerm ν τ k u v ij‖ ≤
      energyOutputHeatKernel ν τ k * energyFiberPairMass k u v ij := by
  have hwk : 0 ≤ latticeModeWeight k :=
    zero_le_one.trans (one_le_latticeModeWeight k)
  have hdec : 0 ≤ complexHeatDecay ν τ (latticeFrequency k) :=
    complexHeatDecay_nonneg _ _ _
  have htransport := complexEuclideanNorm_spectralTransport_output_le
    u v hu ij.1.1 ij.1.2 k ij.2
  have hheat := complexEuclideanNorm_heatLeray_le_decay ν τ k
    (spectralTransport (latticeFrequency ij.1.2)
      (weightedLatticeCoefficient u ij.1.1)
      (weightedLatticeCoefficient v ij.1.2))
  unfold constrainedHeatRegularizedFiberTerm
  rw [norm_smul, Real.norm_of_nonneg hwk]
  change latticeModeWeight k * complexEuclideanNorm
      (complexFrequencyHeatLeray ν τ (latticeFrequency k)
        (spectralTransport (latticeFrequency ij.1.2)
          (weightedLatticeCoefficient u ij.1.1)
          (weightedLatticeCoefficient v ij.1.2))) ≤ _
  calc
    latticeModeWeight k * complexEuclideanNorm
        (complexFrequencyHeatLeray ν τ (latticeFrequency k)
          (spectralTransport (latticeFrequency ij.1.2)
            (weightedLatticeCoefficient u ij.1.1)
            (weightedLatticeCoefficient v ij.1.2))) ≤
      latticeModeWeight k *
        (complexHeatDecay ν τ (latticeFrequency k) *
          complexEuclideanNorm
            (spectralTransport (latticeFrequency ij.1.2)
              (weightedLatticeCoefficient u ij.1.1)
              (weightedLatticeCoefficient v ij.1.2))) :=
        mul_le_mul_of_nonneg_left hheat hwk
    _ ≤ latticeModeWeight k *
        (complexHeatDecay ν τ (latticeFrequency k) *
          (‖complexFrequency (latticeFrequency k)‖ *
            complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htransport hdec) hwk
    _ = energyOutputHeatKernel ν τ k * energyFiberPairMass k u v ij := by
      unfold energyOutputHeatKernel energyFiberPairMass latticeModeSize weightedAmplitude
      ring

/-- Fixed-output nonlinear heat smoothing from raw spectral energy alone. -/
theorem norm_constrainedHeatRegularizedFiber_le_energy
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ ≤
      energyOutputHeatKernel ν τ k *
        (Real.sqrt (rawHighSpectralEnergy 0 u) *
          Real.sqrt (rawHighSpectralEnergy 0 v)) := by
  have hm := summable_energyFiberPairMass k u v
  have hk0 : 0 ≤ energyOutputHeatKernel ν τ k := by
    unfold energyOutputHeatKernel
    exact mul_nonneg
      (mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight k))
        (latticeModeSize_nonneg k))
      (complexHeatDecay_nonneg _ _ _)
  unfold constrainedHeatRegularizedFiber
  calc
    ‖∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        constrainedHeatRegularizedFiberTerm ν τ k u v ij‖ ≤
      ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        ‖constrainedHeatRegularizedFiberTerm ν τ k u v ij‖ :=
      norm_tsum_le_tsum_norm
        (summable_constrainedHeatRegularizedFiberTerm ν τ hν hτ u v hu k).norm
    _ ≤ ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
        energyOutputHeatKernel ν τ k * energyFiberPairMass k u v ij := by
      exact Summable.tsum_le_tsum
        (norm_constrainedHeatRegularizedFiberTerm_le_energy ν τ hν hτ u v hu k)
        (summable_constrainedHeatRegularizedFiberTerm ν τ hν hτ u v hu k).norm
        (hm.mul_left _)
    _ = energyOutputHeatKernel ν τ k *
        ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
          energyFiberPairMass k u v ij := tsum_mul_left
    _ ≤ energyOutputHeatKernel ν τ k *
        (Real.sqrt (rawHighSpectralEnergy 0 u) *
          Real.sqrt (rawHighSpectralEnergy 0 v)) :=
      mul_le_mul_of_nonneg_left (tsum_energyFiberPairMass_le k u v) hk0


/-- Explicit output heat-kernel constant obtained from eight equal substeps. -/
def octupleHeatWeightConstant (ν τ : ℝ) : ℝ :=
  (1 + (Real.sqrt (ν * (τ / 8)))⁻¹) ^ 8

/-- Eight one-weight heat gains leave six inverse lattice weights after paying
for the output carrier weight and transferred derivative. -/
theorem latticeModeWeight_pow_eight_mul_heatDecay_le
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (k : LatticeMode) :
    latticeModeWeight k ^ 8 *
        complexHeatDecay ν τ (latticeFrequency k) ≤
      octupleHeatWeightConstant ν τ := by
  have hstepTime : 0 < τ / 8 := by positivity
  have hstep := latticeModeWeight_heatDecay_le
    ν (τ / 8) hν hstepTime k
  have hdecay : complexHeatDecay ν τ (latticeFrequency k) =
      complexHeatDecay ν (τ / 8) (latticeFrequency k) ^ 8 := by
    unfold complexHeatDecay FrequencyHeatLeray.heatDecay
    let x : ℝ := -ν * (τ / 8) *
      ‖Navier.Analysis.OfficialABEncoding.officialEuclideanPoint
        (latticeFrequency k)‖ ^ 2
    rw [show -ν * τ *
        ‖Navier.Analysis.OfficialABEncoding.officialEuclideanPoint
          (latticeFrequency k)‖ ^ 2 = (8 : ℝ) * x by
      dsimp [x]
      ring]
    convert Real.exp_nat_mul x 8 using 1 <;> dsimp [x]
  rw [hdecay]
  have hnonneg : 0 ≤ latticeModeWeight k *
      complexHeatDecay ν (τ / 8) (latticeFrequency k) :=
    mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight k))
      (complexHeatDecay_nonneg _ _ _)
  have hpow := pow_le_pow_left₀ hnonneg hstep 8
  simpa [octupleHeatWeightConstant, mul_pow] using hpow

/-- The output kernel is dominated by the fixed inverse-sixth lattice kernel. -/
theorem energyOutputHeatKernel_le_inverseSix
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (k : LatticeMode) :
    energyOutputHeatKernel ν τ k ≤
      octupleHeatWeightConstant ν τ * (latticeModeWeight k ^ 6)⁻¹ := by
  have hw : 0 < latticeModeWeight k :=
    lt_of_lt_of_le zero_lt_one (one_le_latticeModeWeight k)
  have hs : latticeModeSize k ≤ latticeModeWeight k := by
    unfold latticeModeWeight latticeModeSize
    linarith [norm_nonneg (complexFrequency (latticeFrequency k))]
  have hd := complexHeatDecay_nonneg ν τ (latticeFrequency k)
  have hbase := latticeModeWeight_pow_eight_mul_heatDecay_le ν τ hν hτ k
  rw [show octupleHeatWeightConstant ν τ * (latticeModeWeight k ^ 6)⁻¹ =
      octupleHeatWeightConstant ν τ / latticeModeWeight k ^ 6 by
    rw [div_eq_mul_inv]]
  apply (le_div_iff₀ (pow_pos hw 6)).2
  calc
    energyOutputHeatKernel ν τ k * latticeModeWeight k ^ 6 =
        latticeModeSize k *
          (latticeModeWeight k ^ 7 *
            complexHeatDecay ν τ (latticeFrequency k)) := by
      unfold energyOutputHeatKernel
      ring
    _ ≤ latticeModeWeight k *
          (latticeModeWeight k ^ 7 *
            complexHeatDecay ν τ (latticeFrequency k)) := by
      exact mul_le_mul_of_nonneg_right hs
        (mul_nonneg (pow_nonneg hw.le 7) hd)
    _ = latticeModeWeight k ^ 8 *
          complexHeatDecay ν τ (latticeFrequency k) := by ring
    _ ≤ octupleHeatWeightConstant ν τ := hbase

/-- The positive-lag energy output heat kernel is summable on the lattice. -/
theorem summable_energyOutputHeatKernel
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ) :
    Summable (energyOutputHeatKernel ν τ) := by
  have hmajor := summable_latticeModeWeight_inv_pow_six.mul_left
    (octupleHeatWeightConstant ν τ)
  exact hmajor.of_nonneg_of_le
    (fun k => by
      unfold energyOutputHeatKernel
      exact mul_nonneg
        (mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight k))
          (latticeModeSize_nonneg k))
        (complexHeatDecay_nonneg _ _ _))
    (energyOutputHeatKernel_le_inverseSix ν τ hν hτ)

/-- **Energy-only smoothing of the actual nonlinear Fourier output.**  At a
strictly positive heat lag, the completed nonlinear output is controlled by
raw spectral energies, with no critical carrier norm on the right-hand side. -/
theorem norm_heatRegularizedSpectralOutput_le_energy
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu‖ ≤
      (∑' k : LatticeMode, energyOutputHeatKernel ν τ k) *
        (Real.sqrt (rawHighSpectralEnergy 0 u) *
          Real.sqrt (rawHighSpectralEnergy 0 v)) := by
  have hk := summable_energyOutputHeatKernel ν τ hν hτ
  have hc : 0 ≤ Real.sqrt (rawHighSpectralEnergy 0 u) *
      Real.sqrt (rawHighSpectralEnergy 0 v) := by positivity
  rw [norm_heatRegularizedSpectralOutput_eq_tsum]
  calc
    (∑' k, ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖) ≤
      ∑' k, energyOutputHeatKernel ν τ k *
        (Real.sqrt (rawHighSpectralEnergy 0 u) *
          Real.sqrt (rawHighSpectralEnergy 0 v)) := by
      exact Summable.tsum_le_tsum
        (norm_constrainedHeatRegularizedFiber_le_energy ν τ hν hτ u v hu)
        (summable_norm_constrainedHeatRegularizedFiber ν τ hν hτ u v hu)
        (hk.mul_right _)
    _ = (∑' k : LatticeMode, energyOutputHeatKernel ν τ k) *
        (Real.sqrt (rawHighSpectralEnergy 0 u) *
          Real.sqrt (rawHighSpectralEnergy 0 v)) := tsum_mul_right


/-- **Datum-only positive-lag bound for the actual mild integrand.**  Along a
physical mild chart, every strictly heat-separated nonlinear history slice is
controlled by the initial spectral energy.  The chart radius is used only to
invoke the proved energy identity and does not occur in the bound. -/
theorem norm_criticalMildPathIntegrand_le_initialEnergy
    (μ : ℝ) (hμ : 0 < μ)
    (a : WeightedLatticeBanach) (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ r, LatticeDivergenceFree (A r))
    (hreal : ∀ r, PhysicalAntiHermitian (A r))
    {R T t s : ℝ} (hR : 0 ≤ R) (hs : s ∈ Set.Icc (0 : ℝ) T)
    (hst : s < t)
    (hbound : ∀ r ∈ Set.Ioc (0 : ℝ) T, ‖A r‖ ≤ R)
    (hmild : ∀ r (hr : r ∈ Set.Icc (0 : ℝ) T),
      A r = criticalMildImage μ hμ a A hdiv r hr.1) :
    ‖criticalMildPathIntegrand μ hμ A hdiv t s‖ ≤
      (∑' k : LatticeMode, energyOutputHeatKernel μ (t - s) k) *
        rawHighSpectralEnergy 0 a := by
  have hlag : 0 < t - s := sub_pos.mpr hst
  have hout := norm_heatRegularizedSpectralOutput_le_energy
    μ (t - s) hμ hlag (A s) (A s) (hdiv s)
  have hE := mild_totalEnergy_le_initial
    μ hμ a ha A hAc hdiv hreal hR hs hbound hmild
  have hE0 : 0 ≤ rawHighSpectralEnergy 0 (A s) := by
    unfold rawHighSpectralEnergy
    exact tsum_nonneg fun k => by
      rw [if_pos (latticeModeSize_nonneg k)]
      exact sq_nonneg _
  have hK0 : 0 ≤ ∑' k : LatticeMode,
      energyOutputHeatKernel μ (t - s) k :=
    tsum_nonneg fun k => by
      unfold energyOutputHeatKernel
      exact mul_nonneg
        (mul_nonneg (zero_le_one.trans (one_le_latticeModeWeight k))
          (latticeModeSize_nonneg k))
        (complexHeatDecay_nonneg _ _ _)
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos μ hμ
    (A s) (A s) (hdiv s) hlag]
  calc
    ‖heatRegularizedSpectralOutput μ (t - s) hμ hlag
        (A s) (A s) (hdiv s)‖ ≤
      (∑' k : LatticeMode, energyOutputHeatKernel μ (t - s) k) *
        (Real.sqrt (rawHighSpectralEnergy 0 (A s)) *
          Real.sqrt (rawHighSpectralEnergy 0 (A s))) := hout
    _ = (∑' k : LatticeMode, energyOutputHeatKernel μ (t - s) k) *
        rawHighSpectralEnergy 0 (A s) := by
      rw [Real.mul_self_sqrt hE0]
    _ ≤ (∑' k : LatticeMode, energyOutputHeatKernel μ (t - s) k) *
        rawHighSpectralEnergy 0 a :=
      mul_le_mul_of_nonneg_left hE hK0

end Navier.Analysis.PhysicalPeriodicEnergyDuhamelSmoothing
