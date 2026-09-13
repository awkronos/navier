import Navier.Analysis.LeiLinPositiveRestartCancellation
import Navier.Analysis.LeiLinCriticalMechanism

/-!
# Modewise heat spending for the frozen periodic nonlinear source

Freezing the nonlinear source at the observation time separates the endpoint
problem into a genuinely time-varying Dini remainder and a constant-source
heat integral.  The latter must not be estimated by the pointwise graph bound
`1 / t`: modewise integration spends the full heat dissipation exactly once.

This file proves the scalar finite-horizon resolvent estimate that drives that
step and then applies it to the exact completed weighted lattice convolution.
The resulting graph bound is a property of the actual frozen nonlinear
Duhamel integral, with no assumed terminal-tail estimate.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Topology

namespace Navier.Analysis.PeriodicDynamicCriticalTail

open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildGlobalReindex
open Navier.Analysis.CriticalMildGlobalWeightedOutput
open Navier.Analysis.CriticalMildHeatCoefficientLift
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.LeiLinCriticalMechanism
open Navier.Analysis.LeiLinPositiveRestartCancellation

/-- A finite positive-time window spends at most the full heat dissipation
budget of one nonzero mode. -/
theorem integral_mode_heat_dissipation_le_inv
    (ν q T : ℝ) (hν : 0 < ν) (hq : 0 < q) (_hT : 0 ≤ T) :
    (∫ τ in Ioc 0 T, q ^ 2 * Real.exp (-((ν * q ^ 2) * τ))) ≤ ν⁻¹ := by
  have ha : 0 < ν * q ^ 2 := by positivity
  have hbase : IntegrableOn
      (fun τ : ℝ => (ν * q ^ 2) * Real.exp (-((ν * q ^ 2) * τ))) (Ioi 0) := by
    change Integrable
      (fun τ : ℝ => (ν * q ^ 2) * Real.exp (-((ν * q ^ 2) * τ)))
      (volume.restrict (Ioi 0))
    convert (exp_neg_integrableOn_Ioi 0 ha).const_mul (ν * q ^ 2) using 1
    funext τ
    congr 2
    ring
  have hsubset : Ioc (0 : ℝ) T ⊆ Ioi 0 := fun _ h => h.1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun τ : ℝ => (ν * q ^ 2) * Real.exp (-((ν * q ^ 2) * τ)) :=
    Filter.Eventually.of_forall fun _ => mul_nonneg ha.le (Real.exp_pos _).le
  have hmono :
      (∫ τ in Ioc 0 T, (ν * q ^ 2) * Real.exp (-((ν * q ^ 2) * τ))) ≤
        ∫ τ in Ioi 0, (ν * q ^ 2) * Real.exp (-((ν * q ^ 2) * τ)) := by
    exact setIntegral_mono_set hbase hnonneg
      (Filter.Eventually.of_forall fun _ hx => hsubset hx)
  rw [dissipation_integral_eq_one (ν * q ^ 2) ha] at hmono
  have hscale :
      (∫ τ in Ioc 0 T, (ν * q ^ 2) * Real.exp (-((ν * q ^ 2) * τ))) =
        ν * ∫ τ in Ioc 0 T, q ^ 2 * Real.exp (-((ν * q ^ 2) * τ)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with τ
    ring
  rw [hscale] at hmono
  have hνne : ν ≠ 0 := ne_of_gt hν
  calc
    (∫ τ in Ioc 0 T, q ^ 2 * Real.exp (-((ν * q ^ 2) * τ))) =
        ν⁻¹ * (ν * ∫ τ in Ioc 0 T,
          q ^ 2 * Real.exp (-((ν * q ^ 2) * τ))) := by field_simp
    _ ≤ ν⁻¹ * 1 := mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr hν.le)
    _ = ν⁻¹ := mul_one _

/-- Static pair mass on the completed one-weight carrier.  The time dependence
is kept entirely in the output heat multiplier. -/
def frozenOutputPairMass (u v : WeightedLatticeBanach)
    (ij : LatticeMode × LatticeMode) : ℝ :=
  ‖u ij.1‖ * ‖v ij.2‖

theorem summable_frozenOutputPairMass (u v : WeightedLatticeBanach) :
    Summable (frozenOutputPairMass u v) := by
  have hu : Summable fun i : LatticeMode => ‖u i‖ := by simpa using u.2.summable
  have hv : Summable fun j : LatticeMode => ‖v j‖ := by simpa using v.2.summable
  exact hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-- Before taking any uniform heat-gain bound, one exact constrained triad
retains its output exponential.  This retained exponential is what makes the
frozen graph integral finite. -/
theorem norm_constrainedHeatRegularizedFiberTerm_le_exactDecay
    (ν τ : ℝ) (_hν : 0 < ν) (_hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode)
    (ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) :
    ‖constrainedHeatRegularizedFiberTerm ν τ k u v ij‖ ≤
      complexHeatDecay ν τ (latticeFrequency k) *
        ‖complexFrequency (latticeFrequency k)‖ *
          frozenOutputPairMass u v ij.1 := by
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
  have hweight : latticeModeWeight k ≤
      latticeModeWeight ij.1.1 * latticeModeWeight ij.1.2 := by
    have hij : ij.1.1 + ij.1.2 = k := by
      have hm := ij.2
      change latticeOutputMode ij.1 = k at hm
      simpa [latticeOutputMode] using hm
    calc
      latticeModeWeight k = latticeModeWeight (ij.1.1 + ij.1.2) :=
        congrArg latticeModeWeight hij.symm
      _ ≤ latticeModeWeight ij.1.1 * latticeModeWeight ij.1.2 :=
        latticeModeWeight_add_le_mul _ _
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
    _ ≤ complexHeatDecay ν τ (latticeFrequency k) *
        ‖complexFrequency (latticeFrequency k)‖ *
          ((latticeModeWeight ij.1.1 *
              complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1)) *
            (latticeModeWeight ij.1.2 *
              complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) := by
      let C := complexHeatDecay ν τ (latticeFrequency k) *
        ‖complexFrequency (latticeFrequency k)‖ *
          (complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
            complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))
      calc
        latticeModeWeight k *
            (complexHeatDecay ν τ (latticeFrequency k) *
              (‖complexFrequency (latticeFrequency k)‖ *
                complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1) *
                  complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) =
            latticeModeWeight k * C := by dsimp [C]; ring
        _ ≤ (latticeModeWeight ij.1.1 * latticeModeWeight ij.1.2) * C :=
          mul_le_mul_of_nonneg_right hweight (by
            dsimp [C]
            exact mul_nonneg (mul_nonneg hdec (norm_nonneg _))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
        _ = complexHeatDecay ν τ (latticeFrequency k) *
            ‖complexFrequency (latticeFrequency k)‖ *
              ((latticeModeWeight ij.1.1 *
                  complexEuclideanNorm (weightedLatticeCoefficient u ij.1.1)) *
                (latticeModeWeight ij.1.2 *
                  complexEuclideanNorm (weightedLatticeCoefficient v ij.1.2))) := by
          dsimp [C]
          ring
    _ = complexHeatDecay ν τ (latticeFrequency k) *
        ‖complexFrequency (latticeFrequency k)‖ *
          frozenOutputPairMass u v ij.1 := by
      have hui := latticeWeightedAmplitude_coefficient u ij.1.1
      have hvj := latticeWeightedAmplitude_coefficient v ij.1.2
      unfold latticeWeightedAmplitude at hui hvj
      rw [hui, hvj]
      unfold frozenOutputPairMass
      ring

/-- Static pair mass grouped by its exact output frequency. -/
def frozenOutputFiberMass (u v : WeightedLatticeBanach) (k : LatticeMode) : ℝ :=
  ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
    frozenOutputPairMass u v ij.1

theorem summable_frozenOutputFiberMass (u v : WeightedLatticeBanach) :
    Summable (frozenOutputFiberMass u v) := by
  have hp := summable_frozenOutputPairMass u v
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      frozenOutputPairMass u v x.2.1) :=
    latticeOutputFiberSigmaEquiv.summable_iff.mpr hp
  exact hsigma.sigma

set_option maxHeartbeats 800000 in
theorem tsum_frozenOutputFiberMass_eq (u v : WeightedLatticeBanach) :
    (∑' k : LatticeMode, frozenOutputFiberMass u v k) = ‖u‖ * ‖v‖ := by
  have hp := summable_frozenOutputPairMass u v
  have hsigma : Summable (fun x :
      Σ k : LatticeMode, latticeOutputMode ⁻¹' ({k} : Set LatticeMode) =>
      frozenOutputPairMass u v x.2.1) :=
    latticeOutputFiberSigmaEquiv.summable_iff.mpr hp
  calc
    (∑' k : LatticeMode, frozenOutputFiberMass u v k) =
        ∑' x : Σ k : LatticeMode,
          latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
          frozenOutputPairMass u v x.2.1 := by
      rw [show frozenOutputFiberMass u v = fun k =>
          ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
            frozenOutputPairMass u v ij.1 by rfl,
        ← hsigma.tsum_sigma]
    _ = ∑' ij : LatticeMode × LatticeMode, frozenOutputPairMass u v ij :=
      latticeOutputFiberSigmaEquiv.tsum_eq _
    _ = ‖u‖ * ‖v‖ := by
      unfold frozenOutputPairMass
      have hu : Summable fun i : LatticeMode => ‖u i‖ := by
        simpa using u.2.summable
      have hv : Summable fun j : LatticeMode => ‖v j‖ := by
        simpa using v.2.summable
      have hp' : Summable fun ij : LatticeMode × LatticeMode =>
          ‖u ij.1‖ * ‖v ij.2‖ :=
        hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      rw [← hu.tsum_mul_tsum hv hp']
      have hnu : ∑' x : LatticeMode, ‖u x‖ = ‖u‖ := by
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
        simp [ENNReal.toReal_one]
      have hnv : ∑' y : LatticeMode, ‖v y‖ = ‖v‖ := by
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
        simp [ENNReal.toReal_one]
      exact (congrArg (fun x : ℝ => x * ∑' y : LatticeMode, ‖v y‖) hnu).trans
        (congrArg (‖u‖ * ·) hnv)

set_option maxHeartbeats 800000 in
/-- Exact-decay bound on one completed output fiber. -/
theorem norm_constrainedHeatRegularizedFiber_le_exactDecay
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ ≤
      complexHeatDecay ν τ (latticeFrequency k) *
        ‖complexFrequency (latticeFrequency k)‖ *
          frozenOutputFiberMass u v k := by
  have hp := (summable_frozenOutputPairMass u v).subtype
    (latticeOutputMode ⁻¹' ({k} : Set LatticeMode))
  let C := complexHeatDecay ν τ (latticeFrequency k) *
    ‖complexFrequency (latticeFrequency k)‖
  let g : Subtype (latticeOutputMode ⁻¹' ({k} : Set LatticeMode)) → ℝ :=
    fun ij => C * (frozenOutputPairMass u v ∘ Subtype.val) ij
  have hc : Summable g := hp.mul_left C
  calc
    ‖constrainedHeatRegularizedFiber ν τ hν hτ u v hu k‖ ≤
        ∑' ij : latticeOutputMode ⁻¹' ({k} : Set LatticeMode),
          complexHeatDecay ν τ (latticeFrequency k) *
            ‖complexFrequency (latticeFrequency k)‖ *
              frozenOutputPairMass u v ij.1 := by
      exact tsum_of_norm_bounded hc.hasSum
        (fun ij => by
          dsimp [g, C]
          exact norm_constrainedHeatRegularizedFiberTerm_le_exactDecay
            ν τ hν hτ u v hu k ij)
    _ = complexHeatDecay ν τ (latticeFrequency k) *
        ‖complexFrequency (latticeFrequency k)‖ *
          frozenOutputFiberMass u v k := by
      unfold frozenOutputFiberMass
      rw [← tsum_mul_left]

set_option maxHeartbeats 800000 in
/-- Each coordinate of the actual frozen-source Bochner integral gains the
full output resolvent. -/
theorem frequency_mul_norm_frozenOutputIntegral_apply_le
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (k : LatticeMode) :
    ‖complexFrequency (latticeFrequency k)‖ *
        ‖positiveTimeHeatRegularizedSpectralOutputIntegral
          ν T hν hT u v hu k‖ ≤
      ν⁻¹ * frozenOutputFiberMass u v k := by
  let q : ℝ := ‖complexFrequency (latticeFrequency k)‖
  by_cases hk : k = 0
  · subst k
    have hq : q = 0 := by
      dsimp [q]
      exact latticeModeSize_zero
    change q * _ ≤ _
    rw [hq, zero_mul]
    exact mul_nonneg (inv_nonneg.mpr hν.le) (by
      unfold frozenOutputFiberMass frozenOutputPairMass
      exact tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · have hq : 0 < q := lt_of_lt_of_le zero_lt_one
      (one_le_latticeModeSize_of_ne_zero hk)
    let F := positiveTimeHeatRegularizedSpectralOutput ν hν u v hu
    have hF : IntegrableOn F (Ioc 0 T) volume :=
      integrableOn_positiveTimeHeatRegularizedSpectralOutput ν T hν hT u v hu
    have hcoord :
        positiveTimeHeatRegularizedSpectralOutputIntegral ν T hν hT u v hu k =
          ∫ τ in Ioc 0 T, F τ k := by
      unfold positiveTimeHeatRegularizedSpectralOutputIntegral
      change (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k)
          (∫ τ in Ioc 0 T, F τ) = _
      exact (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integral_comp_comm hF |>.symm
    have hFk : IntegrableOn (fun τ => F τ k) (Ioc 0 T) volume :=
      (lp.evalCLM ℂ (fun _ : LatticeMode => ComplexE3) 1 k).integrable_comp hF
    let g : ℝ → ℝ := fun τ => q ^ 2 *
      Real.exp (-((ν * q ^ 2) * τ)) * frozenOutputFiberMass u v k
    have hg : IntegrableOn g (Ioc 0 T) volume := by
      have hfull : IntegrableOn
          (fun τ : ℝ => Real.exp (-((ν * q ^ 2) * τ))) (Ioi 0) := by
        have ha : 0 < ν * q ^ 2 := by positivity
        simpa only [neg_mul, mul_assoc] using exp_neg_integrableOn_Ioi 0 ha
      have hres := (hfull.mono_set
        (fun _ (h : _ ∈ Ioc (0 : ℝ) T) => h.1)).const_mul (q ^ 2)
      exact hres.mul_const (frozenOutputFiberMass u v k)
    have hpoint : ∀ τ ∈ Ioc (0 : ℝ) T,
        q * ‖F τ k‖ ≤ g τ := by
      intro τ hτ
      have hpos : 0 < τ := hτ.1
      have hFeq : F τ = heatRegularizedSpectralOutput ν τ hν hpos u v hu :=
        positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν u v hu hpos
      rw [hFeq]
      rw [heatRegularizedSpectralOutput_apply]
      rw [← constrainedHeatRegularizedFiber_eq_heatRegularizedSpectralOutputFiber
        ν τ hν hpos u v hu k]
      have hfiber := norm_constrainedHeatRegularizedFiber_le_exactDecay
        ν τ hν hpos u v hu k
      calc
        q * ‖constrainedHeatRegularizedFiber ν τ hν hpos u v hu k‖ ≤
            q * (complexHeatDecay ν τ (latticeFrequency k) * q *
              frozenOutputFiberMass u v k) :=
          mul_le_mul_of_nonneg_left hfiber hq.le
        _ = g τ := by
          dsimp [g, q]
          unfold complexHeatDecay heatDecay
          rw [← complexFrequency_norm_eq_official (latticeFrequency k)]
          ring_nf
    have hnorm : q * ‖∫ τ in Ioc 0 T, F τ k‖ ≤ ∫ τ in Ioc 0 T, g τ := by
      calc
        q * ‖∫ τ in Ioc 0 T, F τ k‖ ≤
            q * ∫ τ in Ioc 0 T, ‖F τ k‖ :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hq.le
        _ = ∫ τ in Ioc 0 T, q * ‖F τ k‖ := by
          rw [MeasureTheory.integral_const_mul]
        _ ≤ ∫ τ in Ioc 0 T, g τ := by
          apply integral_mono_ae (hFk.norm.const_mul q) hg
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
          exact hpoint τ hτ
    change q * _ ≤ _
    rw [hcoord]
    refine hnorm.trans ?_
    unfold g
    rw [MeasureTheory.integral_mul_const]
    exact mul_le_mul_of_nonneg_right
      (integral_mode_heat_dissipation_le_inv ν q T hν hq hT)
      (by
        unfold frozenOutputFiberMass frozenOutputPairMass
        exact tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The actual frozen nonlinear Duhamel integral belongs to the
half-generator graph domain for arbitrary one-weight data. -/
theorem summable_halfGeneratorMoment_frozenOutputIntegral
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ *
        ‖positiveTimeHeatRegularizedSpectralOutputIntegral
          ν T hν hT u v hu k‖ := by
  have hright : Summable fun k : LatticeMode =>
      ν⁻¹ * frozenOutputFiberMass u v k :=
    (summable_frozenOutputFiberMass u v).mul_left _
  exact hright.of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (frequency_mul_norm_frozenOutputIntegral_apply_le ν T hν hT u v hu)

/-- Quantitative modewise-resolvent bound for the actual frozen nonlinear
Duhamel integral.  Its constant is independent of the window length. -/
theorem heatHalfGeneratorMoment_frozenOutputIntegral_le
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    heatHalfGeneratorMoment
        (positiveTimeHeatRegularizedSpectralOutputIntegral
          ν T hν hT u v hu) ≤
      ν⁻¹ * ‖u‖ * ‖v‖ := by
  unfold heatHalfGeneratorMoment
  have hleft := summable_halfGeneratorMoment_frozenOutputIntegral
    ν T hν hT u v hu
  have hright : Summable fun k : LatticeMode =>
      ν⁻¹ * frozenOutputFiberMass u v k :=
    (summable_frozenOutputFiberMass u v).mul_left _
  calc
    (∑' k : LatticeMode,
      ‖complexFrequency (latticeFrequency k)‖ *
        ‖positiveTimeHeatRegularizedSpectralOutputIntegral
          ν T hν hT u v hu k‖) ≤
        ∑' k : LatticeMode, ν⁻¹ * frozenOutputFiberMass u v k :=
      hleft.tsum_le_tsum
        (frequency_mul_norm_frozenOutputIntegral_apply_le
          ν T hν hT u v hu) hright
    _ = ν⁻¹ * (∑' k : LatticeMode, frozenOutputFiberMass u v k) :=
      tsum_mul_left
    _ = ν⁻¹ * ‖u‖ * ‖v‖ := by
      rw [tsum_frozenOutputFiberMass_eq]
      ring

/-- Positive output heat puts the exact nonlinear carrier in the graph domain
at every strict lag, without graph regularity of either input. -/
theorem summable_halfGeneratorMoment_heatRegularizedSpectralOutput
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ *
        ‖heatRegularizedSpectralOutput ν τ hν hτ u v hu k‖ := by
  let a : ℝ := τ / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let z := heatRegularizedSpectralOutput ν a hν ha u v hu
  have hz : LatticeDivergenceFree z :=
    heatRegularizedSpectralOutput_divergenceFree ν a hν ha u v hu
  have hs := summable_halfGeneratorMoment_weightedHeatFlow ν a hν ha z hz
  have hsemigroup := weightedHeatFlow_heatRegularizedSpectralOutput
    ν a a hν ha ha u v hu
  have haa : a + a = τ := by dsimp [a]; ring
  have heq : weightedHeatFlow ν a hν.le ha.le z =
      heatRegularizedSpectralOutput ν τ hν hτ u v hu := by
    dsimp [z]
    simpa only [haa] using hsemigroup
  rw [heq] at hs
  exact hs

/-- Freezing a constant endpoint path and reversing elapsed time produces
exactly the pre-existing positive-time frozen-source integral. -/
theorem criticalMildDuhamel_constant_eq_frozenOutputIntegral
    (ν T : ℝ) (hν : 0 < ν) (hT : 0 ≤ T)
    (v : WeightedLatticeBanach) (hv : LatticeDivergenceFree v) :
    criticalMildDuhamel ν hν (fun _ => v) (fun _ => hv) T =
      positiveTimeHeatRegularizedSpectralOutputIntegral
        ν T hν hT v v hv := by
  unfold criticalMildDuhamel criticalMildPathIntegrand
  unfold positiveTimeHeatRegularizedSpectralOutputIntegral
  rw [← intervalIntegral.integral_of_le hT,
    ← intervalIntegral.integral_of_le hT]
  have h := intervalIntegral.integral_comp_sub_left
    (a := 0) (b := T)
    (positiveTimeHeatRegularizedSpectralOutput ν hν v v hv) T
  simpa only [sub_self, sub_zero] using h

theorem summable_halfGeneratorMoment_sub
    (x y : WeightedLatticeBanach)
    (hx : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖x k‖)
    (hy : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖y k‖) :
    Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖(x - y) k‖ := by
  have hright : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖x k‖ +
        ‖complexFrequency (latticeFrequency k)‖ * ‖y k‖ := hx.add hy
  exact hright.of_nonneg_of_le
    (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun k => by
      change _ * ‖x k - y k‖ ≤ _
      calc
        ‖complexFrequency (latticeFrequency k)‖ * ‖x k - y k‖ ≤
            ‖complexFrequency (latticeFrequency k)‖ * (‖x k‖ + ‖y k‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
        _ = ‖complexFrequency (latticeFrequency k)‖ * ‖x k‖ +
            ‖complexFrequency (latticeFrequency k)‖ * ‖y k‖ := by ring)

set_option maxHeartbeats 1000000 in
/-- The Dini cancellation plus the exact frozen resolvent puts the actual
nonlinear Duhamel term in the half-generator graph domain.  The only dynamic
input is the displayed endpoint Dini integral; no terminal tail is assumed. -/
theorem criticalMildDuhamel_graph_and_moment_le_of_dini
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (huR : ∀ s ∈ Ioc (0 : ℝ) T, ‖u s‖ ≤ R)
    (hDini : IntervalIntegrable
      (fun s => (2 / (ν * (T - s))) * (‖u s‖ + ‖u T‖) * ‖u s - u T‖)
      volume 0 T) :
    (Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ *
        ‖criticalMildDuhamel ν hν u hu T k‖) ∧
      heatHalfGeneratorMoment (criticalMildDuhamel ν hν u hu T) ≤
        (∫ s in Ioc 0 T,
          (2 / (ν * (T - s))) * (‖u s‖ + ‖u T‖) * ‖u s - u T‖) +
          ν⁻¹ * ‖u T‖ ^ 2 := by
  let cpath : ℝ → WeightedLatticeBanach := fun _ => u T
  let hucpath : ∀ s, LatticeDivergenceFree (cpath s) := fun _ => hu T
  let f : ℝ → WeightedLatticeBanach := fun s =>
    criticalMildPathIntegrand ν hν u hu T s -
      criticalMildPathIntegrand ν hν cpath hucpath T s
  let d : WeightedLatticeBanach := ∫ s in Ioc 0 T, f s
  let c : WeightedLatticeBanach :=
    positiveTimeHeatRegularizedSpectralOutputIntegral
      ν T hν hT (u T) (u T) (hu T)
  have huInt := integrableOn_criticalMildPathIntegrand
    ν hν u huc hu hR hT huR
  have hcInt : IntegrableOn
      (criticalMildPathIntegrand ν hν cpath hucpath T) (Ioc 0 T) volume := by
    apply integrableOn_criticalMildPathIntegrand
      ν hν cpath continuous_const hucpath (norm_nonneg (u T)) hT
    intro s hs
    exact le_rfl
  have hfInt : IntegrableOn f (Ioc 0 T) volume := by
    exact huInt.sub hcInt
  have hfMomentInterval : IntervalIntegrable
      (fun s => heatHalfGeneratorMoment (f s)) volume 0 T := by
    exact intervalIntegrable_heatHalfGeneratorMoment_path_sub_constant_of_dini
      ν hν u huc hu hT hDini
  have hfMoment : IntegrableOn
      (fun s => heatHalfGeneratorMoment (f s)) (Ioc 0 T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hfMomentInterval
  have hfSum : ∀ᵐ s ∂volume.restrict (Ioc 0 T),
      Summable fun k : LatticeMode =>
        ‖complexFrequency (latticeFrequency k)‖ * ‖f s k‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    by_cases hst : s < T
    · have hevol : Summable fun k : LatticeMode =>
          ‖complexFrequency (latticeFrequency k)‖ *
            ‖criticalMildPathIntegrand ν hν u hu T s k‖ := by
        unfold criticalMildPathIntegrand
        rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
          ν hν (u s) (u s) (hu s) (sub_pos.mpr hst)]
        exact summable_halfGeneratorMoment_heatRegularizedSpectralOutput
          ν (T - s) hν (sub_pos.mpr hst) (u s) (u s) (hu s)
      have hconst : Summable fun k : LatticeMode =>
          ‖complexFrequency (latticeFrequency k)‖ *
            ‖criticalMildPathIntegrand ν hν cpath hucpath T s k‖ := by
        unfold criticalMildPathIntegrand
        rw [positiveTimeHeatRegularizedSpectralOutput_of_pos
          ν hν (u T) (u T) (hu T) (sub_pos.mpr hst)]
        exact summable_halfGeneratorMoment_heatRegularizedSpectralOutput
          ν (T - s) hν (sub_pos.mpr hst) (u T) (u T) (hu T)
      exact summable_halfGeneratorMoment_sub _ _ hevol hconst
    · have hst' : s = T := le_antisymm hs.2 (not_lt.mp hst)
      subst s
      simp [f, criticalMildPathIntegrand,
        positiveTimeHeatRegularizedSpectralOutput]
  have hdMoment : heatHalfGeneratorMoment d ≤
      ∫ s in Ioc 0 T, heatHalfGeneratorMoment (f s) := by
    exact heatHalfGeneratorMoment_integral_le_integral f hfInt hfSum hfMoment
  have hDiniOn : IntegrableOn
      (fun s => (2 / (ν * (T - s))) * (‖u s‖ + ‖u T‖) * ‖u s - u T‖)
      (Ioc 0 T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hDini
  have hdMomentDini : heatHalfGeneratorMoment d ≤
      ∫ s in Ioc 0 T,
        (2 / (ν * (T - s))) * (‖u s‖ + ‖u T‖) * ‖u s - u T‖ := by
    refine hdMoment.trans ?_
    apply integral_mono_ae hfMoment hDiniOn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact heatHalfGeneratorMoment_criticalMildPathIntegrand_sub_constant_le
      ν hν u hu hs.2
  have hdSum : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖d k‖ := by
    apply summable_of_sum_le
    · intro k
      exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · intro F
      exact sum_heatHalfGeneratorMoment_integral_le_integral
        F f hfInt hfSum hfMoment
  have hcSum : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖c k‖ :=
    summable_halfGeneratorMoment_frozenOutputIntegral
      ν T hν hT (u T) (u T) (hu T)
  have hcMoment : heatHalfGeneratorMoment c ≤ ν⁻¹ * ‖u T‖ ^ 2 := by
    dsimp [c]
    have hc := heatHalfGeneratorMoment_frozenOutputIntegral_le
      ν T hν hT (u T) (u T) (hu T)
    simpa only [pow_two, mul_assoc] using hc
  have hdecomp : criticalMildDuhamel ν hν u hu T = d + c := by
    have hsub : d = criticalMildDuhamel ν hν u hu T -
        criticalMildDuhamel ν hν cpath hucpath T := by
      dsimp [d, f]
      rw [integral_sub huInt hcInt]
      rfl
    have hconst : criticalMildDuhamel ν hν cpath hucpath T = c := by
      dsimp [cpath, hucpath, c]
      exact criticalMildDuhamel_constant_eq_frozenOutputIntegral
        ν T hν hT (u T) (hu T)
    rw [hsub, hconst]
    abel
  constructor
  · rw [hdecomp]
    have hright : Summable fun k : LatticeMode =>
        ‖complexFrequency (latticeFrequency k)‖ * ‖d k‖ +
          ‖complexFrequency (latticeFrequency k)‖ * ‖c k‖ := hdSum.add hcSum
    exact hright.of_nonneg_of_le
      (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun k => by
        change _ * ‖d k + c k‖ ≤ _
        calc
          ‖complexFrequency (latticeFrequency k)‖ * ‖d k + c k‖ ≤
              ‖complexFrequency (latticeFrequency k)‖ * (‖d k‖ + ‖c k‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
          _ = ‖complexFrequency (latticeFrequency k)‖ * ‖d k‖ +
              ‖complexFrequency (latticeFrequency k)‖ * ‖c k‖ := by ring)
  · rw [hdecomp]
    refine (heatHalfGeneratorMoment_add_le d c hdSum hcSum).trans ?_
    exact add_le_add hdMomentDini hcMoment

end Navier.Analysis.PeriodicDynamicCriticalTail
