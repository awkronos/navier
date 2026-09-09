import Navier.Analysis.LeiLinCoerciveTerminal

/-!
# Zero-mode conservation for the critical mild flow

The exact Fourier transport nonlinearity cannot create its spatial mean.  At
output mode zero, every interacting pair has opposite frequencies; moving the
advecting frequency to the output by divergence freedom makes each summand
vanish.  This removes the zero-mode summand from the mixed terminal estimate:
the remaining open estimate is entirely on nonzero modes.

This statement concerns the lattice mild carrier.  A reconstruction theorem
to the whole-space classical carrier and an arbitrary-data estimate for the
remaining nonzero modes are separate obligations.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildZeroMode

open MeasureTheory Set
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildBoundedContinuation
open Navier.Analysis.CriticalMildDirectLimit
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinTimeMixed
open Navier.Analysis.LeiLinCoerciveTerminal

/-- The zero lattice index embeds as the zero physical frequency. -/
@[simp] theorem latticeFrequency_zero :
    latticeFrequency (0 : LatticeMode) = 0 := by
  ext i
  fin_cases i <;> simp [latticeFrequency]

/-- Every literal transport summand contributing to output mode zero vanishes
when its advecting input is divergence-free. -/
theorem latticeSpectralTerm_zero_output
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (ij : LatticeMode × LatticeMode) :
    latticeSpectralTerm 0 (weightedLatticeCoefficient u)
      (weightedLatticeCoefficient v) ij = 0 := by
  by_cases hij : ij.1 + ij.2 = 0
  · rw [latticeSpectralTerm, if_pos hij]
    rw [spectralTransport_frequency_transfer u v hu ij.1 ij.2 0 hij]
    have hpoint : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
      ext i
      rfl
    rw [spectralTransport, latticeFrequency_zero, complexFrequency_zero, inner_zero_left,
      zero_smul, hpoint]
  · simp [latticeSpectralTerm, hij]

/-- The completed nonlinear convolution has no zero output mode. -/
theorem weightedLatticeSpectralConvolution_zero
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    weightedLatticeSpectralConvolution 0 u v = 0 := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [show (fun ij => latticeSpectralTerm 0 (weightedLatticeCoefficient u)
      (weightedLatticeCoefficient v) ij) = fun _ => 0 by
    funext ij
    exact latticeSpectralTerm_zero_output u v hu ij]
  simp

/-- The physical nonlinear coefficient at zero output frequency vanishes. -/
theorem spectralOutputCoefficient_zero
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    spectralOutputCoefficient 0 u v = 0 := by
  unfold spectralOutputCoefficient
  rw [weightedLatticeSpectralConvolution_zero u v hu]
  rfl

/-- Positive-time heat regularization preserves the zero-mode cancellation. -/
theorem heatRegularizedSpectralOutput_zero_mode
    (ν τ : ℝ) (hν : 0 < ν) (hτ : 0 < τ)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    heatRegularizedSpectralOutput ν τ hν hτ u v hu 0 = 0 := by
  rw [heatRegularizedSpectralOutput_apply]
  unfold heatRegularizedSpectralOutputFiber
  rw [spectralOutputCoefficient_zero u v hu]
  rw [latticeFrequency_zero, complexFrequencyHeatLeray_zero_frequency]
  have hpoint : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
    ext i
    rfl
  rw [hpoint, smul_zero]

/-- The zero-extended heat-regularized output vanishes at mode zero for every
real heat lag. -/
theorem positiveTimeHeatRegularizedSpectralOutput_zero_mode
    (ν : ℝ) (hν : 0 < ν)
    (u v : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) (τ : ℝ) :
    positiveTimeHeatRegularizedSpectralOutput ν hν u v hu τ 0 = 0 := by
  by_cases hτ : 0 < τ
  · rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν u v hu hτ]
    exact heatRegularizedSpectralOutput_zero_mode ν τ hν hτ u v hu
  · simp [positiveTimeHeatRegularizedSpectralOutput, hτ]

/-- Every evolving-path nonlinear integrand has zero spatial mean. -/
theorem criticalMildPathIntegrand_zero_mode
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s)) (t s : ℝ) :
    criticalMildPathIntegrand ν hν u hu t s 0 = 0 := by
  unfold criticalMildPathIntegrand
  exact positiveTimeHeatRegularizedSpectralOutput_zero_mode
    ν hν (u s) (u s) (hu s) (t - s)

/-- Continuous evaluation of the completed carrier at its zero mode. -/
def zeroModeEvalCLM : WeightedLatticeBanach →L[ℂ] ComplexE3 :=
  LinearMap.mkContinuous
    { toFun := fun u => u 0
      map_add' := by intro u v; rfl
      map_smul' := by intro c u; rfl }
    1
    (fun u => by simpa using norm_weightedLattice_eval_le u 0)

@[simp] theorem zeroModeEvalCLM_apply (u : WeightedLatticeBanach) :
    zeroModeEvalCLM u = u 0 :=
  rfl

/-- The actual Bochner Duhamel term has zero spatial mean. -/
theorem criticalMildDuhamel_zero_mode
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    criticalMildDuhamel ν hν u hu t 0 = 0 := by
  have hint := integrableOn_criticalMildPathIntegrand ν hν u huc hu hR ht huR
  change zeroModeEvalCLM
      (∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hu t s) = 0
  rw [← zeroModeEvalCLM.integral_comp_comm hint]
  have hz : (fun s =>
      zeroModeEvalCLM (criticalMildPathIntegrand ν hν u hu t s)) =
      fun _ => 0 := by
    funext s
    exact criticalMildPathIntegrand_zero_mode ν hν u hu t s
  rw [hz, integral_zero]

/-- Heat flow leaves the zero Fourier coefficient unchanged. -/
theorem weightedHeatFlow_zero_mode
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (u : WeightedLatticeBanach) :
    weightedHeatFlow ν t hν ht u 0 = u 0 := by
  rw [Navier.Analysis.CriticalMildHeatCarrierAlgebra.weightedHeatFlow_apply]
  unfold weightedHeatFlowCoordinate
  rw [latticeFrequency_zero, complexFrequencyHeatLeray_zero_frequency]
  exact latticeModeWeight_smul_complexEuclideanPoint_weightedLatticeCoefficient u 0

/-- The assembled critical mild image preserves the initial zero mode. -/
theorem criticalMildImage_zero_mode
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    criticalMildImage ν hν a u hu t ht 0 = a 0 := by
  unfold criticalMildImage
  change weightedHeatFlow ν t hν.le ht a 0 +
      criticalMildDuhamel ν hν u hu t 0 = a 0
  rw [weightedHeatFlow_zero_mode ν t hν.le ht a]
  rw [criticalMildDuhamel_zero_mode ν hν u huc hu hR ht huR, add_zero]

/-- Every actual finite critical mild chart preserves the zero Fourier
coefficient of its original datum, including at the chart's terminal time. -/
theorem criticalMildChart_terminal_zero_mode_eq_initial
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R)
    (hmild : ∀ τ : Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) :
    u.1 ⟨T, ⟨hT, le_rfl⟩⟩ 0 = a 0 := by
  let ext : ℝ → WeightedLatticeBanach := criticalMildPathExtension T hT u.1
  have hextc : Continuous ext := continuous_criticalMildPathExtension T hT u.1
  have hextdf : ∀ s, LatticeDivergenceFree (ext s) :=
    criticalMildPathBallExtension_divergenceFree hT u
  have hR : 0 ≤ R :=
    (norm_nonneg (u.1 ⟨T, ⟨hT, le_rfl⟩⟩)).trans
      (criticalMildPathBall_norm_le u ⟨T, ⟨hT, le_rfl⟩⟩)
  have hextR : ∀ s ∈ Ioc (0 : ℝ) T, ‖ext s‖ ≤ R := by
    intro s _hs
    exact criticalMildPathBallExtension_norm_le hT u s
  have hfixed := congrArg (fun w : WeightedLatticeBanach => w 0)
    (hmild ⟨T, ⟨hT, le_rfl⟩⟩)
  exact hfixed.trans
    (criticalMildImage_zero_mode ν hν a ext hextc hextdf hR hT hextR)

/-- At zero frequency, the physical amplitude is exactly the completed
carrier coordinate norm because the inhomogeneous weight equals one. -/
theorem weightedAmplitude_zero_eq_norm_apply (u : WeightedLatticeBanach) :
    weightedAmplitude u 0 = ‖u 0‖ := by
  have h := norm_apply_eq_weight_mul_amplitude u (0 : LatticeMode)
  rw [latticeModeSize_zero] at h
  simpa using h.symm

/-- Consequently every actual finite mild chart preserves its zero-mode
amplitude at the terminal time. -/
theorem criticalMildChart_terminal_zero_amplitude_eq_initial
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach)
    {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R)
    (hmild : ∀ τ : Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) :
    weightedAmplitude (u.1 ⟨T, ⟨hT, le_rfl⟩⟩) 0 =
      weightedAmplitude a 0 := by
  rw [weightedAmplitude_zero_eq_norm_apply, weightedAmplitude_zero_eq_norm_apply,
    criticalMildChart_terminal_zero_mode_eq_initial ν hν a hT u hmild]

/-- The genuinely nonlinear part of the terminal mixed quantity: only
nonzero modes occur. -/
def offZeroMixedCriticalQty (ν : ℝ) (u : WeightedLatticeBanach) : ℝ :=
  normXm1 latticeModeSize (amplitudeOffZero u) +
    ν * normX1 latticeModeSize (amplitudeOffZero u)

/-- The mixed critical quantity splits exactly into the conserved mean and
its nonzero-mode remainder. -/
theorem mixedCriticalQty_eq_zero_amplitude_add_offZero
    (ν : ℝ) (u : WeightedLatticeBanach) :
    mixedCriticalQty ν u = weightedAmplitude u 0 + offZeroMixedCriticalQty ν u := by
  unfold mixedCriticalQty offZeroMixedCriticalQty
  rw [normXm1_offZero, normX1_offZero]
  ring

/-- The sharp remaining terminal hypothesis after exact zero-mode
conservation: a horizon-independent bound only on nonzero modes. -/
def CriticalMildOffZeroTerminalBound (ν : ℝ) (hν : 0 < ν)
    (a : WeightedLatticeBanach) (K : ℝ) : Prop :=
  ∀ {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R),
    (∀ τ : Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) →
    offZeroMixedCriticalQty ν (u.1 ⟨T, ⟨hT, le_rfl⟩⟩) ≤ K

/-- An off-zero terminal estimate supplies the former full mixed estimate;
the only added constant is the datum's exactly conserved zero-mode amplitude. -/
theorem criticalMildMixedTerminalBound_of_offZero
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (K : ℝ)
    (hoff : CriticalMildOffZeroTerminalBound ν hν a K) :
    CriticalMildMixedTerminalBound ν hν a (weightedAmplitude a 0 + K) := by
  intro T R hT u hmild
  rw [mixedCriticalQty_eq_zero_amplitude_add_offZero,
    criticalMildChart_terminal_zero_amplitude_eq_initial ν hν a hT u hmild]
  exact add_le_add (le_refl _) (hoff hT u hmild)

/-- The nonzero-mode terminal estimate now feeds the existing bounded-chain
consumer directly.  This eliminates the zero-mode burden but does not prove
the remaining arbitrary-data estimate. -/
theorem criticalMildTerminalNormBound_of_offZero
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (K : ℝ)
    (hK : 0 ≤ K)
    (hoff : CriticalMildOffZeroTerminalBound ν hν a K) :
    CriticalMildTerminalNormBound ν hν a
      (coerciveConstant ν * (weightedAmplitude a 0 + K)) := by
  apply criticalMildTerminalNormBound_of_mixed ν hν a
    (weightedAmplitude a 0 + K)
  · exact add_nonneg (weightedAmplitude_nonneg a 0) hK
  · exact criticalMildMixedTerminalBound_of_offZero ν hν a K hoff

/-- The sharpened nonzero-mode premise reaches the existing direct-limit
consumer: it produces a cofinal coherent chain whose total extension satisfies
the actual critical mild equation at every nonnegative time. -/
theorem exists_cofinal_global_mild_of_offZero
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (K : ℝ)
    (hK : 0 ≤ K)
    (hoff : CriticalMildOffZeroTerminalBound ν hν a K) :
    ∃ chain : CriticalMildCoherentChain ν hν a,
      chain.CofinalLifespan ∧
      ∀ t : ℝ, ∀ ht : 0 ≤ t,
        chain.totalExtension t =
          criticalMildImage ν hν a chain.totalExtension
            chain.totalExtension_divergenceFree t ht := by
  let M : ℝ := max ‖a‖
    (coerciveConstant ν * (weightedAmplitude a 0 + K))
  have hM : 0 ≤ M := le_trans (norm_nonneg a) (le_max_left _ _)
  have ha : ‖a‖ ≤ M := le_max_left _ _
  have hbase : CriticalMildTerminalNormBound ν hν a
      (coerciveConstant ν * (weightedAmplitude a 0 + K)) :=
    criticalMildTerminalNormBound_of_offZero ν hν a K hK hoff
  have hbound : CriticalMildTerminalNormBound ν hν a M := by
    intro T R hT u hmild
    exact (hbase hT u hmild).trans (le_max_right _ _)
  let chain : CriticalMildCoherentChain ν hν a :=
    boundedCoherentChain ν hν a M hM ha hbound
  refine ⟨chain, ?_, ?_⟩
  · exact boundedCoherentChain_cofinal ν hν a M hM ha hbound
  · exact bounded_global_mild_of_terminalNormBound ν hν a M hM ha hbound

end Navier.Analysis.CriticalMildZeroMode
