import Navier.Analysis.CriticalMildZeroMode

/-!
# Energy--graph frequency splitting for periodic critical control

The exact nonlinear Duhamel analysis supplies a terminal graph moment once a
time-modulus budget is available.  Native energy controls an `ℓ²` amplitude,
whereas the remaining periodic continuation consumer asks for an `ℓ¹`
critical quantity.  This file supplies the missing quantitative bridge:
low modes are paid for by energy and high modes by the graph moment.

The cutoff is arbitrary.  Its low-frequency constant is an explicit finite
sum, and the high-frequency coefficient decays as `N⁻³ + ν N⁻¹`.  Thus the
result preserves datum dependence and has no dependence on chart horizon or
radius whenever the energy and graph budgets are uniform.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal NNReal ComplexConjugate BigOperators
open MeasureTheory Set Filter Topology

namespace Navier.Analysis.PeriodicGlobalCriticalControl

open Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildDuhamel
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedSpace
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.LerayProjection
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildPathFixedPoint
open Navier.Analysis.CriticalMildPathContraction
open Navier.Analysis.CriticalMildBoundedContinuation
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.CriticalMildZeroMode

/-- Above a positive cutoff, the inverse-critical and viscous-critical
weights are absorbed by two graph derivatives with the sharp powers of the
cutoff. -/
theorem inv_add_viscous_mul_le_graph_cutoff
    (ν N q : ℝ) (hν : 0 ≤ ν) (hN : 0 < N) (hNq : N ≤ q) :
    q⁻¹ + ν * q ≤ (N⁻¹ ^ 3 + ν * N⁻¹) * q ^ 2 := by
  have hq : 0 < q := hN.trans_le hNq
  have hcube : N ^ 3 ≤ q ^ 3 := by
    have hfac : 0 ≤ (q - N) * (q ^ 2 + q * N + N ^ 2) := by positivity
    nlinarith
  have hinv : q⁻¹ ≤ N⁻¹ ^ 3 * q ^ 2 := by
    field_simp [ne_of_gt hN, ne_of_gt hq]
    simpa [pow_succ] using hcube
  have hvisc : ν * q ≤ (ν * N⁻¹) * q ^ 2 := by
    have hqN : q ≤ N⁻¹ * q ^ 2 := by
      field_simp [ne_of_gt hN]
      nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hqN hν
  nlinarith

/-- Finite-band Cauchy--Schwarz: an arbitrary nonnegative coefficient weight
costs its explicit finite `ℓ²` norm times the global amplitude energy. -/
theorem finite_weighted_sum_le_sqrt_energy
    {G : Type*} (S : Finset G) (w f : G → ℝ)
    (hw : ∀ k ∈ S, 0 ≤ w k) (hf : ∀ k, 0 ≤ f k)
    (hf2 : Summable fun k => f k ^ 2) :
    (∑ k ∈ S, w k * f k) ≤
      Real.sqrt (∑ k ∈ S, w k ^ 2) * Real.sqrt (∑' k, f k ^ 2) := by
  have hlow : 0 ≤ ∑ k ∈ S, w k * f k :=
    Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk) (hf k)
  have hA : 0 ≤ ∑ k ∈ S, w k ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : 0 ≤ ∑' k, f k ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hfiniteE : (∑ k ∈ S, f k ^ 2) ≤ ∑' k, f k ^ 2 :=
    hf2.sum_le_tsum S fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S w f
  have hsquare : (∑ k ∈ S, w k * f k) ^ 2 ≤
      (Real.sqrt (∑ k ∈ S, w k ^ 2) * Real.sqrt (∑' k, f k ^ 2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hE]
    exact hcs.trans (mul_le_mul_of_nonneg_left hfiniteE hA)
  exact (sq_le_sq₀ hlow
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hsquare

/-- Abstract low-energy/high-graph split for the mixed critical sum. -/
theorem critical_sum_le_energy_graph_split
    {G : Type*} (S : Finset G) (σ f : G → ℝ) (ν N : ℝ)
    (hν : 0 ≤ ν) (hN : 0 < N)
    (hσ : ∀ k, 0 ≤ σ k) (hf : ∀ k, 0 ≤ f k)
    (hout : ∀ k ∉ S, N ≤ σ k)
    (hmixed : Summable fun k => (σ k)⁻¹ * f k + ν * (σ k * f k))
    (hf2 : Summable fun k => f k ^ 2)
    (hgraph : Summable fun k => σ k ^ 2 * f k) :
    (∑' k : G, ((σ k)⁻¹ * f k + ν * (σ k * f k))) ≤
      Real.sqrt (∑ k ∈ S, ((σ k)⁻¹ + ν * σ k) ^ 2) *
          Real.sqrt (∑' k : G, f k ^ 2) +
        (N⁻¹ ^ 3 + ν * N⁻¹) *
          (∑' k : ↥(↑S : Set G)ᶜ, σ k.1 ^ 2 * f k.1) := by
  let F : G → ℝ := fun k => (σ k)⁻¹ * f k + ν * (σ k * f k)
  have hF : ∀ k, F k = ((σ k)⁻¹ + ν * σ k) * f k := by
    intro k
    dsimp [F]
    ring
  have hw : ∀ k ∈ S, 0 ≤ (σ k)⁻¹ + ν * σ k := by
    intro k _
    exact add_nonneg (inv_nonneg.mpr (hσ k)) (mul_nonneg hν (hσ k))
  have hlow := finite_weighted_sum_le_sqrt_energy S
    (fun k => (σ k)⁻¹ + ν * σ k) f hw hf hf2
  have hcoef : 0 ≤ N⁻¹ ^ 3 + ν * N⁻¹ := by positivity
  have htailPoint : ∀ k : ↥(↑S : Set G)ᶜ,
      F k.1 ≤ (N⁻¹ ^ 3 + ν * N⁻¹) * (σ k.1 ^ 2 * f k.1) := by
    intro k
    rw [hF]
    have hk : k.1 ∉ S := by
      have hk' := k.2
      change k.1 ∉ S at hk'
      exact hk'
    have hc := inv_add_viscous_mul_le_graph_cutoff
      ν N (σ k.1) hν hN (hout k.1 hk)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (hf k.1)
  have htailSum : Summable fun k : ↥(↑S : Set G)ᶜ =>
      (N⁻¹ ^ 3 + ν * N⁻¹) * (σ k.1 ^ 2 * f k.1) :=
    (hgraph.subtype _).mul_left _
  have htail : (∑' k : ↥(↑S : Set G)ᶜ, F k.1) ≤
      (N⁻¹ ^ 3 + ν * N⁻¹) *
        (∑' k : ↥(↑S : Set G)ᶜ, σ k.1 ^ 2 * f k.1) := by
    calc
      (∑' k : ↥(↑S : Set G)ᶜ, F k.1) ≤
          ∑' k : ↥(↑S : Set G)ᶜ,
            (N⁻¹ ^ 3 + ν * N⁻¹) * (σ k.1 ^ 2 * f k.1) := by
        exact (hmixed.subtype _).tsum_le_tsum htailPoint htailSum
      _ = (N⁻¹ ^ 3 + ν * N⁻¹) *
          ∑' k : ↥(↑S : Set G)ᶜ, σ k.1 ^ 2 * f k.1 := tsum_mul_left
  rw [← hmixed.sum_add_tsum_compl (s := S)]
  have hlow' : (∑ k ∈ S, F k) ≤
      Real.sqrt (∑ k ∈ S, ((σ k)⁻¹ + ν * σ k) ^ 2) *
        Real.sqrt (∑' k, f k ^ 2) := by
    simpa only [hF] using hlow
  exact add_le_add hlow' htail

/-- Off-zero spectral energy in the physical amplitude coordinates. -/
def offZeroSpectralEnergy (u : WeightedLatticeBanach) : ℝ :=
  ∑' k : LatticeMode, amplitudeOffZero u k ^ 2

/-- Two-derivative off-zero graph mass.  The dynamic-tail construction
produces this from the actual heat-smoothed Duhamel representation. -/
def offZeroGraphMass (u : WeightedLatticeBanach) : ℝ :=
  ∑' k : LatticeMode, latticeModeSize k ^ 2 * amplitudeOffZero u k

/-- Only the high-frequency part of the graph mass outside a chosen finite
band. -/
def offZeroHighGraphTail (S : Finset LatticeMode)
    (u : WeightedLatticeBanach) : ℝ :=
  ∑' k : ↥(↑S : Set LatticeMode)ᶜ,
    latticeModeSize k.1 ^ 2 * amplitudeOffZero u k.1

def EnergyGraphControlled (S : Finset LatticeMode) (E H : ℝ)
    (u : WeightedLatticeBanach) : Prop :=
  Summable (fun k : LatticeMode => amplitudeOffZero u k ^ 2) ∧
  offZeroSpectralEnergy u ≤ E ^ 2 ∧
  Summable (fun k : LatticeMode =>
    latticeModeSize k ^ 2 * amplitudeOffZero u k) ∧
  offZeroHighGraphTail S u ≤ H

theorem amplitudeOffZero_nonneg (u : WeightedLatticeBanach) (k : LatticeMode) :
    0 ≤ amplitudeOffZero u k := by
  by_cases hk : k = 0
  · simp [amplitudeOffZero, hk]
  · simp [amplitudeOffZero, hk, weightedAmplitude_nonneg]

/-- The off-zero two-derivative amplitude mass is pointwise dominated by the
completed carrier's half-generator graph density. -/
theorem offZeroGraphDensity_le_halfGeneratorDensity
    (u : WeightedLatticeBanach) (k : LatticeMode) :
    latticeModeSize k ^ 2 * amplitudeOffZero u k ≤
      latticeModeSize k * ‖u k‖ := by
  by_cases hk : k = 0
  · subst k
    simp [amplitudeOffZero, latticeModeSize_zero]
  · rw [amplitudeOffZero]
    simp only [if_neg hk]
    have hnorm := norm_apply_eq_weight_mul_amplitude u k
    rw [hnorm]
    have hq := latticeModeSize_nonneg k
    have ha := weightedAmplitude_nonneg u k
    nlinarith

/-- A checked half-generator domain witness supplies summability of the graph
mass used by the energy/graph split. -/
theorem summable_offZeroGraphMass_of_halfGenerator
    (u : WeightedLatticeBanach)
    (hhalf : Summable fun k : LatticeMode =>
      latticeModeSize k * ‖u k‖) :
    Summable fun k : LatticeMode =>
      latticeModeSize k ^ 2 * amplitudeOffZero u k := by
  exact hhalf.of_nonneg_of_le
    (fun k => mul_nonneg (sq_nonneg _) (amplitudeOffZero_nonneg u k))
    (offZeroGraphDensity_le_halfGeneratorDensity u)

/-- Quantitative bridge from the dynamic half-generator moment to the graph
budget consumed below. -/
theorem offZeroGraphMass_le_halfGeneratorMoment
    (u : WeightedLatticeBanach)
    (hhalf : Summable fun k : LatticeMode =>
      latticeModeSize k * ‖u k‖) :
    offZeroGraphMass u ≤ heatHalfGeneratorMoment u := by
  unfold offZeroGraphMass heatHalfGeneratorMoment latticeModeSize
  exact (summable_offZeroGraphMass_of_halfGenerator u hhalf).tsum_le_tsum
    (offZeroGraphDensity_le_halfGeneratorDensity u) hhalf

/-- Energy plus a two-derivative graph budget controls the exact off-zero
mixed continuation quantity.  The constants are explicit and independent of
time. -/
theorem offZeroMixedCriticalQty_le_energy_graph_split
    (ν E H N : ℝ) (hν : 0 ≤ ν) (hE : 0 ≤ E) (hN : 0 < N)
    (S : Finset LatticeMode)
    (hout : ∀ k ∉ S, N ≤ latticeModeSize k)
    (u : WeightedLatticeBanach) (hcontrol : EnergyGraphControlled S E H u) :
    offZeroMixedCriticalQty ν u ≤
      Real.sqrt
          (∑ k ∈ S, ((latticeModeSize k)⁻¹ + ν * latticeModeSize k) ^ 2) * E +
        (N⁻¹ ^ 3 + ν * N⁻¹) * H := by
  let f := amplitudeOffZero u
  have hf : ∀ k, 0 ≤ f k := amplitudeOffZero_nonneg u
  have hm0 := InW_Xm1_offZero u (InW_inv_latticeModeSize u)
  have hp0 := InW_X1_offZero u (InW_latticeModeSize u)
  have hm : Summable fun k : LatticeMode =>
      (latticeModeSize k)⁻¹ * f k := by
    change Summable fun k : LatticeMode =>
      (latticeModeSize k)⁻¹ * |amplitudeOffZero u k| at hm0
    convert hm0 using 1
    funext k
    rw [abs_of_nonneg (amplitudeOffZero_nonneg u k)]
  have hp : Summable fun k : LatticeMode =>
      ν * (latticeModeSize k * f k) := by
    have hp' : Summable fun k : LatticeMode =>
        latticeModeSize k * f k := by
      change Summable fun k : LatticeMode =>
        latticeModeSize k * |amplitudeOffZero u k| at hp0
      convert hp0 using 1
      funext k
      rw [abs_of_nonneg (amplitudeOffZero_nonneg u k)]
    exact hp'.mul_left ν
  have hmixed : Summable fun k : LatticeMode =>
      (latticeModeSize k)⁻¹ * f k + ν * (latticeModeSize k * f k) := hm.add hp
  have hsplit := critical_sum_le_energy_graph_split S latticeModeSize f ν N
    hν hN latticeModeSize_nonneg hf hout hmixed hcontrol.1 hcontrol.2.2.1
  have henergy : Real.sqrt (∑' k : LatticeMode, f k ^ 2) ≤ E := by
    calc
      Real.sqrt (∑' k : LatticeMode, f k ^ 2) ≤ Real.sqrt (E ^ 2) :=
        Real.sqrt_le_sqrt hcontrol.2.1
      _ = E := Real.sqrt_sq hE
  have hA : 0 ≤ Real.sqrt
      (∑ k ∈ S, ((latticeModeSize k)⁻¹ + ν * latticeModeSize k) ^ 2) :=
    Real.sqrt_nonneg _
  have hcoef : 0 ≤ N⁻¹ ^ 3 + ν * N⁻¹ := by positivity
  unfold offZeroMixedCriticalQty normXm1 normX1 wNorm
  simp_rw [abs_of_nonneg (amplitudeOffZero_nonneg u _)]
  change (∑' k : LatticeMode, (latticeModeSize k)⁻¹ * f k) +
      ν * (∑' k : LatticeMode, latticeModeSize k * f k) ≤ _
  have heq :
      (∑' k : LatticeMode, (latticeModeSize k)⁻¹ * f k) +
          ν * (∑' k : LatticeMode, latticeModeSize k * f k) =
        ∑' k : LatticeMode,
          ((latticeModeSize k)⁻¹ * f k + ν * (latticeModeSize k * f k)) := by
    rw [← tsum_mul_left]
    exact (hm.tsum_add hp).symm
  rw [heq]
  exact hsplit.trans (add_le_add
    (mul_le_mul_of_nonneg_left henergy hA)
    (mul_le_mul_of_nonneg_left
      hcontrol.2.2.2 hcoef))

/-- Direct form consumed by the dynamic-tail theorem: native spectral energy
and a half-generator terminal budget imply the off-zero mixed bound. -/
theorem offZeroMixedCriticalQty_le_energy_halfGenerator_split
    (ν E H N : ℝ) (hν : 0 ≤ ν) (hE : 0 ≤ E) (hN : 0 < N)
    (S : Finset LatticeMode)
    (hout : ∀ k ∉ S, N ≤ latticeModeSize k)
    (u : WeightedLatticeBanach)
    (henergySum : Summable fun k : LatticeMode => amplitudeOffZero u k ^ 2)
    (henergy : offZeroSpectralEnergy u ≤ E ^ 2)
    (hhalf : Summable fun k : LatticeMode => latticeModeSize k * ‖u k‖)
    (hhalfBound : heatHalfGeneratorMoment u ≤ H) :
    offZeroMixedCriticalQty ν u ≤
      Real.sqrt
          (∑ k ∈ S, ((latticeModeSize k)⁻¹ + ν * latticeModeSize k) ^ 2) * E +
        (N⁻¹ ^ 3 + ν * N⁻¹) * H := by
  apply offZeroMixedCriticalQty_le_energy_graph_split
    ν E H N hν hE hN S hout u
  have hgraph := summable_offZeroGraphMass_of_halfGenerator u hhalf
  refine ⟨henergySum, henergy, hgraph, ?_⟩
  have hsplit := hgraph.sum_add_tsum_compl (s := S)
  have hfinite : 0 ≤ ∑ k ∈ S,
      latticeModeSize k ^ 2 * amplitudeOffZero u k :=
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (sq_nonneg _) (amplitudeOffZero_nonneg u k)
  have htailTotal : offZeroHighGraphTail S u ≤ offZeroGraphMass u := by
    unfold offZeroHighGraphTail offZeroGraphMass
    linarith
  exact htailTotal.trans
    ((offZeroGraphMass_le_halfGeneratorMoment u hhalf).trans hhalfBound)

/-- Uniform native energy and half-generator control on every reachable finite
critical mild chart.  This separates the conserved quadratic input from the
parabolically generated high-frequency input. -/
def CriticalMildUniformEnergyHalfGeneratorControl
    (ν : ℝ) (hν : 0 < ν) (a : WeightedLatticeBanach) (E H : ℝ) : Prop :=
  ∀ {T R : ℝ} (hT : 0 ≤ T) (u : CriticalMildPathBall T R),
    (∀ τ : Icc (0 : ℝ) T,
      u.1 τ = criticalMildImage ν hν a
        (criticalMildPathExtension T hT u.1)
        (criticalMildPathBallExtension_divergenceFree hT u) τ.1 τ.2.1) →
    let endpoint := u.1 ⟨T, ⟨hT, le_rfl⟩⟩
    Summable (fun k : LatticeMode => amplitudeOffZero endpoint k ^ 2) ∧
    offZeroSpectralEnergy endpoint ≤ E ^ 2 ∧
    Summable (fun k : LatticeMode => latticeModeSize k * ‖endpoint k‖) ∧
    heatHalfGeneratorMoment endpoint ≤ H

/-- A horizon-independent energy/half-generator estimate closes the remaining
off-zero terminal consumer with an explicit constant. -/
theorem criticalMildOffZeroTerminalBound_of_uniformEnergyHalfGeneratorControl
    (ν E H N : ℝ) (hν : 0 < ν) (hE : 0 ≤ E) (hN : 0 < N)
    (a : WeightedLatticeBanach) (S : Finset LatticeMode)
    (hout : ∀ k ∉ S, N ≤ latticeModeSize k)
    (hcontrol : CriticalMildUniformEnergyHalfGeneratorControl ν hν a E H) :
    CriticalMildOffZeroTerminalBound ν hν a
      (Real.sqrt
          (∑ k ∈ S, ((latticeModeSize k)⁻¹ + ν * latticeModeSize k) ^ 2) * E +
        (N⁻¹ ^ 3 + ν * N⁻¹) * H) := by
  intro T R hT u hmild
  have hc := hcontrol hT u hmild
  exact offZeroMixedCriticalQty_le_energy_halfGenerator_split
    ν E H N hν.le hE hN S hout _ hc.1 hc.2.1 hc.2.2.1 hc.2.2.2

/-! ## Actual nonlinear high-frequency flux -/

/-- A high output mode in an exact triad forces at least one input above half
the output cutoff.  This is the low--low exclusion behind the high-tail flux
estimate. -/
theorem high_output_forces_high_input
    (N : ℝ) (i j k : LatticeMode) (hijk : i + j = k)
    (hk : N ≤ latticeModeSize k) :
    N / 2 ≤ latticeModeSize i ∨ N / 2 ≤ latticeModeSize j := by
  have hfreq : latticeModeSize k ≤ latticeModeSize i + latticeModeSize j := by
    unfold latticeModeSize
    rw [← hijk, complexFrequency_latticeFrequency_add]
    exact norm_add_le _ _
  by_contra h
  push Not at h
  linarith

/-- Unweighted completed-carrier mass above a frequency threshold. -/
def carrierHighTail (N : ℝ) (u : WeightedLatticeBanach) : ℝ :=
  ∑' k : LatticeMode, if N ≤ latticeModeSize k then ‖u k‖ else 0

theorem summable_carrierHighTail (N : ℝ) (u : WeightedLatticeBanach) :
    Summable fun k : LatticeMode =>
      if N ≤ latticeModeSize k then ‖u k‖ else 0 := by
  have hu : Summable fun k : LatticeMode => ‖u k‖ := by simpa using u.2.summable
  exact hu.of_nonneg_of_le
    (fun k => by split_ifs <;> positivity)
    (fun k => by split_ifs <;> simp)

/-- Pair mass whose output frequency lies above `N`. -/
def highOutputPairMass (N : ℝ) (u v : WeightedLatticeBanach)
    (ij : LatticeMode × LatticeMode) : ℝ :=
  if N ≤ latticeModeSize (ij.1 + ij.2) then ‖u ij.1‖ * ‖v ij.2‖ else 0

theorem summable_highOutputPairMass
    (N : ℝ) (u v : WeightedLatticeBanach) :
    Summable (highOutputPairMass N u v) := by
  have hu : Summable fun i : LatticeMode => ‖u i‖ := by simpa using u.2.summable
  have hv : Summable fun j : LatticeMode => ‖v j‖ := by simpa using v.2.summable
  have hp : Summable fun ij : LatticeMode × LatticeMode =>
      ‖u ij.1‖ * ‖v ij.2‖ :=
    hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact hp.of_nonneg_of_le
    (fun ij => by unfold highOutputPairMass; split_ifs <;> positivity)
    (fun ij => by
      unfold highOutputPairMass
      split_ifs
      · exact le_rfl
      · positivity)

/-- **High-output nonlinear flux requires a high input.**  The total pair mass
feeding frequencies `|k| ≥ N` is bounded by the two possible high-input
allocations.  This excludes low--low interactions exactly and retains only a
high tail times a total carrier norm. -/
theorem tsum_highOutputPairMass_le_highInputTails
    (N : ℝ) (u v : WeightedLatticeBanach) :
    (∑' ij : LatticeMode × LatticeMode, highOutputPairMass N u v ij) ≤
      carrierHighTail (N / 2) u * ‖v‖ +
        ‖u‖ * carrierHighTail (N / 2) v := by
  let au : LatticeMode → ℝ := fun i =>
    if N / 2 ≤ latticeModeSize i then ‖u i‖ else 0
  let av : LatticeMode → ℝ := fun j =>
    if N / 2 ≤ latticeModeSize j then ‖v j‖ else 0
  let bu : LatticeMode → ℝ := fun i => ‖u i‖
  let bv : LatticeMode → ℝ := fun j => ‖v j‖
  have hau : Summable au := summable_carrierHighTail (N / 2) u
  have hav : Summable av := summable_carrierHighTail (N / 2) v
  have hbu : Summable bu := by dsimp [bu]; simpa using u.2.summable
  have hbv : Summable bv := by dsimp [bv]; simpa using v.2.summable
  have hleft : Summable fun ij : LatticeMode × LatticeMode =>
      au ij.1 * bv ij.2 :=
    hau.mul_of_nonneg hbv
      (fun i => by dsimp [au]; split_ifs <;> positivity)
      (fun _ => norm_nonneg _)
  have hright : Summable fun ij : LatticeMode × LatticeMode =>
      bu ij.1 * av ij.2 :=
    hbu.mul_of_nonneg hav (fun _ => norm_nonneg _)
      (fun j => by dsimp [av]; split_ifs <;> positivity)
  have hpoint : ∀ ij : LatticeMode × LatticeMode,
      highOutputPairMass N u v ij ≤
        au ij.1 * bv ij.2 + bu ij.1 * av ij.2 := by
    intro ij
    unfold highOutputPairMass
    split_ifs with hout
    · rcases high_output_forces_high_input N ij.1 ij.2 (ij.1 + ij.2) rfl hout with hi | hj
      · dsimp [au, av, bu, bv]
        rw [if_pos hi]
        exact le_add_of_nonneg_right (by positivity)
      · dsimp [au, av, bu, bv]
        rw [if_pos hj]
        exact le_add_of_nonneg_left (by positivity)
    · dsimp [au, av, bu, bv]
      positivity
  calc
    (∑' ij : LatticeMode × LatticeMode, highOutputPairMass N u v ij) ≤
        ∑' ij : LatticeMode × LatticeMode,
          (au ij.1 * bv ij.2 + bu ij.1 * av ij.2) :=
      (summable_highOutputPairMass N u v).tsum_le_tsum hpoint (hleft.add hright)
    _ = (∑' i, au i) * (∑' j, bv j) +
        (∑' i, bu i) * (∑' j, av j) := by
      rw [Summable.tsum_add hleft hright,
        ← hau.tsum_mul_tsum hbv hleft,
        ← hbu.tsum_mul_tsum hav hright]
    _ = carrierHighTail (N / 2) u * ‖v‖ +
        ‖u‖ * carrierHighTail (N / 2) v := by
      dsimp [carrierHighTail, au, av, bu, bv]
      have hnu : ∑' k : LatticeMode, ‖u k‖ = ‖u‖ := by
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
        simp [ENNReal.toReal_one]
      have hnv : ∑' k : LatticeMode, ‖v k‖ = ‖v‖ := by
        rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ENNReal).toReal)]
        simp [ENNReal.toReal_one]
      rw [← hnu, ← hnv,
        mul_comm (∑' k : LatticeMode, ‖u k‖)
          (∑' k : LatticeMode, if (N / 2 : ℝ) ≤ latticeModeSize k then ‖v k‖ else 0)]

/-! ## Raw-complex mean drift mechanism -/

/-- The first axial lattice mode. -/
def rawDriftMode : LatticeMode := (1, (0, 0))

/-- A real raw-complex zero-mode coefficient parallel to the drift mode. -/
def rawMeanCoefficient (c : ℝ) : ComplexSpace :=
  Pi.single (0 : Fin 3) (c : ℂ)

/-- A transverse coefficient carried by the first axial mode. -/
def rawTransverseCoefficient (z : ℂ) : ComplexSpace :=
  Pi.single (1 : Fin 3) z

theorem rawTransverseCoefficient_mul (a z : ℂ) :
    rawTransverseCoefficient (a * z) =
      a • rawTransverseCoefficient z := by
  ext i
  fin_cases i <;> simp [rawTransverseCoefficient, Pi.smul_apply]

theorem complexEuclideanNorm_rawTransverseCoefficient (z : ℂ) :
    complexEuclideanNorm (rawTransverseCoefficient z) = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simp [rawTransverseCoefficient, complexEuclideanPoint,
    Fin.sum_univ_succ]

theorem latticeFrequency_rawDriftMode :
    latticeFrequency rawDriftMode = ![1, 0, 0] := by
  ext i
  fin_cases i <;> simp [rawDriftMode, latticeFrequency]

theorem latticeModeSize_rawDriftMode : latticeModeSize rawDriftMode = 1 := by
  unfold latticeModeSize
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [complexFrequency_norm_sq, latticeFrequency_rawDriftMode]
  simp [dotProduct, Fin.sum_univ_succ]

/-- The raw transport couples a real zero mode to the transverse mode with a
real positive scalar.  This is the sign that becomes phase rotation only
after the physical `-i` Fourier normalization. -/
theorem spectralTransport_rawMean_transverse
    (c : ℝ) (z : ℂ) :
    spectralTransport (latticeFrequency rawDriftMode)
      (rawMeanCoefficient c) (rawTransverseCoefficient z) =
        (c : ℂ) • rawTransverseCoefficient z := by
  ext i
  fin_cases i <;>
    simp [spectralTransport, rawMeanCoefficient, rawTransverseCoefficient,
      latticeFrequency_rawDriftMode, complexFrequency, complexEuclideanPoint,
      complexOfReal, complexOfParts, inner]

/-- The transverse mode has no self-advection, so it creates no second
harmonic in this two-mode ansatz. -/
theorem spectralTransport_rawTransverse_self (z w : ℂ) :
    spectralTransport (latticeFrequency rawDriftMode)
      (rawTransverseCoefficient z) (rawTransverseCoefficient w) = 0 := by
  ext i
  fin_cases i <;>
    simp [spectralTransport, rawTransverseCoefficient,
      latticeFrequency_rawDriftMode, complexFrequency, complexEuclideanPoint,
      complexOfReal, complexOfParts, inner]

/-- A zero transport frequency contributes no reverse interaction. -/
theorem spectralTransport_zero_frequency
    (v w : ComplexSpace) :
    spectralTransport (latticeFrequency (0 : LatticeMode)) v w = 0 := by
  have hz : complexFrequency (latticeFrequency (0 : LatticeMode)) = 0 := by
    ext i
    fin_cases i <;>
      simp [latticeFrequency, complexFrequency, complexOfReal, complexOfParts]
  unfold spectralTransport
  rw [hz, inner_zero_left, zero_smul]

/-- Exact scalar Volterra identity for the growing raw mean-drift mode. -/
theorem raw_drift_exponential_mild_identity
    (μ c t : ℝ) :
    Real.exp ((c - μ) * t) = Real.exp (-μ * t) +
      ∫ s in (0 : ℝ)..t,
        Real.exp (-μ * (t - s)) * c * Real.exp ((c - μ) * s) := by
  let F : ℝ → ℝ := fun s => Real.exp (-μ * t + s * c)
  have hF : ∀ s, F s = Real.exp (-μ * (t - s)) * Real.exp ((c - μ) * s) := by
    intro s
    dsimp [F]
    rw [← Real.exp_add]
    congr 1
    ring
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt F (c * F s) s := by
    intro s _
    have hg := ((hasDerivAt_const s (-μ * t)).add
      ((hasDerivAt_id s).mul_const c)).exp
    simpa only [F, Pi.add_apply, id_eq, zero_add, one_mul, mul_one, mul_comm] using hg
  have hint : IntervalIntegrable (fun s => c * F s) volume 0 t := by
    apply Continuous.intervalIntegrable
    dsimp [F]
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [show (fun s => Real.exp (-μ * (t - s)) * c *
      Real.exp ((c - μ) * s)) = fun s => c * F s by
    funext s
    rw [hF]
    ring,
    hFTC]
  have hFt : F t = Real.exp ((c - μ) * t) := by
    dsimp [F]
    congr 1
    ring
  have hF0 : F 0 = Real.exp (-μ * t) := by
    dsimp [F]
    congr 1
    ring
  rw [hFt, hF0]
  ring

theorem rawDriftMode_ne_zero : rawDriftMode ≠ 0 := by
  intro h
  have hfirst := congrArg Prod.fst h
  norm_num [rawDriftMode] at hfirst

/-- The exact weighted two-mode carrier behind the raw mean-drift mechanism.
The nonzero coordinate is stored after multiplication by its native lattice
weight, so decoding returns `rawTransverseCoefficient z` exactly. -/
def rawMeanDriftCarrier (c : ℝ) (z : ℂ) : WeightedLatticeBanach :=
  lp.single 1 (0 : LatticeMode)
      (WithLp.toLp 2 (rawMeanCoefficient c)) +
    lp.single 1 rawDriftMode
      ((latticeModeWeight rawDriftMode : ℂ) •
        WithLp.toLp 2 (rawTransverseCoefficient z))

theorem rawMeanDriftCarrier_apply_zero (c : ℝ) (z : ℂ) :
    rawMeanDriftCarrier c z 0 = WithLp.toLp 2 (rawMeanCoefficient c) := by
  set a : ComplexE3 := WithLp.toLp 2 (rawMeanCoefficient c)
  set b : ComplexE3 := WithLp.toLp 2 (rawTransverseCoefficient z)
  set w : ℂ := (latticeModeWeight rawDriftMode : ℂ)
  set E : LatticeMode → Type := fun _ : LatticeMode => ComplexE3
  calc rawMeanDriftCarrier c z 0
      = (lp.single (E := E) 1 (0 : LatticeMode) a) 0 +
          (lp.single (E := E) 1 rawDriftMode (w • b)) 0 :=
        ((congrArg (fun h : LatticeMode → ComplexE3 => h 0)
          (lp.coeFn_add (E := E)
            (f := lp.single (E := E) 1 (0 : LatticeMode) a)
            (g := lp.single (E := E) 1 rawDriftMode (w • b))))).trans
          (Pi.add_apply _ _ _)
    _ = a + (lp.single (E := E) 1 rawDriftMode (w • b)) 0 :=
        congrArg (fun x : ComplexE3 => x + (lp.single (E := E) 1 rawDriftMode (w • b)) 0)
          (lp.single_apply_self (E := E) 1 (0 : LatticeMode) a)
    _ = a + 0 :=
        congrArg (fun x : ComplexE3 => a + x)
          (lp.single_apply_ne (E := E) 1 rawDriftMode (w • b)
            (Ne.symm rawDriftMode_ne_zero))
    _ = a := add_zero a

theorem rawMeanDriftCarrier_apply_mode (c : ℝ) (z : ℂ) :
    rawMeanDriftCarrier c z rawDriftMode =
      (latticeModeWeight rawDriftMode : ℂ) •
        WithLp.toLp 2 (rawTransverseCoefficient z) := by
  set a : ComplexE3 := WithLp.toLp 2 (rawMeanCoefficient c)
  set b : ComplexE3 := WithLp.toLp 2 (rawTransverseCoefficient z)
  set w : ℂ := (latticeModeWeight rawDriftMode : ℂ)
  set E : LatticeMode → Type := fun _ : LatticeMode => ComplexE3
  calc rawMeanDriftCarrier c z rawDriftMode
      = (lp.single (E := E) 1 (0 : LatticeMode) a) rawDriftMode +
          (lp.single (E := E) 1 rawDriftMode (w • b)) rawDriftMode :=
        ((congrArg (fun h : LatticeMode → ComplexE3 => h rawDriftMode)
          (lp.coeFn_add (E := E)
            (f := lp.single (E := E) 1 (0 : LatticeMode) a)
            (g := lp.single (E := E) 1 rawDriftMode (w • b))))).trans
          (Pi.add_apply _ _ _)
    _ = 0 + (lp.single (E := E) 1 rawDriftMode (w • b)) rawDriftMode :=
        congrArg (fun x : ComplexE3 => x +
            (lp.single (E := E) 1 rawDriftMode (w • b)) rawDriftMode)
          (lp.single_apply_ne (E := E) 1 (0 : LatticeMode) a rawDriftMode_ne_zero)
    _ = 0 + w • b :=
        congrArg (fun x : ComplexE3 => 0 + x)
          (lp.single_apply_self (E := E) 1 rawDriftMode (w • b))
    _ = w • b := zero_add _

theorem rawMeanDriftCarrier_apply_other (c : ℝ) (z : ℂ) (m : LatticeMode)
    (hm0 : m ≠ 0) (hmk : m ≠ rawDriftMode) :
    rawMeanDriftCarrier c z m = 0 := by
  set a : ComplexE3 := WithLp.toLp 2 (rawMeanCoefficient c)
  set b : ComplexE3 := WithLp.toLp 2 (rawTransverseCoefficient z)
  set w : ℂ := (latticeModeWeight rawDriftMode : ℂ)
  set E : LatticeMode → Type := fun _ : LatticeMode => ComplexE3
  calc rawMeanDriftCarrier c z m
      = (lp.single (E := E) 1 (0 : LatticeMode) a) m +
          (lp.single (E := E) 1 rawDriftMode (w • b)) m :=
        ((congrArg (fun h : LatticeMode → ComplexE3 => h m)
          (lp.coeFn_add (E := E)
            (f := lp.single (E := E) 1 (0 : LatticeMode) a)
            (g := lp.single (E := E) 1 rawDriftMode (w • b))))).trans
          (Pi.add_apply _ _ _)
    _ = 0 + (lp.single (E := E) 1 rawDriftMode (w • b)) m :=
        congrArg (fun x : ComplexE3 => x + (lp.single (E := E) 1 rawDriftMode (w • b)) m)
          (lp.single_apply_ne (E := E) 1 (0 : LatticeMode) a hm0)
    _ = 0 + 0 :=
        congrArg (fun x : ComplexE3 => 0 + x)
          (lp.single_apply_ne (E := E) 1 rawDriftMode (w • b) hmk)
    _ = 0 := add_zero 0

theorem weightedLatticeCoefficient_rawMeanDriftCarrier_zero
    (c : ℝ) (z : ℂ) :
    weightedLatticeCoefficient (rawMeanDriftCarrier c z) 0 =
      rawMeanCoefficient c := by
  unfold weightedLatticeCoefficient
  rw [show rawMeanDriftCarrier c z 0 =
      WithLp.toLp 2 (rawMeanCoefficient c)
        from rawMeanDriftCarrier_apply_zero c z]
  have hfreq : complexFrequency (latticeFrequency (0 : LatticeMode)) = 0 := by
    ext i
    fin_cases i <;>
      simp [latticeFrequency, complexFrequency, complexOfReal, complexOfParts]
  have hw : latticeModeWeight (0 : LatticeMode) = 1 := by
    unfold latticeModeWeight
    rw [hfreq, norm_zero]
    ring
  rw [hw]
  simp

theorem weightedLatticeCoefficient_rawMeanDriftCarrier_mode
    (c : ℝ) (z : ℂ) :
    weightedLatticeCoefficient (rawMeanDriftCarrier c z) rawDriftMode =
      rawTransverseCoefficient z := by
  unfold weightedLatticeCoefficient
  rw [show rawMeanDriftCarrier c z rawDriftMode =
      (latticeModeWeight rawDriftMode : ℂ) •
        WithLp.toLp 2 (rawTransverseCoefficient z)
        from rawMeanDriftCarrier_apply_mode c z]
  rw [WithLp.ofLp_smul, WithLp.ofLp_smul, WithLp.ofLp_toLp]
  have hw : latticeModeWeight rawDriftMode ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one
      (one_le_latticeModeWeight rawDriftMode))
  ext i
  fin_cases i <;>
    simp [Pi.smul_apply, Complex.real_smul, rawTransverseCoefficient, hw]

theorem weightedLatticeCoefficient_rawMeanDriftCarrier_other
    (c : ℝ) (z : ℂ) (m : LatticeMode)
    (hm0 : m ≠ 0) (hmk : m ≠ rawDriftMode) :
    weightedLatticeCoefficient (rawMeanDriftCarrier c z) m = 0 := by
  unfold weightedLatticeCoefficient
  rw [show rawMeanDriftCarrier c z m = 0
        from rawMeanDriftCarrier_apply_other c z m hm0 hmk]
  simp

theorem rawMeanDriftCarrier_divergenceFree (c : ℝ) (z : ℂ) :
    LatticeDivergenceFree (rawMeanDriftCarrier c z) := by
  intro m
  by_cases hm0 : m = 0
  · subst m
    rw [weightedLatticeCoefficient_rawMeanDriftCarrier_zero]
    have hz : complexFrequency (latticeFrequency (0 : LatticeMode)) = 0 := by
      ext i
      fin_cases i <;>
        simp [latticeFrequency, complexFrequency, complexOfReal, complexOfParts]
    rw [hz, inner_zero_left]
  · by_cases hmk : m = rawDriftMode
    · subst m
      rw [weightedLatticeCoefficient_rawMeanDriftCarrier_mode,
        latticeFrequency_rawDriftMode]
      simp [rawTransverseCoefficient, complexFrequency, complexEuclideanPoint,
        complexOfReal, complexOfParts, inner]
    · rw [weightedLatticeCoefficient_rawMeanDriftCarrier_other c z m hm0 hmk]
      have hz : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
        ext i
        rfl
      rw [hz, inner_zero_right]

/-- At the active mode, the literal countable transport convolution of the
two-mode carrier consists of exactly the mean--mode interaction. -/
theorem weightedLatticeSpectralConvolution_rawMeanDriftCarrier_mode
    (c : ℝ) (z : ℂ) :
    weightedLatticeSpectralConvolution rawDriftMode
        (rawMeanDriftCarrier c z) (rawMeanDriftCarrier c z) =
      complexEuclideanPoint ((c : ℂ) • rawTransverseCoefficient z) := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [tsum_eq_single ((0 : LatticeMode), rawDriftMode)]
  · unfold latticeSpectralTerm
    rw [if_pos (zero_add rawDriftMode),
      weightedLatticeCoefficient_rawMeanDriftCarrier_zero,
      weightedLatticeCoefficient_rawMeanDriftCarrier_mode,
      spectralTransport_rawMean_transverse]
  · intro ij hij
    unfold latticeSpectralTerm
    by_cases hsum : ij.1 + ij.2 = rawDriftMode
    · rw [if_pos hsum]
      by_cases hi0 : ij.1 = 0
      · have hjk : ij.2 = rawDriftMode := by simpa [hi0] using hsum
        exfalso
        apply hij
        exact Prod.ext hi0 hjk
      · by_cases hik : ij.1 = rawDriftMode
        · have hj0 : ij.2 = 0 := by simpa [hik] using hsum
          rw [hik, hj0,
            weightedLatticeCoefficient_rawMeanDriftCarrier_mode,
            weightedLatticeCoefficient_rawMeanDriftCarrier_zero,
            spectralTransport_zero_frequency]
          rfl
        · rw [weightedLatticeCoefficient_rawMeanDriftCarrier_other
            c z ij.1 hi0 hik]
          unfold spectralTransport
          have hz : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
            ext i
            rfl
          rw [hz, inner_zero_right, zero_smul]
          rfl
    · rw [if_neg hsum]

/-- The active mean--mode interaction is the only nonzero output of the
literal countable convolution.  This identifies every output mode, not only
the growing one. -/
theorem weightedLatticeSpectralConvolution_rawMeanDriftCarrier
    (q : LatticeMode) (c : ℝ) (z : ℂ) :
    weightedLatticeSpectralConvolution q
        (rawMeanDriftCarrier c z) (rawMeanDriftCarrier c z) =
      if rawDriftMode = q then
        complexEuclideanPoint ((c : ℂ) • rawTransverseCoefficient z)
      else 0 := by
  unfold weightedLatticeSpectralConvolution latticeSpectralConvolution
  rw [tsum_eq_single ((0 : LatticeMode), rawDriftMode)]
  · unfold latticeSpectralTerm
    simp only [zero_add]
    by_cases hq : rawDriftMode = q
    · rw [if_pos hq, if_pos hq,
        weightedLatticeCoefficient_rawMeanDriftCarrier_zero,
        weightedLatticeCoefficient_rawMeanDriftCarrier_mode,
        spectralTransport_rawMean_transverse]
    · rw [if_neg hq, if_neg hq]
  · intro ij hij
    unfold latticeSpectralTerm
    by_cases hsum : ij.1 + ij.2 = q
    · rw [if_pos hsum]
      by_cases hi0 : ij.1 = 0
      · by_cases hj0 : ij.2 = 0
        · rw [hi0, hj0,
            weightedLatticeCoefficient_rawMeanDriftCarrier_zero,
            spectralTransport_zero_frequency]
          rfl
        · by_cases hjk : ij.2 = rawDriftMode
          · exfalso
            apply hij
            exact Prod.ext hi0 hjk
          · rw [weightedLatticeCoefficient_rawMeanDriftCarrier_other
              c z ij.2 hj0 hjk]
            unfold spectralTransport
            rw [smul_zero]
            ext i
            rfl
      · by_cases hik : ij.1 = rawDriftMode
        · by_cases hj0 : ij.2 = 0
          · rw [hik, hj0,
              weightedLatticeCoefficient_rawMeanDriftCarrier_mode,
              weightedLatticeCoefficient_rawMeanDriftCarrier_zero,
              spectralTransport_zero_frequency]
            rfl
          · by_cases hjk : ij.2 = rawDriftMode
            · rw [hik, hjk,
                weightedLatticeCoefficient_rawMeanDriftCarrier_mode,
                spectralTransport_rawTransverse_self]
              rfl
            · rw [weightedLatticeCoefficient_rawMeanDriftCarrier_other
                c z ij.2 hj0 hjk]
              unfold spectralTransport
              rw [smul_zero]
              ext i
              rfl
        · rw [weightedLatticeCoefficient_rawMeanDriftCarrier_other
              c z ij.1 hi0 hik]
          unfold spectralTransport
          have hz : complexEuclideanPoint (0 : ComplexSpace) = 0 := by
            ext i
            rfl
          rw [hz, inner_zero_right, zero_smul]
          rfl
    · rw [if_neg hsum]

theorem spectralOutputCoefficient_rawMeanDriftCarrier
    (q : LatticeMode) (c : ℝ) (z : ℂ) :
    spectralOutputCoefficient q
        (rawMeanDriftCarrier c z) (rawMeanDriftCarrier c z) =
      if rawDriftMode = q then
        (c : ℂ) • rawTransverseCoefficient z
      else 0 := by
  unfold spectralOutputCoefficient
  rw [weightedLatticeSpectralConvolution_rawMeanDriftCarrier]
  by_cases hq : rawDriftMode = q
  · rw [if_pos hq, if_pos hq]
    exact WithLp.ofLp_toLp _ _
  · rw [if_neg hq, if_neg hq, WithLp.ofLp_zero]

theorem complexLeray_rawTransverseCoefficient (z : ℂ) :
    complexLeray (latticeFrequency rawDriftMode)
        (rawTransverseCoefficient z) = rawTransverseCoefficient z := by
  apply complexLeray_eq_self_of_hermitian_transverse
  rw [latticeFrequency_rawDriftMode]
  simp [rawTransverseCoefficient, complexFrequency, complexEuclideanPoint,
    complexOfReal, complexOfParts, inner]

theorem complexHeatDecay_rawDriftMode (ν τ : ℝ) :
    complexHeatDecay ν τ (latticeFrequency rawDriftMode) =
      Real.exp (-ν * τ) := by
  unfold complexHeatDecay heatDecay
  rw [latticeFrequency_rawDriftMode]
  congr 1
  rw [officialPoint_norm_sq_eq_dotProduct]
  simp [dotProduct, Fin.sum_univ_succ]

theorem complexHeatDecay_zeroMode (ν τ : ℝ) :
    complexHeatDecay ν τ (latticeFrequency (0 : LatticeMode)) = 1 := by
  unfold complexHeatDecay heatDecay
  have hz : latticeFrequency (0 : LatticeMode) = 0 := by
    ext i
    fin_cases i <;> simp [latticeFrequency]
  rw [hz]
  simp [Navier.Analysis.OfficialABEncoding.officialEuclideanPoint]

theorem heatRegularizedSpectralOutputFiber_rawMeanDriftCarrier_mode
    (ν τ c : ℝ) (z : ℂ) :
    heatRegularizedSpectralOutputFiber ν τ rawDriftMode
        (rawMeanDriftCarrier c z) (rawMeanDriftCarrier c z) =
      latticeModeWeight rawDriftMode • complexEuclideanPoint
        (((Real.exp (-ν * τ) * c : ℝ) : ℂ) • rawTransverseCoefficient z) := by
  unfold heatRegularizedSpectralOutputFiber
  rw [spectralOutputCoefficient_rawMeanDriftCarrier,
    if_pos rfl, complexFrequencyHeatLeray_apply,
    map_smul, complexLeray_rawTransverseCoefficient,
    complexHeatDecay_rawDriftMode]
  congr 1
  rw [complexEuclideanPoint_smul, complexEuclideanPoint_smul, smul_smul]
  norm_num

/-- The completed nonlinear heat output of the two-mode carrier is again a
single transverse mode, with the exact heat-decayed mean-drift amplitude. -/
theorem heatRegularizedSpectralOutput_rawMeanDriftCarrier
    (ν τ c : ℝ) (hν : 0 < ν) (hτ : 0 < τ) (z : ℂ) :
    heatRegularizedSpectralOutput ν τ hν hτ
        (rawMeanDriftCarrier c z) (rawMeanDriftCarrier c z)
        (rawMeanDriftCarrier_divergenceFree c z) =
      rawMeanDriftCarrier 0 (((Real.exp (-ν * τ) * c : ℝ) : ℂ) * z) := by
  apply Subtype.ext
  funext q
  rw [heatRegularizedSpectralOutput_apply]
  by_cases hq : q = rawDriftMode
  · subst q
    rw [heatRegularizedSpectralOutputFiber_rawMeanDriftCarrier_mode]
    rw [show rawMeanDriftCarrier 0
        (((Real.exp (-ν * τ) * c : ℝ) : ℂ) * z) rawDriftMode =
        (latticeModeWeight rawDriftMode : ℂ) • WithLp.toLp 2
          (rawTransverseCoefficient
            (((Real.exp (-ν * τ) * c : ℝ) : ℂ) * z))
      from rawMeanDriftCarrier_apply_mode
        0 (((Real.exp (-ν * τ) * c : ℝ) : ℂ) * z)]
    ext i
    fin_cases i <;>
      simp [complexEuclideanPoint, rawTransverseCoefficient, Complex.real_smul]
  · unfold heatRegularizedSpectralOutputFiber
    rw [spectralOutputCoefficient_rawMeanDriftCarrier, if_neg (Ne.symm hq)]
    have hzero : complexFrequencyHeatLeray ν τ (latticeFrequency q)
        (0 : ComplexSpace) = 0 := by
      rw [complexFrequencyHeatLeray_apply]
      simp
    rw [hzero, show complexEuclideanPoint (0 : ComplexSpace) = 0 by
      ext i
      rfl, smul_zero]
    by_cases hq0 : q = 0
    · subst q
      rw [show rawMeanDriftCarrier 0
          (((Real.exp (-ν * τ) * c : ℝ) : ℂ) * z) 0 =
          WithLp.toLp 2 (rawMeanCoefficient 0)
          from rawMeanDriftCarrier_apply_zero
            0 (((Real.exp (-ν * τ) * c : ℝ) : ℂ) * z)]
      have hm : rawMeanCoefficient 0 = 0 := by
        ext i
        fin_cases i <;> simp [rawMeanCoefficient]
      rw [hm]
      rfl
    · rw [show rawMeanDriftCarrier 0
          (((Real.exp (-ν * τ) * c : ℝ) : ℂ) * z) q = 0
          from rawMeanDriftCarrier_apply_other
            0 (((Real.exp (-ν * τ) * c : ℝ) : ℂ) * z) q hq0 hq]

theorem weightedHeatFlow_rawMeanDriftCarrier
    (μ t c : ℝ) (hμ : 0 ≤ μ) (ht : 0 ≤ t) (z : ℂ) :
    weightedHeatFlow μ t hμ ht (rawMeanDriftCarrier c z) =
      rawMeanDriftCarrier c ((Real.exp (-μ * t) : ℂ) * z) := by
  apply Subtype.ext
  funext q
  rw [weightedHeatFlow_apply_of_divergenceFree μ t hμ ht
    (rawMeanDriftCarrier c z) (rawMeanDriftCarrier_divergenceFree c z) q]
  by_cases hq0 : q = 0
  · subst q
    rw [rawMeanDriftCarrier_apply_zero,
      rawMeanDriftCarrier_apply_zero, complexHeatDecay_zeroMode]
    simp
  · by_cases hqk : q = rawDriftMode
    · subst q
      rw [rawMeanDriftCarrier_apply_mode, rawMeanDriftCarrier_apply_mode,
        complexHeatDecay_rawDriftMode, rawTransverseCoefficient_mul,
        WithLp.toLp_smul]
      rw [smul_smul, smul_smul]
      rw [mul_comm]
    · rw [rawMeanDriftCarrier_apply_other c z q hq0 hqk,
        rawMeanDriftCarrier_apply_other c
          ((Real.exp (-μ * t) : ℂ) * z) q hq0 hqk]
      simp

/-- The explicit smooth raw trajectory suggested by the modal equation. -/
def rawMeanDriftPath (μ c : ℝ) (z : ℂ) : ℝ → WeightedLatticeBanach :=
  fun t => rawMeanDriftCarrier c ((Real.exp ((c - μ) * t) : ℂ) * z)

theorem continuous_rawMeanDriftPath (μ c : ℝ) (z : ℂ) :
    Continuous (rawMeanDriftPath μ c z) := by
  unfold rawMeanDriftPath rawMeanDriftCarrier
  apply Continuous.add continuous_const
  let f : ℝ → ComplexE3 := fun t =>
    (latticeModeWeight rawDriftMode : ℂ) •
      WithLp.toLp 2
        (rawTransverseCoefficient ((Real.exp ((c - μ) * t) : ℂ) * z))
  have hf : Continuous f := by
    dsimp [f]
    simp_rw [rawTransverseCoefficient_mul, WithLp.toLp_smul]
    fun_prop
  have heq : (fun t => lp.single (E := fun _ : LatticeMode => ComplexE3)
      1 rawDriftMode (f t)) =
      fun t => (lp.singleContinuousLinearMap ℂ
        (fun _ : LatticeMode => ComplexE3) 1 rawDriftMode) (f t) := by
    funext t
    rw [lp.singleContinuousLinearMap_apply]
  change Continuous (fun t => lp.single (E := fun _ : LatticeMode => ComplexE3)
    1 rawDriftMode (f t))
  rw [heq]
  exact (lp.singleContinuousLinearMap ℂ
    (fun _ : LatticeMode => ComplexE3) 1 rawDriftMode).continuous.comp hf

theorem rawMeanDriftPath_divergenceFree (μ c : ℝ) (z : ℂ) (t : ℝ) :
    LatticeDivergenceFree (rawMeanDriftPath μ c z t) :=
  rawMeanDriftCarrier_divergenceFree _ _

theorem rawMeanDriftCarrier_zero_mul (a z : ℂ) :
    rawMeanDriftCarrier 0 (a * z) = a • rawMeanDriftCarrier 0 z := by
  have hm : rawMeanCoefficient 0 = 0 := by
    ext i
    fin_cases i <;> simp [rawMeanCoefficient]
  unfold rawMeanDriftCarrier
  rw [hm]
  simp only [WithLp.toLp_zero, lp.single_zero, zero_add,
    rawTransverseCoefficient_mul, WithLp.toLp_smul]
  rw [smul_comm (latticeModeWeight rawDriftMode : ℂ) a,
    smul_smul]
  change (lp.singleContinuousLinearMap ℂ
      (fun _ : LatticeMode => ComplexE3) 1 rawDriftMode)
        ((a * (latticeModeWeight rawDriftMode : ℂ)) •
          WithLp.toLp 2 (rawTransverseCoefficient z)) =
    a • (lp.singleContinuousLinearMap ℂ
      (fun _ : LatticeMode => ComplexE3) 1 rawDriftMode)
        ((latticeModeWeight rawDriftMode : ℂ) •
          WithLp.toLp 2 (rawTransverseCoefficient z))
  rw [map_smul, map_smul, smul_smul]

theorem rawMeanDriftCarrier_add_zero (c : ℝ) (z w : ℂ) :
    rawMeanDriftCarrier c z + rawMeanDriftCarrier 0 w =
      rawMeanDriftCarrier c (z + w) := by
  apply Subtype.ext
  funext q
  change rawMeanDriftCarrier c z q + rawMeanDriftCarrier 0 w q =
    rawMeanDriftCarrier c (z + w) q
  by_cases hq0 : q = 0
  · subst q
    rw [rawMeanDriftCarrier_apply_zero,
      rawMeanDriftCarrier_apply_zero, rawMeanDriftCarrier_apply_zero]
    have hm : rawMeanCoefficient 0 = 0 := by
      ext i
      fin_cases i <;> simp [rawMeanCoefficient]
    rw [hm, WithLp.toLp_zero, add_zero]
  · by_cases hqk : q = rawDriftMode
    · subst q
      rw [rawMeanDriftCarrier_apply_mode,
        rawMeanDriftCarrier_apply_mode, rawMeanDriftCarrier_apply_mode]
      ext i
      fin_cases i <;>
        simp [rawTransverseCoefficient]
    · rw [rawMeanDriftCarrier_apply_other c z q hq0 hqk,
        rawMeanDriftCarrier_apply_other 0 w q hq0 hqk,
        rawMeanDriftCarrier_apply_other c (z + w) q hq0 hqk,
        zero_add]

/-- On the integration interval, the actual nonlinear mild integrand of the
explicit path is the displayed scalar Volterra kernel times its transverse
carrier. -/
theorem criticalMildPathIntegrand_rawMeanDriftPath
    (μ c t s : ℝ) (hμ : 0 < μ) (z : ℂ) (hst : s < t) :
    criticalMildPathIntegrand μ hμ (rawMeanDriftPath μ c z)
        (rawMeanDriftPath_divergenceFree μ c z) t s =
      (((Real.exp (-μ * (t - s)) * c *
          Real.exp ((c - μ) * s) : ℝ) : ℂ) • rawMeanDriftCarrier 0 z) := by
  unfold criticalMildPathIntegrand
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos μ hμ
      (rawMeanDriftPath μ c z s) (rawMeanDriftPath μ c z s)
      (rawMeanDriftPath_divergenceFree μ c z s) (sub_pos.mpr hst)]
  unfold rawMeanDriftPath
  rw [show rawMeanDriftPath_divergenceFree μ c z s =
      rawMeanDriftCarrier_divergenceFree c (↑(Real.exp ((c - μ) * s)) * z)
      from rfl]
  rw [heatRegularizedSpectralOutput_rawMeanDriftCarrier μ (t - s) c hμ
      (sub_pos.mpr hst) (↑(Real.exp ((c - μ) * s)) * z)]
  rw [rawMeanDriftCarrier_zero_mul, rawMeanDriftCarrier_zero_mul, smul_smul]
  congr 1
  push_cast
  ring

/-- The actual Bochner Duhamel integral of the explicit path reduces to its
one scalar Volterra integral. -/
theorem criticalMildDuhamel_rawMeanDriftPath
    (μ c t : ℝ) (hμ : 0 < μ) (ht : 0 ≤ t) (z : ℂ) :
    criticalMildDuhamel μ hμ (rawMeanDriftPath μ c z)
        (rawMeanDriftPath_divergenceFree μ c z) t =
      (∫ s in (0 : ℝ)..t,
        ((Real.exp (-μ * (t - s)) * c *
          Real.exp ((c - μ) * s) : ℝ) : ℂ)) • rawMeanDriftCarrier 0 z := by
  let g : ℝ → ℝ := fun s => Real.exp (-μ * (t - s)) * c *
    Real.exp ((c - μ) * s)
  unfold criticalMildDuhamel
  have hae : (fun s => criticalMildPathIntegrand μ hμ
      (rawMeanDriftPath μ c z) (rawMeanDriftPath_divergenceFree μ c z) t s) =ᵐ[
        volume.restrict (Ioc (0 : ℝ) t)]
      fun s => ((g s : ℝ) : ℂ) • rawMeanDriftCarrier 0 z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc (0 : ℝ) t)).ae_ne t] with s hs hst
    exact criticalMildPathIntegrand_rawMeanDriftPath μ c t s hμ z
      (lt_of_le_of_ne hs.2 hst)
  calc
    (∫ s in Ioc (0 : ℝ) t, criticalMildPathIntegrand μ hμ
        (rawMeanDriftPath μ c z) (rawMeanDriftPath_divergenceFree μ c z) t s) =
        ∫ s in Ioc (0 : ℝ) t,
          ((g s : ℝ) : ℂ) • rawMeanDriftCarrier 0 z := integral_congr_ae hae
    _ = (∫ s in Ioc (0 : ℝ) t, ((g s : ℝ) : ℂ)) •
        rawMeanDriftCarrier 0 z := by rw [integral_smul_const]
    _ = (∫ s in (0 : ℝ)..t, ((g s : ℝ) : ℂ)) •
        rawMeanDriftCarrier 0 z := by
      rw [intervalIntegral.integral_of_le ht]
    _ = (∫ s in (0 : ℝ)..t,
        ((Real.exp (-μ * (t - s)) * c *
          Real.exp ((c - μ) * s) : ℝ) : ℂ)) • rawMeanDriftCarrier 0 z := by
      rfl

/-- The exponentially growing two-mode path is an exact fixed point of the
repository's literal raw-complex mild image on every nonnegative horizon. -/
theorem criticalMildImage_rawMeanDriftPath
    (μ c t : ℝ) (hμ : 0 < μ) (ht : 0 ≤ t) (z : ℂ) :
    criticalMildImage μ hμ (rawMeanDriftCarrier c z)
        (rawMeanDriftPath μ c z) (rawMeanDriftPath_divergenceFree μ c z)
        t ht = rawMeanDriftPath μ c z t := by
  let g : ℝ → ℝ := fun s => Real.exp (-μ * (t - s)) * c *
    Real.exp ((c - μ) * s)
  have hgint : IntervalIntegrable g volume 0 t := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  have hcast := Complex.ofRealCLM.intervalIntegral_comp_comm hgint
  change (∫ s in (0 : ℝ)..t, ((g s : ℝ) : ℂ)) =
      ((∫ s in (0 : ℝ)..t, g s : ℝ) : ℂ) at hcast
  have hreal := raw_drift_exponential_mild_identity μ c t
  have hcomplex : ((Real.exp ((c - μ) * t) : ℝ) : ℂ) =
      ((Real.exp (-μ * t) : ℝ) : ℂ) +
        ((∫ s in (0 : ℝ)..t, g s : ℝ) : ℂ) := by
    norm_cast
  rw [← hcast] at hcomplex
  unfold criticalMildImage
  set_option maxHeartbeats 4000000 in
  rw [weightedHeatFlow_rawMeanDriftCarrier μ t c hμ.le ht z,
    criticalMildDuhamel_rawMeanDriftPath μ c t hμ ht z,
    ← rawMeanDriftCarrier_zero_mul,
    rawMeanDriftCarrier_add_zero]
  unfold rawMeanDriftPath
  congr 1
  rw [← add_mul]
  congr 1
  exact hcomplex.symm

/-- Restriction of the explicit global raw path to a finite mild chart. -/
def rawMeanDriftChart (μ c : ℝ) (z : ℂ) (T : ℝ) : CriticalMildPath T :=
  ⟨fun τ => rawMeanDriftPath μ c z τ.1,
    (continuous_rawMeanDriftPath μ c z).comp continuous_subtype_val⟩

/-- Every finite restriction belongs to a genuine path ball, taking its own
continuous-map norm as the radius. -/
def rawMeanDriftPathBall (μ c : ℝ) (z : ℂ) (T : ℝ) :
    CriticalMildPathBall T ‖rawMeanDriftChart μ c z T‖ :=
  ⟨rawMeanDriftChart μ c z T, fun τ =>
    ⟨rawMeanDriftPath_divergenceFree μ c z τ.1,
      norm_weightedMildPath_eval_le T (rawMeanDriftChart μ c z T) τ⟩⟩

theorem positiveTimeHeatRegularizedSpectralOutput_self_congr
    (μ : ℝ) (hμ : 0 < μ) (u v : WeightedLatticeBanach)
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v)
    (huv : u = v) (r : ℝ) :
    positiveTimeHeatRegularizedSpectralOutput μ hμ u u hu r =
      positiveTimeHeatRegularizedSpectralOutput μ hμ v v hv r := by
  subst v
  rfl

theorem criticalMildDuhamel_pathExtension_rawMeanDriftChart
    (μ c T : ℝ) (hμ : 0 < μ) (hT : 0 ≤ T) (z : ℂ)
    (τ : Icc (0 : ℝ) T) :
    criticalMildDuhamel μ hμ
        (criticalMildPathExtension T hT (rawMeanDriftChart μ c z T))
        (criticalMildPathBallExtension_divergenceFree hT
          (rawMeanDriftPathBall μ c z T)) τ.1 =
      criticalMildDuhamel μ hμ (rawMeanDriftPath μ c z)
        (rawMeanDriftPath_divergenceFree μ c z) τ.1 := by
  unfold criticalMildDuhamel
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsT : s ≤ T := hs.2.trans τ.2.2
  have hext := criticalMildPathExtension_apply T hT
    (rawMeanDriftChart μ c z T) ⟨hs.1.le, hsT⟩
  have hext' :
      criticalMildPathExtension T hT (rawMeanDriftChart μ c z T) s =
        rawMeanDriftPath μ c z s := by
    rw [hext]
    rfl
  exact positiveTimeHeatRegularizedSpectralOutput_self_congr μ hμ
    (criticalMildPathExtension T hT (rawMeanDriftChart μ c z T) s)
    (rawMeanDriftPath μ c z s) _ _ hext' (τ.1 - s)

theorem rawMeanDriftPathBall_mild
    (μ c T : ℝ) (hμ : 0 < μ) (hT : 0 ≤ T) (z : ℂ) :
    ∀ τ : Icc (0 : ℝ) T,
      (rawMeanDriftPathBall μ c z T).1 τ =
        criticalMildImage μ hμ (rawMeanDriftCarrier c z)
          (criticalMildPathExtension T hT (rawMeanDriftPathBall μ c z T).1)
          (criticalMildPathBallExtension_divergenceFree hT
            (rawMeanDriftPathBall μ c z T)) τ.1 τ.2.1 := by
  intro τ
  change rawMeanDriftPath μ c z τ.1 = _
  unfold criticalMildImage
  have hduh :=
    criticalMildDuhamel_pathExtension_rawMeanDriftChart μ c T hμ hT z τ
  rw [show criticalMildDuhamel μ hμ
      (criticalMildPathExtension T hT (rawMeanDriftPathBall μ c z T).1)
      (criticalMildPathBallExtension_divergenceFree hT
        (rawMeanDriftPathBall μ c z T)) τ.1 =
      criticalMildDuhamel μ hμ (rawMeanDriftPath μ c z)
        (rawMeanDriftPath_divergenceFree μ c z) τ.1 by
    simpa [rawMeanDriftPathBall] using hduh]
  exact (criticalMildImage_rawMeanDriftPath μ c τ.1 hμ τ.2.1 z).symm

theorem amplitudeOffZero_rawMeanDriftPath_mode
    (μ c t : ℝ) (z : ℂ) :
    amplitudeOffZero (rawMeanDriftPath μ c z t) rawDriftMode =
      Real.exp ((c - μ) * t) * ‖z‖ := by
  unfold amplitudeOffZero rawMeanDriftPath weightedAmplitude
  rw [if_neg rawDriftMode_ne_zero,
    weightedLatticeCoefficient_rawMeanDriftCarrier_mode,
    complexEuclideanNorm_rawTransverseCoefficient,
    Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem exp_mul_norm_le_normX1_rawMeanDriftPath
    (μ c t : ℝ) (z : ℂ) :
    Real.exp ((c - μ) * t) * ‖z‖ ≤
      normX1 latticeModeSize
        (amplitudeOffZero (rawMeanDriftPath μ c z t)) := by
  let u := rawMeanDriftPath μ c z t
  have hs : InW latticeModeSize (amplitudeOffZero u) :=
    InW_X1_offZero u (InW_latticeModeSize u)
  have hterm := hs.le_tsum rawDriftMode (fun j _ =>
    mul_nonneg (latticeModeSize_nonneg j) (abs_nonneg _))
  unfold normX1 wNorm
  dsimp [u] at hterm
  rw [latticeModeSize_rawDriftMode,
    amplitudeOffZero_rawMeanDriftPath_mode] at hterm
  simpa [abs_of_nonneg
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg z))] using hterm

theorem viscosity_exp_le_offZeroMixedCriticalQty_rawMeanDriftPath
    (μ c t : ℝ) (hμ : 0 ≤ μ) (z : ℂ) :
    μ * (Real.exp ((c - μ) * t) * ‖z‖) ≤
      offZeroMixedCriticalQty μ (rawMeanDriftPath μ c z t) := by
  unfold offZeroMixedCriticalQty
  have hXm1 := normXm1_nonneg latticeModeSize_nonneg
    (amplitudeOffZero (rawMeanDriftPath μ c z t))
  have hX1 := exp_mul_norm_le_normX1_rawMeanDriftPath μ c t z
  nlinarith

theorem exp_mul_norm_le_norm_rawMeanDriftPath
    (μ c t : ℝ) (z : ℂ) :
    Real.exp ((c - μ) * t) * ‖z‖ ≤ ‖rawMeanDriftPath μ c z t‖ := by
  have heval := norm_weightedLattice_eval_le
    (rawMeanDriftPath μ c z t) rawDriftMode
  rw [norm_apply_eq_weight_mul_amplitude,
    latticeModeSize_rawDriftMode,
    show weightedAmplitude (rawMeanDriftPath μ c z t) rawDriftMode =
        Real.exp ((c - μ) * t) * ‖z‖ by
      simpa [amplitudeOffZero, rawDriftMode_ne_zero] using
        amplitudeOffZero_rawMeanDriftPath_mode μ c t z] at heval
  have hnonneg : 0 ≤ Real.exp ((c - μ) * t) * ‖z‖ :=
    mul_nonneg (Real.exp_pos _).le (norm_nonneg z)
  nlinarith

/-- The overbroad raw-complex off-zero terminal-bound endpoint is false.  For
every positive viscosity, one fixed divergence-free datum with a real mean
admits exact finite mild charts whose off-zero mixed quantity grows like
`exp t`.  This datum is outside the anti-Hermitian Fourier image of a real
physical velocity field. -/
theorem not_exists_criticalMildOffZeroTerminalBound_rawMeanDrift
    (μ : ℝ) (hμ : 0 < μ) :
    ¬ ∃ K : ℝ, CriticalMildOffZeroTerminalBound μ hμ
      (rawMeanDriftCarrier (μ + 1) 1) K := by
  rintro ⟨K, hbound⟩
  let T : ℝ := |K| / μ + 1
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  let u := rawMeanDriftPathBall μ (μ + 1) 1 T
  have hterminal := hbound hT u
    (rawMeanDriftPathBall_mild μ (μ + 1) T hμ hT 1)
  change offZeroMixedCriticalQty μ
      (rawMeanDriftPath μ (μ + 1) 1 T) ≤ K at hterminal
  have hlower := viscosity_exp_le_offZeroMixedCriticalQty_rawMeanDriftPath
    μ (μ + 1) T hμ.le (1 : ℂ)
  have hlower' : μ * Real.exp T ≤
      offZeroMixedCriticalQty μ
        (rawMeanDriftPath μ (μ + 1) 1 T) := by
    simpa only [add_sub_cancel_left, one_mul, mul_one, norm_one] using hlower
  have hexp := Real.add_one_le_exp T
  have hμexp : μ * (T + 1) ≤ μ * Real.exp T :=
    mul_le_mul_of_nonneg_left hexp hμ.le
  have hμT : μ * (T + 1) = |K| + 2 * μ := by
    dsimp [T]
    field_simp [ne_of_gt hμ]
    ring
  have hKμT : K < μ * (T + 1) := by
    rw [hμT]
    have hKabs : K ≤ |K| := le_abs_self K
    linarith
  linarith

/-- The same exact trajectory also falsifies the older raw-complex terminal
Banach-norm bound consumed directly by bounded continuation. -/
theorem not_exists_criticalMildTerminalNormBound_rawMeanDrift
    (μ : ℝ) (hμ : 0 < μ) :
    ¬ ∃ M : ℝ, CriticalMildTerminalNormBound μ hμ
      (rawMeanDriftCarrier (μ + 1) 1) M := by
  rintro ⟨M, hbound⟩
  let T : ℝ := |M| + 1
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  let u := rawMeanDriftPathBall μ (μ + 1) 1 T
  have hterminal := hbound hT u
    (rawMeanDriftPathBall_mild μ (μ + 1) T hμ hT 1)
  change ‖rawMeanDriftPath μ (μ + 1) 1 T‖ ≤ M at hterminal
  have hlower := exp_mul_norm_le_norm_rawMeanDriftPath
    μ (μ + 1) T (1 : ℂ)
  have hlower' : Real.exp T ≤ ‖rawMeanDriftPath μ (μ + 1) 1 T‖ := by
    simpa only [add_sub_cancel_left, one_mul, mul_one, norm_one] using hlower
  have hexp := Real.add_one_le_exp T
  have hMT : M < T + 1 := by
    dsimp [T]
    have hMabs : M ≤ |M| := le_abs_self M
    linarith
  linarith

/-- Reality condition for the repository's `A = -i û` raw coefficient
normalization: negating the lattice mode negates the complex conjugate. -/
def RawLatticeAntiHermitian (u : WeightedLatticeBanach) : Prop :=
  ∀ m : LatticeMode,
    weightedLatticeCoefficient u (-m) =
      -complexConjugate (weightedLatticeCoefficient u m)

/-- The growing raw counterexample is excluded by the physical reality
condition already at the zero mode: its mean is real and nonzero, whereas an
anti-Hermitian zero mode must be purely imaginary. -/
theorem rawMeanDrift_counterdatum_not_antiHermitian
    (μ : ℝ) (hμ : 0 < μ) :
    ¬ RawLatticeAntiHermitian (rawMeanDriftCarrier (μ + 1) 1) := by
  intro hphysical
  have hzero := hphysical (0 : LatticeMode)
  simp only [neg_zero] at hzero
  rw [weightedLatticeCoefficient_rawMeanDriftCarrier_zero] at hzero
  have hcoord := congrFun hzero (0 : Fin 3)
  simp [rawMeanCoefficient, complexConjugate] at hcoord
  norm_cast at hcoord
  norm_num at hcoord
  linarith

end Navier.Analysis.PeriodicGlobalCriticalControl
