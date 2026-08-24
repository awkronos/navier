import Navier.Analysis.LeiLinPositiveRestart

/-!
# Canonical heat mollifiers for the positive-time restart

The completed critical mild construction does not currently expose a
Galerkin solution sequence.  Heat mollification is the canonical approximation
available in the actual completed carrier.  This module proves the sharp
uniformity criterion for that family: the mollified half-generator moments are
uniformly bounded exactly when the restart datum already lies in the
half-generator graph domain.

Consequently carrier convergence plus finite positive-time smoothing cannot
manufacture the uniform majorant required by the split Volterra argument.  The
minimal additional positive-time input is precisely graph membership.  Under
that input, the heat mollifiers construct every approximation field required by
`positiveRestart_graph_X2_and_terminal_X1_of_approximation`, with the exact
path moment as their common integrable majorant.

Reference: Z. Lei and F. Lin, CPAM 64 (2011), Sec. 2.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.LeiLinPositiveRestartGalerkin

open Filter
open MeasureTheory
open Set
open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildRestart
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinTimeMixed
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.LeiLinPositiveRestart

/-- The positive mollification time `1/(n+1)`, as a nonnegative real. -/
def mollifierTime (n : ℕ) : NNReal :=
  ⟨(1 : ℝ) / ((n : ℝ) + 1), (one_div_pos.mpr (by positivity)).le⟩

@[simp] theorem coe_mollifierTime (n : ℕ) :
    (mollifierTime n : ℝ) = 1 / ((n : ℝ) + 1) := rfl

theorem mollifierTime_pos (n : ℕ) : 0 < (mollifierTime n : ℝ) := by
  unfold mollifierTime
  exact one_div_pos.mpr (by positivity)

theorem tendsto_mollifierTime_zero : Tendsto mollifierTime atTop (nhds 0) := by
  apply NNReal.tendsto_coe.mp
  simpa only [coe_mollifierTime, NNReal.coe_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Canonical heat-mollified approximation inside the actual completed
weighted lattice carrier. -/
def heatMollification (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (u : WeightedLatticeBanach) : WeightedLatticeBanach :=
  weightedHeatFlow ν (mollifierTime n) hν.le (mollifierTime n).property u

/-- Heat mollification converges in the carrier norm to every divergence-free
datum. -/
theorem tendsto_heatMollification (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Tendsto (fun n => heatMollification ν hν n u) atTop (nhds u) := by
  have h := (continuous_weightedHeatFlow_nnreal ν hν.le u).continuousAt.tendsto.comp
    tendsto_mollifierTime_zero
  have hz : weightedHeatFlow ν ((0 : NNReal) : ℝ) hν.le
      (0 : NNReal).property u = u :=
    weightedHeatFlow_zero_of_divergenceFree ν hν.le u hu
  rw [hz] at h
  change Tendsto
    ((fun τ : NNReal => weightedHeatFlow ν (τ : ℝ) hν.le τ.property u) ∘
      mollifierTime) atTop (nhds u)
  exact h

/-- Every mollified datum lies in the half-generator graph domain. -/
theorem summable_halfGeneratorMoment_heatMollification
    (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ *
        ‖heatMollification ν hν n u m‖ := by
  exact summable_halfGeneratorMoment_weightedHeatFlow
    ν (mollifierTime n) hν (mollifierTime_pos n) u hu

/-- On graph-domain data, heat mollification contracts the half-generator
moment. -/
theorem heatHalfGeneratorMoment_heatMollification_le
    (ν : ℝ) (hν : 0 < ν) (n : ℕ)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (hgraph : Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) :
    heatHalfGeneratorMoment (heatMollification ν hν n u) ≤
      heatHalfGeneratorMoment u := by
  have hpoint : ∀ m : LatticeMode,
      ‖complexFrequency (latticeFrequency m)‖ *
          ‖heatMollification ν hν n u m‖ ≤
        ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖ := by
    intro m
    rw [heatMollification, weightedHeatFlow_apply_of_divergenceFree
      ν (mollifierTime n) hν.le (mollifierTime n).property u hu m]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg
        (complexHeatDecay_nonneg ν (mollifierTime n) (latticeFrequency m))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _)
        (complexHeatDecay_le_one hν.le (mollifierTime n).property _))
      (norm_nonneg _)
  unfold heatHalfGeneratorMoment
  exact (summable_halfGeneratorMoment_heatMollification ν hν n u hu).tsum_le_tsum
    hpoint hgraph

/-- **Sharp uniformity criterion for the canonical mollifiers.**  Uniform
half-generator control of the positive heat mollifications is equivalent to
membership of the original datum in the half-generator graph domain. -/
-- Citation: closedness/Fatou for the half-generator graph and heat contraction.
theorem exists_uniform_heatMollification_bound_iff_halfGeneratorDomain
    (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u) :
    (∃ C : ℝ, ∀ n,
      heatHalfGeneratorMoment (heatMollification ν hν n u) ≤ C) ↔
      Summable (fun m : LatticeMode =>
        ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) := by
  constructor
  · rintro ⟨C, hC⟩
    exact (summable_halfGeneratorMoment_of_tendsto_of_uniform_bound
      (tendsto_heatMollification ν hν u hu)
      (fun n => summable_halfGeneratorMoment_heatMollification ν hν n u hu)
      hC).1
  · intro hgraph
    exact ⟨heatHalfGeneratorMoment u,
      fun n => heatHalfGeneratorMoment_heatMollification_le
        ν hν n u hu hgraph⟩

/-- If a positive restart datum is outside the graph domain, the canonical
finite-smoothing family has no uniform half-generator bound.  This is the
checked obstruction to deriving the approximation majorant from the completed
carrier norm alone. -/
theorem not_exists_uniform_heatMollification_bound_of_not_halfGeneratorDomain
    (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) (hu : LatticeDivergenceFree u)
    (hnot : ¬ Summable (fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖)) :
    ¬ ∃ C : ℝ, ∀ n,
      heatHalfGeneratorMoment (heatMollification ν hν n u) ≤ C := by
  intro hC
  exact hnot
    ((exists_uniform_heatMollification_bound_iff_halfGeneratorDomain
      ν hν u hu).1 hC)

/-- **Realization of the positive-restart approximation payload.**

Once positive-time graph membership and the averaged split-Volterra recurrence
are supplied, the canonical heat mollifiers provide the convergent graph-domain
approximants and the exact path moment provides their common integrable
majorant.  The general positive-restart theorem then yields the literal restart
identity, trailing `L¹_t 𝒳²`, and terminal `𝒳¹` control. -/
-- Citation: Lei--Lin, CPAM 64 (2011), Sec. 2.
theorem positiveRestart_graph_X2_and_terminal_X1_of_halfGeneratorDomain
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R T δ A H : ℝ} (hR : 0 ≤ R)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hδT : δ ≤ T)
    (huR : ∀ s ∈ Ioc (0 : ℝ) T, ‖u s‖ ≤ R)
    (hmild : ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T),
      u s = criticalMildImage ν hν u₀ u hu s hs.1)
    (hhalf : ∀ s ∈ Icc (T - δ) T, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖)
    (hmoment : IntervalIntegrable (fun s => heatHalfGeneratorMoment (u s))
      volume (T - δ) T)
    (hintX1 : IntervalIntegrable
      (fun s => normX1 latticeModeSize (weightedAmplitude (u s)))
      volume (T - δ) T)
    (hmassX1 : (∫ s in (T - δ)..T,
      normX1 latticeModeSize (weightedAmplitude (u s))) ≤ A)
    (hsmall : (4 * R / Real.sqrt ν) * Real.sqrt δ < 1)
    (hvolterra : (∫ s in (T - δ)..T,
        heatHalfGeneratorMoment (u s)) ≤
      H + (4 * R / Real.sqrt ν) * Real.sqrt δ *
        (∫ s in (T - δ)..T, heatHalfGeneratorMoment (u s))) :
    (∀ r (hr : r ∈ Icc (0 : ℝ) δ),
      criticalMildRestartImage ν hν u hu (T - δ) r hr.1 =
        u (T - δ + r)) ∧
    (∀ s ∈ Icc (T - δ) T, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖) ∧
    IntervalIntegrable
      (fun s => normX2 latticeModeSize (weightedAmplitude (u s)))
      volume (T - δ) T ∧
    (∫ s in (T - δ)..T,
      normX2 latticeModeSize (weightedAmplitude (u s))) ≤
        H / (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ) ∧
    normX1 latticeModeSize (weightedAmplitude (u T)) ≤
      (A + (Real.sqrt ν *
          (H / (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ))) *
          Real.sqrt δ) / δ +
        (2 * R ^ 2 / Real.sqrt ν) * Real.sqrt δ := by
  exact positiveRestart_graph_X2_and_terminal_X1_of_approximation
    ν hν u₀ u huc hu hR hT hδ hδT huR hmild
    (v := fun n s => heatMollification ν hν n (u s))
    (M := fun s => heatHalfGeneratorMoment (u s))
    (fun s _hs => tendsto_heatMollification ν hν (u s) (hu s))
    (fun n s _hs =>
      summable_halfGeneratorMoment_heatMollification ν hν n (u s) (hu s))
    (fun n s hs =>
      heatHalfGeneratorMoment_heatMollification_le ν hν n (u s) (hu s)
        (hhalf s hs))
    hmoment hintX1 hmassX1 hsmall hvolterra

end Navier.Analysis.LeiLinPositiveRestartGalerkin

#print axioms Navier.Analysis.LeiLinPositiveRestartGalerkin.tendsto_heatMollification
#print axioms Navier.Analysis.LeiLinPositiveRestartGalerkin.heatHalfGeneratorMoment_heatMollification_le
#print axioms Navier.Analysis.LeiLinPositiveRestartGalerkin.exists_uniform_heatMollification_bound_iff_halfGeneratorDomain
#print axioms Navier.Analysis.LeiLinPositiveRestartGalerkin.not_exists_uniform_heatMollification_bound_of_not_halfGeneratorDomain
#print axioms Navier.Analysis.LeiLinPositiveRestartGalerkin.positiveRestart_graph_X2_and_terminal_X1_of_halfGeneratorDomain
