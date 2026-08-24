import Navier.Analysis.LeiLinCoerciveTerminal
import Navier.Analysis.CriticalMildRestart

/-!
# Positive-time graph closure for the Lei--Lin restart

The split nonlinear estimate is meaningful only after the actual mild path is
known to lie in the half-generator graph domain.  This module isolates the
missing closedness input precisely.  Uniform half-generator control of genuine
graph-domain approximants passes to their pointwise limit; convergence without
that uniform control does not.

On a trailing positive-time window, a single integrable majorant for those
approximants therefore supplies graph membership of the actual mild path.  The
averaged split-Volterra recurrence absorbs under the Lei--Lin small-window
condition, yields the trailing `L¹_t 𝒳²` mass, and feeds the existing terminal
`𝒳¹` sampler.  The theorem also returns the literal terminal-data restart
identity, so the conclusion concerns the actual mild equation rather than an
abstract scalar path.

Reference: Z. Lei and F. Lin, CPAM 64 (2011), Sec. 2.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.LeiLinPositiveRestart

open Filter
open MeasureTheory
open Set
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildRestart
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinTimeMixed
open Navier.Analysis.LeiLinCoerciveTerminal

/-- Coordinate evaluation on the completed weighted lattice carrier is
continuous. -/
theorem continuous_weightedLattice_apply (m : LatticeMode) :
    Continuous fun u : WeightedLatticeBanach => u m := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) fun u v => ?_).continuous
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  change ‖(u - v) m‖ ≤ ‖u - v‖
  exact norm_weightedLattice_eval_le (u - v) m

/-- Norm convergence in the completed carrier implies convergence at every
lattice coordinate. -/
theorem tendsto_weightedLattice_apply {v : ℕ → WeightedLatticeBanach}
    {u : WeightedLatticeBanach} (hv : Tendsto v atTop (nhds u))
    (m : LatticeMode) : Tendsto (fun n => v n m) atTop (nhds (u m)) :=
  (continuous_weightedLattice_apply m).continuousAt.tendsto.comp hv

/-- **Closedness of the half-generator graph ball.**  A norm-convergent
sequence of graph-domain elements with a common moment bound has a graph-domain
limit with the same bound.  The proof is finite-coordinate lower
semicontinuity followed by `summable_of_sum_le`; no abstract closed-operator
assumption is introduced. -/
-- Citation: Fatou/lower-semicontinuity for nonnegative series.
theorem summable_halfGeneratorMoment_of_tendsto_of_uniform_bound
    {v : ℕ → WeightedLatticeBanach} {u : WeightedLatticeBanach} {C : ℝ}
    (hv : Tendsto v atTop (nhds u))
    (hvsum : ∀ n, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖v n m‖)
    (hvbound : ∀ n, heatHalfGeneratorMoment (v n) ≤ C) :
    Summable (fun m : LatticeMode =>
        ‖complexFrequency (latticeFrequency m)‖ * ‖u m‖) ∧
      heatHalfGeneratorMoment u ≤ C := by
  let q : LatticeMode → ℝ := fun m => ‖complexFrequency (latticeFrequency m)‖
  have hfinite : ∀ F : Finset LatticeMode,
      ∑ m ∈ F, q m * ‖u m‖ ≤ C := by
    intro F
    have hlim : Tendsto (fun n => ∑ m ∈ F, q m * ‖v n m‖) atTop
        (nhds (∑ m ∈ F, q m * ‖u m‖)) := by
      apply tendsto_finsetSum
      intro m _hm
      exact (tendsto_weightedLattice_apply hv m).norm.const_mul (q m)
    apply le_of_tendsto hlim
    exact Eventually.of_forall fun n =>
      ((hvsum n).sum_le_tsum F (fun m _hm =>
        mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans (hvbound n)
  have hsum : Summable fun m : LatticeMode => q m * ‖u m‖ :=
    summable_of_sum_le
      (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hfinite
  refine ⟨hsum, ?_⟩
  exact Real.tsum_le_of_sum_le
    (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hfinite

/-- **Uniformity is necessary in the graph-closure step.**  Finite-support
approximants can converge coordinatewise to an absolutely summable sequence
whose linearly weighted moment is the divergent harmonic series.  Thus
approximation membership alone cannot establish the positive-time `𝒳²` /
half-generator claim. -/
-- Citation: the `p = 2` and `p = 1` real p-series criteria.
theorem exists_finite_graph_approximants_with_nonsummable_limit :
    ∃ (f : ℕ → ℝ) (v : ℕ → ℕ → ℝ),
      Summable (fun k => |f k|) ∧
      (∀ n, Summable fun k : ℕ => ((k : ℝ) + 1) * |v n k|) ∧
      (∀ k : ℕ, Tendsto (fun n => v n k) atTop (nhds (f k))) ∧
      ¬ Summable (fun k : ℕ => ((k : ℝ) + 1) * |f k|) := by
  let f : ℕ → ℝ := fun k => (((k : ℝ) + 1) ^ 2)⁻¹
  let v : ℕ → ℕ → ℝ := fun n k => if k < n then f k else 0
  refine ⟨f, v, ?_, ?_, ?_, ?_⟩
  · have hp : Summable fun n : ℕ => (((n : ℝ) ^ 2))⁻¹ :=
      (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
    have hshift : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹ :=
      by simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hp
    have hf0 : ∀ k : ℕ, 0 ≤ f k := fun k => inv_nonneg.mpr (sq_nonneg _)
    simpa [f, abs_of_nonneg (hf0 _)] using hshift
  · intro n
    apply summable_of_ne_finset_zero (s := Finset.range n)
    intro k hk
    have hkn : ¬ k < n := by simpa using hk
    simp [v, hkn]
  · intro k
    apply tendsto_atTop_of_eventually_const (i₀ := k + 1)
    intro n hn
    simp [v, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn]
  · have hp : ¬ Summable fun n : ℕ => ((n : ℝ) ^ 1)⁻¹ := by
      simpa using (not_congr (Real.summable_nat_pow_inv (p := 1))).2 (by norm_num)
    intro hs
    apply hp
    apply (summable_nat_add_iff 1).1
    have hf0 : ∀ k : ℕ, 0 ≤ f k := fun k => inv_nonneg.mpr (sq_nonneg _)
    have heq : (fun k : ℕ => ((k : ℝ) + 1) * |f k|) =
        fun k : ℕ => (((k : ℝ) + 1) ^ 1)⁻¹ := by
      funext k
      rw [abs_of_nonneg (hf0 k)]
      dsimp [f]
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    rw [heq] at hs
    simpa [Nat.cast_add, Nat.cast_one] using hs

/-- The half-generator moment of a continuous weighted-lattice path is a
measurable nonnegative scalar function. -/
theorem measurable_heatHalfGeneratorMoment_comp
    {u : ℝ → WeightedLatticeBanach} (huc : Continuous u) :
    Measurable fun s => heatHalfGeneratorMoment (u s) := by
  unfold heatHalfGeneratorMoment
  exact Measurable.tsum fun m => measurable_const.mul
    (((continuous_weightedLattice_apply m).comp huc).norm.measurable)

/-- A pointwise integrable majorant transfers graph membership and
integrability from uniformly controlled graph approximants to their actual
path limit. -/
theorem halfGeneratorMoment_limit_integrable_of_majorant
    {u : ℝ → WeightedLatticeBanach} (huc : Continuous u)
    {v : ℕ → ℝ → WeightedLatticeBanach} {M : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hv : ∀ s ∈ Icc a b, Tendsto (fun n => v n s) atTop (nhds (u s)))
    (hvsum : ∀ n s, s ∈ Icc a b → Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖v n s m‖)
    (hvbound : ∀ n s, s ∈ Icc a b → heatHalfGeneratorMoment (v n s) ≤ M s)
    (hM : IntervalIntegrable M volume a b) :
    (∀ s ∈ Icc a b, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖) ∧
      IntervalIntegrable (fun s => heatHalfGeneratorMoment (u s)) volume a b ∧
      (∫ s in a..b, heatHalfGeneratorMoment (u s)) ≤ ∫ s in a..b, M s := by
  have hclosed : ∀ s ∈ Icc a b,
      Summable (fun m : LatticeMode =>
          ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖) ∧
        heatHalfGeneratorMoment (u s) ≤ M s := by
    intro s hs
    exact summable_halfGeneratorMoment_of_tendsto_of_uniform_bound
      (hv s hs) (fun n => hvsum n s hs) (fun n => hvbound n s hs)
  have hmoment : IntervalIntegrable (fun s => heatHalfGeneratorMoment (u s))
      volume a b := by
    apply hM.mono_fun'
      (measurable_heatHalfGeneratorMoment_comp huc).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le hab] at hs
    rw [Real.norm_eq_abs, abs_of_nonneg (heatHalfGeneratorMoment_nonneg (u s))]
    exact (hclosed s ⟨hs.1.le, hs.2⟩).2
  refine ⟨fun s hs => (hclosed s hs).1, hmoment, ?_⟩
  exact intervalIntegral.integral_mono_on hab
    hmoment hM fun s hs => (hclosed s hs).2

/-- Physical amplitude is the carrier-coordinate norm divided by the fixed
inhomogeneous mode weight. -/
theorem weightedAmplitude_eq_norm_div (u : WeightedLatticeBanach)
    (m : LatticeMode) :
    weightedAmplitude u m = ‖u m‖ / (1 + latticeModeSize m) := by
  apply (eq_div_iff (by linarith [latticeModeSize_nonneg m] :
    1 + latticeModeSize m ≠ 0)).2
  rw [mul_comm]
  exact (norm_apply_eq_weight_mul_amplitude u m).symm

/-- Each physical amplitude coordinate varies continuously in the completed
carrier. -/
theorem continuous_weightedAmplitude_apply (m : LatticeMode) :
    Continuous fun u : WeightedLatticeBanach => weightedAmplitude u m := by
  rw [show (fun u : WeightedLatticeBanach => weightedAmplitude u m) =
      fun u => ‖u m‖ / (1 + latticeModeSize m) by
    funext u
    exact weightedAmplitude_eq_norm_div u m]
  exact (continuous_weightedLattice_apply m).norm.div_const _

/-- The physical `𝒳²` moment of a continuous path is measurable. -/
theorem measurable_normX2_weightedAmplitude_comp
    {u : ℝ → WeightedLatticeBanach} (huc : Continuous u) :
    Measurable fun s => normX2 latticeModeSize (weightedAmplitude (u s)) := by
  unfold normX2 wNorm
  exact Measurable.tsum fun m => measurable_const.mul
    (((continuous_weightedAmplitude_apply m).comp huc).abs.measurable)

/-- On a graph-domain window the physical `𝒳²` mass is integrable and bounded
by the half-generator mass. -/
theorem intervalIntegrable_normX2_and_integral_le_halfGeneratorMoment
    {u : ℝ → WeightedLatticeBanach} (huc : Continuous u) {a b : ℝ}
    (hab : a ≤ b)
    (hhalf : ∀ s ∈ Icc a b, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖)
    (hmoment : IntervalIntegrable (fun s => heatHalfGeneratorMoment (u s))
      volume a b) :
    IntervalIntegrable
        (fun s => normX2 latticeModeSize (weightedAmplitude (u s))) volume a b ∧
      (∫ s in a..b, normX2 latticeModeSize (weightedAmplitude (u s))) ≤
        ∫ s in a..b, heatHalfGeneratorMoment (u s) := by
  have hpoint : ∀ s ∈ Icc a b,
      normX2 latticeModeSize (weightedAmplitude (u s)) ≤
        heatHalfGeneratorMoment (u s) := by
    intro s hs
    have heq := heatHalfGeneratorMoment_eq_normX1_add_normX2 (u s) (hhalf s hs)
    linarith [normX1_nonneg latticeModeSize_nonneg (weightedAmplitude (u s))]
  have hX2 : IntervalIntegrable
      (fun s => normX2 latticeModeSize (weightedAmplitude (u s))) volume a b := by
    apply hmoment.mono_fun'
      (measurable_normX2_weightedAmplitude_comp huc).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le hab] at hs
    have hX2nonneg : 0 ≤ normX2 latticeModeSize (weightedAmplitude (u s)) := by
      unfold normX2 wNorm
      exact tsum_nonneg fun m => mul_nonneg (sq_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hX2nonneg]
    exact hpoint s ⟨hs.1.le, hs.2⟩
  exact ⟨hX2, intervalIntegral.integral_mono_on hab hX2 hmoment hpoint⟩

/-- **Positive-time nonlinear restart with graph closure and trailing `𝒳²`.**

The approximants are required to converge in the actual completed carrier and
to share one integrable half-generator majorant `M`; the preceding obstruction
shows why the uniform majorant cannot be dropped.  The averaged split-input
Volterra recurrence has the Lei--Lin coefficient `4R/√ν`.  Once its
small-window factor is below one, the exact mild path inherits graph
membership, its trailing `𝒳²` mass is absorbed, and the existing terminal
sampler gives the displayed `𝒳¹` bound. -/
-- Citation: Lei--Lin, CPAM 64 (2011), Sec. 2, split Fourier convolution estimate.
theorem positiveRestart_graph_X2_and_terminal_X1_of_approximation
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {v : ℕ → ℝ → WeightedLatticeBanach} {M : ℝ → ℝ}
    {R T δ A H : ℝ} (hR : 0 ≤ R)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hδT : δ ≤ T)
    (huR : ∀ s ∈ Ioc (0 : ℝ) T, ‖u s‖ ≤ R)
    (hmild : ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T),
      u s = criticalMildImage ν hν u₀ u hu s hs.1)
    (hv : ∀ s ∈ Icc (T - δ) T,
      Tendsto (fun n => v n s) atTop (nhds (u s)))
    (hvsum : ∀ n s, s ∈ Icc (T - δ) T → Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖v n s m‖)
    (hvbound : ∀ n s, s ∈ Icc (T - δ) T →
      heatHalfGeneratorMoment (v n s) ≤ M s)
    (hM : IntervalIntegrable M volume (T - δ) T)
    (hintX1 : IntervalIntegrable
      (fun s => normX1 latticeModeSize (weightedAmplitude (u s)))
      volume (T - δ) T)
    (hmassX1 : (∫ s in (T - δ)..T,
      normX1 latticeModeSize (weightedAmplitude (u s))) ≤ A)
    (hsmall : (4 * R / Real.sqrt ν) * Real.sqrt δ < 1)
    (hvolterra : (∫ s in (T - δ)..T, M s) ≤
      H + (4 * R / Real.sqrt ν) * Real.sqrt δ *
        (∫ s in (T - δ)..T, M s)) :
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
  have hwindow : T - δ ≤ T := by linarith
  have hlimit := halfGeneratorMoment_limit_integrable_of_majorant
    huc hwindow hv hvsum hvbound hM
  have hhalf := hlimit.1
  have hmoment := hlimit.2.1
  have hmomentLeM := hlimit.2.2
  have hMMass : (∫ s in (T - δ)..T, M s) ≤
      H / (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ) :=
    le_div_one_sub_of_volterra_sqrt hsmall hvolterra
  have hmomentMass : (∫ s in (T - δ)..T,
      heatHalfGeneratorMoment (u s)) ≤
      H / (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ) :=
    hmomentLeM.trans hMMass
  have hX2 := intervalIntegrable_normX2_and_integral_le_halfGeneratorMoment
    huc hwindow hhalf hmoment
  have hX2Mass : (∫ s in (T - δ)..T,
      normX2 latticeModeSize (weightedAmplitude (u s))) ≤
      H / (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ) :=
    hX2.2.trans hmomentMass
  have hterminal :=
    terminal_X1_le_of_trailingMass_and_integrated_halfGeneratorMoment
      ν hν u₀ u huc hu hR hT hδ hδT huR hmild hhalf hintX1 hmoment
      hmassX1 hmomentMass
  refine ⟨?_, hhalf, hX2.1, hX2Mass, hterminal⟩
  intro r hr
  have ha0 : 0 ≤ T - δ := by linarith
  have harT : T - δ + r ≤ T := by linarith [hr.2]
  have har0 : 0 ≤ T - δ + r := add_nonneg ha0 hr.1
  exact criticalMildRestartImage_eq_shifted_trajectory
    ν hν u₀ u huc hu hR ha0 hr.1
    (fun s hs => huR s ⟨hs.1, hs.2.trans harT⟩)
    (hmild (T - δ) ⟨ha0, hwindow⟩)
    (hmild (T - δ + r) ⟨har0, harT⟩)

end Navier.Analysis.LeiLinPositiveRestart

#print axioms Navier.Analysis.LeiLinPositiveRestart.summable_halfGeneratorMoment_of_tendsto_of_uniform_bound
#print axioms Navier.Analysis.LeiLinPositiveRestart.exists_finite_graph_approximants_with_nonsummable_limit
#print axioms Navier.Analysis.LeiLinPositiveRestart.halfGeneratorMoment_limit_integrable_of_majorant
#print axioms Navier.Analysis.LeiLinPositiveRestart.intervalIntegrable_normX2_and_integral_le_halfGeneratorMoment
#print axioms Navier.Analysis.LeiLinPositiveRestart.positiveRestart_graph_X2_and_terminal_X1_of_approximation
