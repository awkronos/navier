import Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification

/-!
# Quantitative terminal traces of whole-space heat-curl momentum

Uniform energy and the actual weak evolution imply a Lipschitz time modulus
for each fixed positive-time Gaussian curl test.  We construct its terminal
value with the same modulus, even though the classical solution is only given
strictly before the terminal time.  No terminal velocity or terminal critical
norm is assumed.

The scalar extension step uses Mathlib's `LipschitzOnWith.extend_real`
(the infimum construction of the McShane extension).  This is an application
of the standard Lipschitz extension argument, not a novelty claim.  The result
is a trace of the native whole-space momentum pairing; constructing a smooth
terminal velocity and a continuation remains a separate obligation.
-/

set_option autoImplicit false
noncomputable section

open Filter Set MeasureTheory
open scoped Topology Interval

namespace Navier.Analysis.WholeSpaceHeatCurlTerminalTrace

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification

private theorem exists_terminal_of_lipschitz_bound
    {f : ℝ → ℝ} {T W : ℝ} (hT : 0 < T) (hW : 0 ≤ W)
    (hf : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ioo 0 T, |f t - f s| ≤ W * |t - s|) :
    ∃ L : ℝ, Tendsto f (𝓝[<] T) (𝓝 L) ∧
      ∀ s ∈ Ioo 0 T, |L - f s| ≤ W * (T - s) := by
  have hlip : LipschitzOnWith (NNReal.mk W hW) f (Ioo 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [Real.dist_eq, NNReal.coe_mk] using hf t ht s hs
  obtain ⟨g, hg, heq⟩ := hlip.extend_real
  refine ⟨g T, ?_, ?_⟩
  · apply (hg.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [Ioo_mem_nhdsLT hT] with s hs
    exact (heq hs).symm
  · intro s hs
    have h := hg.dist_le_mul T s
    simpa only [Real.dist_eq, heq hs, NNReal.coe_mk,
      abs_of_pos (sub_pos.mpr hs.2)] using h

/-- The energy bound controls the time modulus uniformly up to the terminal
time for each fixed heat-curl observable on the actual `SolvesBefore` carrier. -/
theorem SolvesBefore.exists_heatCurlMomentum_lipschitz_bound
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ s ∈ Ioo 0 T, ∀ t ∈ Ioo 0 T,
      |backwardHeatCurlMomentum κ τ x₀ a u t -
        backwardHeatCurlMomentum κ τ x₀ a u s| ≤ W * |t - s| := by
  obtain ⟨W, hW, hbound⟩ :=
    SolvesBefore.exists_uniformBound_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
      hT hsol hκ hτ x₀ a
  have hordered : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ioo 0 T, s ≤ t →
      |backwardHeatCurlMomentum κ τ x₀ a u t -
        backwardHeatCurlMomentum κ τ x₀ a u s| ≤ W * |t - s| := by
    intro s hs t ht hst
    have hlim :=
      Navier.Analysis.WholeSpaceSolenoidalHeatIntegratedRhsLimit.SolvesBefore.tendsto_integral_compactBackwardHeatCurlTest_lerayWeakRhs
        hT hsol hs.1 hst ht.2 hκ hτ x₀ a
    have hnorm := le_of_tendsto' hlim.norm (fun R : ℝ =>
      intervalIntegral.norm_integral_le_of_norm_le_const (fun z hz => by
        rw [uIoc_of_le hst] at hz
        simpa only [Real.norm_eq_abs] using
          hbound R (hs.1.le.trans hz.1.le) (hz.2.trans_lt ht.2)))
    simpa only [Real.norm_eq_abs] using hnorm
  refine ⟨W, hW, ?_⟩
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hordered s hs t ht hst
  · simpa only [abs_sub_comm] using hordered t ht s hs hts

/-- A finite terminal heat-curl momentum is constructed, with linear error
`W * (T - s)` and the same constant controlling every preterminal increment. -/
theorem SolvesBefore.exists_heatCurlMomentum_terminalTrace
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    ∃ W L : ℝ, 0 ≤ W ∧
      Tendsto (backwardHeatCurlMomentum κ τ x₀ a u) (𝓝[<] T) (𝓝 L) ∧
      (∀ s ∈ Ioo 0 T,
        |L - backwardHeatCurlMomentum κ τ x₀ a u s| ≤ W * (T - s)) := by
  obtain ⟨W, hW, hmod⟩ :=
    SolvesBefore.exists_heatCurlMomentum_lipschitz_bound hT hsol hκ hτ x₀ a
  obtain ⟨L, hL, herr⟩ := exists_terminal_of_lipschitz_bound hT hW hmod
  exact ⟨W, L, hW, hL, herr⟩

/-- The constructed trace is the endpoint of the actual cutoff-free weak
evolution: its integrated right-hand side tends to the terminal momentum
increment for every positive starting time. -/
theorem SolvesBefore.exists_terminal_heatCurlEvolution
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    ∃ W L : ℝ, 0 ≤ W ∧
      Tendsto (backwardHeatCurlMomentum κ τ x₀ a u) (𝓝[<] T) (𝓝 L) ∧
      (∀ s ∈ Ioo 0 T,
        |L - backwardHeatCurlMomentum κ τ x₀ a u s| ≤ W * (T - s)) ∧
      ∀ s ∈ Ioo 0 T,
        Tendsto (fun t => ∫ r in s..t, backwardHeatCurlRhs ν κ τ x₀ a u r)
          (𝓝[<] T) (𝓝 (L - backwardHeatCurlMomentum κ τ x₀ a u s)) := by
  obtain ⟨W, L, hW, hL, herr⟩ :=
    SolvesBefore.exists_heatCurlMomentum_terminalTrace hT hsol hκ hτ x₀ a
  refine ⟨W, L, hW, hL, herr, ?_⟩
  intro s hs
  apply (hL.sub_const (backwardHeatCurlMomentum κ τ x₀ a u s)).congr'
  filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
  exact (SolvesBefore.intervalIntegral_backwardHeatCurlRhs_eq_momentumDiff
    hT hsol hs.1 ht.1.le ht.2 hκ hτ x₀ a).symm

/-- The cutoff-free right-hand side remains integrable on an interval reaching
the terminal time.  Its value at that single time is irrelevant to the Lebesgue
integral; all bounds and measurability are proved strictly before it. -/
theorem SolvesBefore.intervalIntegrable_heatCurlRhs_to_terminal
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    {s : ℝ} (hs : s ∈ Ioo 0 T) :
    IntervalIntegrable (backwardHeatCurlRhs ν κ τ x₀ a u) volume s T := by
  obtain ⟨W, _hW, hbound⟩ :=
    SolvesBefore.exists_uniformBound_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
      hT hsol hκ hτ x₀ a
  have hcont : ∀ R : ℝ, ContinuousOn (fun t =>
      lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u t)
      (Ioo s T) := by
    intro R t ht
    have ht0 : 0 < t := hs.1.trans ht.1
    have hc :=
      SolvesBefore.continuousOn_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
        hT hsol (ta := t / 2) (tb := (t + T) / 2)
        (by linarith) (by linarith) (by linarith [ht.2])
        R κ τ x₀ a
    exact (hc.continuousAt (Icc_mem_nhds (by linarith)
      (by linarith [ht.2]))).continuousWithinAt
  have hlim : ∀ᵐ t ∂volume.restrict (Ioo s T), Tendsto (fun R : ℝ =>
      lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u t)
      atTop (𝓝 (backwardHeatCurlRhs ν κ τ x₀ a u t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact SolvesBefore.tendsto_compactBackwardHeatCurlTest_lerayWeakRhs
      hsol (hs.1.le.trans ht.1.le) ht.2 hκ hτ x₀ a
  have hmeas := aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℝ)
    (fun R => (hcont R).aestronglyMeasurable measurableSet_Ioo) hlim
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioo s T),
      ‖backwardHeatCurlRhs ν κ τ x₀ a u t‖ ≤ W := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hlim] with t ht htl
    exact le_of_tendsto' htl.norm (fun R => by
      simpa only [Real.norm_eq_abs] using
        hbound R (hs.1.le.trans ht.1.le) ht.2)
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hs.2.le).mpr
  exact (integrable_const W).mono' hmeas hnorm

/-- The terminal value satisfies the weak evolution equation with an actual
integral ending at `T`, and the quantitative terminal error remains explicit. -/
theorem SolvesBefore.exists_terminal_heatCurlEvolution_integral
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    ∃ W L : ℝ, 0 ≤ W ∧
      Tendsto (backwardHeatCurlMomentum κ τ x₀ a u) (𝓝[<] T) (𝓝 L) ∧
      ∀ s ∈ Ioo 0 T,
        |L - backwardHeatCurlMomentum κ τ x₀ a u s| ≤ W * (T - s) ∧
        IntervalIntegrable (backwardHeatCurlRhs ν κ τ x₀ a u) volume s T ∧
        (∫ r in s..T, backwardHeatCurlRhs ν κ τ x₀ a u r) =
          L - backwardHeatCurlMomentum κ τ x₀ a u s := by
  obtain ⟨W, L, hW, hL, herr, hevol⟩ :=
    SolvesBefore.exists_terminal_heatCurlEvolution hT hsol hκ hτ x₀ a
  refine ⟨W, L, hW, hL, ?_⟩
  intro s hs
  have hi := SolvesBefore.intervalIntegrable_heatCurlRhs_to_terminal
    hT hsol hκ hτ x₀ a hs
  refine ⟨herr s hs, hi, ?_⟩
  have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hm : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝[uIcc s T] T) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
    simpa only [uIcc_of_le hs.2.le] using ⟨ht.1.le, ht.2.le⟩
  exact tendsto_nhds_unique ((hc T right_mem_uIcc).tendsto.comp hm) (hevol s hs)

end Navier.Analysis.WholeSpaceHeatCurlTerminalTrace

#print axioms Navier.Analysis.WholeSpaceHeatCurlTerminalTrace.SolvesBefore.exists_heatCurlMomentum_lipschitz_bound
#print axioms Navier.Analysis.WholeSpaceHeatCurlTerminalTrace.SolvesBefore.exists_heatCurlMomentum_terminalTrace
#print axioms Navier.Analysis.WholeSpaceHeatCurlTerminalTrace.SolvesBefore.exists_terminal_heatCurlEvolution
#print axioms Navier.Analysis.WholeSpaceHeatCurlTerminalTrace.SolvesBefore.intervalIntegrable_heatCurlRhs_to_terminal
#print axioms Navier.Analysis.WholeSpaceHeatCurlTerminalTrace.SolvesBefore.exists_terminal_heatCurlEvolution_integral
