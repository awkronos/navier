import Navier.Analysis.WholeSpaceHeatCurlTerminalTrace

/-!
# Heat-curl evolution including the prescribed initial time

Compactly supported momentum pairings are continuous at the initial time by
joint classical regularity.  The radius-independent weak evolution bound then
survives removal of the spatial cutoff at time zero.  This constructs the
initial trace of the actual whole-space heat-curl pairing without assuming
uniform spatial decay.  Together with the terminal trace it identifies the
weak evolution integral over the full closed time interval.
-/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval

namespace Navier.Analysis.WholeSpaceHeatCurlClosedEvolution

open Navier
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceDuhamel
open Navier.Analysis.WholeSpaceCutoffLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatFullViscousLimit
open Navier.Analysis.WholeSpaceSolenoidalHeatRhsIntervalIdentification
open Navier.Analysis.WholeSpaceHeatCurlTerminalTrace

/-- Compact tests detect the prescribed initial velocity continuously. -/
theorem SolvesBefore.continuousOn_testedMomentum
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore ν T u p) (φ : CompactSolenoidalTest) :
    ContinuousOn (testedMomentum φ u) (Ico 0 T) := by
  unfold testedMomentum cutoffMomentumCoordinate
  apply continuousOn_finsetSum
  intro j _
  apply continuousOn_integral_of_compact_support (φ.compact j)
  · have hfield : Continuous (fun z : ℝ × Space => φ.field z.2 j) :=
      (φ.smooth j).continuous.comp continuous_snd
    have hu : ContinuousOn (fun z : ℝ × Space => u z.1 z.2 j)
        (Ico 0 T ×ˢ (univ : Set Space)) :=
      (continuous_apply j).comp_continuousOn hsol.classical.1.continuousOn
    exact hfield.continuousOn.mul hu
  · intro t x ht hx
    exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hx) _

private theorem initial_bound_of_continuousOn
    {f : ℝ → ℝ} {T W : ℝ} (hT : 0 < T)
    (hc : ContinuousOn f (Ico 0 T))
    (hmod : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ioo 0 T, |f t - f s| ≤ W * |t-s|)
    {t : ℝ} (ht : t ∈ Ioo 0 T) : |f t - f 0| ≤ W * t := by
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝[Ico 0 T] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    exact ⟨hs.1.le, hs.2⟩
  have hf : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    (hc 0 ⟨le_rfl, hT⟩).tendsto.comp hid
  have hleft : Tendsto (fun s => |f t - f s|) (𝓝[>] 0)
      (𝓝 |f t - f 0|) := (tendsto_const_nhds.sub hf).abs
  have hi : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun s : ℝ => W * |t-s|) (𝓝[>] 0) (𝓝 (W*t)) := by
    simpa [abs_of_pos ht.1] using
      (((tendsto_const_nhds (x := t)).sub hi).abs.const_mul W)
  exact le_of_tendsto_of_tendsto hleft hright (by
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    exact hmod s hs t ht)

/-- The uncut Gaussian curl observable approaches its actual initial value
with a linear error bound.  Spatial cutoff removal includes time zero. -/
theorem SolvesBefore.exists_heatCurlMomentum_initial_bound
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ t ∈ Ioo 0 T,
      |backwardHeatCurlMomentum κ τ x₀ a u t -
        backwardHeatCurlMomentum κ τ x₀ a u 0| ≤ W * t := by
  obtain ⟨W, hW, hbound⟩ :=
    SolvesBefore.exists_uniformBound_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
      hT hsol hκ hτ x₀ a
  have hmod (R : ℝ) : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ioo 0 T,
      |testedMomentum (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u t -
        testedMomentum (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s| ≤
          W * |t-s| := by
    have hordered : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ioo 0 T, s ≤ t →
        |testedMomentum (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u t -
          testedMomentum (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u s| ≤
            W * |t-s| := by
      intro s hs t ht hst
      rw [solvesBefore_lerayWeakEvolution_timeIntegrated hT hsol _ hs.1 hst ht.2]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun z => lerayWeakRhs ν
          (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u z)
        (a := s) (b := t) (C := W) (fun z hz => by
          rw [uIoc_of_le hst] at hz
          simpa only [Real.norm_eq_abs] using
            hbound R (hs.1.le.trans hz.1.le) (hz.2.trans_lt ht.2))
      simpa only [Real.norm_eq_abs] using hb
    intro s hs t ht
    rcases le_total s t with hst | hts
    · exact hordered s hs t ht hst
    · simpa only [abs_sub_comm] using hordered t ht s hs hts
  refine ⟨W, hW, ?_⟩
  intro t ht
  have hlim := SolvesBefore.tendsto_compactBackwardHeatCurlTest_testedMomentum_sub
    hsol (ta := 0) le_rfl hT ht.1.le ht.2 hκ hτ x₀ a
  apply le_of_tendsto' hlim.abs
  intro R
  exact initial_bound_of_continuousOn hT
    (SolvesBefore.continuousOn_testedMomentum hsol _) (hmod R) ht

/-- The initial trace equals the Gaussian curl pairing of the prescribed
velocity, rather than an unspecified scalar completion. -/
theorem SolvesBefore.tendsto_heatCurlMomentum_initial
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    Tendsto (backwardHeatCurlMomentum κ τ x₀ a u) (𝓝[>] 0)
      (𝓝 (backwardHeatCurlMomentum κ τ x₀ a u 0)) := by
  obtain ⟨W, _hW, hb⟩ :=
    SolvesBefore.exists_heatCurlMomentum_initial_bound hT hsol hκ hτ x₀ a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hi : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_
    (by simpa using hi.const_mul W)
  filter_upwards [Ioo_mem_nhdsGT hT] with t ht
  simpa only [Real.dist_eq] using hb t ht

/-- The actual weak right-hand side is integrable across the full interval,
including both time endpoints without assumptions on its endpoint values. -/
theorem SolvesBefore.intervalIntegrable_heatCurlRhs_closed
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    IntervalIntegrable (backwardHeatCurlRhs ν κ τ x₀ a u) volume 0 T := by
  obtain ⟨W, _hW, hbound⟩ :=
    SolvesBefore.exists_uniformBound_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
      hT hsol hκ hτ x₀ a
  have hcont : ∀ R : ℝ, ContinuousOn (fun t =>
      lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u t)
      (Ioo 0 T) := by
    intro R t ht
    have ht0 : 0 < t := ht.1
    have hc :=
      SolvesBefore.continuousOn_lerayWeakRhs_atTopCompactBackwardHeatCurlTest
        hT hsol (ta := t / 2) (tb := (t + T) / 2)
        (by linarith) (by linarith) (by linarith [ht.2])
        R κ τ x₀ a
    exact (hc.continuousAt (Icc_mem_nhds (by linarith)
      (by linarith [ht.2]))).continuousWithinAt
  have hlim : ∀ᵐ t ∂volume.restrict (Ioo 0 T), Tendsto (fun R : ℝ =>
      lerayWeakRhs ν (atTopCompactBackwardHeatCurlTest R κ τ x₀ a) u t)
      atTop (𝓝 (backwardHeatCurlRhs ν κ τ x₀ a u t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact SolvesBefore.tendsto_compactBackwardHeatCurlTest_lerayWeakRhs
      hsol (ht.1.le) ht.2 hκ hτ x₀ a
  have hmeas := aestronglyMeasurable_of_tendsto_ae (atTop : Filter ℝ)
    (fun R => (hcont R).aestronglyMeasurable measurableSet_Ioo) hlim
  have hnorm : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      ‖backwardHeatCurlRhs ν κ τ x₀ a u t‖ ≤ W := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hlim] with t ht htl
    exact le_of_tendsto' htl.norm (fun R => by
      simpa only [Real.norm_eq_abs] using
        hbound R (ht.1.le) ht.2)
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr
  exact (integrable_const W).mono' hmeas hnorm

/-- The actual initial pairing and the constructed terminal trace satisfy
the heat-curl weak evolution on every interval `[s,T]`, including `s = 0`. -/
theorem SolvesBefore.exists_closed_heatCurlEvolution_integral
    {ν T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT : 0 < T) (hsol : SolvesBefore ν T u p)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space) :
    ∃ W L : ℝ, 0 ≤ W ∧
      Tendsto (backwardHeatCurlMomentum κ τ x₀ a u) (𝓝[<] T) (𝓝 L) ∧
      Tendsto (backwardHeatCurlMomentum κ τ x₀ a u) (𝓝[>] 0)
        (𝓝 (backwardHeatCurlMomentum κ τ x₀ a u 0)) ∧
      ∀ s ∈ Ico 0 T,
        |L - backwardHeatCurlMomentum κ τ x₀ a u s| ≤ W * (T - s) ∧
        IntervalIntegrable (backwardHeatCurlRhs ν κ τ x₀ a u) volume s T ∧
        (∫ r in s..T, backwardHeatCurlRhs ν κ τ x₀ a u r) =
          L - backwardHeatCurlMomentum κ τ x₀ a u s := by
  obtain ⟨W, L, hW, hL, hevol⟩ :=
    SolvesBefore.exists_terminal_heatCurlEvolution_integral hT hsol hκ hτ x₀ a
  have hM := SolvesBefore.tendsto_heatCurlMomentum_initial hT hsol hκ hτ x₀ a
  have hi := SolvesBefore.intervalIntegrable_heatCurlRhs_closed hT hsol hκ hτ x₀ a
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hleft : Tendsto (fun s => |L - backwardHeatCurlMomentum κ τ x₀ a u s|)
      (𝓝[>] 0) (𝓝 |L - backwardHeatCurlMomentum κ τ x₀ a u 0|) :=
    (tendsto_const_nhds.sub hM).abs
  have hright : Tendsto (fun s : ℝ => W * (T-s)) (𝓝[>] 0) (𝓝 (W*T)) := by
    simpa using ((tendsto_const_nhds (x := T)).sub hid).const_mul W
  have herr0 : |L - backwardHeatCurlMomentum κ τ x₀ a u 0| ≤ W*T :=
    le_of_tendsto_of_tendsto hleft hright (by
      filter_upwards [Ioo_mem_nhdsGT hT] with s hs
      exact (hevol s hs).1)
  have hc : ContinuousOn (fun s => ∫ r in s..T,
      backwardHeatCurlRhs ν κ τ x₀ a u r) (uIcc 0 T) := by
    apply intervalIntegral.continuousOn_primitive_interval_left
    simpa only [uIcc_of_le hT.le] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp hi
  have hm : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝[uIcc 0 T] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hid, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    simpa only [uIcc_of_le hT.le] using ⟨hs.1.le, hs.2.le⟩
  have hlim : Tendsto (fun s => ∫ r in s..T,
      backwardHeatCurlRhs ν κ τ x₀ a u r) (𝓝[>] 0)
      (𝓝 (L - backwardHeatCurlMomentum κ τ x₀ a u 0)) := by
    apply (tendsto_const_nhds.sub hM).congr'
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    exact (hevol s hs).2.2.symm
  have heq := tendsto_nhds_unique ((hc 0 left_mem_uIcc).tendsto.comp hm) hlim
  refine ⟨W, L, hW, hL, hM, ?_⟩
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    exact ⟨by simpa using herr0, hi, heq⟩
  · exact hevol s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩

end Navier.Analysis.WholeSpaceHeatCurlClosedEvolution

#print axioms Navier.Analysis.WholeSpaceHeatCurlClosedEvolution.SolvesBefore.continuousOn_testedMomentum
#print axioms Navier.Analysis.WholeSpaceHeatCurlClosedEvolution.SolvesBefore.exists_heatCurlMomentum_initial_bound
#print axioms Navier.Analysis.WholeSpaceHeatCurlClosedEvolution.SolvesBefore.tendsto_heatCurlMomentum_initial

#print axioms Navier.Analysis.WholeSpaceHeatCurlClosedEvolution.SolvesBefore.intervalIntegrable_heatCurlRhs_closed
#print axioms Navier.Analysis.WholeSpaceHeatCurlClosedEvolution.SolvesBefore.exists_closed_heatCurlEvolution_integral
