/-
The compact-support jet arguments adapt CompactSpatialForceDecay.lean from
OpenAI/NavierStokesAndEuler, revision 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538.
Apache-2.0: references/licenses/OpenAI-Apache-2.0.txt.
Changes: native Pi carrier, natural polynomial weights, original force predicate.
-/
import Navier.Breakdown.CompactSmoothForce

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace Navier.Breakdown.CompactFutureForce

private theorem jet_zero_outside {S : Set Space} (hS : IsClosed S) {f : ForceField}
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, x ∉ S → f t x = 0)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) {x : Space} (hx : x ∉ S) :
    iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x) = 0 := by
  have he : (fun z : ℝ × Space => f z.1 z.2) =ᶠ[𝓝[nonnegativeSpacetime] (t, x)]
      (fun _ => 0) := by
    have hn : {z : ℝ × Space | z.2 ∉ S} ∈ 𝓝 (t, x) :=
      (hS.isOpen_compl.preimage continuous_snd).mem_nhds hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with z hz hd
    exact hs z.1 hd.1 z.2 hz
  simpa using he.iteratedFDerivWithin_eq (hs t ht x hx) n (𝕜 := ℝ)

private theorem jet_zero_after {f : ForceField} {T : ℝ}
    (hs : ∀ t : ℝ, T ≤ t → ∀ x : Space, f t x = 0)
    (n : ℕ) {t : ℝ} (ht : T < t) (x : Space) :
    iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
      nonnegativeSpacetime (t, x) = 0 := by
  have he : (fun z : ℝ × Space => f z.1 z.2) =ᶠ[𝓝[nonnegativeSpacetime] (t, x)]
      (fun _ => 0) := by
    have hn : {z : ℝ × Space | T < z.1} ∈ 𝓝 (t, x) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds ht
    filter_upwards [mem_nhdsWithin_of_mem_nhds hn] with z hz
    exact hs z.1 hz.le z.2
  simpa using he.iteratedFDerivWithin_eq (hs t ht.le x) n (𝕜 := ℝ)

/-- The force actually produced on physical time needs no smooth extension to
negative time: compact space and future-time support bound every native jet. -/
theorem forcedDataRapidDecay_of_compactFutureSupport
    {f : ForceField} {S : Set Space} {T : ℝ}
    (hf : SmoothForceOnNonnegativeTime f) (hS : IsCompact S)
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, x ∉ S → f t x = 0)
    (htime : ∀ t : ℝ, T ≤ t → ∀ x : Space, f t x = 0) :
    ForcedDataRapidDecay f := by
  refine ⟨hf, ?_⟩
  intro n K
  let J := iteratedFDerivWithin ℝ n (fun z : ℝ × Space => f z.1 z.2)
    nonnegativeSpacetime
  have hj : ContinuousOn J nonnegativeSpacetime :=
    hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast le_top)
      ((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ)
  have hsub : Icc (0 : ℝ) (T + 1) ×ˢ S ⊆ nonnegativeSpacetime :=
    fun _ h => ⟨h.1.1, mem_univ _⟩
  have hw : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖ + z.1) ^ K) := by
    fun_prop
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn
    (hw.continuousOn.mul ((hj.mono hsub).norm))
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ S
  · by_cases htt : t ≤ T + 1
    · have hb := hM (t, x) ⟨⟨ht, htt⟩, hx⟩
      exact (le_abs_self _).trans (hb.trans (le_max_left _ _))
    · rw [jet_zero_after htime n (by linarith) x, norm_zero, mul_zero]
      exact le_max_right _ _
  · rw [jet_zero_outside hS.isClosed hs n ht hx, norm_zero, mul_zero]
    exact le_max_right _ _

end Navier.Breakdown.CompactFutureForce

#print axioms Navier.Breakdown.CompactFutureForce.forcedDataRapidDecay_of_compactFutureSupport
