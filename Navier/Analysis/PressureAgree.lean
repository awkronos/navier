import Navier.Analysis.RestartPaste

/-!
# Normalized pressures of agreeing solutions agree

If a solution `(u, p)` on `[0, T)` and a restart strip `(w, q)` from `T₀` have the same
velocity on `[T₀, T)` and both pressures are normalized (`p t 0 = 0 = q t 0`), then
`p = q` on `[T₀, T)` (`pressure_agree`).  Interior times: the two equations share every
velocity term, so `∇p = ∇q`, and a smooth function with zero gradient is constant.
The start time `T₀`: joint continuity of both pressures from the right.

This supplies the pressure-agreement hypothesis of `RestartPaste.restart_paste_explicit`
and of the `R`-restart leaf from velocity agreement alone (velocity agreement comes from
`RestartUniqueness.uniqueness_from`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Navier.Analysis.PressureAgree

open Navier Navier.Breakdown
open Navier.Analysis.RestartPaste
open Navier.Analysis.CriticalControlDecomposition

theorem timeDerivative_congr_nhds {u v : VelocityEvolution} {t : ℝ}
    (h : ∀ᶠ s in 𝓝 t, u s = v s) (x : Space) :
    timeDerivative u t x = timeDerivative v t x := by
  have hev : (fun s : ℝ => u s x) =ᶠ[nhdsWithin t (Set.Ici (0 : ℝ))] fun s : ℝ => v s x :=
    (h.filter_mono nhdsWithin_le_nhds).mono fun s hs => congrFun hs x
  simpa [timeDerivative] using congrArg (fun L : ℝ →L[ℝ] Space => L 1)
    (Filter.EventuallyEq.fderivWithin_eq hev (congrFun h.self_of_nhds x))

/-- Slices of a jointly smooth scalar field are differentiable. -/
theorem differentiable_slice {S : Set ℝ} {p : PressureEvolution}
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (S ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ S) : Differentiable ℝ (p t) := by
  have h : ContDiff ℝ ∞ (p t) := by
    rw [← contDiffOn_univ]
    exact hp.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun y _ => ⟨ht, mem_univ _⟩
  exact h.differentiable (by simp)

/-- Equal pressure gradients and equal values at the origin give equal slices. -/
theorem eq_of_gradient_eq {P Q : Space → ℝ} (hP : Differentiable ℝ P)
    (hQ : Differentiable ℝ Q) (hg : ∀ x (i : Fin 3), fderiv ℝ P x (basisVector i) =
      fderiv ℝ Q x (basisVector i)) (h0 : P 0 = Q 0) : P = Q := by
  have hD : Differentiable ℝ (fun x => P x - Q x) := hP.sub hQ
  have hz : ∀ x, fderiv ℝ (fun x => P x - Q x) x = 0 := by
    intro x
    rw [fderiv_fun_sub (hP x) (hQ x)]
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : v = ∑ i : Fin 3, v i • basisVector i := by
      funext k
      simp [basisVector, Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum, zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, ContinuousLinearMap.sub_apply, hg x i, sub_self, smul_zero]
  have hc := is_const_of_fderiv_eq_zero hD hz
  funext x
  have h1 : P x - Q x = P 0 - Q 0 := hc x 0
  linarith

/-- **Normalized pressures of agreeing solutions agree.** -/
theorem pressure_agree {ν T T₀ L : ℝ} {u w : VelocityEvolution} {p q : PressureEvolution}
    (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T) (hTL : T ≤ T₀ + L) (hsol : SolvesBefore ν T u p)
    (hnorm : PressureNormalizedBefore T p) (hw : SolvesFrom ν T₀ L w q)
    (hqn : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → q t 0 = 0)
    (hagree : ∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) :
    ∀ t : ℝ, T₀ ≤ t → t < T → p t = q t := by
  obtain ⟨-, hps, -, heq⟩ := hsol.classical
  -- interior times
  have hint : ∀ t : ℝ, T₀ < t → t < T → p t = q t := by
    intro t ht1 ht2
    have hev : ∀ᶠ s in 𝓝 t, u s = w s :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht2) fun s hs => hagree s hs.1.le hs.2
    have hgrad : ∀ x (i : Fin 3), fderiv ℝ (p t) x (basisVector i) =
        fderiv ℝ (q t) x (basisVector i) := by
      intro x i
      have e1 := heq t (hT₀.trans ht1.le) ht2 x
      have e2 := hw.equation t ht1 (by linarith) x
      have hut : u t = w t := hagree t ht1.le ht2
      have htd := timeDerivative_congr_nhds hev x
      have hc : convection u t x = convection w t x := by
        unfold convection spatialDerivative; rw [hut]
      have hl : laplacian u t x = laplacian w t x := by unfold laplacian; rw [hut]
      rw [show zeroForce t x = (0 : Space) from rfl, add_zero] at e1
      have hpg : pressureGradient p t x = pressureGradient q t x := by
        have : ν • laplacian u t x - pressureGradient p t x =
            ν • laplacian w t x - pressureGradient q t x := by
          rw [← e1, ← e2, htd, hc]
        rw [hl] at this
        exact sub_right_injective this
      exact congrFun hpg i
    exact eq_of_gradient_eq (differentiable_slice hps ⟨hT₀.trans ht1.le, ht2⟩)
      (differentiable_slice hw.pres_smooth ⟨ht1.le, by linarith⟩) hgrad
      ((hnorm t (hT₀.trans ht1.le) ht2).trans (hqn t ht1.le (by linarith)).symm)
  intro t ht1 ht2
  rcases ht1.lt_or_eq with hlt | heq0
  · exact hint t hlt ht2
  subst heq0
  funext x
  -- right continuity at the start
  have hpc : ContinuousWithinAt (fun s => p s x) (Ioo T₀ T) T₀ := by
    have h1 : ContinuousWithinAt (fun z : ℝ × Space => p z.1 z.2)
        (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) (T₀, x) :=
      (hps.continuousOn) (T₀, x) ⟨⟨hT₀, hT₀T⟩, mem_univ _⟩
    have hm : ContinuousWithinAt (fun s : ℝ => ((s, x) : ℝ × Space)) (Ioo T₀ T) T₀ :=
      (continuous_id.prodMk continuous_const).continuousWithinAt
    have hmap : MapsTo (fun s : ℝ => ((s, x) : ℝ × Space)) (Ioo T₀ T)
        (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
      fun s hs => ⟨⟨hT₀.trans hs.1.le, hs.2⟩, mem_univ _⟩
    exact ContinuousWithinAt.comp (g := fun z : ℝ × Space => p z.1 z.2)
      (f := fun s : ℝ => ((s, x) : ℝ × Space)) h1 hm hmap
  have hqc : ContinuousWithinAt (fun s => q s x) (Ioo T₀ T) T₀ := by
    have h1 : ContinuousWithinAt (fun z : ℝ × Space => q z.1 z.2)
        (Ico T₀ (T₀ + L) ×ˢ (univ : Set Space)) (T₀, x) :=
      (hw.pres_smooth.continuousOn) (T₀, x) ⟨⟨le_rfl, by linarith⟩, mem_univ _⟩
    have hm : ContinuousWithinAt (fun s : ℝ => ((s, x) : ℝ × Space)) (Ioo T₀ T) T₀ :=
      (continuous_id.prodMk continuous_const).continuousWithinAt
    have hmap : MapsTo (fun s : ℝ => ((s, x) : ℝ × Space)) (Ioo T₀ T)
        (Ico T₀ (T₀ + L) ×ˢ (univ : Set Space)) :=
      fun s hs => ⟨⟨hs.1.le, by linarith [hs.2]⟩, mem_univ _⟩
    exact ContinuousWithinAt.comp (g := fun z : ℝ × Space => q z.1 z.2)
      (f := fun s : ℝ => ((s, x) : ℝ × Space)) h1 hm hmap
  have hne : (𝓝[Ioo T₀ T] T₀).NeBot := left_nhdsWithin_Ioo_neBot hT₀T
  refine tendsto_nhds_unique_of_eventuallyEq hpc hqc ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact congrFun (hint s hs.1 hs.2) x

end Navier.Analysis.PressureAgree

set_option pp.fullNames true in
#print axioms Navier.Analysis.PressureAgree.pressure_agree
