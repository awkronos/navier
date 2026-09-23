import Navier.Analysis.RestartPaste
import Navier.Analysis.WienerRegularityFull

/-!
# The R-restart leaf and its gluing

`RegSlice K v` is the `Ḣ¹ ∩ Ḣ² ∩ Ḣ³` bound of a single velocity slice, so that
`RegularOnCompacts T u` is `∀ T' < T, ∃ K, ∀ t ∈ [0,T'], RegSlice K (u t)`.
`RegularOnCompactsFrom T₀ L w` is the same on the restart strip `[T₀, T₀ + L)`.

* `regularOnCompacts_glue`: pasting an R-solution on `[0,T)` with an R-strip on
  `[T₀, T + h)` that agrees with it on `[T₀, T)` gives an R-solution on `[0, T + h)`;
* `DatumHorizonIndependentRestartR N`: the R-version of the restart leaf
  (input in R, output strip in R);
* `datumContinuationR_of_datumRestartR`: it implies the R continuation leaf;
* `wholeSpaceGlobalRegularity_of_R_restart_apriori`: the crown from the R-restart
  and the R a priori leaves alone (local existence discharged).
OBLIGATION (2026-09-23): `R` now also carries `∇p ∈ H¹` and `∂ₜu ∈ L²` bounds,
and the R-restart leaf must RETURN an R-strip.  Any discharge of
`DatumHorizonIndependentRestartR` through local existence from `H³` data
(item 6) must therefore produce the pressure and `∂ₜu` bounds on the restart
strip as well, or the leaf would be unsatisfiable by that route.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Navier.Analysis.RegularRestart

open Navier Navier.Breakdown
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.RestartPaste

/-- R on a restart strip `[T₀, T₀ + L)` (velocity, pressure and `∂ₜ` slices). -/
def RegularOnCompactsFrom (T₀ L : ℝ) (w : VelocityEvolution) (q : PressureEvolution) : Prop :=
  ∀ T' : ℝ, T' < T₀ + L → ∃ K : ℝ, ∀ t ∈ Icc T₀ T',
    RegSlice K (w t) ∧ PresSlice K (q t) ∧ TimeSlice K w t

/-- **Gluing preserves R.** -/
theorem regularOnCompacts_glue {T T₀ h : ℝ} {u w : VelocityEvolution}
    {p q : PressureEvolution} (hT₀ : 0 ≤ T₀)
    (hT₀T : T₀ < T) (hR : RegularOnCompacts T u p)
    (hRw : RegularOnCompactsFrom T₀ (T - T₀ + h) w q)
    (hagree : ∀ t : ℝ, T₀ ≤ t → t < T → u t = w t)
    (hagreep : ∀ t : ℝ, T₀ ≤ t → t < T → p t = q t) :
    RegularOnCompacts (T + h) (fun t => if t < T then u t else w t)
      (fun t => if t < T then p t else q t) := by
  intro T' hT'
  set m : ℝ := (T₀ + T) / 2 with hm
  have hmT : m < T := by rw [hm]; linarith
  have hT₀m : T₀ < m := by rw [hm]; linarith
  obtain ⟨K₁, hK₁⟩ := hR m hmT
  obtain ⟨K₂, hK₂⟩ := hRw T' (by linarith)
  set u' : VelocityEvolution := fun t => if t < T then u t else w t
  have hu_on : ∀ s : ℝ, s < T → u' s = u s := fun s hs => if_pos hs
  have hw_on : ∀ s : ℝ, T₀ < s → u' s = w s := by
    intro s hs
    by_cases hsT : s < T
    · simp only [u', if_pos hsT]; exact hagree s hs.le hsT
    · exact if_neg hsT
  have hp_on : ∀ s : ℝ, s < T → (fun t => if t < T then p t else q t) s = p s :=
    fun s hs => if_pos hs
  have hq_on : ∀ s : ℝ, T₀ < s → (fun t => if t < T then p t else q t) s = q s := by
    intro s hs
    by_cases hsT : s < T
    · simp only [if_pos hsT]; exact hagreep s hs.le hsT
    · exact if_neg hsT
  have htd : ∀ (v : VelocityEvolution) (S : Set ℝ) (t : ℝ), IsOpen S → t ∈ S →
      (∀ s ∈ S, u' s = v s) → ∀ x, timeDerivative u' t x = timeDerivative v t x := by
    intro v S t hS ht hEq x
    have hev : (fun s : ℝ => u' s x) =ᶠ[nhdsWithin t (Set.Ici (0 : ℝ))] fun s => v s x := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hS.mem_nhds ht)] with s hs
      exact congrFun (hEq s hs) x
    simpa [timeDerivative] using
      congrArg (fun L : ℝ →L[ℝ] Space => L 1)
        (hev.fderivWithin_eq (congrFun (hEq t ht) x))
  refine ⟨max K₁ K₂, fun t ht => ?_⟩
  rcases le_or_gt t m with htm | htm
  · have htT : t < T := lt_of_le_of_lt htm hmT
    obtain ⟨a1, a2, a3⟩ := hK₁ t ⟨ht.1, htm⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hu_on t htT]; exact a1.mono (le_max_left _ _)
    · rw [hp_on t htT]; exact a2.mono (le_max_left _ _)
    · have e : ∀ x, timeDerivative u' t x = timeDerivative u t x :=
        htd u (Set.Iio T) t isOpen_Iio htT (fun s hs => hu_on s hs)
      refine (TimeSlice.mono ?_ (le_max_left _ _))
      simp only [TimeSlice, e]
      exact a3
  · have hT₀t : T₀ < t := lt_trans hT₀m htm
    obtain ⟨a1, a2, a3⟩ := hK₂ t ⟨hT₀t.le, ht.2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hw_on t hT₀t]; exact a1.mono (le_max_right _ _)
    · rw [hq_on t hT₀t]; exact a2.mono (le_max_right _ _)
    · have e : ∀ x, timeDerivative u' t x = timeDerivative w t x :=
        htd w (Set.Ioi T₀) t isOpen_Ioi hT₀t (fun s hs => hw_on s hs)
      refine (TimeSlice.mono ?_ (le_max_right _ _))
      simp only [TimeSlice, e]
      exact a3

/-- **The R-restart leaf**: the restart is requested only from R-solutions and
must return an R-strip. -/
def DatumHorizonIndependentRestartR (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ M : ℝ≥0, ∃ h : ℝ, 0 < h ∧
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → RegularOnCompacts T u p →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ T₀ : ℝ, 0 ≤ T₀ ∧ T₀ < T ∧ ∃ w : VelocityEvolution, ∃ q : PressureEvolution,
          (∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) ∧
          (∀ t : ℝ, T₀ ≤ t → t < T → p t = q t) ∧
          SolvesFrom ν T₀ (T - T₀ + h) w q ∧
          RegularOnCompactsFrom T₀ (T - T₀ + h) w q ∧
          (∀ t : ℝ, T₀ ≤ t → t < T + h → q t 0 = 0)

/-- **The R-restart leaf implies the R continuation leaf.** -/
theorem datumContinuationR_of_datumRestartR {N : CriticalQuantity}
    (hN : DatumHorizonIndependentRestartR N) : DatumContinuationIn RegularOnCompacts N := by
  intro ν hν u₀ hu₀ M
  obtain ⟨h, hh, heng⟩ := hN ν hν u₀ hu₀ M
  refine ⟨h, hh, fun T hT u p hinit hsol hR hnorm hNbound => ?_⟩
  obtain ⟨T₀, hT₀, hT₀T, w, q, hv, hp, hw, hRw, hq⟩ :=
    heng T hT u p hinit hsol hR hnorm hNbound
  obtain ⟨u', p', h1, h2, h3, h4, hform, hformp⟩ :=
    restart_paste_explicit hT₀ hT₀T hh hsol hnorm hw hq hv hp
  have hu' : u' = fun t => if t < T then u t else w t := funext hform
  have hp' : p' = fun t => if t < T then p t else q t := funext hformp
  refine ⟨u', p', h1, ?_, h2, h3, h4⟩
  rw [hu', hp']
  exact regularOnCompacts_glue hT₀ hT₀T hR hRw hv hp

/-- **The crown from the two R-leaves** (restart and a priori), local existence
being discharged in R. -/
theorem wholeSpaceGlobalRegularity_of_R_restart_apriori (N : CriticalQuantity)
    (hrestart : DatumHorizonIndependentRestartR N)
    (hapriori : APrioriIn RegularOnCompacts N) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  Navier.Analysis.WienerRegularityFull.wholeSpaceGlobalRegularity_of_R_leaves N
    (datumContinuationR_of_datumRestartR hrestart) hapriori

end Navier.Analysis.RegularRestart

set_option pp.fullNames true in
#check @Navier.Analysis.RegularRestart.wholeSpaceGlobalRegularity_of_R_restart_apriori
set_option pp.fullNames true in
#print axioms Navier.Analysis.RegularRestart.wholeSpaceGlobalRegularity_of_R_restart_apriori
