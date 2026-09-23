import Navier.Analysis.RestartPaste
import Navier.Analysis.WienerRegularity

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

/-- The `Ḣ¹ ∩ Ḣ² ∩ Ḣ³` bound `K` of a single slice. -/
def RegSlice (K : ℝ) (v : VelocityField) : Prop :=
  ∀ i j l : Fin 3,
    Integrable (fun x : Space => ‖fderiv ℝ v x (basisVector i)‖ ^ 2) ∧
    (∫ x : Space, ‖fderiv ℝ v x (basisVector i)‖ ^ 2) ≤ K ∧
    Integrable (fun x : Space =>
      ‖fderiv ℝ (fun y => fderiv ℝ v y (basisVector i)) x (basisVector j)‖ ^ 2) ∧
    (∫ x : Space, ‖fderiv ℝ (fun y => fderiv ℝ v y (basisVector i)) x (basisVector j)‖ ^ 2)
      ≤ K ∧
    Integrable (fun x : Space =>
      ‖fderiv ℝ (fun z => fderiv ℝ (fun y => fderiv ℝ v y (basisVector i)) z
        (basisVector j)) x (basisVector l)‖ ^ 2) ∧
    (∫ x : Space, ‖fderiv ℝ (fun z => fderiv ℝ (fun y => fderiv ℝ v y (basisVector i)) z
        (basisVector j)) x (basisVector l)‖ ^ 2) ≤ K

theorem RegSlice.mono {K K' : ℝ} {v : VelocityField} (h : RegSlice K v) (hK : K ≤ K') :
    RegSlice K' v := fun i j l => by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h i j l
  exact ⟨a1, a2.trans hK, a3, a4.trans hK, a5, a6.trans hK⟩

theorem regularOnCompacts_iff (T : ℝ) (u : VelocityEvolution) :
    RegularOnCompacts T u ↔
      ∀ T' : ℝ, T' < T → ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) T', RegSlice K (u t) := Iff.rfl

/-- R on a restart strip `[T₀, T₀ + L)`. -/
def RegularOnCompactsFrom (T₀ L : ℝ) (w : VelocityEvolution) : Prop :=
  ∀ T' : ℝ, T' < T₀ + L → ∃ K : ℝ, ∀ t ∈ Icc T₀ T', RegSlice K (w t)

/-- **Gluing preserves R.** -/
theorem regularOnCompacts_glue {T T₀ h : ℝ} {u w : VelocityEvolution}
    (hT₀T : T₀ < T) (hR : RegularOnCompacts T u)
    (hRw : RegularOnCompactsFrom T₀ (T - T₀ + h) w)
    (hagree : ∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) :
    RegularOnCompacts (T + h) (fun t => if t < T then u t else w t) := by
  intro T' hT'
  set m : ℝ := (T₀ + T) / 2 with hm
  have hmT : m < T := by rw [hm]; linarith
  have hT₀m : T₀ < m := by rw [hm]; linarith
  obtain ⟨K₁, hK₁⟩ := (regularOnCompacts_iff T u).mp hR m hmT
  obtain ⟨K₂, hK₂⟩ := hRw T' (by linarith)
  refine ⟨max K₁ K₂, fun t ht => ?_⟩
  rcases le_or_gt t m with htm | htm
  · have hu : (fun t => if t < T then u t else w t) t = u t := if_pos (by linarith)
    rw [hu]
    exact (hK₁ t ⟨ht.1, htm⟩).mono (le_max_left _ _)
  · have hw : (fun t => if t < T then u t else w t) t = w t := by
      by_cases htT : t < T
      · simp only [if_pos htT]; exact hagree t (by linarith) htT
      · exact if_neg htT
    rw [hw]
    exact (hK₂ t ⟨by linarith, ht.2⟩).mono (le_max_right _ _)

/-- **The R-restart leaf**: the restart is requested only from R-solutions and
must return an R-strip. -/
def DatumHorizonIndependentRestartR (N : CriticalQuantity) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
    ∀ M : ℝ≥0, ∃ h : ℝ, 0 < h ∧
      ∀ T : ℝ, 0 < T → ∀ u : VelocityEvolution, ∀ p : PressureEvolution,
        (∀ x : Space, u 0 x = u₀ x) → SolvesBefore ν T u p → RegularOnCompacts T u →
        PressureNormalizedBefore T p → N T u ≤ (M : ℝ≥0∞) →
        ∃ T₀ : ℝ, 0 ≤ T₀ ∧ T₀ < T ∧ ∃ w : VelocityEvolution, ∃ q : PressureEvolution,
          (∀ t : ℝ, T₀ ≤ t → t < T → u t = w t) ∧
          (∀ t : ℝ, T₀ ≤ t → t < T → p t = q t) ∧
          SolvesFrom ν T₀ (T - T₀ + h) w q ∧
          RegularOnCompactsFrom T₀ (T - T₀ + h) w ∧
          (∀ t : ℝ, T₀ ≤ t → t < T + h → q t 0 = 0)

/-- **The R-restart leaf implies the R continuation leaf.** -/
theorem datumContinuationR_of_datumRestartR {N : CriticalQuantity}
    (hN : DatumHorizonIndependentRestartR N) : DatumContinuationIn RegularOnCompacts N := by
  intro ν hν u₀ hu₀ M
  obtain ⟨h, hh, heng⟩ := hN ν hν u₀ hu₀ M
  refine ⟨h, hh, fun T hT u p hinit hsol hR hnorm hNbound => ?_⟩
  obtain ⟨T₀, hT₀, hT₀T, w, q, hv, hp, hw, hRw, hq⟩ :=
    heng T hT u p hinit hsol hR hnorm hNbound
  obtain ⟨u', p', h1, h2, h3, h4, hform⟩ :=
    restart_paste_explicit hT₀ hT₀T hh hsol hnorm hw hq hv hp
  have hu' : u' = fun t => if t < T then u t else w t := funext hform
  refine ⟨u', p', h1, ?_, h2, h3, h4⟩
  rw [hu']
  exact regularOnCompacts_glue hT₀T hR hRw hv

/-- **The crown from the two R-leaves** (restart and a priori), local existence
being discharged in R. -/
theorem wholeSpaceGlobalRegularity_of_R_restart_apriori (N : CriticalQuantity)
    (hrestart : DatumHorizonIndependentRestartR N)
    (hapriori : APrioriIn RegularOnCompacts N) :
    ProblemStatements.WholeSpaceGlobalRegularity :=
  Navier.Analysis.WienerRegularity.wholeSpaceGlobalRegularity_of_R_leaves N
    (datumContinuationR_of_datumRestartR hrestart) hapriori

end Navier.Analysis.RegularRestart

set_option pp.fullNames true in
#check @Navier.Analysis.RegularRestart.wholeSpaceGlobalRegularity_of_R_restart_apriori
set_option pp.fullNames true in
#print axioms Navier.Analysis.RegularRestart.wholeSpaceGlobalRegularity_of_R_restart_apriori
