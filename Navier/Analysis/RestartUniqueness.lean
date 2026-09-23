import Navier.Analysis.RegularUniqueness
import Navier.Analysis.RegularRestart

/-!
# Uniqueness from a restart time

A restart strip `SolvesFrom ν T₀ L w q` that lies in `R` on its strip
(`RegularOnCompactsFrom T₀ L w q`) and starts from the slice `u T₀` of an energy-class
solution `u` in `R` on `[0, T)` coincides with `u` on `[T₀, min T (T₀ + L))`.

Route: shift time by `T₀` so both fields become energy-class solutions
(`SolClass`, equation at interior times only) on `[0, min T (T₀ + L) - T₀)`, then apply
`RegularUniqueness.uniqueness_class`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Navier.Analysis.RestartUniqueness

open Navier Navier.Breakdown Navier.Analysis.RegularUniqueness Navier.Analysis.ClassDecomposition
open Navier.Analysis.RestartPaste Navier.Analysis.RegularRestart
open Navier.Analysis.CriticalControlDecomposition

/-- Time translation of an evolution by `a`. -/
def shiftE {α : Type*} (a : ℝ) (u : ℝ → α) : ℝ → α := fun s => u (s + a)

/-- Smoothness on the strip `[T₀, T₀ + L)` transports to `[0, L)` after the shift. -/
theorem smooth_shift {T₀ L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → Space → E}
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Ico T₀ (T₀ + L) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => shiftE T₀ v z.1 z.2) (spacetimeBefore L) := by
  refine hv.comp (((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn) ?_
  rintro ⟨a, _⟩ ⟨⟨ha1, ha2⟩, -⟩
  exact ⟨⟨by simp only; linarith, by simp only; linarith⟩, mem_univ _⟩

/-- Restriction of `[0, T)`-smoothness to a strip inside it. -/
theorem strip_of_before {T T₀ L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → Space → E} (hT₀ : 0 ≤ T₀) (hL : T₀ + L ≤ T)
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (spacetimeBefore T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Ico T₀ (T₀ + L) ×ˢ univ) :=
  hv.mono (prod_mono (fun _ hr => ⟨hT₀.trans hr.1, lt_of_lt_of_le hr.2 hL⟩) subset_rfl)

/-- The time derivative commutes with the shift at interior strip times. -/
theorem timeDerivative_shiftE {T₀ L t : ℝ} {v : VelocityEvolution} (hT₀ : 0 ≤ T₀)
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Ico T₀ (T₀ + L) ×ˢ univ))
    (ht : t ∈ Ioo (0 : ℝ) L) (x : Space) :
    timeDerivative (shiftE T₀ v) t x = timeDerivative v (t + T₀) x := by
  have hs : SmoothVelocityBefore L (shiftE T₀ v) := smooth_shift hv
  have hd := hasDerivAt_tD hs ht x
  rw [timeDerivative_eq_tD hs ht x]
  have hd' : HasDerivAt (fun r => v r x) (tD (shiftE T₀ v) t x) (t + T₀) := by
    have h2 := HasDerivAt.comp_sub_const (t + T₀) T₀ (by rw [add_sub_cancel_right]; exact hd)
    simpa [shiftE, sub_add_cancel] using h2
  exact (hd'.hasDerivWithinAt (s := Ici (0 : ℝ)) |>.derivWithin
    (uniqueDiffOn_Ici 0 _ (by have := ht.1; show (0 : ℝ) ≤ t + T₀; linarith))).symm

/-- **Shifted strips are energy-class solutions.** -/
theorem solClass_shift {ν T₀ L E0 : ℝ} {v : VelocityEvolution} {q : PressureEvolution}
    (hT₀ : 0 ≤ T₀)
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Ico T₀ (T₀ + L) ×ˢ univ))
    (hq : ContDiffOn ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) (Ico T₀ (T₀ + L) ×ˢ univ))
    (hinc : ∀ t : ℝ, T₀ < t → t < T₀ + L → ∀ x : Space, ∑ i : Fin 3, pd (v t) i i x = 0)
    (heqn : ∀ t : ℝ, T₀ < t → t < T₀ + L → ∀ x : Space,
      timeDerivative v t x = ν • lapF (v t) x - gradF (q t) x - fderiv ℝ (v t) x (v t x))
    (hfe : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → Integrable (fun x : Space => ‖v t x‖ ^ 2))
    (hebd : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → kineticEnergy v t ≤ E0) :
    SolClass ν L (shiftE T₀ v) (shiftE T₀ q) E0 where
  smooth := smooth_shift hv
  psmooth := smooth_shift hq
  inc t ht htL x := hinc (t + T₀) (by linarith) (by linarith) x
  eqn t ht htL x := by
    rw [timeDerivative_shiftE hT₀ hv ⟨ht, htL⟩ x]
    exact heqn (t + T₀) (by linarith) (by linarith) x
  fe t ht htL := hfe (t + T₀) (by linarith) (by linarith)
  ebd t ht htL := hebd (t + T₀) (by linarith) (by linarith)

/-- A restart strip, shifted to start at `0`, is an energy-class solution. -/
theorem solClass_of_solvesFrom {ν T₀ L L' : ℝ} {w : VelocityEvolution} {q : PressureEvolution}
    (hT₀ : 0 ≤ T₀) (hL' : L' ≤ L) (hw : SolvesFrom ν T₀ L w q) :
    SolClass ν L' (shiftE T₀ w) (shiftE T₀ q) (kineticEnergy w T₀) := by
  have hsub : Ico T₀ (T₀ + L') ×ˢ (univ : Set Space) ⊆ Ico T₀ (T₀ + L) ×ˢ univ :=
    prod_mono (Ico_subset_Ico_right (by linarith)) subset_rfl
  refine solClass_shift hT₀ (hw.vel_smooth.mono hsub) (hw.pres_smooth.mono hsub)
    (fun t ht htL x => hw.incompressible t ht.le (by linarith) x)
    (fun t ht htL x => ?_)
    (fun t ht htL => hw.finite_energy t ht (by linarith))
    (fun t ht htL => hw.energy_le_start t ht (by linarith))
  have h := hw.equation t ht (by linarith) x
  have h' : timeDerivative w t x = ν • laplacian w t x - pressureGradient q t x -
      convection w t x := by rw [← h]; abel
  exact h'

/-- The tail of an energy-class solution, shifted to start at `0`, is energy class. -/
theorem solClass_tail {ν T T₀ L E : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hT₀ : 0 ≤ T₀) (hL : T₀ + L ≤ T) (hu : SolClass ν T u p E) :
    SolClass ν L (shiftE T₀ u) (shiftE T₀ p) E :=
  solClass_shift hT₀ (strip_of_before hT₀ hL hu.smooth) (strip_of_before hT₀ hL hu.psmooth)
    (fun t ht htL x => hu.inc t (by linarith) (by linarith) x)
    (fun t ht htL x => hu.eqn t (by linarith) (by linarith) x)
    (fun t ht htL => hu.fe t (by linarith) (by linarith))
    (fun t ht htL => hu.ebd t (by linarith) (by linarith))

/-- `R`-slices transport through the shift at interior strip times. -/
theorem rslice_shift {K T₀ L r : ℝ} {v : VelocityEvolution} {q : PressureEvolution}
    (hT₀ : 0 ≤ T₀)
    (hv : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (Ico T₀ (T₀ + L) ×ˢ univ))
    (hr : r ∈ Ioo (0 : ℝ) L) (h : Rslice K v q (r + T₀)) :
    Rslice K (shiftE T₀ v) (shiftE T₀ q) r := by
  have hfun : (fun x : Space => ‖timeDerivative (shiftE T₀ v) r x‖ ^ 2) =
      fun x => ‖timeDerivative v (r + T₀) x‖ ^ 2 := by
    funext x; rw [timeDerivative_shiftE hT₀ hv hr x]
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1, h.2.2.2.2⟩
  show TimeSlice K (shiftE T₀ v) r
  unfold TimeSlice
  rw [hfun]
  exact h.2.2.1

/-- **Uniqueness from a restart time.**  An `R`-strip from `T₀` that starts at the
slice `u T₀` of an energy-class `R`-solution `u` on `[0, T)` coincides with `u` on
`[T₀, min T (T₀ + L))`. -/
theorem uniqueness_from {ν T T₀ L Eu : ℝ} (hν : 0 < ν) {u w : VelocityEvolution}
    {p q : PressureEvolution} (hT₀ : 0 ≤ T₀) (hu : SolClass ν T u p Eu)
    (hRu : RegularOnCompacts T u p) (hw : SolvesFrom ν T₀ L w q)
    (hRw : RegularOnCompactsFrom T₀ L w q) (h0 : w T₀ = u T₀) :
    ∀ t : ℝ, T₀ ≤ t → t < min T (T₀ + L) → w t = u t := by
  intro t ht htM
  set M : ℝ := min T (T₀ + L) with hM
  have hMT : M ≤ T := min_le_left _ _
  have hML : M ≤ T₀ + L := min_le_right _ _
  set L' : ℝ := M - T₀ with hL'
  set S : ℝ := (t + M) / 2 - T₀ with hS
  have hSL : S < L' := by rw [hS, hL']; linarith
  have htS : t - T₀ ≤ S := by rw [hS]; linarith
  obtain ⟨Ku, hKu⟩ := hRu (S + T₀) (by linarith)
  obtain ⟨Kw, hKw⟩ := hRw (S + T₀) (by linarith)
  set K : ℝ := max Ku Kw
  have hwL : ContDiffOn ℝ ∞ (fun z : ℝ × Space => w z.1 z.2) (Ico T₀ (T₀ + L') ×ˢ univ) :=
    hw.vel_smooth.mono (prod_mono (Ico_subset_Ico_right (by linarith)) subset_rfl)
  have huL : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Ico T₀ (T₀ + L') ×ˢ univ) :=
    strip_of_before hT₀ (by linarith) hu.smooth
  have hK0 : 0 ≤ K :=
    (norm_nonneg _).trans ((hKw T₀ ⟨le_rfl, by linarith⟩).2.2.2.1.1 0 |>.trans
      (le_max_right _ _))
  have hR : ∀ r ∈ Ioc (0 : ℝ) S, Rslice K (shiftE T₀ w) (shiftE T₀ q) r ∧
      Rslice K (shiftE T₀ u) (shiftE T₀ p) r := by
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) L' := ⟨hr.1, lt_of_le_of_lt hr.2 hSL⟩
    refine ⟨rslice_shift hT₀ hwL hr' ?_, rslice_shift hT₀ huL hr' ?_⟩
    · exact Rslice.mono (hKw (r + T₀) ⟨by linarith [hr.1], by linarith [hr.2]⟩)
        (le_max_right _ _)
    · exact Rslice.mono (hKu (r + T₀) ⟨by linarith [hr.1], by linarith [hr.2]⟩)
        (le_max_left _ _)
  have hcl := uniqueness_class hν (solClass_of_solvesFrom hT₀ (by linarith) hw)
    (solClass_tail hT₀ (by linarith) hu) hSL hK0 hR
    (by show w (0 + T₀) = u (0 + T₀); rw [zero_add]; exact h0) (t - T₀) ⟨by linarith, htS⟩
  simpa [shiftE, sub_add_cancel] using hcl

/-- The same for a `SolvesBefore` base solution. -/
theorem uniqueness_from_solvesBefore {ν T T₀ L : ℝ} (hν : 0 < ν) {u w : VelocityEvolution}
    {p q : PressureEvolution} (hT₀ : 0 ≤ T₀) (hu : SolvesBefore ν T u p)
    (hRu : RegularOnCompacts T u p) (hw : SolvesFrom ν T₀ L w q)
    (hRw : RegularOnCompactsFrom T₀ L w q) (h0 : w T₀ = u T₀) :
    ∀ t : ℝ, T₀ ≤ t → t < min T (T₀ + L) → w t = u t :=
  uniqueness_from hν hT₀ (SolClass.of_solvesBefore hu) hRu hw hRw h0

end Navier.Analysis.RestartUniqueness

#print axioms Navier.Analysis.RestartUniqueness.uniqueness_from
#print axioms Navier.Analysis.RestartUniqueness.uniqueness_from_solvesBefore
#print axioms Navier.Analysis.RegularUniqueness.uniqueness_class
#print axioms Navier.Analysis.RegularUniqueness.uniqueness_R
