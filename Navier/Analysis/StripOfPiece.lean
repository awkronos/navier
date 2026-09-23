import Navier.Analysis.RestartUniqueness
import Navier.Analysis.PressureAgree

/-!
# A restart strip from a piece started at a slice

Given an `R`-solution `(u, p)` on `[0, T)` with normalized pressure, and a solution
`(v, q)` on `[0, L)` in `R` with normalized pressure, started at the slice
`v 0 = u T₀` (`T₀ < T ≤ T₀ + L`), the glued strip
`w t = if t < T then u t else v (t - T₀)` (and likewise the pressure) is a
`SolvesFrom` strip from `T₀` of length `L`, in `R` on the strip, with normalized
pressure, agreeing with `(u, p)` on `[T₀, T)` and with the translated piece on `[T₀, ∞)`
(`strip_of_piece`).

The glue (rather than the bare translate) makes the time-derivative clause of `R` hold
at the strip start `T₀` itself: there `w = u` on a one-sided neighbourhood.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Navier.Analysis.StripOfPiece

open Navier Navier.Breakdown
open Navier.Analysis.RestartPaste
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.ClassDecomposition
open Navier.Analysis.RegularRestart
open Navier.Analysis.RegularUniqueness
open Navier.Analysis.RestartUniqueness
open Navier.Analysis.PressureAgree

/-- **Uniqueness against a piece started at a slice.** -/
theorem uniqueness_piece {ν T T₀ L : ℝ} (hν : 0 < ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} (hT₀ : 0 ≤ T₀) (hu : SolvesBefore ν T u p)
    (hRu : RegularOnCompacts T u p) (hv : SolvesBefore ν L v q) (hRv : RegularOnCompacts L v q)
    (h0 : v 0 = u T₀) :
    ∀ t : ℝ, T₀ ≤ t → t < min T (T₀ + L) → v (t - T₀) = u t := by
  intro t ht htM
  set M : ℝ := min T (T₀ + L) with hM
  have hMT : M ≤ T := min_le_left _ _
  have hML : M ≤ T₀ + L := min_le_right _ _
  set L' : ℝ := M - T₀ with hL'
  set S : ℝ := (t + M) / 2 - T₀ with hS
  have hSL : S < L' := by rw [hS, hL']; linarith
  have htS : t - T₀ ≤ S := by rw [hS]; linarith
  obtain ⟨Ku, hKu⟩ := hRu (S + T₀) (by linarith)
  obtain ⟨Kv, hKv⟩ := hRv S (by linarith)
  set K : ℝ := max Ku Kv
  have huL : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) (Ico T₀ (T₀ + L') ×ˢ univ) :=
    strip_of_before hT₀ (by linarith) hu.classical.1
  have hK0 : 0 ≤ K :=
    (norm_nonneg _).trans ((hKu T₀ ⟨hT₀, by linarith⟩).2.2.2.1.1 0 |>.trans (le_max_left _ _))
  have hv0 : shiftE 0 v = v := funext fun s => by simp [shiftE]
  have hq0 : shiftE 0 q = q := funext fun s => by simp [shiftE]
  have hvc : SolClass ν L' v q (kineticEnergy v 0) := by
    have h := solClass_tail (T₀ := 0) le_rfl (by linarith : 0 + L' ≤ L) (SolClass.of_solvesBefore hv)
    rwa [hv0, hq0] at h
  have hR : ∀ r ∈ Ioc (0 : ℝ) S, Rslice K v q r ∧ Rslice K (shiftE T₀ u) (shiftE T₀ p) r := by
    intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) L' := ⟨hr.1, lt_of_le_of_lt hr.2 hSL⟩
    refine ⟨Rslice.mono (hKv r ⟨hr.1.le, hr.2⟩) (le_max_right _ _), rslice_shift hT₀ huL hr' ?_⟩
    exact Rslice.mono (hKu (r + T₀) ⟨by linarith [hr.1], by linarith [hr.2]⟩) (le_max_left _ _)
  have hcl := uniqueness_class hν hvc (solClass_tail hT₀ (by linarith)
    (SolClass.of_solvesBefore hu)) hSL hK0 hR
    (by show v 0 = u (0 + T₀); rw [zero_add]; exact h0) (t - T₀) ⟨by linarith, htS⟩
  simpa [shiftE, sub_add_cancel] using hcl

/-- **`SolvesFrom` transfers along agreement on `[T₀, ∞)`.** -/
theorem SolvesFrom.congr {ν T₀ L : ℝ} {w w' : VelocityEvolution} {q q' : PressureEvolution}
    (h : SolvesFrom ν T₀ L w q) (hw : ∀ t, T₀ ≤ t → w' t = w t)
    (hq : ∀ t, T₀ ≤ t → q' t = q t) : SolvesFrom ν T₀ L w' q' := by
  refine ⟨h.vel_smooth.congr fun z hz => by simp only [hw z.1 hz.1.1],
    h.pres_smooth.congr fun z hz => by simp only [hq z.1 hz.1.1], ?_, ?_, ?_, ?_⟩
  · intro t ht1 ht2 x
    have := h.incompressible t ht1 ht2 x
    unfold divergence spatialDerivative at this ⊢
    rwa [hw t ht1]
  · intro t ht1 ht2 x
    have e := h.equation t ht1 ht2 x
    have hev : ∀ᶠ s in 𝓝 t, w' s = w s :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht1) fun s hs => hw s (le_of_lt hs)
    have htd := timeDerivative_congr_nhds hev x
    have hs := hw t ht1.le
    have hps := hq t ht1.le
    unfold convection spatialDerivative laplacian pressureGradient at e ⊢
    rw [htd, hs, hps]
    exact e
  · intro t ht1 ht2
    rw [hw t ht1]; exact h.finite_energy t ht1 ht2
  · intro t ht1 ht2
    unfold kineticEnergy
    rw [hw t ht1, hw T₀ le_rfl]
    exact h.energy_le_start t ht1 ht2

/-- `R` at a single time transfers along an agreement of slices and time derivatives. -/
theorem rslice_congr {K : ℝ} {u w : VelocityEvolution} {p r : PressureEvolution} {t s : ℝ}
    (h : Rslice K u p s) (hw : w t = u s) (hr : r t = p s)
    (htd : ∀ x, timeDerivative w t x = timeDerivative u s x) :
    RegSlice K (w t) ∧ PresSlice K (r t) ∧ TimeSlice K w t ∧ SupSlice K (w t) ∧
      PresL2 K (r t) := by
  refine ⟨hw ▸ h.1, hr ▸ h.2.1, ?_, hw ▸ h.2.2.2.1, hr ▸ h.2.2.2.2⟩
  have hf : (fun x => ‖timeDerivative w t x‖ ^ 2) = fun x => ‖timeDerivative u s x‖ ^ 2 :=
    funext fun x => by rw [htd x]
  unfold TimeSlice
  rw [hf]
  exact h.2.2.1

/-- **The strip from a piece.** -/
theorem strip_of_piece {ν T T₀ L : ℝ} (hν : 0 < ν) {u v : VelocityEvolution}
    {p q : PressureEvolution} (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T) (hTL : T ≤ T₀ + L)
    (hu : SolvesBefore ν T u p) (hRu : RegularOnCompacts T u p)
    (hpn : PressureNormalizedBefore T p)
    (hv : SolvesBefore ν L v q) (hRv : RegularOnCompacts L v q)
    (hqn : PressureNormalizedBefore L q) (h0 : v 0 = u T₀) :
    SolvesFrom ν T₀ L (fun t => if t < T then u t else v (t - T₀))
        (fun t => if t < T then p t else q (t - T₀)) ∧
      RegularOnCompactsFrom T₀ L (fun t => if t < T then u t else v (t - T₀))
        (fun t => if t < T then p t else q (t - T₀)) ∧
      (∀ t : ℝ, T₀ ≤ t → t < T₀ + L → (if t < T then p t else q (t - T₀)) 0 = 0) ∧
      (∀ t : ℝ, T₀ ≤ t → (if t < T then u t else v (t - T₀)) = v (t - T₀) ∧
        (if t < T then p t else q (t - T₀)) = q (t - T₀)) := by
  set w : VelocityEvolution := fun t => if t < T then u t else v (t - T₀) with hwdef
  set r : PressureEvolution := fun t => if t < T then p t else q (t - T₀) with hrdef
  have hvs : SolvesFrom ν T₀ L (fun t => v (t - T₀)) (fun t => q (t - T₀)) :=
    SolvesBefore.to_solvesFrom_shift hT₀ hv
  have hqn' : ∀ t : ℝ, T₀ ≤ t → t < T₀ + L → (fun t => q (t - T₀)) t 0 = 0 :=
    fun t h1 h2 => hqn (t - T₀) (by linarith) (by linarith)
  have hvel : ∀ t, T₀ ≤ t → t < T → v (t - T₀) = u t := fun t h1 h2 =>
    uniqueness_piece hν hT₀ hu hRu hv hRv h0 t h1 (lt_min h2 (by linarith))
  have hpres : ∀ t, T₀ ≤ t → t < T → p t = q (t - T₀) :=
    pressure_agree hT₀ hT₀T hTL hu hpn hvs hqn' fun t h1 h2 => (hvel t h1 h2).symm
  have hwe : ∀ t, T₀ ≤ t → w t = v (t - T₀) := by
    intro t ht
    simp only [hwdef]
    split_ifs with h
    · exact (hvel t ht h).symm
    · rfl
  have hre : ∀ t, T₀ ≤ t → r t = q (t - T₀) := by
    intro t ht
    simp only [hrdef]
    split_ifs with h
    · exact hpres t ht h
    · rfl
  refine ⟨SolvesFrom.congr hvs hwe hre, ?_, fun t h1 h2 => by
    show r t 0 = 0; rw [hre t h1]; exact hqn' t h1 h2, fun t ht => ⟨hwe t ht, hre t ht⟩⟩
  -- R on the strip
  intro T' hT'
  obtain ⟨Ku, hKu⟩ := hRu T₀ hT₀T
  obtain ⟨Kv, hKv⟩ := hRv (max (T' - T₀) 0) (by
    rcases le_total (T' - T₀) 0 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith)
  refine ⟨max Ku Kv, fun t ht => ?_⟩
  rcases ht.1.lt_or_eq with hlt | heq
  · -- interior of the strip: the translated piece
    have hs : t - T₀ ∈ Icc (0 : ℝ) (max (T' - T₀) 0) :=
      ⟨by linarith, le_max_of_le_left (by linarith [ht.2])⟩
    have hsL : t - T₀ ∈ Ioo (0 : ℝ) L := ⟨by linarith, by linarith [ht.2]⟩
    have htd : ∀ x, timeDerivative w t x = timeDerivative v (t - T₀) x := by
      intro x
      have hev : ∀ᶠ s in 𝓝 t, w s = (fun s => v (s - T₀)) s :=
        Filter.eventually_of_mem (Ioi_mem_nhds hlt) fun s hs => hwe s (le_of_lt hs)
      rw [timeDerivative_congr_nhds hev x]
      exact timeDerivative_shift v L T₀ t x (by linarith) hv.classical.1 hsL
    exact rslice_congr (Rslice.mono (hKv (t - T₀) hs) (le_max_right _ _)) (hwe t ht.1)
      (hre t ht.1) htd
  · -- the strip start: the glued field is `u` near `T₀`
    subst heq
    have hwt : w T₀ = u T₀ := by
      show (if T₀ < T then u T₀ else v (T₀ - T₀)) = u T₀; rw [if_pos hT₀T]
    have hrt : r T₀ = p T₀ := by
      show (if T₀ < T then p T₀ else q (T₀ - T₀)) = p T₀; rw [if_pos hT₀T]
    have htd : ∀ x, timeDerivative w T₀ x = timeDerivative u T₀ x := by
      intro x
      have hev : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] T₀, w s = u s := by
        refine Filter.eventually_of_mem (inter_mem_nhdsWithin _ (Iio_mem_nhds hT₀T)) ?_
        intro s hs
        show (if s < T then u s else v (s - T₀)) = u s
        rw [if_pos (show s < T from hs.2)]
      have hev' : (fun s : ℝ => w s x) =ᶠ[𝓝[Ici (0 : ℝ)] T₀] fun s : ℝ => u s x :=
        hev.mono fun s hs => congrFun hs x
      simpa [timeDerivative] using congrArg (fun L : ℝ →L[ℝ] Space => L 1)
        (Filter.EventuallyEq.fderivWithin_eq hev' (congrFun hwt x))
    exact rslice_congr (Rslice.mono (hKu T₀ ⟨hT₀, le_rfl⟩) (le_max_left _ _)) hwt hrt htd

end Navier.Analysis.StripOfPiece

set_option pp.fullNames true in
#print axioms Navier.Analysis.StripOfPiece.strip_of_piece
