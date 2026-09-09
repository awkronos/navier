import Navier.Analysis.ForceMultiIndexConvention

/-!
# Successive coordinate differentiation of a smooth force

The recursive operator below actually differentiates the preceding function.
It is not a notation alias for evaluation of a multilinear jet. The comparison
holds for every ordered direction family, including at time zero using the
same right-within derivative convention as the original PDE.
-/

noncomputable section
open scoped ContDiff

namespace Navier.Analysis.ForceRecursivePartials

open Navier Navier.Breakdown.OfficialCDEncoding

def successivePartialWithin (f : (ℝ × Space) → Space) :
    (n : ℕ) → (Fin n → ℝ × Space) → (ℝ × Space) → Space
  | 0, _, z => f z
  | n + 1, directions, z =>
      fderivWithin ℝ (successivePartialWithin f n (Fin.tail directions))
        nonnegativeSpacetime z (directions 0)

theorem successivePartialWithin_eq_iteratedFDerivWithin
    {f : (ℝ × Space) → Space}
    (hf : ContDiffOn ℝ ∞ f nonnegativeSpacetime)
    (n : ℕ) (directions : Fin n → ℝ × Space)
    {z : ℝ × Space} (hz : z ∈ nonnegativeSpacetime) :
    successivePartialWithin f n directions z =
      iteratedFDerivWithin ℝ n f nonnegativeSpacetime z directions := by
  have hs : UniqueDiffOn ℝ nonnegativeSpacetime :=
    (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  induction n generalizing z with
  | zero => simp [successivePartialWithin]
  | succ n ih =>
    simp only [successivePartialWithin, iteratedFDerivWithin_succ_apply_left]
    rw [fderivWithin_congr' (fun y hy => ih (Fin.tail directions) hy) hz]
    exact fderivWithin_continuousMultilinear_apply_const_apply (hs z hz)
      (hf.differentiableOn_iteratedFDerivWithin (by exact_mod_cast WithTop.coe_lt_top n) hs z hz)
      (Fin.tail directions) (directions 0)

theorem forcedDataRapidDecay_bounds_successivePartials
    {f : ForceField} (hf : ForcedDataRapidDecay f)
    (n K : ℕ) (axes : Fin n → Option (Fin 3)) (component : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      (1 + euclideanNorm x + t) ^ K *
        |successivePartialWithin (fun z => f z.1 z.2) n
          (fun j => spacetimeCoordinateDirection (axes j)) (t, x) component| ≤ C := by
  obtain ⟨C, hC, hb⟩ := forcedDataRapidDecay_implies_coordinatewise hf n K axes component
  refine ⟨C, hC, ?_⟩
  intro t ht x
  rw [successivePartialWithin_eq_iteratedFDerivWithin hf.1 n _
    (z := (t, x)) ⟨ht, Set.mem_univ x⟩]
  exact hb t ht x

end Navier.Analysis.ForceRecursivePartials

#print axioms Navier.Analysis.ForceRecursivePartials.successivePartialWithin_eq_iteratedFDerivWithin
#print axioms Navier.Analysis.ForceRecursivePartials.forcedDataRapidDecay_bounds_successivePartials
