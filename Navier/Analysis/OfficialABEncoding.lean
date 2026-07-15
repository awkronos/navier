import Navier.ConventionBridges

/-!
# Official A/B encoding: the spatial norm bridge

`Navier.Space = Fin 3 → ℝ` carries Mathlib's product (supremum) norm, while
Fefferman's clauses use the Euclidean norm on `ℝ³`.  This file isolates that
representation mismatch and proves the sharp dimension-dependent comparison

`‖x‖∞ ≤ ‖x‖₂ ≤ √3 · ‖x‖∞`.

As a concrete consumer, the comparison transports the rapid-decay predicate
from `Navier.ConventionBridges` to an otherwise identical predicate whose
spatial weight uses the Euclidean norm.  This closes only the point-norm part
of Fefferman clause (4)'s representation bridge.  The conversion between
total Fréchet derivatives and coordinate multi-index derivatives, and the
conversion from polynomial weights to the literal `(1 + |x|) ^ (-K)` clause,
remain separate obligations.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Navier.Analysis.OfficialABEncoding

open Navier

/-- The current `Space` coordinates, equipped with the Euclidean `ℓ²` norm. -/
def officialEuclideanPoint (x : Space) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 x

@[simp] theorem officialEuclideanPoint_apply (x : Space) (i : Fin 3) :
    (officialEuclideanPoint x : Fin 3 → ℝ) i = x i := rfl

/-- Fefferman's Euclidean point norm on the coordinates of `Space`. -/
def officialEuclideanNorm (x : Space) : ℝ :=
  ‖officialEuclideanPoint x‖

theorem officialEuclideanNorm_nonneg (x : Space) :
    0 ≤ officialEuclideanNorm x :=
  norm_nonneg _

/-- Coordinate formula for Fefferman's Euclidean point norm. -/
theorem officialEuclideanNorm_eq_sqrt_sum_sq (x : Space) :
    officialEuclideanNorm x = Real.sqrt (∑ i : Fin 3, |x i| ^ 2) := by
  rw [officialEuclideanNorm, EuclideanSpace.norm_eq]
  simp [officialEuclideanPoint, Real.norm_eq_abs]

/-- The product norm currently inherited by `Space` is bounded by the
official Euclidean point norm. -/
theorem norm_le_officialEuclideanNorm (x : Space) :
    ‖x‖ ≤ officialEuclideanNorm x := by
  rw [officialEuclideanNorm_eq_sqrt_sum_sq]
  refine (pi_norm_le_iff_of_nonneg
    (G := fun _ : Fin 3 => ℝ) (x := x)
    (r := Real.sqrt (∑ i : Fin 3, |x i| ^ 2))
    (Real.sqrt_nonneg _)).2 ?_
  intro i
  exact (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
    (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j : Fin 3 => |x j| ^ 2)
      (fun j _ => sq_nonneg |x j|)
      (Finset.mem_univ i))

/-- In dimension three, the official Euclidean point norm is at most `√3`
times the product norm currently inherited by `Space`. -/
theorem officialEuclideanNorm_le (x : Space) :
    officialEuclideanNorm x ≤ Real.sqrt 3 * ‖x‖ := by
  rw [officialEuclideanNorm_eq_sqrt_sum_sq]
  have hcoord : ∀ i : Fin 3, |x i| ≤ ‖x‖ := by
    intro i
    simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hsum :
      (∑ i : Fin 3, |x i| ^ 2) ≤ 3 * ‖x‖ ^ 2 := by
    calc
      (∑ i : Fin 3, |x i| ^ 2) ≤ ∑ _i : Fin 3, ‖x‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
      _ = 3 * ‖x‖ ^ 2 := by simp
  calc
    Real.sqrt (∑ i : Fin 3, |x i| ^ 2)
        ≤ Real.sqrt (3 * ‖x‖ ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * ‖x‖ := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (3 : ℝ))]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]

/-- The rapid-decay predicate from `ConventionBridges`, with only its spatial
polynomial weight changed to Fefferman's Euclidean point norm. -/
def FeffermanEuclideanWeightRapidDecayBound (f : Space → Space) : Prop :=
  ∀ (k n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space,
    officialEuclideanNorm x ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C

/-- Replacing the inherited product norm by the official Euclidean point norm
does not change the rapid-decay class. -/
theorem feffermanRapidDecayBound_iff_euclideanWeight (f : Space → Space) :
    Navier.ConventionBridges.FeffermanRapidDecayBound f ↔
      FeffermanEuclideanWeightRapidDecayBound f := by
  constructor
  · intro h k n
    obtain ⟨C, hC, hbound⟩ := h k n
    refine ⟨Real.sqrt 3 ^ k * C,
      mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hC, ?_⟩
    intro x
    calc
      officialEuclideanNorm x ^ k * ‖iteratedFDeriv ℝ n f x‖
          ≤ (Real.sqrt 3 * ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (officialEuclideanNorm_nonneg x)
            (officialEuclideanNorm_le x) k)
          (norm_nonneg _)
      _ = Real.sqrt 3 ^ k * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
        rw [mul_pow]
        ring
      _ ≤ Real.sqrt 3 ^ k * C :=
        mul_le_mul_of_nonneg_left (hbound x)
          (pow_nonneg (Real.sqrt_nonneg _) _)
  · intro h k n
    obtain ⟨C, hC, hbound⟩ := h k n
    refine ⟨C, hC, ?_⟩
    intro x
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
          ≤ officialEuclideanNorm x ^ k * ‖iteratedFDeriv ℝ n f x‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg x)
            (norm_le_officialEuclideanNorm x) k)
          (norm_nonneg _)
      _ ≤ C := hbound x

/-- A Mathlib Schwartz map satisfies the rapid-decay bound after replacing
the inherited product norm in its spatial weight by Fefferman's Euclidean
point norm. -/
theorem schwartzmap_satisfies_fefferman_euclidean_weight_rapid_decay
    (s : SchwartzMap Space Space) :
    FeffermanEuclideanWeightRapidDecayBound s.toFun :=
  (feffermanRapidDecayBound_iff_euclideanWeight s.toFun).1
    (Navier.ConventionBridges.schwartzmap_satisfies_fefferman_rapid_decay s)

end Navier.Analysis.OfficialABEncoding
