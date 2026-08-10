import Navier.Analysis.OfficialABEncoding

/-!
# Inherited sup-norm versus Euclidean kinetic energy

`Navier.Space = Fin 3 → ℝ` inherits Mathlib's finite-product **supremum** norm,
whereas Fefferman's clause (7) uses the **Euclidean** norm on `R^3`.  This file
carries that single pointwise discrepancy up to integrability and to the
uniform energy bound.

## What changed, and why most of this file was rewritten

`Navier.kineticEnergy` is now defined as `∫ ∑ᵢ uᵢ²`, i.e. it is *already* the
Euclidean energy.  Consequently `officialKineticEnergy` and `kineticEnergy` are
provably **equal** (`officialKineticEnergy_eq_kineticEnergy`), and the former
`kineticEnergy_le_officialKineticEnergy` / `officialKineticEnergy_le_three_mul_
kineticEnergy` / `uniformlyBoundedEnergy_iff_official` trio degenerated into
`X ≤ X`, `X ≤ 3X` and `P ↔ P` — inequalities whose analytic-looking measurability
and integrability hypotheses did no work.  All three are now deleted in favour of
the equality: an inequality, or an `iff`, between two provably equal quantities
carries no information, and keeping one as a "transport shim" only disguises the
identity as an analytic step.  Consumers rewrite with
`officialKineticEnergy_eq_kineticEnergy` directly.

## Where the genuine content now lives

The surviving discrepancy is between the Euclidean `kineticEnergy` and the
**sup-norm** energy `supKineticEnergy = ∫ ‖u t x‖²`, which is the quantity that
`Navier.IsClassicalSolution.finite_energy` actually asserts integrable and that
`LerayWeak.UniformKineticBound` actually bounds.  That comparison is two-sided
but **asymmetric in the constant**: `supKineticEnergy ≤ kineticEnergy ≤
3 * supKineticEnergy`, and the factor `3` is attained
(`officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness`), so it cannot be
improved.  The strictness witness
(`norm_sq_lt_officialEuclideanNorm_sq_witness`) machine-checks that the two
norms really do differ, i.e. that the `currentSpaceNormEuclideanNormEquivalence`
encoding residual disclosed in `Navier.Problem` is **live rather than vacuous**.

Nothing here proves an energy identity or any a priori estimate.  The remaining
representation step is to derive the slice measurability used below from the
official smooth spacetime solution predicate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.EnergyNormBridge

open Navier
open Navier.Analysis.OfficialABEncoding

/-- Fefferman's Euclidean kinetic-energy integral at one time. -/
def officialKineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, officialEuclideanNorm (u t x) ^ 2

/-- The kinetic-energy integral in the norm `Space` actually inherits (the
finite-product supremum norm).  This is the integrand of
`Navier.IsClassicalSolution.finite_energy` and the quantity bounded by
`LerayWeak.UniformKineticBound`; it is *not* Fefferman's energy. -/
def supKineticEnergy (u : VelocityEvolution) (t : ℝ) : ℝ :=
  ∫ x : Space, ‖u t x‖ ^ 2

theorem continuous_officialEuclideanNorm :
    Continuous officialEuclideanNorm := by
  unfold officialEuclideanNorm officialEuclideanPoint
  fun_prop

/-- The inherited squared norm is bounded by the official squared norm. -/
theorem norm_sq_le_officialEuclideanNorm_sq (x : Space) :
    ‖x‖ ^ 2 ≤ officialEuclideanNorm x ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg x) (norm_le_officialEuclideanNorm x) 2

/-- In dimension three, the official squared norm is at most three times the
inherited squared norm. -/
theorem officialEuclideanNorm_sq_le_three_mul_norm_sq (x : Space) :
    officialEuclideanNorm x ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
  calc
    officialEuclideanNorm x ^ 2 ≤
        (Real.sqrt 3 * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (officialEuclideanNorm_nonneg x)
        (officialEuclideanNorm_le x) 2
    _ = 3 * ‖x‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

/-- For a strongly measurable spatial field, the inherited and official
squared energy densities are integrable simultaneously. -/
theorem integrable_norm_sq_iff_officialEuclideanNorm_sq
    (f : Space → Space) (hf : AEStronglyMeasurable f) :
    Integrable (fun x => ‖f x‖ ^ 2) ↔
      Integrable (fun x => officialEuclideanNorm (f x) ^ 2) := by
  have hnorm :
      AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) :=
    hf.norm.pow 2
  have hoff :
      AEStronglyMeasurable
        (fun x => officialEuclideanNorm (f x) ^ 2) :=
    (continuous_officialEuclideanNorm.comp_aestronglyMeasurable hf).pow 2
  constructor
  · intro h
    apply (h.const_mul (3 : ℝ)).mono' hoff
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact officialEuclideanNorm_sq_le_three_mul_norm_sq (f x)
  · intro h
    apply h.mono' hnorm
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_sq_le_officialEuclideanNorm_sq (f x)

/-- The Euclidean norm squared equals the component-wise sum of squares. -/
theorem officialEuclideanNorm_sq_eq_sum_sq (x : Space) :
    officialEuclideanNorm x ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  simp [officialEuclideanNorm, officialEuclideanPoint,
    EuclideanSpace.real_norm_sq_eq]

/-- The sup norm squared is bounded by the sum of squares. -/
theorem norm_sq_le_sum_sq (x : Space) : ‖x‖ ^ 2 ≤ ∑ i : Fin 3, x i ^ 2 := by
  calc
    ‖x‖ ^ 2 ≤ officialEuclideanNorm x ^ 2 := norm_sq_le_officialEuclideanNorm_sq x
    _ = ∑ i : Fin 3, x i ^ 2 := officialEuclideanNorm_sq_eq_sum_sq x

/-! ### The two norms genuinely differ

The all-ones point is a single witness that settles both non-degeneracy
questions: it makes `norm_sq_le_officialEuclideanNorm_sq` strict, and it
*attains* the constant `3` in `officialEuclideanNorm_sq_le_three_mul_norm_sq`.
-/

/-- The inherited supremum norm of the all-ones point is `1`, not `√3`. -/
theorem norm_onesPoint : ‖(![1, 1, 1] : Space)‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by norm_num)).2 ?_) ?_
  · intro i
    fin_cases i <;> simp
  · calc (1 : ℝ) = ‖(![1, 1, 1] : Space) 0‖ := by simp
      _ ≤ ‖(![1, 1, 1] : Space)‖ := norm_le_pi_norm _ 0

/-- **The sup/Euclidean gap is not vacuous.**  At the all-ones point the
inherited squared norm is `1` while the Euclidean squared norm is `3`, so
`norm_sq_le_officialEuclideanNorm_sq` is a strict inequality somewhere.  This is
the machine-checked reason the `currentSpaceNormEuclideanNormEquivalence`
residual of `Navier.Problem` may not be retired. -/
theorem norm_sq_lt_officialEuclideanNorm_sq_witness :
    ∃ x : Space, ‖x‖ ^ 2 < officialEuclideanNorm x ^ 2 := by
  refine ⟨![1, 1, 1], ?_⟩
  rw [norm_onesPoint, officialEuclideanNorm_sq_eq_sum_sq]
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- **The dimension constant `3` is attained, hence sharp.**  No smaller
constant works in `officialEuclideanNorm_sq_le_three_mul_norm_sq`, so the
factor-`3` loss in `kineticEnergy_le_three_mul_supKineticEnergy` below is a real
feature of the encoding rather than proof slack. -/
theorem officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness :
    ∃ x : Space, officialEuclideanNorm x ^ 2 = 3 * ‖x‖ ^ 2 := by
  refine ⟨![1, 1, 1], ?_⟩
  rw [norm_onesPoint, officialEuclideanNorm_sq_eq_sum_sq]
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### Energy level

`kineticEnergy` is already Euclidean, so the comparison against
`officialKineticEnergy` is an identity.  The surviving comparison is against
`supKineticEnergy`.
-/

/-- **Fefferman's Euclidean energy is literally the project `kineticEnergy`.**
`kineticEnergy` integrates `∑ᵢ uᵢ²` and the squared Euclidean norm *is* that
sum, so no inequality, measurability hypothesis, or dimension constant is
involved.  This equality supersedes the former
`kineticEnergy_le_officialKineticEnergy` and
`officialKineticEnergy_le_three_mul_kineticEnergy`, which stated `X ≤ X` and
`X ≤ 3X` under hypotheses their proofs never used. -/
theorem officialKineticEnergy_eq_kineticEnergy (u : VelocityEvolution) (t : ℝ) :
    officialKineticEnergy u t = kineticEnergy u t := by
  simp only [officialKineticEnergy, kineticEnergy,
    officialEuclideanNorm_sq_eq_sum_sq]

/-- The sup-norm energy is dominated by the Euclidean energy at the **same**
constant.  Unlike the deleted `kineticEnergy_le_officialKineticEnergy`, this is
not a tautology: the two integrands differ, and
`norm_sq_lt_officialEuclideanNorm_sq_witness` shows the domination is somewhere
strict. -/
theorem supKineticEnergy_le_kineticEnergy
    (u : VelocityEvolution) (t : ℝ)
    (hmeas : AEStronglyMeasurable (u t))
    (hint : Integrable (fun x => ‖u t x‖ ^ 2)) :
    supKineticEnergy u t ≤ kineticEnergy u t := by
  have hsum : Integrable (fun x : Space => ∑ i : Fin 3, (u t x i) ^ 2) :=
    ((integrable_norm_sq_iff_officialEuclideanNorm_sq (u t) hmeas).1
      hint).congr
      (Filter.Eventually.of_forall fun x =>
        officialEuclideanNorm_sq_eq_sum_sq (u t x))
  unfold supKineticEnergy kineticEnergy
  exact integral_mono hint hsum fun x => norm_sq_le_sum_sq (u t x)

/-- The reverse domination costs exactly the dimension factor `3`, which
`officialEuclideanNorm_sq_eq_three_mul_norm_sq_witness` shows is attained
pointwise and therefore not removable by a sharper argument. -/
theorem kineticEnergy_le_three_mul_supKineticEnergy
    (u : VelocityEvolution) (t : ℝ)
    (hmeas : AEStronglyMeasurable (u t))
    (hint : Integrable (fun x => ‖u t x‖ ^ 2)) :
    kineticEnergy u t ≤ 3 * supKineticEnergy u t := by
  have hsum : Integrable (fun x : Space => ∑ i : Fin 3, (u t x i) ^ 2) :=
    ((integrable_norm_sq_iff_officialEuclideanNorm_sq (u t) hmeas).1
      hint).congr
      (Filter.Eventually.of_forall fun x =>
        officialEuclideanNorm_sq_eq_sum_sq (u t x))
  unfold supKineticEnergy kineticEnergy
  calc
    (∫ x : Space, ∑ i : Fin 3, (u t x i) ^ 2) ≤
        ∫ x : Space, 3 * ‖u t x‖ ^ 2 := by
      refine integral_mono hsum (hint.const_mul 3) fun x => ?_
      have h := officialEuclideanNorm_sq_le_three_mul_norm_sq (u t x)
      rwa [officialEuclideanNorm_sq_eq_sum_sq (u t x)] at h
    _ = 3 * ∫ x : Space, ‖u t x‖ ^ 2 := integral_const_mul 3 _

/-- Under slice measurability and the existing integrability clause, uniform
boundedness of the **inherited sup-norm** energy and of Fefferman's Euclidean
energy are equivalent, the bound changing by at most the fixed dimension factor
three.  This is the load-bearing replacement for the former
`uniformlyBoundedEnergy_iff_official`, whose two sides had become the same
proposition.  The asymmetry is essential: the Euclidean-to-sup direction keeps
the constant, the sup-to-Euclidean direction cannot (see
`LerayWeak.UniformOfficialKineticBound` for the consequence). -/
theorem uniformlyBoundedEnergy_iff_sup
    (u : VelocityEvolution)
    (hmeas : ∀ t : ℝ, 0 ≤ t → AEStronglyMeasurable (u t))
    (hint : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun x => ‖u t x‖ ^ 2)) :
    (∃ E : ℝ, 0 < E ∧
      ∀ t : ℝ, 0 ≤ t → supKineticEnergy u t < E) ↔
      ∃ E : ℝ, 0 < E ∧
        ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E := by
  constructor
  · rintro ⟨E, hE, hbound⟩
    refine ⟨3 * E, mul_pos (by norm_num) hE, fun t ht => ?_⟩
    exact lt_of_le_of_lt
      (kineticEnergy_le_three_mul_supKineticEnergy u t (hmeas t ht) (hint t ht))
      (mul_lt_mul_of_pos_left (hbound t ht) (by norm_num))
  · rintro ⟨E, hE, hbound⟩
    refine ⟨E, hE, fun t ht => ?_⟩
    exact lt_of_le_of_lt
      (supKineticEnergy_le_kineticEnergy u t (hmeas t ht) (hint t ht))
      (hbound t ht)

end Navier.Analysis.EnergyNormBridge
