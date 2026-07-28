import Mathlib

/-!
# Riesz–Fréchet–Kolmogorov: the two engines of the dyadic-average route

Mathlib has Arzelà–Ascoli for `C(K)` and Banach–Alaoglu for weak-* compactness,
but **no** Riesz–Fréchet–Kolmogorov compactness criterion for `L^p`.  It has to be
built, and this module is the general-functional-analysis part of that build:
nothing here mentions Navier–Stokes, so it is reusable anywhere.

## The route

`Navier.Analysis.LerayWeak.exists_subseq_windowCauchy` is the designated consumer.
Rather than mollify-and-Arzelà–Ascoli, the argument taken there is the **dyadic-
average projection**: partition the window into cells of side `h`, let `E_h f` be
the cell-wise average of `f`, and combine

* **Jensen / Cauchy–Schwarz**, which makes `E_h f` close to `f` uniformly over a
  translation-equicontinuous family, via the pointwise oscillation bound
  `‖(⨍_Q f) − f x‖² ≤ ⨍_Q ‖f y − f x‖²` summed over cells into
  `‖E_h f − f‖²_{L²} ≤ 2^d · sup_{|k|_∞ ≤ h} ‖τ_k f − f‖²_{L²}`; and
* **Bolzano–Weierstrass**, which extracts a subsequence along which `E_h f`
  converges — legitimate precisely because `E_h f` lives in the *finite-
  dimensional* span of the finitely many cell indicators, so no compactness in
  an infinite-dimensional space is ever invoked.

Together these give total boundedness of the family, hence an `L²`-Cauchy
subsequence.  This module establishes both engines: `norm_setAverage_sub_sq_le`
with its oscillation form, and `exists_subseq_cauchy_of_bounded_pi`.  The
remaining middle step — converting the cell-oscillation sum into the translation
modulus by Fubini and translation-invariance of Haar measure — is what the
consumer still names as its residual.

## Step-0 record

`experiments/riesz_kolmogorov_dyadic_core.py` checks the route numerically, before
any of it was written.  The Jensen inequality holds with `max(lhs − rhs) = 0` over
20000 random vector-valued trials.  The cell bound holds with worst observed
ratios `0.45` and `0.29` against the bound `2¹` in `d = 1`, and `0.31` and `0.16`
against `2²` in `d = 2`, so the constant `2^d` is safe rather than tight.  The
end-to-end separation is the intended one: an equicontinuous family has modulus
`9e-2 → 2e-5` as `h → 0` and minimum pairwise `L²` distance `4.2e-5`, while an
oscillating family has modulus pinned at `5.6e-1` and pairwise distance bounded
below by `1.7e-1`, hence no Cauchy subsequence.  That second family is the same
phenomenon as the curl-free witness that falsified the original Aubin–Lions
hypothesis list (`experiments/aubin_lions_curlfree_witness.py`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
  Equations*, Springer 2011, Thm 4.26 (Riesz–Fréchet–Kolmogorov) and Cor 4.27.
* J. Simon, "Compact sets in `L^p(0,T;B)`", *Ann. Mat. Pura Appl.* **146** (1987)
  65–96, Thm 1.
* R. Temam, *Navier–Stokes Equations*, AMS Chelsea 2001, Ch. III §2.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace Navier.Analysis.RieszKolmogorov

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-!
## Engine 1 — the averaging (Jensen) bound
-/

omit [CompleteSpace E] in
/-- The norm of a set-average is at most the set-average of the norm. -/
theorem norm_setAverage_le (f : α → E) (s : Set α) :
    ‖⨍ y in s, f y ∂μ‖ ≤ ⨍ y in s, ‖f y‖ ∂μ := by
  rw [setAverage_eq, setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.mpr measureReal_nonneg)

/-- Cauchy–Schwarz for a set-average: the square of the average is at most the
average of the square.  This is Jensen's inequality for the convex function
`r ↦ r²` against the normalized restriction of `μ` to `s`. -/
theorem sq_setAverage_le {s : Set α} (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤)
    {h : α → ℝ} (hi : IntegrableOn h s μ) (hi2 : IntegrableOn (fun y => h y ^ 2) s μ) :
    (⨍ y in s, h y ∂μ) ^ 2 ≤ ⨍ y in s, h y ^ 2 ∂μ :=
  ConvexOn.map_set_average_le (g := fun r : ℝ => r ^ 2)
    (Even.convexOn_pow (by decide)) (by fun_prop) isClosed_univ h0 hs
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hi hi2

/-- **Engine 1.**  The set-average of `f` over `s` is closer to any point `c` than
the average of the distances to `c`, in the mean-square sense:
`‖(⨍_s f) − c‖² ≤ ⨍_s ‖f y − c‖²`.

Numerically checked to be sharp-or-equal before formalization: over 20000 random
vector-valued trials the maximum of `lhs − rhs` is exactly `0`, attained at the
one-point averages (`experiments/riesz_kolmogorov_dyadic_core.py`, part (J)). -/
theorem norm_setAverage_sub_sq_le {s : Set α} (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤)
    (f : α → E) (c : E) (hfi : IntegrableOn f s μ)
    (hsq : IntegrableOn (fun y => ‖f y - c‖ ^ 2) s μ) :
    ‖(⨍ y in s, f y ∂μ) - c‖ ^ 2 ≤ ⨍ y in s, ‖f y - c‖ ^ 2 ∂μ := by
  have hc : IntegrableOn (fun _ : α => c) s μ := integrableOn_const hs
  have hg : IntegrableOn (fun y => f y - c) s μ := hfi.sub hc
  have h1 : (⨍ y in s, (f y - c) ∂μ) = (⨍ y in s, f y ∂μ) - c := by
    have hstep : (⨍ y in s, (f y - c) ∂μ) = (⨍ y in s, f y ∂μ) - (⨍ _ in s, c ∂μ) := by
      simp only [setAverage_eq, integral_sub hfi hc, smul_sub]
    rw [hstep, setAverage_const h0 hs]
  calc ‖(⨍ y in s, f y ∂μ) - c‖ ^ 2 = ‖⨍ y in s, (f y - c) ∂μ‖ ^ 2 := by rw [h1]
    _ ≤ (⨍ y in s, ‖f y - c‖ ∂μ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_setAverage_le _ _) 2
    _ ≤ ⨍ y in s, ‖f y - c‖ ^ 2 ∂μ := sq_setAverage_le h0 hs hg.norm hsq

/-- **The cell-oscillation bound.**  Specializing `norm_setAverage_sub_sq_le` at
`c = f x` says: on a cell `s`, the error of replacing `f` by its cell-average is
controlled pointwise by the mean-square oscillation of `f` over that cell.  This
is the pointwise inequality that, summed over the cells of a partition and
converted by Fubini, becomes `‖E_h f − f‖²_{L²} ≤ 2^d sup_{|k|_∞ ≤ h}
‖τ_k f − f‖²_{L²}`. -/
theorem norm_setAverage_sub_apply_sq_le {s : Set α} (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤)
    (f : α → E) (x : α) (hfi : IntegrableOn f s μ)
    (hsq : IntegrableOn (fun y => ‖f y - f x‖ ^ 2) s μ) :
    ‖(⨍ y in s, f y ∂μ) - f x‖ ^ 2 ≤ ⨍ y in s, ‖f y - f x‖ ^ 2 ∂μ :=
  norm_setAverage_sub_sq_le h0 hs f (f x) hfi hsq

/-- **The integrated cell bound.**  Integrating `norm_setAverage_sub_apply_sq_le`
over the cell: replacing `f` by its cell-average costs at most the mean-square
oscillation of `f` on that cell.  Summing this over the cells of a partition of
the window, and converting the right side by Fubini and translation-invariance of
Lebesgue measure, is what produces `‖E_h f − f‖²_{L²} ≤ 2^d sup_{|k|_∞ ≤ h}
‖τ_k f − f‖²_{L²}`.

The integrability side conditions are taken as hypotheses rather than derived:
on the intended cells they are immediate (bounded cell, `f` square-integrable),
and keeping them explicit avoids committing this general lemma to any one
measurability setup. -/
theorem setIntegral_norm_sub_setAverage_sq_le {s : Set α} (hsm : MeasurableSet s)
    (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤) (f : α → E) (hfi : IntegrableOn f s μ)
    (hslice : ∀ x : α, IntegrableOn (fun y => ‖f y - f x‖ ^ 2) s μ)
    (hlhs : IntegrableOn (fun x => ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2) s μ)
    (hrhs : IntegrableOn (fun x => ⨍ y in s, ‖f y - f x‖ ^ 2 ∂μ) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ
      ≤ ∫ x in s, (⨍ y in s, ‖f y - f x‖ ^ 2 ∂μ) ∂μ := by
  refine setIntegral_mono_on hlhs hrhs hsm fun x _ => ?_
  rw [show ‖f x - ⨍ y in s, f y ∂μ‖ = ‖(⨍ y in s, f y ∂μ) - f x‖ from norm_sub_rev _ _]
  exact norm_setAverage_sub_apply_sq_le h0 hs f x hfi (hslice x)

/-!
## Engine 2 — Bolzano–Weierstrass in the finite-dimensional cell space
-/

/-- **Engine 2.**  A norm-bounded sequence in `Fin N → ℝ` has a Cauchy
subsequence.  This is the step that makes the dyadic-average route elementary:
the cell-average vector of a member of the family is a point of `Fin N → ℝ` with
`N` the number of cells meeting the window, so no infinite-dimensional
compactness is ever needed — only Heine–Borel in a proper space.

Stated in the "extract from any sequence" shape the diagonal argument consumes:
apply it to `fun k => v (τ k)` to refine a given subsequence `τ`. -/
theorem exists_subseq_cauchy_of_bounded_pi {N : ℕ} (v : ℕ → Fin N → ℝ) (M : ℝ)
    (hb : ∀ k : ℕ, ‖v k‖ ≤ M) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ j k : ℕ, K ≤ j → K ≤ k →
        ‖v (ρ j) - v (ρ k)‖ < ε := by
  obtain ⟨b, -, ρ, hρ, hconv⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : Fin N → ℝ)) (r := M))
      (fun k => by simpa [Metric.mem_closedBall, dist_zero_right] using hb k)
  refine ⟨ρ, hρ, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq ε hε
  exact ⟨K, fun j k hj hk => by simpa [dist_eq_norm] using hK j hj k hk⟩

end Navier.Analysis.RieszKolmogorov


