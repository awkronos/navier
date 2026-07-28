import Navier.Problem

/-!
# The weighted Plancherel rungs (Fourier residual, substep 3)

The multiplier rungs of the `exists_fourierSpectralData` attack map:
on the Euclidean model `ES = EuclideanSpace ℝ (Fin 3)`,

  `∑ⱼ ∫ ‖∂ⱼ f‖² = (2π)² ∫ ‖ξ‖² ‖𝓕f(ξ)‖²`          (`sum_integral_normSq_lineDeriv_eq`, n = 1)
  `∑ⱼ∑ᵢ ∫ ‖∂ᵢ∂ⱼ f‖² = (2π)⁴ ∫ ‖ξ‖⁴ ‖𝓕f(ξ)‖²`      (`sum_integral_normSq_pd_two_eq`, n = 2)
  `∑ₗ∑ⱼ∑ᵢ ∫ ‖∂ᵢ∂ⱼ∂ₗ f‖² = (2π)⁶ ∫ ‖ξ‖⁶ ‖𝓕f(ξ)‖²`  (`sum_integral_normSq_pd_three_eq`, n = 3)

Each rung uses Mathlib's Schwartz-level `fourier_lineDerivOp_eq` multiplier
identity (`𝓕(∂ₘf) = 2πi⟨ξ,m⟩·𝓕f`), Plancherel per direction
(`integral_norm_sq_fourier`), and the basis expansion `∑ⱼ⟨ξ,eⱼ⟩² = ‖ξ‖²`.
With `spacePlancherel` (n = 0) they build the ladder
`∫(1+‖ξ‖²)ⁿ‖𝓕f‖² ≈ ∑_{k≤n}‖Dᵏf‖²` toward the substep-3 weighted Plancherel of
`exists_fourierSpectralData`; the higher rungs iterate the *same* multiplier
identity on `∂ⱼf` via the "raise the weight by two" collapse lemmas
(`sum_integral_norm_pow_mul_normSq_fourier_pd_2`,
`sum_integral_norm_pow_mul_normSq_fourier_pd_4`).

Elaborator note (2026-07-22): a `calc` chain over the weighted derivative-
transform integrand `‖ξ‖ᵏ·‖𝓕(∂ⱼf)ξ‖²` provokes a deterministic `whnf` timeout
(the calc transitivity machinery over-normalises `𝓕` on `𝓢(ES,ℂ)` under the
Fourier instances).  Each individual step type-checks in isolation, so the
collapse and rung proofs are written as independent `have` equalities chained
by a final syntactic `rw`, which side-steps the loop entirely.

Recon note (2026-07-22): Mathlib now also ships
`Mathlib/Analysis/Distribution/Sobolev.lean` (Bessel-potential Sobolev
spaces) with `MemSobolev.fourier_memL1` — the qualitative `𝓕f ∈ L¹` half of
the embedding for `2s > d` — and `SchwartzMap.memSobolev`.  The remaining
quantitative content of the residual is exactly this ladder (physical
derivative norms vs the spectral weight), plus the inversion-domination
substep.

Supporting: `integrable_normSq` — the square of a Schwartz map is integrable;
`integrable_norm_pow_mul_normSq` — the weighted square `‖x‖ᵏ‖g x‖²` is
integrable (decay bound times `integrable_pow_mul`); `sum_inner_single_sq` —
the basis expansion `∑ⱼ⟨ξ,eⱼ⟩² = ‖ξ‖²`.

Reference: Stein, *Singular Integrals* III.2; Majda–Bertozzi Lemma 3.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory SchwartzMap LineDeriv
open scoped FourierTransform SchwartzMap

namespace Navier.Analysis.FourierWeightedPlancherel

open Navier

abbrev ES := EuclideanSpace ℝ (Fin 3)

theorem integrable_normSq (g : 𝓢(ES, ℂ)) :
    Integrable (fun x : ES => ‖g x‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := g.decay 0 0
  have hCnn : ∀ x : ES, ‖g x‖ ≤ C := by
    intro x
    have := hC x
    simpa using this
  refine (g.integrable.norm.const_mul C).mono'
    ((map_continuous g).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc ‖g x‖ ^ 2 = ‖g x‖ * ‖g x‖ := sq (‖g x‖)
    _ ≤ C * ‖g x‖ := mul_le_mul_of_nonneg_right (hCnn x) (norm_nonneg _)

theorem norm_fourier_lineDerivOp_sq (f : 𝓢(ES, ℂ)) (m : ES) (ξ : ES) :
    ‖(𝓕 (∂_{m} f)) ξ‖ ^ 2 =
      (2 * Real.pi) ^ 2 * (inner ℝ ξ m) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have hg : (fun x : ES => inner ℝ x m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [smul_apply, smulLeftCLM_apply_apply hg]
  rw [norm_smul, norm_smul]
  have h2πi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_mul]
    simp [Real.pi_nonneg]
  rw [h2πi, Real.norm_eq_abs]
  ring_nf
  rw [sq_abs]
  ring

/-- **The n = 1 weighted Plancherel (multiplier) identity on the Euclidean
model**: the summed derivative L² masses equal `(2π)²` times the
`|ξ|²`-weighted L² mass of the Fourier transform. -/
theorem sum_integral_normSq_lineDeriv_eq (f : 𝓢(ES, ℂ)) :
    ∑ j : Fin 3, ∫ x : ES, ‖(∂_{EuclideanSpace.single j (1:ℝ)} f) x‖ ^ 2
      = (2 * Real.pi) ^ 2 * ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have hstep : ∀ j : Fin 3,
      (∫ x : ES, ‖(∂_{EuclideanSpace.single j (1:ℝ)} f) x‖ ^ 2) =
      ∫ ξ : ES, (2 * Real.pi) ^ 2 *
        (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
    intro j
    rw [← SchwartzMap.integral_norm_sq_fourier (∂_{EuclideanSpace.single j (1:ℝ)} f)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
      norm_fourier_lineDerivOp_sq f (EuclideanSpace.single j (1:ℝ)) ξ)
  have hint : ∀ j : Fin 3, Integrable (fun ξ : ES =>
      (2 * Real.pi) ^ 2 * (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
        ‖(𝓕 f) ξ‖ ^ 2) := by
    intro j
    have := integrable_normSq (𝓕 (∂_{EuclideanSpace.single j (1:ℝ)} f))
    refine this.congr ?_
    filter_upwards with ξ
    exact norm_fourier_lineDerivOp_sq f (EuclideanSpace.single j (1:ℝ)) ξ
  calc ∑ j : Fin 3, ∫ x : ES, ‖(∂_{EuclideanSpace.single j (1:ℝ)} f) x‖ ^ 2
      = ∑ j : Fin 3, ∫ ξ : ES, (2 * Real.pi) ^ 2 *
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => hstep j
    _ = ∫ ξ : ES, ∑ j : Fin 3, (2 * Real.pi) ^ 2 *
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
        (integral_finsetSum _ fun j _ => hint j).symm
    _ = ∫ ξ : ES, (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
        apply integral_congr_ae
        filter_upwards with ξ
        have hsum : ∑ j : Fin 3, (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2
            = ‖ξ‖ ^ 2 := by
          have hin : ∀ j : Fin 3,
              (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) = ξ j := by
            intro j
            rw [EuclideanSpace.inner_single_right]
            simp
          rw [Finset.sum_congr rfl fun j _ => by rw [hin j]]
          rw [EuclideanSpace.norm_eq]
          rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Real.norm_eq_abs, sq_abs]
        calc ∑ j : Fin 3, (2 * Real.pi) ^ 2 *
              (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2
            = ∑ j : Fin 3,
                (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
                  ((2 * Real.pi) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) :=
              Finset.sum_congr rfl fun j _ => by ring
            _ = ‖ξ‖ ^ 2 * ((2 * Real.pi) ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
              rw [← Finset.sum_mul, hsum]
            _ = (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2) := by
              ring
    _ = (2 * Real.pi) ^ 2 * ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
        integral_const_mul _ _

/-- Weighted square-integrability of a Schwartz map: `‖x‖ᵏ‖g x‖²` is
integrable (decay bound times `integrable_pow_mul`). -/
theorem integrable_norm_pow_mul_normSq (g : 𝓢(ES, ℂ)) (k : ℕ) :
    Integrable (fun x : ES => ‖x‖ ^ k * ‖g x‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := g.decay 0 0
  have hCnn : ∀ x : ES, ‖g x‖ ≤ C := by
    intro x
    have := hC x
    simpa using this
  refine ((g.integrable_pow_mul volume k).const_mul C).mono'
    ((continuous_norm.pow k).mul
      ((map_continuous g).norm.pow 2)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖x‖ ^ k * ‖g x‖ ^ 2 = ‖g x‖ * (‖x‖ ^ k * ‖g x‖) := by ring
    _ ≤ C * (‖x‖ ^ k * ‖g x‖) :=
        mul_le_mul_of_nonneg_right (hCnn x) (by positivity)

/-- Basis expansion of the Euclidean norm square:
`∑ⱼ ⟨ξ, eⱼ⟩² = ‖ξ‖²`. -/
theorem sum_inner_single_sq (ξ : ES) :
    ∑ j : Fin 3, (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 = ‖ξ‖ ^ 2 := by
  have hin : ∀ j : Fin 3,
      (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) = ξ j := by
    intro j
    rw [EuclideanSpace.inner_single_right]
    simp
  rw [Finset.sum_congr rfl fun j _ => by rw [hin j]]
  rw [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun j _ => by
    rw [Real.norm_eq_abs, sq_abs]

/-- Single-coordinate line-derivative wrapper. -/
def pd (j : Fin 3) (f : 𝓢(ES, ℂ)) : 𝓢(ES, ℂ) :=
  ∂_{EuclideanSpace.single j (1:ℝ)} f

theorem pd_def (j : Fin 3) (f : 𝓢(ES, ℂ)) :
    pd j f = ∂_{EuclideanSpace.single j (1:ℝ)} f := rfl

/-- The n = 1 rung in `pd` form. -/
theorem sum_integral_normSq_pd_eq (f : 𝓢(ES, ℂ)) :
    ∑ j : Fin 3, ∫ x : ES, ‖(pd j f) x‖ ^ 2
      = (2 * Real.pi) ^ 2 * ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 := by
  simp only [pd_def]
  exact sum_integral_normSq_lineDeriv_eq f

/-- **The generic multiplier collapse** (`pd` form): summing the
`‖ξ‖²`-weighted L² mass of `𝓕(∂ⱼf)` over the standard basis raises the
weight by two.  Proved with independent `have` equalities chained by a final
`rw` (a `calc` over this weighted derivative-transform integrand triggers a
`whnf` timeout; see the file header). -/
theorem sum_integral_norm_pow_mul_normSq_fourier_pd_2 (f : 𝓢(ES, ℂ)) :
    ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 (pd j f)) ξ‖ ^ 2
      = (2 * Real.pi) ^ 2 * ∫ ξ : ES, ‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have hpt : ∀ (j : Fin 3) (ξ : ES),
      ‖ξ‖ ^ 2 * ‖(𝓕 (pd j f)) ξ‖ ^ 2 =
      (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
        ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2)) := by
    intro j ξ
    rw [pd_def, norm_fourier_lineDerivOp_sq f (EuclideanSpace.single j (1:ℝ)) ξ]
    ring
  have hint : ∀ j : Fin 3, Integrable (fun ξ : ES =>
      (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
        ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2))) := by
    intro j
    refine (integrable_norm_pow_mul_normSq (𝓕 (pd j f)) 2).congr ?_
    filter_upwards with ξ
    exact hpt j ξ
  have e1 : ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 2 * ‖(𝓕 (pd j f)) ξ‖ ^ 2
      = ∑ j : Fin 3, ∫ ξ : ES,
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
            ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2)) :=
    Finset.sum_congr rfl fun j _ => integral_congr_ae
      (Filter.Eventually.of_forall fun ξ => hpt j ξ)
  have e2 : ∑ j : Fin 3, ∫ ξ : ES,
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
            ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2))
      = ∫ ξ : ES, ∑ j : Fin 3,
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
            ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2)) :=
    (integral_finsetSum _ fun j _ => hint j).symm
  have e3 : ∫ ξ : ES, ∑ j : Fin 3,
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
            ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2))
      = ∫ ξ : ES, (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [← Finset.sum_mul, sum_inner_single_sq]
    ring
  rw [e1, e2, e3, integral_const_mul]

/-- **The generic multiplier collapse** (`pd` form): summing the
`‖ξ‖⁴`-weighted L² mass of `𝓕(∂ⱼf)` over the standard basis raises the
weight by two. -/
theorem sum_integral_norm_pow_mul_normSq_fourier_pd_4 (f : 𝓢(ES, ℂ)) :
    ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 4 * ‖(𝓕 (pd j f)) ξ‖ ^ 2
      = (2 * Real.pi) ^ 2 * ∫ ξ : ES, ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have hpt : ∀ (j : Fin 3) (ξ : ES),
      ‖ξ‖ ^ 4 * ‖(𝓕 (pd j f)) ξ‖ ^ 2 =
      (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
        ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2)) := by
    intro j ξ
    rw [pd_def, norm_fourier_lineDerivOp_sq f (EuclideanSpace.single j (1:ℝ)) ξ]
    ring
  have hint : ∀ j : Fin 3, Integrable (fun ξ : ES =>
      (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
        ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2))) := by
    intro j
    refine (integrable_norm_pow_mul_normSq (𝓕 (pd j f)) 4).congr ?_
    filter_upwards with ξ
    exact hpt j ξ
  have e1 : ∑ j : Fin 3, ∫ ξ : ES, ‖ξ‖ ^ 4 * ‖(𝓕 (pd j f)) ξ‖ ^ 2
      = ∑ j : Fin 3, ∫ ξ : ES,
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
            ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2)) :=
    Finset.sum_congr rfl fun j _ => integral_congr_ae
      (Filter.Eventually.of_forall fun ξ => hpt j ξ)
  have e2 : ∑ j : Fin 3, ∫ ξ : ES,
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
            ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2))
      = ∫ ξ : ES, ∑ j : Fin 3,
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
            ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2)) :=
    (integral_finsetSum _ fun j _ => hint j).symm
  have e3 : ∫ ξ : ES, ∑ j : Fin 3,
          (inner ℝ ξ (EuclideanSpace.single j (1:ℝ))) ^ 2 *
            ((2 * Real.pi) ^ 2 * (‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2))
      = ∫ ξ : ES, (2 * Real.pi) ^ 2 * (‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [← Finset.sum_mul, sum_inner_single_sq]
    ring
  rw [e1, e2, e3, integral_const_mul]

/-- **The n = 2 weighted Plancherel rung** (`pd` form):
`∑ⱼ∑ᵢ ∫‖∂ᵢ∂ⱼf‖² = (2π)⁴ ∫‖ξ‖⁴‖𝓕f‖²`. -/
theorem sum_integral_normSq_pd_two_eq (f : 𝓢(ES, ℂ)) :
    ∑ j : Fin 3, ∑ i : Fin 3, ∫ x : ES, ‖(pd i (pd j f)) x‖ ^ 2
      = (2 * Real.pi) ^ 4 * ∫ ξ : ES, ‖ξ‖ ^ 4 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have h1 : ∑ j : Fin 3, ∑ i : Fin 3, ∫ x : ES, ‖(pd i (pd j f)) x‖ ^ 2
      = ∑ j : Fin 3, (2 * Real.pi) ^ 2 * ∫ ξ : ES, ‖ξ‖ ^ 2 *
          ‖(𝓕 (pd j f)) ξ‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ => sum_integral_normSq_pd_eq (pd j f)
  rw [h1, ← Finset.mul_sum, sum_integral_norm_pow_mul_normSq_fourier_pd_2 f]
  ring

/-- **The n = 3 weighted Plancherel rung** (`pd` form):
`∑ₗ∑ⱼ∑ᵢ ∫‖∂ᵢ∂ⱼ∂ₗf‖² = (2π)⁶ ∫‖ξ‖⁶‖𝓕f‖²`. -/
theorem sum_integral_normSq_pd_three_eq (f : 𝓢(ES, ℂ)) :
    ∑ l : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, ∫ x : ES,
        ‖(pd i (pd j (pd l f))) x‖ ^ 2
      = (2 * Real.pi) ^ 6 * ∫ ξ : ES, ‖ξ‖ ^ 6 * ‖(𝓕 f) ξ‖ ^ 2 := by
  have h1 : ∑ l : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, ∫ x : ES,
        ‖(pd i (pd j (pd l f))) x‖ ^ 2
      = ∑ l : Fin 3, (2 * Real.pi) ^ 4 * ∫ ξ : ES, ‖ξ‖ ^ 4 *
          ‖(𝓕 (pd l f)) ξ‖ ^ 2 :=
    Finset.sum_congr rfl fun l _ => sum_integral_normSq_pd_two_eq (pd l f)
  rw [h1, ← Finset.mul_sum, sum_integral_norm_pow_mul_normSq_fourier_pd_4 f]
  ring

end Navier.Analysis.FourierWeightedPlancherel
