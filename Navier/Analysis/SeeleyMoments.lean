import Navier.Analysis.SeeleyExtension

/-!
# Seeley coefficients — the infinite moment identities

The skeleton `Navier/Analysis/SeeleyExtension.lean` builds the finite
Vandermonde solutions `aN N k` (nodes `−2^k`, `k ≤ N`), proves the uniform
bound `|aN N k| ≤ exp 4 · 4^k / 2^(triSum k)`, and passes to the pointwise
limit `seeleyA k`.  This leaf establishes the **infinite Seeley moment
system**, the algebraic heart of the reflection-series extension:

  `∑' k, seeleyA k · (−2^k)^j = 1`  for every `j : ℕ`.

At `t → 0⁻` the `j`-th time derivative of the Seeley series
`∑ₖ aₖ φ(−2^k t) g(−2^k t, x)` formally tends to
`(∑ₖ aₖ (−2^k)^j) · ∂_t^j g(0⁺, x)`; the moment identity is exactly what
collapses that limit to `∂_t^j g(0⁺, x)` and makes the extension `C^∞`
across the boundary (Seeley, Proc. Amer. Math. Soc. 15 (1964) 625–626).

**Established here** (all `#print axioms ⊆ {propext, Classical.choice,
Quot.sound}`):

- `summable_seeleyA_abs_pow` — absolute summability of `|seeleyA k|·2^{kj}`
  for every `j` (super-polynomial decay of the coefficients);
- `summable_seeleyA_mul_pow` — summability of the signed moment terms;
- `tendsto_seeleyA_mul_two_pow` — `seeleyA k · 2^{kj} → 0` for every `j`;
- `seeley_moment` — the infinite moment identity `∑' seeleyA k · (−2^k)^j = 1`,
  proved by Tannery's dominated convergence theorem from the finite
  Vandermonde identities `finite_moment` and the uniform coefficient bound;
- `seeley_moment_zero` — the `j = 0` case `∑' seeleyA k = 1`.

**Residual** (the rung-2 analytic half, Seeley 1964, est ~450 LOC):
the reflection series itself — a `C^∞` cutoff `φ` with `φ = 1` on `[0,2]`
supported in `(−1,3)`, termwise smoothness of the summands, uniform
convergence of all derivative series on `t ≤ 0` (the summability leaves
above are the coefficient input), matching of all one-sided derivatives at
`t = 0` (via `seeley_moment`), and the two-sided `C^∞` glueing that builds
`HalfSpaceSmoothExtension` — closing `seeleyExtensionProperty_holds`.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.HalfSpaceSmoothnessBridge.SeeleyCoeff

open Finset Filter Topology

/-- The dominating bound of the skeleton, reindexed for multiplication by
`2^(k*j)`: `|seeleyA k| * 2^(k*j) ≤ exp 4 * 4^k * 2^(k*j) / 2^triSum k`. -/
theorem seeleyA_abs_mul_two_pow_le (j k : ℕ) :
    |seeleyA k| * (2 : ℝ) ^ (k * j) ≤
      Real.exp 4 * 4 ^ k * (2 : ℝ) ^ (k * j) / 2 ^ triSum k := by
  have h := mul_le_mul_of_nonneg_right (seeleyA_abs_le k) (by positivity :
    (0 : ℝ) ≤ 2 ^ (k * j))
  rwa [div_mul_eq_mul_div] at h

/-- **Absolute summability with arbitrary dyadic-polynomial weight**: the
Seeley coefficients decay faster than any power of `2^k`.  This is the
coefficient input to the uniform convergence of every derivative series of
the reflection extension. -/
theorem summable_seeleyA_abs_pow (j : ℕ) :
    Summable fun k => |seeleyA k| * (2 : ℝ) ^ (k * j) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => seeleyA_abs_mul_two_pow_le j k) (seeley_bound_summable j)

/-- Absolute-value normalization of a moment term: `|a * (−2^k)^j| =
|a| * 2^(k*j)`. -/
theorem abs_mul_neg_two_pow (a : ℝ) (j k : ℕ) :
    |a * (-(2 : ℝ) ^ k) ^ j| = |a| * (2 : ℝ) ^ (k * j) := by
  have h1 : |(-(2 : ℝ) ^ k) ^ j| = (2 : ℝ) ^ (k * j) := by
    rw [abs_pow, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ k),
      ← pow_mul]
  rw [abs_mul, h1]

/-- Summability of the signed moment terms `seeleyA k * (−2^k)^j`. -/
theorem summable_seeleyA_mul_pow (j : ℕ) :
    Summable fun k => seeleyA k * (-(2 : ℝ) ^ k) ^ j := by
  apply Summable.of_norm_bounded (seeley_bound_summable j) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul_neg_two_pow]
  exact seeleyA_abs_mul_two_pow_le j k

/-- **Super-polynomial decay**: `seeleyA k * 2^(k*j) → 0` for every `j`. -/
theorem tendsto_seeleyA_mul_two_pow (j : ℕ) :
    Tendsto (fun k => seeleyA k * (2 : ℝ) ^ (k * j)) atTop (𝓝 0) := by
  have h0 := (summable_seeleyA_mul_pow j).tendsto_atTop_zero
  have hsign : (fun k => seeleyA k * (2 : ℝ) ^ (k * j)) =
      fun k => (-1 : ℝ) ^ j * (seeleyA k * (-(2 : ℝ) ^ k) ^ j) := by
    funext k
    have e : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by
      rw [← mul_pow]; norm_num
    have e2 : (-(2 : ℝ) ^ k) ^ j = (-1 : ℝ) ^ j * (2 ^ k) ^ j := neg_pow _ _
    calc seeleyA k * (2 : ℝ) ^ (k * j)
        = seeleyA k * (2 ^ k) ^ j := by rw [pow_mul]
      _ = ((-1 : ℝ) ^ j * (-1) ^ j) * (seeleyA k * (2 ^ k) ^ j) := by
          rw [e, one_mul]
      _ = (-1 : ℝ) ^ j * (seeleyA k * (-(2 : ℝ) ^ k) ^ j) := by
          rw [e2]; ring
  rw [hsign]
  simpa using h0.const_mul ((-1 : ℝ) ^ j)

/-- The partial sums of the moment series converge to the infinite sum:
Tannery's theorem applied to the truncated finite-Vandermonde sums. -/
theorem tendsto_sum_aN_moment (j : ℕ) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), aN N k * (-(2 : ℝ) ^ k) ^ j)
      atTop (𝓝 (∑' k, seeleyA k * (-(2 : ℝ) ^ k) ^ j)) := by
  set bound : ℕ → ℝ := fun k =>
    2 * (Real.exp 4 * 4 ^ k * (2 : ℝ) ^ (k * j) / 2 ^ triSum k)
  have hbound_sum : Summable bound :=
    (seeley_bound_summable j).mul_left 2
  have hterm : ∀ k : ℕ, Tendsto (fun N =>
      if k ≤ N then aN N k * (-(2 : ℝ) ^ k) ^ j else 0) atTop
      (𝓝 (seeleyA k * (-(2 : ℝ) ^ k) ^ j)) := by
    intro k
    apply Tendsto.congr' ((eventually_ge_atTop k).mono fun N hN => by
      rw [if_pos hN])
    exact (tendsto_aN k).mul_const _
  have hbound : ∀ᶠ N in atTop, ∀ k : ℕ,
      ‖if k ≤ N then aN N k * (-(2 : ℝ) ^ k) ^ j else 0‖ ≤ bound k := by
    refine Filter.Eventually.of_forall fun N k => ?_
    by_cases hk : k ≤ N
    · rw [if_pos hk, Real.norm_eq_abs, abs_mul_neg_two_pow]
      calc |aN N k| * (2 : ℝ) ^ (k * j)
          ≤ (Real.exp 4 * 4 ^ k / 2 ^ triSum k) * (2 : ℝ) ^ (k * j) :=
            mul_le_mul_of_nonneg_right (aN_abs_le N k hk) (by positivity)
        _ = Real.exp 4 * 4 ^ k * (2 : ℝ) ^ (k * j) / 2 ^ triSum k := by
            rw [div_mul_eq_mul_div]
        _ ≤ bound k := by
            have hpos : (0 : ℝ) ≤
                Real.exp 4 * 4 ^ k * (2 : ℝ) ^ (k * j) / 2 ^ triSum k := by
              positivity
            simp only [bound]
            linarith
    · rw [if_neg hk, norm_zero]
      exact mul_nonneg (by norm_num) (by positivity)
  have htan := tendsto_tsum_of_dominated_convergence hbound_sum hterm hbound
  refine htan.congr' (Filter.Eventually.of_forall fun N => ?_)
  rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun k hk => by
    rw [if_neg]
    simp only [Finset.mem_range] at hk
    omega)]
  exact Finset.sum_congr rfl fun b hb => by
    rw [if_pos (Finset.mem_range_succ_iff.mp hb)]

/-- **The infinite Seeley moment identity**: `∑' k, seeleyA k * (−2^k)^j = 1`
for every `j`.  The limit coefficients solve the full infinite Vandermonde
system — the exact algebraic content of derivative matching at the boundary
in Seeley's extension theorem. -/
theorem seeley_moment (j : ℕ) :
    ∑' k, seeleyA k * (-(2 : ℝ) ^ k) ^ j = 1 := by
  have hconst : Tendsto
      (fun N => ∑ k ∈ Finset.range (N + 1), aN N k * (-(2 : ℝ) ^ k) ^ j)
      atTop (𝓝 1) := by
    apply Tendsto.congr' ((eventually_ge_atTop j).mono fun N hN =>
      (finite_moment N j hN).symm)
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (tendsto_sum_aN_moment j) hconst

/-- The zeroth moment: the Seeley coefficients sum to `1` (the extension
interpolates the boundary value). -/
theorem seeley_moment_zero : ∑' k, seeleyA k = 1 := by
  have h := seeley_moment 0
  simpa using h

end Navier.Analysis.HalfSpaceSmoothnessBridge.SeeleyCoeff
