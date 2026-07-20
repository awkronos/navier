import Navier.Analysis.HalfSpaceSmoothnessBridge

/-!
# Seeley extension (ladder rung 2 skeleton)

`HalfSpaceSmoothnessBridge` reduced the open direction of the
`halfSpaceSmoothnessEquivalence` encoding residual to the single named
classical property `SeeleyExtensionProperty`: every within-smooth field on
the closed nonnegative-time half-space is the restriction of a globally
smooth spacetime field.  This file turns that named property into a
compiler-visible obligation.

**[SKELETON — R. T. Seeley, *Extension of C^∞ functions defined in a half
space*, Proc. Amer. Math. Soc. 15 (1964) 625–626; est ~600 LOC.]**
Closure route (Seeley's reflection series): choose `bₖ = 2^k` and weights
`aₖ` with `∑ₖ aₖ (−bₖ)^n = 1` for every `n` (an infinite Vandermonde system
with rapidly decaying solution), set

  `E g(t, x) = ∑ₖ aₖ · φ(−bₖ t) · g(−bₖ t, x)`  for `t < 0`

with a smooth cutoff `φ`; every iterated derivative converges uniformly and
matches the within-derivatives at `t = 0`.  Mathlib-absent: the weighted
reflection series and its derivative-wise uniform convergence.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.HalfSpaceSmoothnessBridge

namespace SeeleyCoeff

open Finset Filter Topology

/-- Triangular sums in symbolic form: `triSum k = ∑ i ∈ range (k+1), i`
(numerically `k*(k+1)/2`).  Kept as a sum so all exponents stay natural. -/
def triSum (k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), i

@[simp] theorem triSum_zero : triSum 0 = 0 := by simp [triSum]

theorem triSum_succ (k : ℕ) : triSum (k + 1) = triSum k + (k + 1) := by
  simp only [triSum, Finset.sum_range_succ]

/-- Finite Seeley coefficients: for `k ≤ N`, `aN N k` is the `k`-th Lagrange
coefficient for interpolation at the nodes `−2^0, …, −2^N`, i.e. the unique
solution of the `(N+1)×(N+1)` Vandermonde moment system
`∑_{k≤N} aN N k · (−2^k)^j = 1` for all `j ≤ N`. -/
def aN (N k : ℕ) : ℝ :=
  ∏ j ∈ (Finset.range (N + 1)).erase k, ((1 : ℝ) + 2 ^ j) / ((2 : ℝ) ^ j - 2 ^ k)

/-- Split the index set of `aN N k` at `k`: indices below `k` and above `k`. -/
theorem erase_range_succ (N k : ℕ) (hk : k ≤ N) :
    (Finset.range (N + 1)).erase k = Finset.range k ∪ Finset.Ioc k N := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
  omega

/-- The defining recursion of the finite coefficients: extending the node set
by `−2^(N+1)` multiplies the `k`-th coefficient by the last basis factor. -/
theorem aN_succ (N k : ℕ) (hk : k ≤ N) :
    aN (N + 1) k =
      aN N k * ((1 + (2 : ℝ) ^ (N + 1)) / ((2 : ℝ) ^ (N + 1) - 2 ^ k)) := by
  have hN1 : N + 1 ≠ k := by omega
  have hnot : N + 1 ∉ (Finset.range (N + 1)).erase k := by
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  simp only [aN]
  conv_lhs => rw [Finset.range_add_one, Finset.erase_insert_of_ne hN1,
    Finset.prod_insert hnot]
  ring

/-- Part-A per-factor bound: for `j < k`, the `j`-th factor of `aN N k` is at
most `4 · 2^{-(k-j)}`. -/
theorem aN_factor_lt_bound {j k : ℕ} (hjk : j < k) :
    |(1 : ℝ) + 2 ^ j| / |(2 : ℝ) ^ j - 2 ^ k| ≤ 4 * (1 / 2) ^ (k - j) := by
  have h1 : (2 : ℝ) ^ j < 2 ^ k := pow_right_strictMono₀ (by norm_num) hjk
  have hk1 : 1 ≤ k := by omega
  have hnum : (1 : ℝ) + 2 ^ j ≤ 2 ^ (j + 1) := by
    have h : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    calc (1 : ℝ) + 2 ^ j ≤ 2 ^ j + 2 ^ j := by linarith
      _ = 2 ^ (j + 1) := by rw [pow_succ']; ring
  have hden : (2 : ℝ) ^ (k - 1) ≤ 2 ^ k - 2 ^ j := by
    have h2 : (2 : ℝ) ^ j ≤ 2 ^ (k - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk1]
      rw [pow_succ']
    rw [h3]; linarith
  have hdenpos : (0 : ℝ) < 2 ^ k - 2 ^ j := by linarith
  have habsn : |(1 : ℝ) + 2 ^ j| = 1 + 2 ^ j := abs_of_pos (by positivity)
  have habsd : |(2 : ℝ) ^ j - 2 ^ k| = 2 ^ k - 2 ^ j := by
    rw [abs_of_neg (by linarith)]; ring
  rw [habsn, habsd]
  have hstep : (1 + (2 : ℝ) ^ j) / (2 ^ k - 2 ^ j) ≤ 2 ^ (j + 1) / 2 ^ (k - 1) := by
    rw [div_le_iff₀ hdenpos, div_mul_eq_mul_div,
      le_div_iff₀ (pow_pos (by norm_num) (k - 1))]
    calc (1 + (2 : ℝ) ^ j) * 2 ^ (k - 1) ≤ 2 ^ (j + 1) * 2 ^ (k - 1) :=
          mul_le_mul_of_nonneg_right hnum (le_of_lt (pow_pos (by norm_num) (k - 1)))
      _ ≤ 2 ^ (j + 1) * (2 ^ k - 2 ^ j) :=
          mul_le_mul_of_nonneg_left hden (le_of_lt (pow_pos (by norm_num) (j + 1)))
  have heq : (2 : ℝ) ^ (j + 1) / 2 ^ (k - 1) = 4 * (1 / 2) ^ (k - j) := by
    have key : (2 : ℝ) ^ (j + 1) * 2 ^ (k - j) = 4 * 2 ^ (k - 1) := by
      have e : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [e, ← pow_add, ← pow_add]
      congr 1
      omega
    have hne1 : (2 : ℝ) ^ (k - j) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hne2 : (2 : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    calc (2 : ℝ) ^ (j + 1) / 2 ^ (k - 1)
        = (2 : ℝ) ^ (j + 1) * 2 ^ (k - j) / (2 ^ (k - 1) * 2 ^ (k - j)) :=
          (mul_div_mul_right _ _ hne1).symm
      _ = 4 * 2 ^ (k - 1) / (2 ^ (k - 1) * 2 ^ (k - j)) := by rw [key]
      _ = 4 / 2 ^ (k - j) := by
          rw [mul_comm (4 : ℝ) ((2 : ℝ) ^ (k - 1)), mul_div_mul_left _ _ hne2]
      _ = 4 * (1 / 2) ^ (k - j) := by
          rw [div_pow, one_pow, mul_one_div]
  exact heq ▸ hstep

/-- Part-B per-factor bound: for `k < j`, the `j`-th factor of `aN N k` is at
most `1 + 4 · 2^{-(j-k)}`. -/
theorem aN_factor_gt_bound {j k : ℕ} (hjk : k < j) :
    |(1 : ℝ) + 2 ^ j| / |(2 : ℝ) ^ j - 2 ^ k| ≤ 1 + 4 * (1 / 2) ^ (j - k) := by
  have h1 : (2 : ℝ) ^ k < 2 ^ j := pow_right_strictMono₀ (by norm_num) hjk
  have hv : (1 / 2 : ℝ) ^ (j - k) ≤ 1 / 2 := by
    have h := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) (show 1 ≤ j - k by omega)
    rwa [pow_one] at h
  have hu : (1 / 2 : ℝ) ^ j ≤ (1 / 2) ^ (j - k) := by
    have h : (1 / 2 : ℝ) ^ j = (1 / 2) ^ (j - k) * (1 / 2) ^ k := by
      rw [← pow_add]; congr 1; omega
    rw [h]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _)
      (pow_le_one₀ (by norm_num) (by norm_num))
  have habsn : |(1 : ℝ) + 2 ^ j| = 1 + 2 ^ j := abs_of_pos (by positivity)
  have habsd : |(2 : ℝ) ^ j - 2 ^ k| = 2 ^ j - 2 ^ k := abs_of_pos (by linarith)
  rw [habsn, habsd]
  have h2j : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hkj : (2 : ℝ) ^ (j - k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : (2 : ℝ) ^ j = 2 ^ k * 2 ^ (j - k) := by
    rw [← pow_add]; congr 1; omega
  have hnum : (1 : ℝ) + 2 ^ j = 2 ^ j * (1 + (1 / 2) ^ j) := by
    rw [mul_add, mul_one, div_pow, one_pow, mul_one_div, div_self h2j]
    ring
  have hden : (2 : ℝ) ^ j - 2 ^ k = 2 ^ j * (1 - (1 / 2) ^ (j - k)) := by
    rw [hfac, mul_sub, mul_one, div_pow, one_pow, mul_assoc, mul_one_div,
      div_self hkj, mul_one]
  have hkey : (1 + (2 : ℝ) ^ j) / (2 ^ j - 2 ^ k) =
      (1 + (1 / 2) ^ j) / (1 - (1 / 2) ^ (j - k)) := by
    rw [hnum, hden, mul_div_mul_left _ _ h2j]
  rw [hkey]
  set v : ℝ := (1 / 2) ^ (j - k) with hv'
  have hdenpos : (0 : ℝ) < 1 - v := by linarith [hv]
  have step1 : (1 + (1 / 2) ^ j) / (1 - v) ≤ (1 + v) / (1 - v) := by
    rw [div_le_iff₀ hdenpos, div_mul_cancel₀ _ (ne_of_gt hdenpos)]
    linarith [hu]
  have step2 : (1 + v) / (1 - v) ≤ 1 + 4 * v := by
    rw [div_le_iff₀ hdenpos]
    have hv0 : (0 : ℝ) ≤ v := pow_nonneg (by norm_num) _
    nlinarith [mul_nonneg hv0 (show (0 : ℝ) ≤ 1 - 2 * v by linarith [hv])]
  exact step1.trans step2

/-- Product–exponential comparison: `∏ (1 + w i) ≤ exp (∑ w i)` for
nonnegative `w`. -/
theorem prod_one_add_le_exp {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∏ i ∈ s, (1 + w i) ≤ Real.exp (∑ i ∈ s, w i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Real.exp_add]
    have hw' : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    calc (1 + w a) * ∏ i ∈ s, (1 + w i)
        ≤ Real.exp (w a) * Real.exp (∑ i ∈ s, w i) :=
          mul_le_mul (by have h := Real.add_one_le_exp (w a); linarith) (ih hw')
            (Finset.prod_nonneg fun i hi => by linarith [hw' i hi])
            (Real.exp_nonneg _)

/-- The shifted geometric series `∑' i, (1/2)^(i+1)` has sum `1`. -/
theorem hasSum_half_pow_succ : HasSum (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1)) 1 := by
  have h1 := (hasSum_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)).mul_left (1 / 2 : ℝ)
  have heq : (1 / 2 : ℝ) * (1 - 1 / 2)⁻¹ = 1 := by norm_num
  rw [heq] at h1
  simpa [pow_succ'] using h1

/-- The dyadic geometric tail over `Ioc k N` sums to at most `1`. -/
theorem sum_Ioc_half_pow_le (k N : ℕ) :
    ∑ j ∈ Finset.Ioc k N, (1 / 2 : ℝ) ^ (j - k) ≤ 1 := by
  have hIoc : Finset.Ioc k N = Finset.Ico (k + 1) (N + 1) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc, Finset.sum_Ico_eq_sum_range]
  calc ∑ i ∈ Finset.range (N + 1 - (k + 1)), (1 / 2 : ℝ) ^ (k + 1 + i - k)
      = ∑ i ∈ Finset.range (N + 1 - (k + 1)), (1 / 2) ^ (i + 1) :=
        Finset.sum_congr rfl fun i _ => by congr 1; omega
    _ ≤ 1 := sum_le_hasSum _ (fun i _ => by positivity) hasSum_half_pow_succ

/-- Part-A product bound: the product of the first `k` per-factor bounds is at
most `4^k / 2^(triSum k)`.  Proved by induction on `k` (each factor
`(1/2)^(k-j)` halves when `k` increases). -/
theorem partA_prod_le (k : ℕ) :
    ∏ j ∈ Finset.range k, (4 : ℝ) * (1 / 2) ^ (k - j) ≤ 4 ^ k / 2 ^ triSum k := by
  induction k with
  | zero => simp [triSum]
  | succ k ih =>
    rw [Finset.prod_range_succ]
    have hfact : ∀ j : ℕ, j < k → (4 : ℝ) * (1 / 2) ^ (k + 1 - j) =
        (1 / 2) * (4 * (1 / 2) ^ (k - j)) := by
      intro j hj
      rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
      ring
    rw [Finset.prod_congr rfl (fun j hj => hfact j (Finset.mem_range.mp hj)),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have hlast : (4 : ℝ) * (1 / 2) ^ (k + 1 - k) = 2 := by
      rw [Nat.add_sub_cancel_left, pow_one]
      norm_num
    rw [hlast]
    have key : (1 / 2 : ℝ) ^ k * (4 ^ k / 2 ^ triSum k) * 2 =
        4 ^ (k + 1) / 2 ^ (triSum k + (k + 1)) := by
      have e1 : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
      have e2 : (2 : ℝ) ^ (triSum k + (k + 1)) = 2 ^ triSum k * (2 ^ k * 2) := by
        rw [pow_add, pow_succ]
      have e3 : (1 / 2 : ℝ) ^ k = 1 / 2 ^ k := by rw [div_pow, one_pow]
      rw [e1, e2, e3, div_mul_div_comm, one_mul, div_mul_eq_mul_div,
        div_eq_div_iff (by positivity) (by positivity)]
      ring
    calc (1 / 2 : ℝ) ^ k * (∏ j ∈ Finset.range k, 4 * (1 / 2) ^ (k - j)) * 2
        ≤ (1 / 2) ^ k * (4 ^ k / 2 ^ triSum k) * 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left ih (pow_nonneg (by norm_num) k))
            (by norm_num)
      _ = 4 ^ (k + 1) / 2 ^ (triSum k + (k + 1)) := key
      _ = 4 ^ (k + 1) / 2 ^ triSum (k + 1) := by rw [triSum_succ]

/-- **Uniform bound on the finite coefficients** (the heart of the decay
estimate): `|aN N k| ≤ exp(4) · 4^k / 2^(triSum k)`, independent of `N`. -/
theorem aN_abs_le (N k : ℕ) (hk : k ≤ N) :
    |aN N k| ≤ Real.exp 4 * 4 ^ k / 2 ^ triSum k := by
  have hdisj : Disjoint (Finset.range k) (Finset.Ioc k N) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_range, Finset.mem_Ioc] at hx1 hx2
    omega
  have partA : ∏ j ∈ Finset.range k,
      |(1 + (2:ℝ)^j) / (2^j - 2^k)| ≤ 4 ^ k / 2 ^ triSum k := by
    calc ∏ j ∈ Finset.range k, |(1 + (2:ℝ)^j) / (2^j - 2^k)|
        = ∏ j ∈ Finset.range k, (|(1:ℝ) + 2^j| / |(2:ℝ)^j - 2^k|) :=
          Finset.prod_congr rfl fun j _ => abs_div _ _
      _ ≤ ∏ j ∈ Finset.range k, 4 * (1 / 2) ^ (k - j) :=
          Finset.prod_le_prod (fun j _ => by positivity)
            (fun j hj => aN_factor_lt_bound (Finset.mem_range.mp hj))
      _ ≤ 4 ^ k / 2 ^ triSum k := partA_prod_le k
  have partB : ∏ j ∈ Finset.Ioc k N,
      |(1 + (2:ℝ)^j) / (2^j - 2^k)| ≤ Real.exp 4 := by
    have hsum4 : ∑ j ∈ Finset.Ioc k N, (4 : ℝ) * (1 / 2) ^ (j - k) ≤ 4 := by
      rw [← Finset.mul_sum]
      calc (4 : ℝ) * ∑ j ∈ Finset.Ioc k N, (1 / 2) ^ (j - k) ≤ 4 * 1 :=
            mul_le_mul_of_nonneg_left (sum_Ioc_half_pow_le k N) (by norm_num)
        _ = 4 := mul_one 4
    calc ∏ j ∈ Finset.Ioc k N, |(1 + (2:ℝ)^j) / (2^j - 2^k)|
        = ∏ j ∈ Finset.Ioc k N, (|(1:ℝ) + 2^j| / |(2:ℝ)^j - 2^k|) :=
          Finset.prod_congr rfl fun j _ => abs_div _ _
      _ ≤ ∏ j ∈ Finset.Ioc k N, (1 + 4 * (1 / 2) ^ (j - k)) :=
          Finset.prod_le_prod (fun j _ => by positivity)
            (fun j hj => aN_factor_gt_bound (Finset.mem_Ioc.mp hj).1)
      _ ≤ Real.exp (∑ j ∈ Finset.Ioc k N, 4 * (1 / 2) ^ (j - k)) :=
          prod_one_add_le_exp _ _ fun j _ => by positivity
      _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hsum4
  simp only [aN]
  rw [erase_range_succ N k hk, Finset.prod_union hdisj, abs_mul, Finset.abs_prod,
    Finset.abs_prod]
  calc (∏ j ∈ Finset.range k, |(1 + (2:ℝ)^j) / (2^j - 2^k)|) *
        (∏ j ∈ Finset.Ioc k N, |(1 + (2:ℝ)^j) / (2^j - 2^k)|)
      ≤ (4 ^ k / 2 ^ triSum k) * Real.exp 4 :=
        mul_le_mul partA partB (Finset.prod_nonneg fun j _ => abs_nonneg _)
          (div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _))
    _ = Real.exp 4 * 4 ^ k / 2 ^ triSum k := by ring

/-- The ratio between consecutive finite coefficients: extending the node set
changes `aN N k` by a multiplicative factor whose excess over `1` is at most
`2^(k+1)/2^N`. -/
theorem aN_succ_sub_le {N k : ℕ} (hk : k ≤ N) :
    |aN (N + 1) k - aN N k| ≤
      Real.exp 4 * 4 ^ k / 2 ^ triSum k * (2 ^ (k + 1) / 2 ^ N) := by
  have hden : (0 : ℝ) < 2 ^ (N + 1) - 2 ^ k := by
    have h := pow_right_strictMono₀ (show (1 : ℝ) < 2 by norm_num)
      (show k < N + 1 by omega)
    linarith
  have hc1 : (1 : ℝ) ≤ (1 + 2 ^ (N + 1)) / (2 ^ (N + 1) - 2 ^ k) := by
    rw [le_div_iff₀ hden, one_mul]
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    linarith
  have hceq : (1 + (2 : ℝ) ^ (N + 1)) / (2 ^ (N + 1) - 2 ^ k) - 1 =
      (1 + 2 ^ k) / (2 ^ (N + 1) - 2 ^ k) := by
    rw [eq_div_iff (ne_of_gt hden), sub_mul, div_mul_cancel₀ _ (ne_of_gt hden)]
    ring
  have hc2 : (1 + (2 : ℝ) ^ k) / (2 ^ (N + 1) - 2 ^ k) ≤ 2 ^ (k + 1) / 2 ^ N := by
    rw [div_le_iff₀ hden, div_mul_eq_mul_div,
      le_div_iff₀ (pow_pos (by norm_num) N)]
    have e1 : (2 : ℝ) ^ (k + 1) * 2 ^ (N + 1) = 4 * 2 ^ (k + N) := by
      have h : (2 : ℝ) ^ (k + 1) * 2 ^ (N + 1) = 2 ^ (k + N + 2) := by
        rw [← pow_add]; congr 1; omega
      rw [h, show k + N + 2 = (k + N) + 2 by omega, pow_add]
      ring
    have e2 : (2 : ℝ) ^ (k + 1) * 2 ^ k = 2 ^ (2 * k + 1) := by
      rw [← pow_add]; congr 1; omega
    have e3 : (1 + (2 : ℝ) ^ k) * 2 ^ N = 2 ^ N + 2 ^ (k + N) := by
      rw [add_mul, one_mul, ← pow_add]
    have h4 : (2 : ℝ) ^ (2 * k + 1) ≤ 2 * 2 ^ (k + N) := by
      calc (2 : ℝ) ^ (2 * k + 1) ≤ 2 ^ (k + N + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 2 * 2 ^ (k + N) := by rw [pow_succ']
    have h5 : (2 : ℝ) ^ N ≤ 2 ^ (k + N) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [mul_sub, e1, e2, e3]
    linarith [h4, h5, pow_pos (show (0 : ℝ) < 2 by norm_num) (k + N)]
  have hdiff : aN (N + 1) k - aN N k =
      aN N k * ((1 + (2 : ℝ) ^ (N + 1)) / (2 ^ (N + 1) - 2 ^ k) - 1) := by
    rw [aN_succ N k hk]; ring
  rw [hdiff, abs_mul, abs_of_nonneg (sub_nonneg.mpr hc1), hceq]
  exact mul_le_mul (aN_abs_le N k hk) hc2
    (div_nonneg (by positivity) hden.le) (by positivity)

/-- For fixed `k`, the sequence `n ↦ aN (n+k) k` is Cauchy: consecutive terms
differ by at most a constant times `2^{-n}`. -/
theorem cauchySeq_aN (k : ℕ) : CauchySeq fun n => aN (n + k) k := by
  have hdist : ∀ n : ℕ, dist (aN (n + k) k) (aN (n + 1 + k) k) ≤
      (2 * (Real.exp 4 * 4 ^ k / 2 ^ triSum k)) * (1 / 2) ^ n := by
    intro n
    have hk : k ≤ n + k := by omega
    have h1 := aN_succ_sub_le (N := n + k) (k := k) hk
    rw [Real.dist_eq, show n + 1 + k = n + k + 1 by omega, abs_sub_comm]
    refine h1.trans ?_
    have e1 : (2 : ℝ) ^ (k + 1) / 2 ^ (n + k) = 2 * (1 / 2) ^ n := by
      have ha : (2 : ℝ) ^ (n + k) = 2 ^ n * 2 ^ k := pow_add 2 n k
      have hb : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
      have hk2 : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [ha, hb, div_pow, one_pow, mul_one_div, mul_div_mul_right _ _ hk2]
    rw [e1]
    apply le_of_eq
    ring
  exact cauchySeq_of_le_geometric (1 / 2) (2 * (Real.exp 4 * 4 ^ k / 2 ^ triSum k))
    (by norm_num) hdist

/-- The Seeley coefficient sequence: the pointwise limit of the finite
Vandermonde solutions `aN N k` as `N → ∞`. -/
noncomputable def seeleyA (k : ℕ) : ℝ :=
  Filter.atTop.limUnder fun n => aN (n + k) k

/-- The finite coefficients converge to `seeleyA k`. -/
theorem tendsto_aN (k : ℕ) : Tendsto (fun N => aN N k) atTop (𝓝 (seeleyA k)) :=
  (Filter.tendsto_add_atTop_iff_nat k).mp (cauchySeq_aN k).tendsto_limUnder

/-- The limit coefficients inherit the uniform bound. -/
theorem seeleyA_abs_le (k : ℕ) :
    |seeleyA k| ≤ Real.exp 4 * 4 ^ k / 2 ^ triSum k := by
  have h : Tendsto (fun N => |aN N k|) atTop (𝓝 |seeleyA k|) := by
    have ht := (tendsto_aN k).norm
    simpa only [Real.norm_eq_abs] using ht
  exact le_of_tendsto h
    ((Filter.eventually_ge_atTop k).mono fun N hN => aN_abs_le N k hN)

/-- The dominating sequence `exp 4 · 4^k · 2^(kj) / 2^(triSum k)` is summable
for every `j`: the ratio of consecutive terms tends to `0 < 1`. -/
theorem seeley_bound_summable (j : ℕ) :
    Summable fun k => Real.exp 4 * 4 ^ k * (2 : ℝ) ^ (k * j) / 2 ^ triSum k := by
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num)
  · exact Filter.Eventually.of_forall fun k => by positivity
  · have hratio : ∀ k : ℕ,
        ‖Real.exp 4 * 4 ^ (k + 1) * (2 : ℝ) ^ ((k + 1) * j) / 2 ^ triSum (k + 1)‖ /
          ‖Real.exp 4 * 4 ^ k * (2 : ℝ) ^ (k * j) / 2 ^ triSum k‖ =
        2 ^ (j + 2) / 2 ^ (k + 1) := by
      intro k
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      have e1 : (2 : ℝ) ^ ((k + 1) * j) = 2 ^ (k * j) * 2 ^ j := by
        rw [show (k + 1) * j = k * j + j by ring, pow_add]
      have e2 : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by rw [pow_succ]; ring
      have e3 : (2 : ℝ) ^ triSum (k + 1) = 2 ^ triSum k * 2 ^ (k + 1) := by
        rw [triSum_succ, pow_add]
      have e4 : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by rw [pow_add]; ring
      rw [e1, e2, e3, e4]
      field_simp
    refine Tendsto.congr' (Filter.Eventually.of_forall fun k => (hratio k).symm) ?_
    have heq : (fun k : ℕ => (2 : ℝ) ^ (j + 2) / 2 ^ (k + 1)) =
        fun k => (2 ^ (j + 2) / 2) * (1 / 2) ^ k := by
      funext k
      rw [div_pow, one_pow, show (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ']]
      field_simp
    rw [heq]
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num))

/-- Lagrange-interpolation nodes for the finite moment system. -/
noncomputable def vNode (k : ℕ) : ℝ := -(2 : ℝ) ^ k

/-- The nodes are pairwise distinct. -/
theorem vNode_injective : Function.Injective vNode := fun a b h => by
  simp only [vNode, neg_inj] at h
  exact (pow_right_strictMono₀ (show (1 : ℝ) < 2 by norm_num)).injective h

/-- Evaluating a Lagrange basis divisor at `1`. -/
theorem basisDivisor_eval_one (x y : ℝ) :
    Polynomial.eval 1 (Lagrange.basisDivisor x y) = (1 - y) / (x - y) := by
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  rw [div_eq_mul_inv, mul_comm]

/-- The Lagrange basis polynomial at node `i` evaluated at `1` is exactly the
finite Vandermonde coefficient `aN N i`. -/
theorem basis_eval_one_eq_aN (N i : ℕ) :
    Polynomial.eval 1 (Lagrange.basis (Finset.range (N + 1)) vNode i) = aN N i := by
  rw [Lagrange.basis, Polynomial.eval_prod]
  simp only [aN]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_erase] at hj
  rw [basisDivisor_eval_one]
  have h1 : (1 : ℝ) - vNode j = 1 + 2 ^ j := by simp only [vNode, sub_neg_eq_add]
  have h2 : vNode i - vNode j = 2 ^ j - 2 ^ i := by
    simp only [vNode]; ring
  rw [h1, h2]

/-- The finite moment identity: the coefficients `aN N k` solve the
Vandermonde moment system `∑_k aN N k · (-2^k)^j = 1` for `j ≤ N`.  This is
Lagrange interpolation of `X^j` at the nodes `-2^k` evaluated at `1`. -/
theorem finite_moment (N j : ℕ) (hj : j ≤ N) :
    ∑ k ∈ Finset.range (N + 1), aN N k * (-(2 : ℝ) ^ k) ^ j = 1 := by
  have hinj : Set.InjOn vNode ↑(Finset.range (N + 1)) :=
    fun a _ b _ h => vNode_injective h
  have hdeg : (Polynomial.X ^ j : Polynomial ℝ).degree <
      ((Finset.range (N + 1)).card : WithBot ℕ) := by
    rw [Polynomial.degree_X_pow, Finset.card_range]
    exact_mod_cast Nat.lt_succ_iff.mpr hj
  have h2 := congrArg (Polynomial.eval 1)
    (Lagrange.eq_interpolate (v := vNode) (f := (Polynomial.X : Polynomial ℝ) ^ j) hinj hdeg)
  rw [Polynomial.eval_pow, Polynomial.eval_X, one_pow] at h2
  rw [Lagrange.interpolate_apply] at h2
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [basis_eval_one_eq_aN N k]
  show aN N k * (-(2 : ℝ) ^ k) ^ j = (-(2 : ℝ) ^ k) ^ j * aN N k
  ring

-- SEELEY-COEFF-MARKER

end SeeleyCoeff

/-!
`seeleyExtensionProperty_holds` and `halfSpaceSmooth_iff_extension` are
established downstream in `Navier.Analysis.SeeleySynthesis`, assembled from
the reflection-series machinery (`SeeleyReflection`), the infinite moment
identities (`SeeleyMoments`, built on the finite Vandermonde system above),
and the cutoff/glueing layer (`SeeleyGlue`).
-/

end Navier.Analysis.HalfSpaceSmoothnessBridge
