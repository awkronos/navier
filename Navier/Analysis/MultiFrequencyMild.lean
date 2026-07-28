import Navier.Analysis.FrequencyCascadeObstruction

/-!
# Multi-frequency mild layer: the honest Galerkin truncation

`FrequencyMildGlobal` proved unconditional global regularity at ONE frequency.
This file lays the multi-frequency mild layer (ladder rung 3), with the
cross-mode transport term **explicit** — the frequency-cascade obstruction
(`FrequencyCascadeObstruction`) is its spec: the diagonal cancels on transverse
states, the cross terms must be *controlled*, never cancelled.

## The honest truncation

For frequencies `q : Fin n → E3`, the convective interaction of modes `i,j`
outputs at the **sum frequency** `q i + q j`; a Galerkin truncation keeps only
outputs landing back in the frequency set.  `truncatedConvectionSymbol` places
`⟪q j, v i⟫ • w j` at every `k` with `q i + q j = q k`.

Certified here (no sorry):

* `truncatedSymbol_eq_zero_of_no_resonance` — no pair sums into the set ⟹
  zero nonlinearity.
* `multiMild_oneFrequency_heatFlow` — at one nonzero frequency the
  self-interaction exits the set, so the honest truncated mild equation
  collapses to the free heat–Leray flow **without any transversality
  hypothesis** — consistent with (and freer than) `FrequencyMildGlobal`.
* `truncatedSymbol_resonantTriple` — for a resonant triple
  `q i + q j = q k` (and no other resonance at `k`), the output at `k` is
  **exactly** the `crossInteraction` of the obstruction file.
* `truncated_cascade_witness` — a concrete resonant triple with per-mode
  transverse (divergence-free) data whose truncated nonlinearity is nonzero:
  the cascade survives the honest truncation, as the obstruction predicted.
* `truncatedConvection_diff_sum_norm_le` — bilinear (Kato-type quadratic)
  Lipschitz bound for the honest Galerkin nonlinearity.
* `isMultiMildSolutionOn_unique` — uniqueness on a common horizon
  (Grönwall/contraction: `Δ t ≤ L ∫₀ᵗ Δ` forces `Δ ≡ 0`).
* `multiMild_inner_frequency_eq_zero` — per-mode transversality is automatic
  (the Duhamel integrand is Leray-projected, hence pointwise transverse).
* `continuousOn_Ico_of_forall_lt`, `continuousOn_truncatedSymbol`,
  `truncatedSymbol_norm_le_of_bound`, `integrableOn_heatWeighted`,
  `continuousOn_primitive_Icc_of_integrableOn` — the five analytic leaves of the
  continuation argument.
* `multiMild_extends_of_apriori_bound` — **the finite-mode continuation criterion**:
  a solution on every `[0,T']`, `T' < T`, with a uniform amplitude bound extends to
  the closed horizon `[0,T]`.  The extension is the Duhamel formula itself; the
  a-priori bound is what makes its integrand integrable up to `T`.

## The product Duhamel contraction (certified inputs)

* `multiDuhamelImage`, `truncatedSymbol_diff_norm_le_sup`,
  `continuousOn_multiDuhamelImage`, `norm_multiDuhamelImage_sub_heat_le` — the
  self-map, sup-norm Lipschitz and ball-invariance inputs to the Banach fixed point.
* `multiPicard`, `multiPicard_norm_le`, `multiPicard_continuousOn`,
  `norm_multiDuhamelImage_sub_le`, `continuousOn_duhamelIntegrand`,
  `intervalIntegrable_duhamelIntegrand` — the explicit Picard iteration: ball
  invariance, continuity of every iterate, and the sup-norm Lipschitz estimate that
  makes the Duhamel map a strict contraction for a short horizon.
* `exists_multiMild_fixedPoint_of_smallHorizon` — the contraction core: under
  `M + K·T ≤ R` and `L·T ≤ 1/2` the Picard iterates converge uniformly on `[0,T]` to a
  continuous, `R`-bounded fixed point of `multiDuhamelImage`.
* `exists_multiMild_shortHorizon` — the product Duhamel contraction itself
  [Kato, Math. Z. 187 (1984) §2], instantiating the core at
  `R = ∑ₘ‖u₀ ₘ‖ + 1` and `T = 1/(2(K+L+1))`.
* `exists_isMultiMildSolutionOn_local` — local existence on the CLOSED horizon,
  derived from the short-horizon contraction plus the continuation criterion.

This file carries no `sorry`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace Navier.Analysis.MultiFrequencyMild

open Navier.Analysis.LerayProjection
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.FrequencyDuhamel
open Navier.Analysis.FrequencyCascadeObstruction

open scoped Classical

/-!
## The truncated convection symbol
-/

/-- The Galerkin-truncated Navier–Stokes convection symbol on the frequency
set `q`: the pair `(i,j)` contributes the transport term `⟪q j, v i⟫ • w j`
at every output `k` whose frequency is the exact sum `q i + q j`.  Outputs
landing outside the set are discarded (the R7 generated-support growth is the
statement that they are always generated). -/
def truncatedConvectionSymbol {n : ℕ} (q : Fin n → E3)
    (v w : Fin n → E3) (k : Fin n) : E3 :=
  ∑ i : Fin n, ∑ j : Fin n,
    if q i + q j = q k then (inner ℝ (q j) (v i)) • w j else 0

/-- If no pair of set frequencies sums to `q k`, the truncated nonlinearity
vanishes at `k`. -/
theorem truncatedSymbol_eq_zero_of_no_resonance {n : ℕ}
    (q : Fin n → E3) (v w : Fin n → E3) (k : Fin n)
    (hno : ∀ i j : Fin n, q i + q j ≠ q k) :
    truncatedConvectionSymbol q v w k = 0 := by
  classical
  unfold truncatedConvectionSymbol
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [hno i j]

/-- **Resonant-triple reduction.**  If `q i + q j = q k` is the ONLY resonance
at output `k` (up to order), the truncated symbol at `k` is exactly the
cross-frequency interaction of the obstruction file:
`crossInteraction (q i) (q j) (v i) (v j)` when `w = v`. -/
theorem truncatedSymbol_resonantTriple {n : ℕ}
    (q : Fin n → E3) (v w : Fin n → E3) {i j k : Fin n}
    (hij : i ≠ j)
    (hsum : q i + q j = q k)
    (honly : ∀ a b : Fin n, q a + q b = q k →
      (a = i ∧ b = j) ∨ (a = j ∧ b = i)) :
    truncatedConvectionSymbol q v w k =
      (inner ℝ (q j) (v i)) • w j + (inner ℝ (q i) (v j)) • w i := by
  classical
  unfold truncatedConvectionSymbol
  rw [← Finset.sum_product', Finset.univ_product_univ, ← Finset.sum_filter]
  have hset : (Finset.univ.filter
      (fun p : Fin n × Fin n => q p.1 + q p.2 = q k)) =
      ({(i, j), (j, i)} : Finset (Fin n × Fin n)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · intro h
      rcases honly a b h with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hb⟩
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;> subst ha <;> subst hb
      · exact hsum
      · rw [add_comm]; exact hsum
  rw [hset]
  have hne : ((i, j) : Fin n × Fin n) ≠ (j, i) := by
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro h; exact absurd h hij
  rw [Finset.sum_pair hne]

/-- At a single nonzero frequency the self-interaction `q + q` exits the
frequency set, so the honest truncated nonlinearity vanishes identically —
regardless of transversality. -/
theorem truncatedSymbol_oneFrequency (q₀ : E3) (hq : q₀ ≠ 0)
    (v w : Fin 1 → E3) (k : Fin 1) :
    truncatedConvectionSymbol (fun _ => q₀) v w k = 0 := by
  apply truncatedSymbol_eq_zero_of_no_resonance
  intro _ _ h
  refine hq ?_
  have := congrArg (fun x => x - q₀) h
  simpa using this

/-!
## The multi-frequency mild solution concept
-/

/-- A multi-frequency mild solution on `[0,T]`: each mode follows its own
heat–Leray propagator, sourced by the Leray-projected truncated convection of
the full mode family (Duhamel).  This is the product-space generalization of
`FrequencyDuhamel.IsMildSolutionOn`, with the cross-mode transport explicit
through `truncatedConvectionSymbol`. -/
def IsMultiMildSolutionOn (ν : ℝ) {n : ℕ} (q : Fin n → E3)
    (u₀ : Fin n → E3) (T : ℝ) (u : ℝ → Fin n → E3) : Prop :=
  (∀ k : Fin n, ContinuousOn (fun t => u t k) (Set.Icc 0 T)) ∧
    ∀ k : Fin n, ∀ t ∈ Set.Icc (0:ℝ) T,
      u t k = frequencyHeatLeray ν t (q k) (u₀ k) +
        ∫ s in (0:ℝ)..t,
          frequencyHeatLeray ν (t - s) (q k)
            (truncatedConvectionSymbol q (u s) (u s) k)

/-- **One-frequency consistency, strengthened.**  At a single nonzero
frequency the honest truncated mild equation is solved by the free heat–Leray
flow launched from ANY data — no transversality needed, because the
self-interaction exits the frequency set.  Consistent with (and freer than)
`FrequencyMildGlobal.isMildSolutionOn_iff_heatFlow`. -/
theorem multiMild_oneFrequency_heatFlow
    (ν : ℝ) (q₀ : E3) (hq : q₀ ≠ 0) (u₀ : Fin 1 → E3) (T : ℝ) :
    IsMultiMildSolutionOn ν (fun _ => q₀) u₀ T
      (fun t _ => frequencyHeatLeray ν t q₀ (u₀ 0)) := by
  constructor
  · intro k
    have : Continuous fun t => frequencyHeatLeray ν t q₀ (u₀ 0) :=
      continuous_heatFlow (ν := ν) (q := q₀) (u₀ := u₀ 0)
    exact this.continuousOn
  · intro k t _
    have hzero : ∀ s : ℝ,
        truncatedConvectionSymbol (fun _ : Fin 1 => q₀)
          (fun _ => frequencyHeatLeray ν s q₀ (u₀ 0))
          (fun _ => frequencyHeatLeray ν s q₀ (u₀ 0)) k = 0 :=
      fun s => truncatedSymbol_oneFrequency q₀ hq _ _ k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    simp only [hzero, map_zero, intervalIntegral.integral_zero, add_zero]

/-!
## The cascade survives the honest truncation
-/

set_option linter.unusedSimpArgs false in
/-- **Concrete cascade witness.**  There is a resonant frequency triple with
per-mode transverse (divergence-free) amplitudes whose truncated nonlinearity
is NONZERO: the cross-mode transport predicted by
`crossInteraction_survives_transversality` is realized inside the honest
Galerkin layer.  Witness: `q = (e₀, e₁, e₀+e₁)`, `v = (e₁, e₀, 0)`; the output
at the sum frequency is `e₀ + e₁ ≠ 0`. -/
theorem truncated_cascade_witness :
    ∃ (q v : Fin 3 → E3),
      (∀ m : Fin 3, (inner ℝ (q m) (v m) : ℝ) = 0) ∧
      ∃ k : Fin 3, truncatedConvectionSymbol q v v k ≠ 0 := by
  classical
  set e₀ : E3 := EuclideanSpace.single 0 1 with he₀
  set e₁ : E3 := EuclideanSpace.single 1 1 with he₁
  -- distinguishing coordinate evaluations
  have hcoord : ∀ (x : E3) (i : Fin 3), (WithLp.ofLp x) i = x i := fun _ _ => rfl
  have he₀0 : e₀ 0 = 1 := by simp [he₀]
  have he₀1 : e₀ 1 = 0 := by simp [he₀]
  have he₁0 : e₁ 0 = 0 := by simp [he₁]
  have he₁1 : e₁ 1 = 1 := by simp [he₁]
  refine ⟨![e₀, e₁, e₀ + e₁], ![e₁, e₀, 0], ?_, ⟨2, ?_⟩⟩
  · intro m
    fin_cases m
    · simp [he₀, he₁, EuclideanSpace.inner_single_left]
    · simp [he₀, he₁, EuclideanSpace.inner_single_left]
    · simp
  · -- reduce to the cross interaction via the resonant-triple identity
    have hij : (0 : Fin 3) ≠ 1 := by decide
    have hsum : (![e₀, e₁, e₀ + e₁] : Fin 3 → E3) 0 +
        (![e₀, e₁, e₀ + e₁] : Fin 3 → E3) 1 =
        (![e₀, e₁, e₀ + e₁] : Fin 3 → E3) 2 := by
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have honly : ∀ a b : Fin 3,
        (![e₀, e₁, e₀ + e₁] : Fin 3 → E3) a +
          (![e₀, e₁, e₀ + e₁] : Fin 3 → E3) b =
          (![e₀, e₁, e₀ + e₁] : Fin 3 → E3) 2 →
        (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
      intro a b h
      fin_cases a <;> fin_cases b <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] at h ⊢
      -- (0,0): e₀+e₀ = e₀+e₁ ⟹ coordinate 1: 0 = 1
      · exfalso
        have := congrFun (congrArg WithLp.ofLp h) 1
        simp [he₀1, he₁1, hcoord] at this
      · exact Or.inl ⟨rfl, rfl⟩
      -- (0,2): e₀+(e₀+e₁) = e₀+e₁ ⟹ coordinate 0: 2 = 1
      · exfalso
        have := congrFun (congrArg WithLp.ofLp h) 0
        simp [he₀0, he₁0, hcoord] at this
      · exact Or.inr ⟨rfl, rfl⟩
      -- (1,1): e₁+e₁ = e₀+e₁ ⟹ coordinate 0: 0 = 1
      · exfalso
        have := congrFun (congrArg WithLp.ofLp h) 0
        simp [he₀0, he₁0, hcoord] at this
      -- (1,2): e₁+(e₀+e₁) = e₀+e₁ ⟹ coordinate 1: 2 = 1
      · exfalso
        have := congrFun (congrArg WithLp.ofLp h) 1
        simp [he₀1, he₁1, hcoord] at this
      -- (2,0): (e₀+e₁)+e₀ = e₀+e₁ ⟹ coordinate 0: 2 = 1
      · exfalso
        have := congrFun (congrArg WithLp.ofLp h) 0
        simp [he₀0, he₁0, hcoord] at this
      -- (2,1): (e₀+e₁)+e₁ = e₀+e₁ ⟹ coordinate 1: 2 = 1
      · exfalso
        have := congrFun (congrArg WithLp.ofLp h) 1
        simp [he₀1, he₁1, hcoord] at this
      -- (2,2): (e₀+e₁)+(e₀+e₁) = e₀+e₁ ⟹ coordinate 0: 2 = 1
      · exfalso
        have := congrFun (congrArg WithLp.ofLp h) 0
        simp [he₀0, he₁0, hcoord] at this
    rw [truncatedSymbol_resonantTriple _ _ _ hij hsum honly]
    -- the value is ⟪e₁,e₁⟫•e₀ + ⟪e₀,e₀⟫•e₁ = e₀ + e₁ ≠ 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    intro h
    have := congrFun (congrArg WithLp.ofLp h) 0
    simp [he₀, he₁, EuclideanSpace.inner_single_left,
      PiLp.single_apply, hcoord] at this

/-!
## Skeletons: existence, uniqueness, transversality, continuation
-/


/-- **Bilinear Lipschitz bound for the honest Galerkin nonlinearity.**  The
truncated convection symbol is quadratic, hence locally Lipschitz on the
product frequency fiber: summed over output modes, the difference of two
truncated nonlinearities with inputs bounded by `R` is controlled by the total
input difference `∑ ‖a m - b m‖`.  This is the Kato-type quadratic estimate that
drives mild-solution uniqueness (Kato, Math. Z. 187 (1984)); no measure theory
is involved. -/
theorem truncatedConvection_diff_sum_norm_le {n : ℕ} (q a b : Fin n → E3)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ m, ‖a m‖ ≤ R) (hb : ∀ m, ‖b m‖ ≤ R) :
    ∑ k, ‖truncatedConvectionSymbol q a a k -
        truncatedConvectionSymbol q b b k‖ ≤
      2 * (n : ℝ) ^ 2 * R * (∑ j, ‖q j‖) * (∑ m, ‖a m - b m‖) := by
  classical
  set Δ : ℝ := ∑ m, ‖a m - b m‖ with hΔ
  have hΔnn : 0 ≤ Δ := Finset.sum_nonneg fun m _ => norm_nonneg _
  have hsingle : ∀ m : Fin n, ‖a m - b m‖ ≤ Δ := by
    intro m
    have := Finset.single_le_sum (f := fun m : Fin n => ‖a m - b m‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ m)
    simpa only [hΔ] using this
  set Q : ℝ := ∑ j, ‖q j‖ with hQ
  have hQnn : 0 ≤ Q := Finset.sum_nonneg fun j _ => norm_nonneg _
  -- pointwise bilinear estimate of a single (i,j) term
  have hX : ∀ i j : Fin n,
      ‖(inner ℝ (q j) (a i) : ℝ) • a j -
          (inner ℝ (q j) (b i) : ℝ) • b j‖ ≤
        ‖q j‖ * R * (‖a i - b i‖ + ‖a j - b j‖) := by
    intro i j
    have hsplit :
        (inner ℝ (q j) (a i) : ℝ) • a j - (inner ℝ (q j) (b i) : ℝ) • b j =
          (inner ℝ (q j) (a i - b i) : ℝ) • a j +
            (inner ℝ (q j) (b i) : ℝ) • (a j - b j) := by
      rw [inner_sub_right, sub_smul, smul_sub]; abel
    have c1 : |(inner ℝ (q j) (a i - b i) : ℝ)| ≤ ‖q j‖ * ‖a i - b i‖ :=
      abs_real_inner_le_norm _ _
    have c2 : |(inner ℝ (q j) (b i) : ℝ)| ≤ ‖q j‖ * ‖b i‖ :=
      abs_real_inner_le_norm _ _
    rw [hsplit]
    calc ‖(inner ℝ (q j) (a i - b i) : ℝ) • a j +
            (inner ℝ (q j) (b i) : ℝ) • (a j - b j)‖
        ≤ ‖(inner ℝ (q j) (a i - b i) : ℝ) • a j‖ +
            ‖(inner ℝ (q j) (b i) : ℝ) • (a j - b j)‖ := norm_add_le _ _
      _ = |(inner ℝ (q j) (a i - b i) : ℝ)| * ‖a j‖ +
            |(inner ℝ (q j) (b i) : ℝ)| * ‖a j - b j‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (‖q j‖ * ‖a i - b i‖) * R + (‖q j‖ * R) * ‖a j - b j‖ := by
          apply add_le_add
          · exact mul_le_mul c1 (ha j) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact le_trans c2 (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
      _ = ‖q j‖ * R * (‖a i - b i‖ + ‖a j - b j‖) := by ring
  -- per-output-mode bound
  have hk : ∀ k : Fin n,
      ‖truncatedConvectionSymbol q a a k -
          truncatedConvectionSymbol q b b k‖ ≤
        2 * (n : ℝ) * R * Q * Δ := by
    intro k
    have hdiff :
        truncatedConvectionSymbol q a a k -
            truncatedConvectionSymbol q b b k =
          ∑ i : Fin n, ∑ j : Fin n,
            (if q i + q j = q k then
              (inner ℝ (q j) (a i) : ℝ) • a j -
                (inner ℝ (q j) (b i) : ℝ) • b j
             else 0) := by
      unfold truncatedConvectionSymbol
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : q i + q j = q k <;> simp [h]
    rw [hdiff]
    calc ‖∑ i : Fin n, ∑ j : Fin n,
            (if q i + q j = q k then
              (inner ℝ (q j) (a i) : ℝ) • a j -
                (inner ℝ (q j) (b i) : ℝ) • b j else 0)‖
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            ‖(if q i + q j = q k then
              (inner ℝ (q j) (a i) : ℝ) • a j -
                (inner ℝ (q j) (b i) : ℝ) • b j else 0)‖ :=
          le_trans (norm_sum_le _ _)
            (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖q j‖ * R * (2 * Δ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have hterm : ‖(if q i + q j = q k then
              (inner ℝ (q j) (a i) : ℝ) • a j -
                (inner ℝ (q j) (b i) : ℝ) • b j else 0)‖ ≤
              ‖q j‖ * R * (‖a i - b i‖ + ‖a j - b j‖) := by
            by_cases h : q i + q j = q k
            · rw [if_pos h]; exact hX i j
            · rw [if_neg h, norm_zero]
              positivity
          refine le_trans hterm ?_
          have h2 : ‖a i - b i‖ + ‖a j - b j‖ ≤ 2 * Δ := by
            have := hsingle i; have := hsingle j; linarith
          exact mul_le_mul_of_nonneg_left h2
            (mul_nonneg (norm_nonneg _) hR)
      _ = 2 * (n : ℝ) * R * Q * Δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp only [nsmul_eq_mul]
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          simp only [hQ]
          ring
  calc ∑ k, ‖truncatedConvectionSymbol q a a k -
          truncatedConvectionSymbol q b b k‖
      ≤ ∑ _k : Fin n, 2 * (n : ℝ) * R * Q * Δ :=
        Finset.sum_le_sum fun k _ => hk k
    _ = 2 * (n : ℝ) ^ 2 * R * Q * Δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **Quadratic a-priori self-bound for the truncated nonlinearity**
[Kato, Math. Z. 187 (1984); Fujita–Kato, Arch. Rational Mech. Anal. 16 (1964)].
Ball-invariance companion to `truncatedConvection_diff_sum_norm_le`: on a
frequency fiber bounded by `R`, the summed norm of the truncated convection
symbol is controlled by `2n²·R·(∑‖q‖)·(∑‖a‖)` (quadratic in the amplitudes).
Derived from the difference bound at `b = 0` (the symbol is bilinear, so
`truncatedConvectionSymbol q 0 0 = 0`).  This is the ball-invariance ingredient
of the mild-solution Banach fixed point (`exists_isMultiMildSolutionOn_local`),
the companion of the contraction ingredient already supplied by the difference
bound. -/
theorem truncatedConvection_sum_norm_le {n : ℕ} (q a : Fin n → E3)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ m, ‖a m‖ ≤ R) :
    ∑ k, ‖truncatedConvectionSymbol q a a k‖ ≤
      2 * (n : ℝ) ^ 2 * R * (∑ j, ‖q j‖) * (∑ m, ‖a m‖) := by
  have hzero : ∀ k : Fin n,
      truncatedConvectionSymbol q (0 : Fin n → E3) (0 : Fin n → E3) k = 0 := by
    intro k
    unfold truncatedConvectionSymbol
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp
  have hb : ∀ m : Fin n, ‖(0 : Fin n → E3) m‖ ≤ R := by
    intro m; simp only [Pi.zero_apply, norm_zero]; exact hR
  have hdiff := truncatedConvection_diff_sum_norm_le q a (0 : Fin n → E3) hR ha hb
  have hL : ∑ k, ‖truncatedConvectionSymbol q a a k -
        truncatedConvectionSymbol q (0 : Fin n → E3) (0 : Fin n → E3) k‖
      = ∑ k, ‖truncatedConvectionSymbol q a a k‖ :=
    Finset.sum_congr rfl fun k _ => by rw [hzero k, sub_zero]
  have hRHS : ∑ m, ‖a m - (0 : Fin n → E3) m‖ = ∑ m, ‖a m‖ :=
    Finset.sum_congr rfl fun m _ => by rw [Pi.zero_apply, sub_zero]
  rw [hL, hRHS] at hdiff
  exact hdiff

/-- **Uniqueness of multi-frequency mild solutions.**  Two multi-frequency
mild solutions with the same data agree on their common horizon: compactness
of the horizon gives a uniform amplitude bound `R` on both solutions, the
bilinear Lipschitz estimate (`truncatedConvection_diff_sum_norm_le`) turns
the Duhamel difference into `Δ t ≤ L ∫₀ᵗ Δ`, and the time-dependent Grönwall
bound (`gronwallBound` with `δ = ε = 0`) forces `Δ ≡ 0`.  Product-space
generalization of `FrequencyDuhamel.isMildSolutionOn_unique`.
Reference: Kato, Math. Z. 187 (1984); Fujita–Kato, Arch. Rational Mech.
Anal. 16 (1964) — mild-solution uniqueness by Grönwall/contraction. -/
theorem isMultiMildSolutionOn_unique
    {ν T : ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T) {n : ℕ} {q : Fin n → E3}
    {u₀ : Fin n → E3} {u v : ℝ → Fin n → E3}
    (hu : IsMultiMildSolutionOn ν q u₀ T u)
    (hv : IsMultiMildSolutionOn ν q u₀ T v) :
    ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t := by
  classical
  obtain ⟨huc, hueq⟩ := hu
  obtain ⟨hvc, hveq⟩ := hv
  have hcompact : IsCompact (Set.Icc (0:ℝ) T) := isCompact_Icc
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) T := ⟨le_rfl, hT⟩
  -- uniform per-mode bound R on both solutions over the compact horizon
  have hbnd : ∀ k : Fin n, ∃ Rk : ℝ, 0 ≤ Rk ∧
      ∀ t ∈ Set.Icc (0:ℝ) T, ‖u t k‖ ≤ Rk ∧ ‖v t k‖ ≤ Rk := by
    intro k
    obtain ⟨Cu, hCu⟩ := hcompact.exists_bound_of_continuousOn (huc k)
    obtain ⟨Cv, hCv⟩ := hcompact.exists_bound_of_continuousOn (hvc k)
    refine ⟨max Cu Cv,
      le_trans (norm_nonneg _) (le_trans (hCu 0 h0mem) (le_max_left _ _)), ?_⟩
    intro t ht
    exact ⟨le_trans (hCu t ht) (le_max_left _ _),
      le_trans (hCv t ht) (le_max_right _ _)⟩
  choose Rk hRknn hRk using hbnd
  set R : ℝ := ∑ k, Rk k with hRdef
  have hRnn : 0 ≤ R := Finset.sum_nonneg fun k _ => hRknn k
  have hRkle : ∀ k, Rk k ≤ R := fun k =>
    Finset.single_le_sum (fun i _ => hRknn i) (Finset.mem_univ k)
  have huR : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, ‖u t k‖ ≤ R :=
    fun t ht k => le_trans (hRk k t ht).1 (hRkle k)
  have hvR : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, ‖v t k‖ ≤ R :=
    fun t ht k => le_trans (hRk k t ht).2 (hRkle k)
  set Q : ℝ := ∑ j, ‖q j‖ with hQdef
  have hQnn : 0 ≤ Q := Finset.sum_nonneg fun j _ => norm_nonneg _
  set L : ℝ := 2 * (n : ℝ) ^ 2 * R * Q with hLdef
  have hLnn : 0 ≤ L :=
    mul_nonneg (mul_nonneg (by positivity) hRnn) hQnn
  set Δ : ℝ → ℝ := fun s => ∑ k, ‖u s k - v s k‖ with hΔdef
  have hΔnn : ∀ s, 0 ≤ Δ s := fun s => Finset.sum_nonneg fun k _ => norm_nonneg _
  have hΔcont : ContinuousOn Δ (Set.Icc 0 T) := by
    apply continuousOn_finsetSum
    intro k _
    exact ((huc k).sub (hvc k)).norm
  -- continuity of the truncated symbol along a componentwise-continuous field
  have symCont : ∀ (w : ℝ → Fin n → E3),
      (∀ k, ContinuousOn (fun s => w s k) (Set.Icc 0 T)) → ∀ k : Fin n,
      ContinuousOn (fun s => truncatedConvectionSymbol q (w s) (w s) k)
        (Set.Icc 0 T) := by
    intro w hwc k
    unfold truncatedConvectionSymbol
    apply continuousOn_finsetSum; intro i _
    apply continuousOn_finsetSum; intro j _
    by_cases h : q i + q j = q k
    · simp only [if_pos h]; exact (continuousOn_const.inner (hwc i)).smul (hwc j)
    · simp only [if_neg h]; exact continuousOn_const
  -- continuity of the Duhamel integrand
  have contHD : ∀ (w : ℝ → Fin n → E3),
      (∀ k, ContinuousOn (fun s => w s k) (Set.Icc 0 T)) → ∀ (t' : ℝ) (k : Fin n),
      ContinuousOn (fun s => frequencyHeatLeray ν (t' - s) (q k)
        (truncatedConvectionSymbol q (w s) (w s) k)) (Set.Icc 0 T) := by
    intro w hwc t' k
    have hheat : ContinuousOn (fun s => heatDecay ν (t' - s) (q k))
        (Set.Icc 0 T) := by
      apply Continuous.continuousOn; unfold heatDecay; fun_prop
    have hshape : (fun s => frequencyHeatLeray ν (t' - s) (q k)
          (truncatedConvectionSymbol q (w s) (w s) k)) =
        fun s => heatDecay ν (t' - s) (q k) • euclideanLeray (q k)
          (truncatedConvectionSymbol q (w s) (w s) k) := by
      funext s; exact frequencyHeatLeray_apply _ _ _ _
    rw [hshape]
    exact hheat.smul
      ((euclideanLeray (q k)).continuous.comp_continuousOn (symCont w hwc k))
  -- restrict Icc-0-T continuity to a sub-horizon
  have subT : ∀ t ∈ Set.Icc (0:ℝ) T, Set.uIcc (0:ℝ) t ⊆ Set.Icc 0 T := by
    intro t ht; rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
  -- interval integrability of the norm-difference integrand
  have hintnorm : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k : Fin n,
      IntervalIntegrable (fun s => ‖truncatedConvectionSymbol q (u s) (u s) k -
        truncatedConvectionSymbol q (v s) (v s) k‖) MeasureTheory.volume 0 t := by
    intro t ht k
    apply ContinuousOn.intervalIntegrable
    exact (((symCont u huc k).sub (symCont v hvc k)).norm).mono (subT t ht)
  -- Δ is interval-integrable on every sub-horizon
  have hΔII : ∀ t ∈ Set.Icc (0:ℝ) T,
      IntervalIntegrable Δ MeasureTheory.volume 0 t := fun t ht =>
    (hΔcont.mono (subT t ht)).intervalIntegrable
  -- the Lipschitz integral inequality  Δ t ≤ L ∫₀ᵗ Δ
  have key : ∀ t ∈ Set.Icc (0:ℝ) T, Δ t ≤ L * ∫ s in (0:ℝ)..t, Δ s := by
    intro t ht
    have hdiffk : ∀ k, u t k - v t k =
        ∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) (q k)
          (truncatedConvectionSymbol q (u s) (u s) k -
            truncatedConvectionSymbol q (v s) (v s) k) := by
      intro k
      have hIu : IntervalIntegrable (fun s => frequencyHeatLeray ν (t - s) (q k)
          (truncatedConvectionSymbol q (u s) (u s) k)) MeasureTheory.volume 0 t :=
        ((contHD u huc t k).mono (subT t ht)).intervalIntegrable
      have hIv : IntervalIntegrable (fun s => frequencyHeatLeray ν (t - s) (q k)
          (truncatedConvectionSymbol q (v s) (v s) k)) MeasureTheory.volume 0 t :=
        ((contHD v hvc t k).mono (subT t ht)).intervalIntegrable
      rw [hueq k t ht, hveq k t ht, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub hIu hIv]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [← map_sub]
    have hnormk : ∀ k, ‖u t k - v t k‖ ≤
        ∫ s in (0:ℝ)..t, ‖truncatedConvectionSymbol q (u s) (u s) k -
          truncatedConvectionSymbol q (v s) (v s) k‖ := by
      intro k
      have hHDcont : ContinuousOn (fun s => frequencyHeatLeray ν (t - s) (q k)
          (truncatedConvectionSymbol q (u s) (u s) k -
            truncatedConvectionSymbol q (v s) (v s) k)) (Set.Icc 0 T) := by
        have hheat : ContinuousOn (fun s => heatDecay ν (t - s) (q k))
            (Set.Icc 0 T) := by apply Continuous.continuousOn; unfold heatDecay; fun_prop
        have hshape : (fun s => frequencyHeatLeray ν (t - s) (q k)
              (truncatedConvectionSymbol q (u s) (u s) k -
                truncatedConvectionSymbol q (v s) (v s) k)) =
            fun s => heatDecay ν (t - s) (q k) • euclideanLeray (q k)
              (truncatedConvectionSymbol q (u s) (u s) k -
                truncatedConvectionSymbol q (v s) (v s) k) := by
          funext s; exact frequencyHeatLeray_apply _ _ _ _
        rw [hshape]
        exact hheat.smul ((euclideanLeray (q k)).continuous.comp_continuousOn
          ((symCont u huc k).sub (symCont v hvc k)))
      rw [hdiffk k]
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm ht.1) ?_
      refine intervalIntegral.integral_mono_on ht.1
        ((hHDcont.norm.mono (subT t ht)).intervalIntegrable) (hintnorm t ht k)
        (fun s hs => ?_)
      have hts : (0:ℝ) ≤ t - s := by linarith [hs.2]
      exact frequencyHeatLeray_norm_le hν hts (q k) _
    calc Δ t = ∑ k, ‖u t k - v t k‖ := rfl
      _ ≤ ∑ k, ∫ s in (0:ℝ)..t, ‖truncatedConvectionSymbol q (u s) (u s) k -
            truncatedConvectionSymbol q (v s) (v s) k‖ :=
          Finset.sum_le_sum fun k _ => hnormk k
      _ = ∫ s in (0:ℝ)..t, ∑ k, ‖truncatedConvectionSymbol q (u s) (u s) k -
            truncatedConvectionSymbol q (v s) (v s) k‖ :=
          (intervalIntegral.integral_finsetSum (s := Finset.univ)
            (fun k _ => hintnorm t ht k)).symm
      _ ≤ ∫ s in (0:ℝ)..t, L * Δ s := by
          have hsumcont : ContinuousOn (fun s => ∑ k,
              ‖truncatedConvectionSymbol q (u s) (u s) k -
                truncatedConvectionSymbol q (v s) (v s) k‖) (Set.Icc 0 T) := by
            apply continuousOn_finsetSum; intro k _
            exact ((symCont u huc k).sub (symCont v hvc k)).norm
          refine intervalIntegral.integral_mono_on ht.1
            ((hsumcont.mono (subT t ht)).intervalIntegrable)
            ((hΔII t ht).const_mul L) (fun s hs => ?_)
          have hsIcc : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1, le_trans hs.2 ht.2⟩
          have hsub := truncatedConvection_diff_sum_norm_le q (u s) (v s) hRnn
            (huR s hsIcc) (hvR s hsIcc)
          calc ∑ k, ‖truncatedConvectionSymbol q (u s) (u s) k -
                truncatedConvectionSymbol q (v s) (v s) k‖
              ≤ 2 * (n : ℝ) ^ 2 * R * (∑ j, ‖q j‖) *
                  (∑ m, ‖u s m - v s m‖) := hsub
            _ = L * Δ s := by rw [hLdef, hQdef, hΔdef]
      _ = L * ∫ s in (0:ℝ)..t, Δ s := intervalIntegral.integral_const_mul L Δ
  -- FTC engine: extend Δ continuously, g = ∫₀ᵗ Δ' has g' = Δ' ≤ L·g,
  -- Grönwall with δ=ε=0 forces g ≡ 0, hence Δ ≡ 0, hence u = v.
  have hΔzero : ∀ t ∈ Set.Icc (0:ℝ) T, Δ t = 0 := by
    set Δ' : ℝ → ℝ := Set.IccExtend hT (Set.restrict (Set.Icc 0 T) Δ) with hΔ'
    have hΔ'cont : Continuous Δ' := hΔcont.restrict.Icc_extend'
    have hΔ'eq : ∀ x ∈ Set.Icc (0:ℝ) T, Δ' x = Δ x :=
      fun x hx => Set.IccExtend_of_mem hT _ hx
    set g : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, Δ' s with hg
    have hgderiv : ∀ t : ℝ, HasDerivAt g (Δ' t) t := fun t =>
      intervalIntegral.integral_hasDerivAt_right (hΔ'cont.intervalIntegrable 0 t)
        (hΔ'cont.stronglyMeasurableAtFilter _ _) hΔ'cont.continuousAt
    have hgcont : Continuous g :=
      continuous_iff_continuousAt.2 fun t => (hgderiv t).continuousAt
    have hgeq : ∀ t ∈ Set.Icc (0:ℝ) T, g t = ∫ s in (0:ℝ)..t, Δ s := by
      intro t ht
      refine intervalIntegral.integral_congr fun s hs => ?_
      exact hΔ'eq s ⟨(Set.uIcc_of_le ht.1 ▸ hs).1,
        le_trans (Set.uIcc_of_le ht.1 ▸ hs).2 ht.2⟩
    have hgnn : ∀ t ∈ Set.Icc (0:ℝ) T, 0 ≤ g t := fun t ht => by
      rw [hgeq t ht]; exact intervalIntegral.integral_nonneg ht.1 fun s _ => hΔnn s
    have hgr : ∀ t ∈ Set.Icc (0:ℝ) T, ‖g t‖ ≤ gronwallBound 0 L 0 (t - 0) := by
      refine norm_le_gronwallBound_of_norm_deriv_right_le hgcont.continuousOn
        (fun x _ => (hgderiv x).hasDerivWithinAt) (by simp [hg]) (fun x hx => ?_)
      have hxIcc : x ∈ Set.Icc (0:ℝ) T := ⟨hx.1, le_of_lt hx.2⟩
      have hΔ'x : 0 ≤ Δ' x := by rw [hΔ'eq x hxIcc]; exact hΔnn x
      rw [Real.norm_of_nonneg hΔ'x, Real.norm_of_nonneg (hgnn x hxIcc), add_zero,
        hΔ'eq x hxIcc, hgeq x hxIcc]
      exact key x hxIcc
    intro t ht
    have h0 : g t = 0 :=
      norm_le_zero_iff.1 (by simpa [gronwallBound_ε0_δ0] using hgr t ht)
    have hk := key t ht
    rw [← hgeq t ht, h0, mul_zero] at hk
    exact le_antisymm hk (hΔnn t)
  intro t ht
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    fun k _ => norm_nonneg (u t k - v t k)).1 (hΔzero t ht)
  funext k
  exact sub_eq_zero.1 (norm_eq_zero.1 (hz k (Finset.mem_univ k)))

/-- **Transversality is automatic.**  Every multi-frequency mild solution is
per-mode transverse to its own frequency at every time of its horizon — no
hypothesis on the data is needed, because both the heat–Leray propagator and
the Duhamel integrand carry the Leray projection
(`frequencyHeatLeray_transverse`), and the inner product commutes with the
Duhamel integral.  This generalizes
`FrequencyDuhamel.IsMildSolutionOn.inner_frequency_eq_zero` to the truncated
multi-frequency layer. -/
theorem multiMild_inner_frequency_eq_zero
    {ν T : ℝ} {n : ℕ} {q : Fin n → E3} {u₀ : Fin n → E3}
    {u : ℝ → Fin n → E3}
    (hu : IsMultiMildSolutionOn ν q u₀ T u) :
    ∀ k : Fin n, ∀ t ∈ Set.Icc (0:ℝ) T,
      (inner ℝ (q k) (u t k) : ℝ) = 0 := by
  intro k t ht
  rw [hu.2 k t ht, inner_add_right,
    frequencyHeatLeray_transverse, zero_add]
  by_cases hInt : IntervalIntegrable
    (fun s => frequencyHeatLeray ν (t - s) (q k)
      (truncatedConvectionSymbol q (u s) (u s) k)) volume 0 t
  · have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
      (innerSL ℝ (q k)) hInt
    have hpt : ∀ s : ℝ,
        (innerSL ℝ (q k))
          (frequencyHeatLeray ν (t - s) (q k)
            (truncatedConvectionSymbol q (u s) (u s) k)) = 0 := by
      intro s
      simpa using frequencyHeatLeray_transverse ν (t - s) (q k)
        (truncatedConvectionSymbol q (u s) (u s) k)
    calc (inner ℝ (q k)
          (∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) (q k)
            (truncatedConvectionSymbol q (u s) (u s) k)) : ℝ)
        = (innerSL ℝ (q k))
            (∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) (q k)
              (truncatedConvectionSymbol q (u s) (u s) k)) := rfl
      _ = ∫ s in (0:ℝ)..t, (innerSL ℝ (q k))
            (frequencyHeatLeray ν (t - s) (q k)
              (truncatedConvectionSymbol q (u s) (u s) k)) := hcomm.symm
      _ = ∫ s in (0:ℝ)..t, (0:ℝ) := by simp only [hpt]
      _ = 0 := intervalIntegral.integral_zero
  · rw [intervalIntegral.integral_undef hInt, inner_zero_right]

/-- **Half-open-horizon continuity from every shorter horizon.**  If `u` solves the
truncated mild equation on `[0,T']` for *every* `T' < T`, then each amplitude is
continuous on the half-open horizon `[0,T)`: around any `x < T` pick the midpoint
`T' = (x+T)/2`, whose closed horizon is a neighbourhood of `x` inside `[0,T)`.
Strictly lower than the continuation theorem, which consumes it. -/
theorem continuousOn_Ico_of_forall_lt {ν T : ℝ} {n : ℕ}
    {q : Fin n → E3} {u₀ : Fin n → E3} {u : ℝ → Fin n → E3}
    (hu : ∀ T' : ℝ, 0 ≤ T' → T' < T → IsMultiMildSolutionOn ν q u₀ T' u)
    (m : Fin n) : ContinuousOn (fun t => u t m) (Set.Ico 0 T) := by
  intro x hx
  have hxT : x < T := hx.2
  have hx0 : (0:ℝ) ≤ x := hx.1
  set T' : ℝ := (x + T) / 2 with hT'def
  have hxT' : x < T' := by rw [hT'def]; linarith
  have hT'T : T' < T := by rw [hT'def]; linarith
  have hT'0 : (0:ℝ) ≤ T' := by rw [hT'def]; linarith
  have hcont := (hu T' hT'0 hT'T).1 m
  have hmem : Set.Icc (0:ℝ) T' ∈ nhdsWithin x (Set.Ico 0 T) := by
    refine mem_nhdsWithin.2 ⟨Set.Iio T', isOpen_Iio, hxT', ?_⟩
    rintro y ⟨hy1, hy2⟩
    exact ⟨hy2.1, le_of_lt hy1⟩
  exact (hcont x ⟨hx0, le_of_lt hxT'⟩).mono_of_mem_nhdsWithin hmem


/-- **The truncated symbol inherits continuity from the amplitudes.**  The resonance
condition `q i + q j = q k` does not depend on time, so the symbol is a finite sum of
constant-or-bilinear terms in the amplitudes; continuity is termwise. -/
theorem continuousOn_truncatedSymbol {n : ℕ} {q : Fin n → E3} {u : ℝ → Fin n → E3}
    {S : Set ℝ} (hu : ∀ m : Fin n, ContinuousOn (fun t => u t m) S) (k : Fin n) :
    ContinuousOn (fun s => truncatedConvectionSymbol q (u s) (u s) k) S := by
  classical
  unfold truncatedConvectionSymbol
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
  by_cases h : q i + q j = q k
  · simp only [if_pos h]
    exact (continuousOn_const.inner (hu i)).smul (hu j)
  · simp only [if_neg h]
    exact continuousOn_const

/-- **Per-mode quadratic a-priori self-bound.**  Sharpening of
`truncatedConvection_sum_norm_le` from the summed bound to a bound on each output mode,
using `∑ m ‖a m‖ ≤ n·R`.  This is the form the continuation argument consumes: it makes
the Duhamel integrand uniformly bounded on the horizon. -/
theorem truncatedSymbol_norm_le_of_bound {n : ℕ} (q a : Fin n → E3)
    {R : ℝ} (hR : 0 ≤ R) (ha : ∀ m, ‖a m‖ ≤ R) (k : Fin n) :
    ‖truncatedConvectionSymbol q a a k‖ ≤
      2 * (n : ℝ) ^ 2 * R * (∑ j, ‖q j‖) * ((n : ℝ) * R) := by
  have hsum := truncatedConvection_sum_norm_le q a hR ha
  have hsingle : ‖truncatedConvectionSymbol q a a k‖ ≤
      ∑ k', ‖truncatedConvectionSymbol q a a k'‖ :=
    Finset.single_le_sum (f := fun k' : Fin n => ‖truncatedConvectionSymbol q a a k'‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ k)
  have hamp : (∑ m, ‖a m‖) ≤ (n : ℝ) * R := by
    calc (∑ m, ‖a m‖) ≤ ∑ _m : Fin n, R := Finset.sum_le_sum fun m _ => ha m
      _ = (n : ℝ) * R := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcoef : 0 ≤ 2 * (n : ℝ) ^ 2 * R * (∑ j, ‖q j‖) := by
    have : 0 ≤ ∑ j, ‖q j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    positivity
  exact hsingle.trans (hsum.trans (mul_le_mul_of_nonneg_left hamp hcoef))


/-- **Integrability of the factorized Duhamel integrand up to the closed horizon.**
A field continuous and uniformly bounded on the *half-open* horizon `[0,T)` gives, after
the heat-weight factorization `heatDecay ν (t-s) = heatDecay ν t · heatDecay ν (-s)`, an
integrand that is integrable on the *closed* horizon `[0,T]`: the missing endpoint is
Lebesgue-null (`Ico_ae_eq_Icc`) and the weight is bounded by `exp (ν T ‖q₀‖²)`.
This is the analytic step that lets the solution be evaluated at the terminal time. -/
theorem integrableOn_heatWeighted {ν T : ℝ} (hν : 0 ≤ ν) (q₀ : E3)
    {G : ℝ → E3} {M : ℝ}
    (hGc : ContinuousOn G (Set.Ico 0 T))
    (hGb : ∀ s ∈ Set.Ico (0:ℝ) T, ‖G s‖ ≤ M) :
    IntegrableOn (fun s => heatDecay ν (-s) q₀ • euclideanLeray q₀ (G s))
      (Set.Icc 0 T) volume := by
  have hset : volume.restrict (Set.Icc (0:ℝ) T) = volume.restrict (Set.Ico 0 T) :=
    (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  haveI : Fact (volume (Set.Ico (0:ℝ) T) < ⊤) := ⟨by
    rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top⟩
  rw [IntegrableOn, hset]
  have hmeas : AEStronglyMeasurable
      (fun s => heatDecay ν (-s) q₀ • euclideanLeray q₀ (G s))
      (volume.restrict (Set.Ico (0:ℝ) T)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ico
    have h1 : ContinuousOn (fun s : ℝ => heatDecay ν (-s) q₀) (Set.Ico 0 T) := by
      unfold heatDecay; fun_prop
    exact h1.smul ((euclideanLeray q₀).continuous.comp_continuousOn hGc)
  refine Integrable.mono'
    (g := fun _ : ℝ => Real.exp (ν * T * ‖q₀‖ ^ 2) * M)
    (integrable_const _) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ico).2 (Filter.Eventually.of_forall fun s hs => ?_)
  have hGs := hGb s hs
  have hexp : heatDecay ν (-s) q₀ ≤ Real.exp (ν * T * ‖q₀‖ ^ 2) := by
    unfold heatDecay
    apply Real.exp_le_exp.2
    have hs0 : (0:ℝ) ≤ s := hs.1
    have hsT : s ≤ T := le_of_lt hs.2
    nlinarith [mul_nonneg (mul_nonneg hν (sub_nonneg.2 hsT)) (sq_nonneg ‖q₀‖)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (heatDecay_nonneg ν (-s) q₀)]
  calc heatDecay ν (-s) q₀ * ‖euclideanLeray q₀ (G s)‖
      ≤ heatDecay ν (-s) q₀ * ‖G s‖ :=
        mul_le_mul_of_nonneg_left (euclideanLeray_norm_le q₀ (G s))
          (heatDecay_nonneg ν (-s) q₀)
    _ ≤ Real.exp (ν * T * ‖q₀‖ ^ 2) * ‖G s‖ :=
        mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
    _ ≤ Real.exp (ν * T * ‖q₀‖ ^ 2) * M :=
        mul_le_mul_of_nonneg_left hGs (Real.exp_nonneg _)

/-- **The running Duhamel primitive is continuous on the closed horizon.**  Specialization
of `intervalIntegral.continuousOn_primitive_interval` to `uIcc 0 T = Icc 0 T`. -/
theorem continuousOn_primitive_Icc_of_integrableOn {T : ℝ} (hT : (0:ℝ) ≤ T)
    {f : ℝ → E3} (hf : IntegrableOn f (Set.Icc 0 T) volume) :
    ContinuousOn (fun t => ∫ s in (0:ℝ)..t, f s) (Set.Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval
    (a := (0:ℝ)) (b := T) (μ := volume) (f := f) (by rwa [Set.uIcc_of_le hT])
  rwa [Set.uIcc_of_le hT] at h


/-- **The finite-mode continuation criterion.**  A multi-frequency mild solution uniformly
bounded on every sub-horizon of `[0,T)` extends to the closed horizon `[0,T]`.
This is the finite-dimensional analogue of the Beale–Kato–Majda continuation
criterion, and the precise sense in which the surviving cross-mode transport
(`truncated_cascade_witness`) must be *controlled* — bounded, not cancelled —
for the truncated dynamics to run forever. -/
theorem multiMild_extends_of_apriori_bound
    {ν T : ℝ} (hν : 0 ≤ ν) (hT : 0 < T) {n : ℕ}
    {q : Fin n → E3} {u₀ : Fin n → E3} {u : ℝ → Fin n → E3}
    (hu : ∀ T' : ℝ, 0 ≤ T' → T' < T → IsMultiMildSolutionOn ν q u₀ T' u)
    (R : ℝ)
    (hR : ∀ t : ℝ, 0 ≤ t → t < T → ∀ k : Fin n, ‖u t k‖ ≤ R) :
    ∃ v : ℝ → Fin n → E3,
      IsMultiMildSolutionOn ν q u₀ T v ∧
      ∀ t : ℝ, 0 ≤ t → t < T → v t = u t := by
  classical
  set g : ℝ → Fin n → E3 := fun s k => truncatedConvectionSymbol q (u s) (u s) k with hgdef
  set v : ℝ → Fin n → E3 := fun t k =>
    frequencyHeatLeray ν t (q k) (u₀ k) +
      ∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) (q k) (g s k) with hvdef
  have hvu : ∀ t : ℝ, 0 ≤ t → t < T → v t = u t := by
    intro t ht0 htT
    funext k
    exact ((hu t ht0 htT).2 k t ⟨ht0, le_rfl⟩).symm
  set R' : ℝ := max R 0 with hR'def
  have hR'0 : (0:ℝ) ≤ R' := le_max_right _ _
  have hR' : ∀ t : ℝ, 0 ≤ t → t < T → ∀ k, ‖u t k‖ ≤ R' :=
    fun t h1 h2 k => (hR t h1 h2 k).trans (le_max_left _ _)
  have hucont : ∀ m : Fin n, ContinuousOn (fun t => u t m) (Set.Ico 0 T) :=
    fun m => continuousOn_Ico_of_forall_lt hu m
  have hgcont : ∀ k : Fin n, ContinuousOn (fun s => g s k) (Set.Ico 0 T) :=
    fun k => continuousOn_truncatedSymbol hucont k
  set M₀ : ℝ := 2 * (n:ℝ)^2 * R' * (∑ j, ‖q j‖) * ((n:ℝ) * R') with hM₀def
  have hgbd : ∀ k : Fin n, ∀ s ∈ Set.Ico (0:ℝ) T, ‖g s k‖ ≤ M₀ := by
    intro k s hs
    exact truncatedSymbol_norm_le_of_bound q (u s) hR'0 (hR' s hs.1 hs.2) k
  have hint : ∀ k : Fin n, IntegrableOn
      (fun s => heatDecay ν (-s) (q k) • euclideanLeray (q k) (g s k))
      (Set.Icc 0 T) volume :=
    fun k => integrableOn_heatWeighted hν (q k) (hgcont k) (hgbd k)
  have hker : ∀ (k : Fin n) (t : ℝ),
      (∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) (q k) (g s k))
        = heatDecay ν t (q k) •
            ∫ s in (0:ℝ)..t, heatDecay ν (-s) (q k) • euclideanLeray (q k) (g s k) := by
    intro k t
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun s _hs => ?_
    show frequencyHeatLeray ν (t - s) (q k) (g s k)
        = heatDecay ν t (q k) • (heatDecay ν (-s) (q k) • euclideanLeray (q k) (g s k))
    rw [frequencyHeatLeray_apply, smul_smul, ← heatDecay_factor]
  have hvcont : ∀ k : Fin n, ContinuousOn (fun t => v t k) (Set.Icc 0 T) := by
    intro k
    have hprim := continuousOn_primitive_Icc_of_integrableOn (le_of_lt hT) (hint k)
    have h1 : ContinuousOn (fun t : ℝ => frequencyHeatLeray ν t (q k) (u₀ k))
        (Set.Icc 0 T) := by
      have hrw : (fun t : ℝ => frequencyHeatLeray ν t (q k) (u₀ k))
          = fun t : ℝ => heatDecay ν t (q k) • euclideanLeray (q k) (u₀ k) := by
        funext t; exact frequencyHeatLeray_apply ν t (q k) (u₀ k)
      rw [hrw]
      refine ContinuousOn.smul ?_ continuousOn_const
      unfold heatDecay; fun_prop
    have h2 : ContinuousOn (fun t : ℝ => heatDecay ν t (q k)) (Set.Icc 0 T) := by
      unfold heatDecay; fun_prop
    have hrw2 : (fun t => v t k) = fun t => frequencyHeatLeray ν t (q k) (u₀ k)
        + heatDecay ν t (q k) •
            ∫ s in (0:ℝ)..t, heatDecay ν (-s) (q k) • euclideanLeray (q k) (g s k) := by
      funext t; simp only [hvdef]; rw [hker k t]
    rw [hrw2]
    exact h1.add (h2.smul hprim)
  refine ⟨v, ⟨hvcont, ?_⟩, hvu⟩
  intro k t ht
  obtain ⟨ht0, htT⟩ := ht
  have hswap : (∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) (q k)
        (truncatedConvectionSymbol q (v s) (v s) k))
      = ∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) (q k) (g s k) := by
    refine intervalIntegral.integral_congr_uIoo ?_
    intro s hs
    rw [Set.uIoo_of_le ht0] at hs
    have hvs : v s = u s := hvu s (le_of_lt hs.1) (lt_of_lt_of_le hs.2 htT)
    simp only [hgdef, hvs]
  show v t k = _
  rw [hswap]


/-!
## The product Duhamel map and the inputs to its contraction
-/

/-- **The multi-frequency Duhamel image.**  The self-map whose fixed point is a
multi-frequency mild solution: mode `k` is propagated by the diagonal heat–Leray
multiplier and forced by the truncated convection symbol of the whole amplitude
vector.  `IsMultiMildSolutionOn ν q u₀ T u` says exactly that `u` is continuous on
`[0,T]` and is a fixed point of this map there. -/
def multiDuhamelImage (ν : ℝ) {n : ℕ} (q : Fin n → E3) (u₀ : Fin n → E3)
    (f : ℝ → Fin n → E3) (t : ℝ) (k : Fin n) : E3 :=
  frequencyHeatLeray ν t (q k) (u₀ k) +
    ∫ s in (0:ℝ)..t, frequencyHeatLeray ν (t - s) (q k)
      (truncatedConvectionSymbol q (f s) (f s) k)

/-- **Sup-norm bilinear Lipschitz bound for the truncated symbol.**  Sup-form of
`truncatedConvection_diff_sum_norm_le`: on the sup-normed product fibre
`Fin n → E3` — which is the norm the product path space `C(Icc 0 T, Fin n → E3)`
carries — the difference of two truncated nonlinearities is controlled mode-by-mode
by the sup distance of the inputs.  This is the estimate the Duhamel contraction
consumes; the summed form is the wrong norm for the product path space. -/
theorem truncatedSymbol_diff_norm_le_sup {n : ℕ} (q a b : Fin n → E3)
    {R D : ℝ} (hR : 0 ≤ R) (ha : ∀ m, ‖a m‖ ≤ R) (hb : ∀ m, ‖b m‖ ≤ R)
    (hD : ∀ m, ‖a m - b m‖ ≤ D) (k : Fin n) :
    ‖truncatedConvectionSymbol q a a k - truncatedConvectionSymbol q b b k‖
      ≤ 2 * (n : ℝ) ^ 2 * R * (∑ j, ‖q j‖) * ((n : ℝ) * D) := by
  have hsum := truncatedConvection_diff_sum_norm_le q a b hR ha hb
  have hsingle : ‖truncatedConvectionSymbol q a a k - truncatedConvectionSymbol q b b k‖
      ≤ ∑ k', ‖truncatedConvectionSymbol q a a k' - truncatedConvectionSymbol q b b k'‖ :=
    Finset.single_le_sum
      (f := fun k' : Fin n => ‖truncatedConvectionSymbol q a a k' -
        truncatedConvectionSymbol q b b k'‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ k)
  have hamp : (∑ m, ‖a m - b m‖) ≤ (n : ℝ) * D := by
    calc (∑ m, ‖a m - b m‖) ≤ ∑ _m : Fin n, D := Finset.sum_le_sum fun m _ => hD m
      _ = (n : ℝ) * D := by simp [Finset.sum_const, nsmul_eq_mul]
  have hcoef : 0 ≤ 2 * (n : ℝ) ^ 2 * R * (∑ j, ‖q j‖) := by
    have : 0 ≤ ∑ j, ‖q j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    positivity
  exact hsingle.trans (hsum.trans (mul_le_mul_of_nonneg_left hamp hcoef))

/-- **The Duhamel image of a continuous bounded path is continuous on the closed
horizon.**  Self-map property of the product Duhamel map: this is what makes it an
endomorphism of the path space `C(Icc 0 T, Fin n → E3)`, the first hypothesis of the
Banach fixed-point theorem.  Consumes `continuousOn_truncatedSymbol`,
`truncatedSymbol_norm_le_of_bound`, `integrableOn_heatWeighted` and
`continuousOn_primitive_Icc_of_integrableOn`. -/
theorem continuousOn_multiDuhamelImage {ν T : ℝ} (hν : 0 ≤ ν) (hT : (0:ℝ) ≤ T) {n : ℕ}
    {q : Fin n → E3} {u₀ : Fin n → E3} {f : ℝ → Fin n → E3} {R : ℝ} (hR : 0 ≤ R)
    (hfc : ∀ m : Fin n, ContinuousOn (fun t => f t m) (Set.Ico 0 T))
    (hfb : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ m, ‖f t m‖ ≤ R) (k : Fin n) :
    ContinuousOn (fun t => multiDuhamelImage ν q u₀ f t k) (Set.Icc 0 T) := by
  have hgc : ContinuousOn (fun s => truncatedConvectionSymbol q (f s) (f s) k)
      (Set.Ico 0 T) := continuousOn_truncatedSymbol hfc k
  have hgb : ∀ s ∈ Set.Ico (0:ℝ) T,
      ‖truncatedConvectionSymbol q (f s) (f s) k‖
        ≤ 2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R) :=
    fun s hs => truncatedSymbol_norm_le_of_bound q (f s) hR (hfb s hs) k
  have hint := integrableOn_heatWeighted hν (q k) hgc hgb
  have hprim := continuousOn_primitive_Icc_of_integrableOn hT hint
  have h1 : ContinuousOn (fun t : ℝ => frequencyHeatLeray ν t (q k) (u₀ k))
      (Set.Icc 0 T) := by
    have hrw : (fun t : ℝ => frequencyHeatLeray ν t (q k) (u₀ k))
        = fun t : ℝ => heatDecay ν t (q k) • euclideanLeray (q k) (u₀ k) := by
      funext t; exact frequencyHeatLeray_apply ν t (q k) (u₀ k)
    rw [hrw]
    refine ContinuousOn.smul ?_ continuousOn_const
    unfold heatDecay; fun_prop
  have h2 : ContinuousOn (fun t : ℝ => heatDecay ν t (q k)) (Set.Icc 0 T) := by
    unfold heatDecay; fun_prop
  have hrw2 : (fun t => multiDuhamelImage ν q u₀ f t k)
      = fun t => frequencyHeatLeray ν t (q k) (u₀ k)
        + heatDecay ν t (q k) • ∫ s in (0:ℝ)..t,
            heatDecay ν (-s) (q k) •
              euclideanLeray (q k) (truncatedConvectionSymbol q (f s) (f s) k) := by
    funext t
    unfold multiDuhamelImage
    congr 1
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun s _hs => ?_
    show frequencyHeatLeray ν (t - s) (q k) (truncatedConvectionSymbol q (f s) (f s) k)
        = heatDecay ν t (q k) • (heatDecay ν (-s) (q k) •
            euclideanLeray (q k) (truncatedConvectionSymbol q (f s) (f s) k))
    rw [frequencyHeatLeray_apply, smul_smul, ← heatDecay_factor]
  rw [hrw2]
  exact h1.add (h2.smul hprim)

/-- **The Duhamel image moves off the free flow by at most `O(t)`.**  Quantitative
ball-invariance estimate: the nonlinear correction is bounded by the quadratic symbol
bound times the elapsed time, so for a short enough horizon the Duhamel map preserves
any ball around the free heat–Leray flow.  This is the second hypothesis of the Banach
fixed-point theorem (invariant complete subset). -/
theorem norm_multiDuhamelImage_sub_heat_le {ν T : ℝ} (hν : 0 ≤ ν) {n : ℕ}
    {q : Fin n → E3} {u₀ : Fin n → E3} {f : ℝ → Fin n → E3} {R : ℝ} (hR : 0 ≤ R)
    (hfb : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ m, ‖f t m‖ ≤ R)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) (k : Fin n) :
    ‖multiDuhamelImage ν q u₀ f t k - frequencyHeatLeray ν t (q k) (u₀ k)‖
      ≤ (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * t := by
  obtain ⟨ht0, htT⟩ := ht
  unfold multiDuhamelImage
  rw [add_sub_cancel_left]
  have hbound : ∀ s ∈ Set.uIoc (0:ℝ) t,
      ‖frequencyHeatLeray ν (t - s) (q k)
        (truncatedConvectionSymbol q (f s) (f s) k)‖
        ≤ 2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R) := by
    intro s hs
    rw [Set.uIoc_of_le ht0] at hs
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs.1
    have hsT : s ≤ T := le_trans hs.2 htT
    refine le_trans (frequencyHeatLeray_norm_le hν (by linarith [hs.2]) _ _) ?_
    exact truncatedSymbol_norm_le_of_bound q (f s) hR (hfb s ⟨hs0, hsT⟩) k
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa [abs_of_nonneg ht0] using h

/-!
### Picard iteration for the product Duhamel map

The Duhamel map is a contraction on the sup-normed product path space once the horizon
is short compared with the quadratic symbol bound.  Rather than bundle
`C(Icc 0 T, Fin n → E3)` and invoke `ContractingWith.exists_fixedPoint'`, the iteration
is run explicitly: the iterates are continuous and uniformly bounded on the *closed*
horizon, their successive differences decay geometrically, and the uniform limit is the
mild solution.  Running it by hand keeps every estimate in the repo's own
`frequencyHeatLeray`/`truncatedConvectionSymbol` vocabulary.

Reference: T. Kato, *Strong `L^p` solutions of the Navier–Stokes equation in `R^m`*,
Math. Z. **187** (1984) 471–480, §2; H. Fujita and T. Kato, *On the Navier–Stokes initial
value problem I*, Arch. Rational Mech. Anal. **16** (1964) 269–315.
-/

/-- **The free heat–Leray flow is continuous on the closed horizon.** -/
theorem continuousOn_freeFlow (ν : ℝ) (q₀ v : E3) (T : ℝ) :
    ContinuousOn (fun t : ℝ => frequencyHeatLeray ν t q₀ v) (Set.Icc 0 T) := by
  have hrw : (fun t : ℝ => frequencyHeatLeray ν t q₀ v)
      = fun t : ℝ => heatDecay ν t q₀ • euclideanLeray q₀ v := by
    funext t; exact frequencyHeatLeray_apply ν t q₀ v
  rw [hrw]
  refine ContinuousOn.smul ?_ continuousOn_const
  unfold heatDecay; fun_prop

/-- **The Duhamel integrand is continuous on the closed horizon.**  Continuity — rather
than the `integrableOn_heatWeighted` route through the half-open horizon — is what makes
the Duhamel integral interval-integrable, hence splittable across a difference of two
amplitude fields (`intervalIntegral.integral_sub`). -/
theorem continuousOn_duhamelIntegrand {T : ℝ} (ν : ℝ) {n : ℕ} {q : Fin n → E3}
    {f : ℝ → Fin n → E3} (hfc : ∀ m : Fin n, ContinuousOn (fun t => f t m) (Set.Icc 0 T))
    (t : ℝ) (k : Fin n) :
    ContinuousOn (fun s => frequencyHeatLeray ν (t - s) (q k)
      (truncatedConvectionSymbol q (f s) (f s) k)) (Set.Icc 0 T) := by
  have hsym : ContinuousOn (fun s => truncatedConvectionSymbol q (f s) (f s) k)
      (Set.Icc 0 T) := continuousOn_truncatedSymbol hfc k
  have hrw : (fun s => frequencyHeatLeray ν (t - s) (q k)
        (truncatedConvectionSymbol q (f s) (f s) k))
      = fun s => heatDecay ν (t - s) (q k) •
          euclideanLeray (q k) (truncatedConvectionSymbol q (f s) (f s) k) := by
    funext s; exact frequencyHeatLeray_apply _ _ _ _
  rw [hrw]
  refine ContinuousOn.smul ?_ ?_
  · unfold heatDecay; fun_prop
  · exact (euclideanLeray (q k)).continuous.comp_continuousOn hsym

/-- **Interval integrability of the Duhamel integrand** on every sub-interval of the
closed horizon, for a continuous amplitude field. -/
theorem intervalIntegrable_duhamelIntegrand {T : ℝ} (ν : ℝ) {n : ℕ} {q : Fin n → E3}
    {f : ℝ → Fin n → E3} (hfc : ∀ m : Fin n, ContinuousOn (fun t => f t m) (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) (k : Fin n) :
    IntervalIntegrable (fun s => frequencyHeatLeray ν (t - s) (q k)
      (truncatedConvectionSymbol q (f s) (f s) k)) volume 0 t := by
  obtain ⟨ht0, htT⟩ := ht
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le ht0]
  exact (continuousOn_duhamelIntegrand ν hfc t k).mono (Set.Icc_subset_Icc le_rfl htT)

/-- **Lipschitz estimate for the product Duhamel map.**  Two amplitude fields that are
continuous, bounded by `R` and within sup-distance `D` on the closed horizon have Duhamel
images within `L·D·t`, with `L = 2n²R(∑ⱼ‖qⱼ‖)n` the sup-norm Lipschitz constant of the
truncated symbol.  This is the contraction hypothesis of the Banach fixed-point argument:
for `L·T < 1` the map is a strict contraction of the path space. -/
theorem norm_multiDuhamelImage_sub_le {ν T : ℝ} (hν : 0 ≤ ν) {n : ℕ}
    {q : Fin n → E3} {u₀ : Fin n → E3} {f g : ℝ → Fin n → E3} {R D : ℝ} (hR : 0 ≤ R)
    (hfc : ∀ m : Fin n, ContinuousOn (fun t => f t m) (Set.Icc 0 T))
    (hgc : ∀ m : Fin n, ContinuousOn (fun t => g t m) (Set.Icc 0 T))
    (hfb : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ m, ‖f t m‖ ≤ R)
    (hgb : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ m, ‖g t m‖ ≤ R)
    (hD : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ m, ‖f t m - g t m‖ ≤ D)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) T) (k : Fin n) :
    ‖multiDuhamelImage ν q u₀ f t k - multiDuhamelImage ν q u₀ g t k‖
      ≤ (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * D)) * t := by
  obtain ⟨ht0, htT⟩ := ht
  have hIf := intervalIntegrable_duhamelIntegrand (q := q) ν hfc ⟨ht0, htT⟩ k
  have hIg := intervalIntegrable_duhamelIntegrand (q := q) ν hgc ⟨ht0, htT⟩ k
  have hcancel : ∀ A X Y : E3, (A + X) - (A + Y) = X - Y := by intro A X Y; abel
  unfold multiDuhamelImage
  rw [hcancel, ← intervalIntegral.integral_sub hIf hIg]
  have hbound : ∀ s ∈ Set.uIoc (0:ℝ) t,
      ‖frequencyHeatLeray ν (t - s) (q k) (truncatedConvectionSymbol q (f s) (f s) k)
        - frequencyHeatLeray ν (t - s) (q k) (truncatedConvectionSymbol q (g s) (g s) k)‖
        ≤ 2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * D) := by
    intro s hs
    rw [Set.uIoc_of_le ht0] at hs
    have hs0 : (0:ℝ) ≤ s := le_of_lt hs.1
    have hsT : s ≤ T := le_trans hs.2 htT
    rw [← map_sub]
    refine le_trans (frequencyHeatLeray_norm_le hν (by linarith [hs.2]) _ _) ?_
    exact truncatedSymbol_diff_norm_le_sup q (f s) (g s) hR (hfb s ⟨hs0, hsT⟩)
      (hgb s ⟨hs0, hsT⟩) (hD s ⟨hs0, hsT⟩) k
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa [abs_of_nonneg ht0] using h

/-- **The Picard iterates of the product Duhamel map**, launched from the free
heat–Leray flow. -/
noncomputable def multiPicard (ν : ℝ) {n : ℕ} (q : Fin n → E3) (u₀ : Fin n → E3) :
    ℕ → ℝ → Fin n → E3
  | 0 => fun t k => frequencyHeatLeray ν t (q k) (u₀ k)
  | m + 1 => multiDuhamelImage ν q u₀ (multiPicard ν q u₀ m)

@[simp] theorem multiPicard_zero (ν : ℝ) {n : ℕ} (q : Fin n → E3) (u₀ : Fin n → E3) :
    multiPicard ν q u₀ 0 = fun t k => frequencyHeatLeray ν t (q k) (u₀ k) := rfl

@[simp] theorem multiPicard_succ (ν : ℝ) {n : ℕ} (q : Fin n → E3) (u₀ : Fin n → E3) (m : ℕ) :
    multiPicard ν q u₀ (m + 1) = multiDuhamelImage ν q u₀ (multiPicard ν q u₀ m) := rfl

/-- **Uniform ball invariance for the Picard iterates.**  If the free flow is bounded by
`M` and the horizon is short enough that `M + K·T ≤ R` with `K` the quadratic symbol
bound at radius `R`, every iterate stays in the ball of radius `R` on `[0,T]`. -/
theorem multiPicard_norm_le {ν T : ℝ} (hν : 0 ≤ ν) {n : ℕ}
    (q : Fin n → E3) (u₀ : Fin n → E3) {M R : ℝ}
    (hM : ∀ k : Fin n, ‖u₀ k‖ ≤ M) (hR0 : 0 ≤ R) (hT : (0:ℝ) ≤ T)
    (hstep : M + (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * T ≤ R) :
    ∀ m : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, ‖multiPicard ν q u₀ m t k‖ ≤ R := by
  have hS : (0:ℝ) ≤ ∑ j, ‖q j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hK : (0:ℝ) ≤ 2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R) := by positivity
  intro m
  induction m with
  | zero =>
      intro t ht k
      have h0 : ‖frequencyHeatLeray ν t (q k) (u₀ k)‖ ≤ M :=
        le_trans (frequencyHeatLeray_norm_le hν ht.1 _ _) (hM k)
      have : (0:ℝ) ≤ (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * T :=
        mul_nonneg hK hT
      simpa using h0.trans (by linarith)
  | succ m ih =>
      intro t ht k
      have hsub := norm_multiDuhamelImage_sub_heat_le (q := q) (u₀ := u₀) hν hR0
        (fun s hs j => ih s hs j) ht k
      have hfree : ‖frequencyHeatLeray ν t (q k) (u₀ k)‖ ≤ M :=
        le_trans (frequencyHeatLeray_norm_le hν ht.1 _ _) (hM k)
      have hKt : (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * t
          ≤ (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * T :=
        mul_le_mul_of_nonneg_left ht.2 hK
      rw [multiPicard_succ]
      calc ‖multiDuhamelImage ν q u₀ (multiPicard ν q u₀ m) t k‖
          ≤ ‖multiDuhamelImage ν q u₀ (multiPicard ν q u₀ m) t k
              - frequencyHeatLeray ν t (q k) (u₀ k)‖
            + ‖frequencyHeatLeray ν t (q k) (u₀ k)‖ := by
              simpa using norm_le_norm_sub_add
                (multiDuhamelImage ν q u₀ (multiPicard ν q u₀ m) t k)
                (frequencyHeatLeray ν t (q k) (u₀ k))
        _ ≤ (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * T + M := by
              exact add_le_add (hsub.trans hKt) hfree
        _ ≤ R := by linarith

/-- **Continuity of every Picard iterate on the closed horizon.** -/
theorem multiPicard_continuousOn {ν T : ℝ} (hν : 0 ≤ ν) (hT : (0:ℝ) ≤ T) {n : ℕ}
    (q : Fin n → E3) (u₀ : Fin n → E3) {R : ℝ} (hR : 0 ≤ R)
    (hbd : ∀ m : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, ‖multiPicard ν q u₀ m t k‖ ≤ R) :
    ∀ (m : ℕ) (k : Fin n),
      ContinuousOn (fun t => multiPicard ν q u₀ m t k) (Set.Icc 0 T) := by
  intro m
  induction m with
  | zero => intro k; exact continuousOn_freeFlow ν (q k) (u₀ k) T
  | succ m ih =>
      intro k
      rw [multiPicard_succ]
      exact continuousOn_multiDuhamelImage hν hT hR
        (fun j => (ih j).mono Set.Ico_subset_Icc_self)
        (fun t ht j => hbd m t (Set.Ico_subset_Icc_self ht) j) k

/-- **The contraction core: a bounded continuous fixed point of the product Duhamel map
on a short closed horizon.**  Given a ball radius `R` that absorbs the free flow plus the
quadratic Duhamel correction (`hstep`) and a horizon short enough that the sup-norm
Lipschitz constant satisfies `L·T ≤ 1/2` (`hLip`), the Picard iterates `multiPicard`
converge uniformly on `[0,T]` to a continuous field bounded by `R` which is a fixed point
of `multiDuhamelImage`.  This is the Banach fixed-point argument for the Galerkin-truncated
mild equation, run explicitly rather than through `ContractingWith.exists_fixedPoint'` so
that every estimate stays in the repo's `frequencyHeatLeray`/`truncatedConvectionSymbol`
vocabulary.

Reference: T. Kato, *Strong `L^p` solutions of the Navier–Stokes equation in `R^m`*,
Math. Z. **187** (1984) 471–480, §2; H. Fujita and T. Kato, *On the Navier–Stokes initial
value problem I*, Arch. Rational Mech. Anal. **16** (1964) 269–315, §4. -/
theorem exists_multiMild_fixedPoint_of_smallHorizon {ν T : ℝ} (hν : 0 ≤ ν) (hT : 0 < T)
    {n : ℕ} (q : Fin n → E3) (u₀ : Fin n → E3) {M R : ℝ}
    (hM : ∀ k : Fin n, ‖u₀ k‖ ≤ M) (hR0 : 0 ≤ R)
    (hstep : M + (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * T ≤ R)
    (hLip : (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ)) * T ≤ 1/2) :
    ∃ u : ℝ → Fin n → E3,
      (∀ k : Fin n, ContinuousOn (fun t => u t k) (Set.Icc 0 T)) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, ‖u t k‖ ≤ R) ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, u t k = multiDuhamelImage ν q u₀ u t k) := by
  classical
  have hS : (0:ℝ) ≤ ∑ j, ‖q j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hK0 : (0:ℝ) ≤ 2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R) := by positivity
  have hL0 : (0:ℝ) ≤ 2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ) := by positivity
  have hbd := multiPicard_norm_le hν q u₀ hM hR0 hT.le hstep
  have hcont := multiPicard_continuousOn hν hT.le q u₀ hR0 hbd
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ,
      C = (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * T := ⟨_, rfl⟩
  have hC₀0 : (0:ℝ) ≤ C₀ := by rw [hC₀]; exact mul_nonneg hK0 hT.le
  -- Geometric decay of successive Picard differences.
  have hdiff : ∀ m : ℕ, ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k,
      ‖multiPicard ν q u₀ (m + 1) t k - multiPicard ν q u₀ m t k‖ ≤ C₀ * (1/2)^m := by
    intro m
    induction m with
    | zero =>
        intro t ht k
        have h := norm_multiDuhamelImage_sub_heat_le (q := q) (u₀ := u₀) hν hR0
          (fun s hs j => hbd 0 s hs j) ht k
        refine le_trans h ?_
        rw [hC₀, pow_zero, mul_one]
        exact mul_le_mul_of_nonneg_left ht.2 hK0
    | succ m ih =>
        intro t ht k
        have h := norm_multiDuhamelImage_sub_le (q := q) (u₀ := u₀) hν hR0
          (hcont (m + 1)) (hcont m)
          (fun s hs j => hbd (m + 1) s hs j) (fun s hs j => hbd m s hs j)
          (fun s hs j => ih s hs j) ht k
        refine le_trans h ?_
        have hCn : (0:ℝ) ≤ C₀ * (1/2:ℝ)^m := mul_nonneg hC₀0 (by positivity)
        have h1 : (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * (C₀ * (1/2)^m))) * t
            = ((2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ)) * t) * (C₀ * (1/2)^m) := by ring
        rw [h1]
        have h2 : (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ)) * t ≤ 1/2 :=
          le_trans (mul_le_mul_of_nonneg_left ht.2 hL0) hLip
        calc ((2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ)) * t) * (C₀ * (1/2)^m)
            ≤ (1/2) * (C₀ * (1/2)^m) := mul_le_mul_of_nonneg_right h2 hCn
          _ = C₀ * (1/2)^(m + 1) := by ring
  -- Cauchy, hence convergent, pointwise on the horizon.
  have hgeo : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, ∀ m : ℕ,
      dist (multiPicard ν q u₀ m t k) (multiPicard ν q u₀ (m + 1) t k) ≤ C₀ * (1/2)^m := by
    intro t ht k m
    rw [dist_eq_norm, norm_sub_rev]
    exact hdiff m t ht k
  have hcauchy : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k,
      CauchySeq (fun m => multiPicard ν q u₀ m t k) := fun t ht k =>
    cauchySeq_of_le_geometric (1/2) C₀ (by norm_num) (hgeo t ht k)
  obtain ⟨u, hudef⟩ : ∃ u : ℝ → Fin n → E3,
      u = fun t k => Filter.limUnder Filter.atTop
        (fun m => multiPicard ν q u₀ m t k) := ⟨_, rfl⟩
  have htend : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k,
      Filter.Tendsto (fun m => multiPicard ν q u₀ m t k) Filter.atTop (nhds (u t k)) := by
    intro t ht k
    rw [hudef]
    exact (hcauchy t ht k).tendsto_limUnder
  have hrate : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, ∀ m : ℕ,
      ‖multiPicard ν q u₀ m t k - u t k‖ ≤ 2 * C₀ * (1/2)^m := by
    intro t ht k m
    have h := dist_le_of_le_geometric_of_tendsto (1/2) C₀ (by norm_num)
      (hgeo t ht k) (htend t ht k) m
    rw [← dist_eq_norm]
    refine le_trans h (le_of_eq ?_)
    ring
  have hubd : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, ‖u t k‖ ≤ R := by
    intro t ht k
    exact le_of_tendsto (htend t ht k).norm
      (Filter.Eventually.of_forall fun m => hbd m t ht k)
  have hpow : Filter.Tendsto (fun m : ℕ => C₀ * (1/2:ℝ)^m) Filter.atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    simpa using hp.const_mul C₀
  have hpow2 : Filter.Tendsto (fun m : ℕ => 2 * C₀ * (1/2:ℝ)^m) Filter.atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)
    simpa [mul_assoc] using hp.const_mul (2 * C₀)
  -- Uniform convergence gives continuity of the limit.
  have hucont : ∀ k : Fin n, ContinuousOn (fun t => u t k) (Set.Icc 0 T) := by
    intro k
    have hunif : TendstoUniformlyOn (fun m t => multiPicard ν q u₀ m t k)
        (fun t => u t k) Filter.atTop (Set.Icc 0 T) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hpow2.eventually (gt_mem_nhds hε)] with m hm t ht
      have := hrate t ht k m
      rw [dist_comm, dist_eq_norm]
      exact lt_of_le_of_lt this hm
    exact hunif.continuousOn
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun m => hcont m k))
  -- The limit is a fixed point of the Duhamel map.
  have hfix : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ k, u t k = multiDuhamelImage ν q u₀ u t k := by
    intro t ht k
    have h1 : Filter.Tendsto (fun m => multiPicard ν q u₀ (m + 1) t k) Filter.atTop
        (nhds (u t k)) :=
      (htend t ht k).comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun m => multiPicard ν q u₀ (m + 1) t k) Filter.atTop
        (nhds (multiDuhamelImage ν q u₀ u t k)) := by
      rw [← tendsto_sub_nhds_zero_iff]
      refine squeeze_zero_norm ?_ hpow
      intro m
      have h := norm_multiDuhamelImage_sub_le (q := q) (u₀ := u₀) hν hR0
        (hcont m) hucont
        (fun s hs j => hbd m s hs j) (fun s hs j => hubd s hs j)
        (fun s hs j => hrate s hs j m) ht k
      refine le_trans h ?_
      have hCn : (0:ℝ) ≤ 2 * C₀ * (1/2:ℝ)^m := by positivity
      have h1' : (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * (2 * C₀ * (1/2)^m))) * t
          = ((2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ)) * t) * (2 * C₀ * (1/2)^m) := by ring
      rw [h1']
      have h2' : (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ)) * t ≤ 1/2 :=
        le_trans (mul_le_mul_of_nonneg_left ht.2 hL0) hLip
      calc ((2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ)) * t) * (2 * C₀ * (1/2)^m)
          ≤ (1/2) * (2 * C₀ * (1/2)^m) := mul_le_mul_of_nonneg_right h2' hCn
        _ = C₀ * (1/2)^m := by ring
    exact tendsto_nhds_unique h1 h2
  exact ⟨u, hucont, hubd, hfix⟩

/-- **[RESIDUAL — the product Duhamel contraction on the half-open horizon.
Reference: Kato, *Strong L^p solutions of the Navier–Stokes equation*, Math. Z. 187
(1984) 471–480 §2; Fujita–Kato, Arch. Rational Mech. Anal. 16 (1964) 269–315.
Est ~250 LOC.  Dependencies (all present and kernel-clean): the product path space
`C(Icc 0 T, Fin n → E3)` with its sup metric and Mathlib's
`ContractingWith.exists_fixedPoint'`; `continuousOn_multiDuhamelImage` for the
self-map property; `norm_multiDuhamelImage_sub_heat_le` for ball invariance;
`truncatedSymbol_diff_norm_le_sup` for the Lipschitz constant; and
`intervalIntegral.norm_integral_le_of_norm_le_const` to turn that constant into a
factor `L·T < 1`.]**  For every viscosity `ν ≥ 0`, finite frequency family and
initial amplitudes there is a positive horizon `T` carrying an amplitude field that
solves the truncated mild equation on *every* strictly shorter horizon and stays
uniformly bounded there.

Deliberately stated on the half-open horizon: the contraction naturally produces a
solution on each `[0,T']` with `T' < T`, and the passage to the closed horizon `[0,T]`
is no longer part of this obligation — it is supplied by
`multiMild_extends_of_apriori_bound`. -/
theorem exists_multiMild_shortHorizon
    (ν : ℝ) (hν : 0 ≤ ν) {n : ℕ} (q : Fin n → E3) (u₀ : Fin n → E3) :
    ∃ T : ℝ, 0 < T ∧ ∃ (u : ℝ → Fin n → E3) (R : ℝ),
      (∀ T' : ℝ, 0 ≤ T' → T' < T → IsMultiMildSolutionOn ν q u₀ T' u) ∧
      (∀ t : ℝ, 0 ≤ t → t < T → ∀ k : Fin n, ‖u t k‖ ≤ R) := by
  classical
  have hS : (0:ℝ) ≤ ∑ j, ‖q j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hM0 : (0:ℝ) ≤ ∑ m, ‖u₀ m‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (∑ m, ‖u₀ m‖) + 1 := ⟨_, rfl⟩
  have hR0 : (0:ℝ) ≤ R := by rw [hRdef]; linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = 2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R) := ⟨_, rfl⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ,
      L = 2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ) := ⟨_, rfl⟩
  have hK0 : (0:ℝ) ≤ K := by rw [hKdef]; positivity
  have hL0 : (0:ℝ) ≤ L := by rw [hLdef]; positivity
  have hP : (0:ℝ) < K + L + 1 := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 / (2 * (K + L + 1)) := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hTdef]; positivity
  have hprod : (K + L + 1) * T = 1/2 := by
    rw [hTdef]
    field_simp
  have hKT : K * T ≤ 1/2 := by
    have h1 : K * T ≤ (K + L + 1) * T :=
      mul_le_mul_of_nonneg_right (by linarith) hT0.le
    linarith
  have hLT : L * T ≤ 1/2 := by
    have h1 : L * T ≤ (K + L + 1) * T :=
      mul_le_mul_of_nonneg_right (by linarith) hT0.le
    linarith
  have hstep : (∑ m, ‖u₀ m‖)
      + (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * ((n:ℝ) * R)) * T ≤ R := by
    rw [← hKdef, hRdef]
    linarith
  have hLip : (2 * (n:ℝ)^2 * R * (∑ j, ‖q j‖) * (n:ℝ)) * T ≤ 1/2 := by
    rw [← hLdef]; exact hLT
  have hMle : ∀ k : Fin n, ‖u₀ k‖ ≤ ∑ m, ‖u₀ m‖ := fun k =>
    Finset.single_le_sum (f := fun m : Fin n => ‖u₀ m‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ k)
  obtain ⟨u, hucont, hubd, hufix⟩ :=
    exists_multiMild_fixedPoint_of_smallHorizon (ν := ν) hν hT0 q u₀ hMle hR0 hstep hLip
  refine ⟨T, hT0, u, R, ?_, ?_⟩
  · intro T' hT'0 hT'T
    refine ⟨fun k => (hucont k).mono (Set.Icc_subset_Icc le_rfl hT'T.le), ?_⟩
    intro k t ht
    exact hufix t ⟨ht.1, le_trans ht.2 hT'T.le⟩ k
  · intro t ht0 htT k
    exact hubd t ⟨ht0, htT.le⟩ k

/-- **Local existence for the honest Galerkin truncation.**  For every viscosity
`ν ≥ 0`, finite frequency family and initial amplitudes there is a positive horizon
carrying a multi-frequency mild solution on the *closed* horizon.

The closed-horizon statement is derived, not assumed: the contraction supplies only a
uniformly bounded solution on every strictly shorter horizon
(`exists_multiMild_shortHorizon`), and the finite-mode continuation criterion
`multiMild_extends_of_apriori_bound` carries it to the terminal time. -/
theorem exists_isMultiMildSolutionOn_local
    (ν : ℝ) (hν : 0 ≤ ν) {n : ℕ} (q : Fin n → E3) (u₀ : Fin n → E3) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → Fin n → E3,
      IsMultiMildSolutionOn ν q u₀ T u := by
  obtain ⟨T, hT, u, R, hsol, hbd⟩ := exists_multiMild_shortHorizon ν hν q u₀
  obtain ⟨v, hv, _⟩ := multiMild_extends_of_apriori_bound hν hT hsol R hbd
  exact ⟨T, hT, v, hv⟩


end Navier.Analysis.MultiFrequencyMild

