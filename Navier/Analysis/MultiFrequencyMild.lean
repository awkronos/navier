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

## Skeletons (honest `sorry`, truth-checked signatures)

* `exists_isMultiMildSolutionOn_local` — local existence via the Duhamel
  contraction on the product path space [Kato 1984; product generalization of
  `FrequencyDuhamel`; est ~400 LOC].
* `multiMild_extends_of_apriori_bound` — the finite-dimensional continuation
  criterion: a uniformly bounded mild solution on `[0,T)` extends to `[0,T]`
  (the finite-mode analogue of Beale–Kato–Majda) [standard ODE continuation;
  est ~300 LOC].
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

/-- **[SKELETON — local existence; Kato 1984; product generalization of
`FrequencyDuhamel.exists_isMildSolutionOn`; est ~400 LOC.]**  For every
viscosity `ν ≥ 0`, finite frequency family, and initial amplitudes there is a
positive horizon carrying a multi-frequency mild solution.  Closure route:
Banach fixed point (`ContractingWith.exists_fixedPoint'`) on the product path
space `C(Icc 0 T, Fin n → E3)` with the sup norm; the truncated symbol is a
finite sum of continuous bilinear terms, so the Duhamel map is locally
Lipschitz and contracts for small `T`, exactly as at one frequency. -/
theorem exists_isMultiMildSolutionOn_local
    (ν : ℝ) (hν : 0 ≤ ν) {n : ℕ} (q : Fin n → E3) (u₀ : Fin n → E3) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → Fin n → E3,
      IsMultiMildSolutionOn ν q u₀ T u := by
  sorry

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

/-- **[SKELETON — finite-mode continuation criterion; standard ODE
continuation; est ~300 LOC.]**  A multi-frequency mild solution uniformly
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
  sorry

end Navier.Analysis.MultiFrequencyMild
