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

## Skeletons (honest `sorry`, truth-checked signatures)

* `exists_isMultiMildSolutionOn_local` — local existence via the Duhamel
  contraction on the product path space [Kato 1984; product generalization of
  `FrequencyDuhamel`; est ~400 LOC].
* `isMultiMildSolutionOn_unique` — uniqueness on a common horizon
  [Grönwall/contraction as in `FrequencyDuhamel`; est ~150 LOC].
* `multiMild_inner_frequency_eq_zero` — per-mode transversality propagates
  (the Duhamel integrand is Leray-projected, hence pointwise transverse)
  [route: `ContinuousLinearMap.intervalIntegral_comp_comm` +
  `frequencyHeatLeray_transverse`; est ~200 LOC].
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

/-- **[SKELETON — uniqueness; Grönwall/contraction as in
`FrequencyDuhamel.isMildSolutionOn_unique`; est ~150 LOC.]**  Two
multi-frequency mild solutions with the same data agree on their common
horizon. -/
theorem isMultiMildSolutionOn_unique
    {ν T : ℝ} (hT : 0 ≤ T) {n : ℕ} {q : Fin n → E3} {u₀ : Fin n → E3}
    {u v : ℝ → Fin n → E3}
    (hu : IsMultiMildSolutionOn ν q u₀ T u)
    (hv : IsMultiMildSolutionOn ν q u₀ T v) :
    ∀ t ∈ Set.Icc (0:ℝ) T, u t = v t := by
  sorry

/-- **[SKELETON — transversality propagation; route:
`ContinuousLinearMap.intervalIntegral_comp_comm` +
`frequencyHeatLeray_transverse`; est ~200 LOC.]**  Per-mode transversality
(the divergence-free condition mode-by-mode) propagates: the heat–Leray
propagator preserves it and the Duhamel integrand is Leray-projected, hence
pointwise transverse to its own frequency. -/
theorem multiMild_inner_frequency_eq_zero
    {ν T : ℝ} {n : ℕ} {q : Fin n → E3} {u₀ : Fin n → E3}
    {u : ℝ → Fin n → E3}
    (hu : IsMultiMildSolutionOn ν q u₀ T u)
    (h₀ : ∀ k : Fin n, (inner ℝ (q k) (u₀ k) : ℝ) = 0) :
    ∀ k : Fin n, ∀ t ∈ Set.Icc (0:ℝ) T,
      (inner ℝ (q k) (u t k) : ℝ) = 0 := by
  sorry

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
