import Navier.Analysis.BealeKatoMajda

/-!
# Kernel-clean leaves for the BKM log bootstrap

The four analytic inputs of the Beale–Kato–Majda criterion
(`Navier/Analysis/BKMLogBootstrap.lean`) are stated in a *repository-normalised*
shape — `log (1 + ‖u‖²_{H³})` rather than the textbook `log (e + ‖u‖_{H³})`,
hypothesis-carried majorants rather than suprema, and the full `H³` sum rather
than one derivative order at a time.  Turning the citable classical statements
into that shape is pure real-analytic bookkeeping, and it is certified here so
that the bootstrap file carries only the genuinely Mathlib-absent cores.

## Certified here (no sorry)

* `bkm_log_shape_transfer` — the textbook `log (e + ‖u‖_{H³})` Biot–Savart shape
  implies the repository's `log (1 + ‖u‖²_{H³})` shape with constant `3C`, and
  simultaneously transfers to any `H³`-majorant.  This discharges the
  "the `log(1+‖·‖²)` form is equivalent to the textbook `log(e+‖·‖)` up to `C`"
  claim that `BKMLogBootstrap` previously only asserted.
* `le_mul_sqrt_of_le_majorant` — `√`-monotone transfer of a `C·√·` bound to any
  majorant; the certified form of the "each statement is monotone in its
  majorant" remark.
* `continuousOn_sum_range` — continuity of a `Finset.range` sum from continuity
  of each summand (the `H³` norm is such a sum over derivative orders).
* `exists_hasDerivAt_sum_range_le` — a `Finset.range m` sum of functions each
  differentiable at `t` with derivative `≤ B` is differentiable at `t` with
  derivative `≤ m·B` (the per-order energy estimates assemble to the `H³` one).

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.BKMLogLeaves

/-!
## Log-shape normalisation
-/

/-- **Textbook-to-repository log shape, with majorant transfer.**

The classical Biot–Savart logarithmic inequality (BKM 1984 Lemma 1;
Majda–Bertozzi Prop. 3.8) is stated with `log (e + ‖u‖_{H³})`, i.e.
`Real.log (Real.exp 1 + Real.sqrt L)` for `L = ‖u‖²_{H³}`.  The BKM bootstrap
consumes the shape `log (1 + Ms)` for an arbitrary `H³`-majorant `Ms ≥ L`.
This lemma performs both conversions at once, at the cost of the factor `3`:

`log (e + √L) ≤ log ((e+1)(1+Ms)) = log (e+1) + log (1+Ms) ≤ 2 + log (1+Ms)`,

using `√L ≤ √Ms ≤ 1 + Ms` and `e + 1 ≤ e²`; then `1 + log(e+√L) ≤ 3·(1 +
log(1+Ms))` because `1 + log(1+Ms) ≥ 1`, and the outer `1` and `√M₂` terms are
absorbed by the same factor `3`. -/
theorem bkm_log_shape_transfer {y C Mω M₂ L Ms : ℝ}
    (hC : 0 ≤ C) (hMω : 0 ≤ Mω) (hL : 0 ≤ L) (hLMs : L ≤ Ms)
    (h : y ≤ C * (1 + Mω * (1 + Real.log (Real.exp 1 + Real.sqrt L)) +
      Real.sqrt M₂)) :
    y ≤ 3 * C * (1 + Mω * (1 + Real.log (1 + Ms)) + Real.sqrt M₂) := by
  have hMs : (0:ℝ) ≤ Ms := le_trans hL hLMs
  have hlogMs : (0:ℝ) ≤ Real.log (1 + Ms) := Real.log_nonneg (by linarith)
  have hsL : Real.sqrt L ≤ Real.sqrt Ms := Real.sqrt_le_sqrt hLMs
  have hsMs : Real.sqrt Ms ≤ 1 + Ms := by
    nlinarith [Real.sq_sqrt hMs, Real.sqrt_nonneg Ms]
  have he : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hchain : Real.exp 1 + Real.sqrt L ≤ (Real.exp 1 + 1) * (1 + Ms) := by
    have hb : Real.sqrt L ≤ 1 + Ms := le_trans hsL hsMs
    nlinarith [he.le]
  have hlog1 : Real.log (Real.exp 1 + Real.sqrt L)
      ≤ Real.log ((Real.exp 1 + 1) * (1 + Ms)) :=
    Real.log_le_log (by positivity) hchain
  have hsplit : Real.log ((Real.exp 1 + 1) * (1 + Ms))
      = Real.log (Real.exp 1 + 1) + Real.log (1 + Ms) := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have hexp2 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  have hle2 : Real.log (Real.exp 1 + 1) ≤ 2 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h1 : Real.exp 1 + 1 ≤ Real.exp 2 := by nlinarith [hexp2]
    calc Real.log (Real.exp 1 + 1) ≤ Real.log (Real.exp 2) :=
          Real.log_le_log (by positivity) h1
      _ = 2 := Real.log_exp 2
  have hA : Real.log (Real.exp 1 + Real.sqrt L) ≤ 2 * (1 + Real.log (1 + Ms)) := by
    rw [hsplit] at hlog1; linarith
  have hsq : (0:ℝ) ≤ Real.sqrt M₂ := Real.sqrt_nonneg _
  have step1 : Mω * (1 + Real.log (Real.exp 1 + Real.sqrt L))
      ≤ 3 * (Mω * (1 + Real.log (1 + Ms))) := by nlinarith [hMω, hA, hlogMs]
  have inner : 1 + Mω * (1 + Real.log (Real.exp 1 + Real.sqrt L)) + Real.sqrt M₂
      ≤ 3 * (1 + Mω * (1 + Real.log (1 + Ms)) + Real.sqrt M₂) := by linarith
  calc y ≤ C * (1 + Mω * (1 + Real.log (Real.exp 1 + Real.sqrt L)) +
              Real.sqrt M₂) := h
    _ ≤ C * (3 * (1 + Mω * (1 + Real.log (1 + Ms)) + Real.sqrt M₂)) :=
        mul_le_mul_of_nonneg_left inner hC
    _ = 3 * C * (1 + Mω * (1 + Real.log (1 + Ms)) + Real.sqrt M₂) := by ring

/-- **Majorant transfer for a `C·√·` bound.**  A bound by `C·√a` upgrades to a
bound by `C·√Ms` for every majorant `Ms ≥ a`, by monotonicity of `√`.  This is
the certified content of the "each statement is monotone in its majorant"
remark in `BKMLogBootstrap`. -/
theorem le_mul_sqrt_of_le_majorant {y C a Ms : ℝ} (hC : 0 ≤ C)
    (h : y ≤ C * Real.sqrt a) (hle : a ≤ Ms) : y ≤ C * Real.sqrt Ms :=
  le_trans h (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hC)

/-!
## Assembling derivative orders
-/

/-- **A `Finset.range` sum of continuous functions is continuous.**  The `H³`
norm is the sum over derivative orders `n < 4` of the `L²` norms of `D^n u`;
this reduces its continuity in time to the continuity of one order at a time. -/
theorem continuousOn_sum_range {m : ℕ} {s : Set ℝ} {F : ℕ → ℝ → ℝ}
    (h : ∀ n ∈ Finset.range m, ContinuousOn (F n) s) :
    ContinuousOn (fun t => ∑ n ∈ Finset.range m, F n t) s :=
  continuousOn_finsetSum _ h

/-- **Per-order derivative bounds assemble to a sum bound.**  If each of `m`
functions is differentiable at `t` with derivative at most `B`, then their sum
is differentiable at `t` with derivative at most `m·B`.  This is the step that
turns the per-derivative-order `H³` energy estimates into the estimate for the
full `H³` norm, at the cost of the factor `m`. -/
theorem exists_hasDerivAt_sum_range_le {m : ℕ} {F : ℕ → ℝ → ℝ} {t B : ℝ}
    (h : ∀ n ∈ Finset.range m, ∃ D : ℝ, HasDerivAt (F n) D t ∧ D ≤ B) :
    ∃ D : ℝ, HasDerivAt (fun s => ∑ n ∈ Finset.range m, F n s) D t ∧
      D ≤ m * B := by
  have hd : ∀ n ∈ Finset.range m,
      HasDerivAt (F n) (deriv (F n) t) t ∧ deriv (F n) t ≤ B := by
    intro n hn
    obtain ⟨D, hD, hle⟩ := h n hn
    have hdd : deriv (F n) t = D := hD.deriv
    rw [hdd]
    exact ⟨hD, hle⟩
  refine ⟨∑ n ∈ Finset.range m, deriv (F n) t,
    HasDerivAt.fun_sum (fun n hn => (hd n hn).1), ?_⟩
  calc ∑ n ∈ Finset.range m, deriv (F n) t ≤ ∑ _n ∈ Finset.range m, B :=
        Finset.sum_le_sum (fun n hn => (hd n hn).2)
    _ = m * B := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Navier.Analysis.BKMLogLeaves
