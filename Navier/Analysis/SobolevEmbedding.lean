import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.BKMLogBootstrap
import Navier.Analysis.SingularIntegralPrelims

/-!
# Sobolev embedding `H³(ℝ³) ↪ L^∞` for the BKM assembly

The Sobolev embedding theorem on `ℝ³` states that for `s > 3/2`, the Sobolev
space `Hˢ(ℝ³)` embeds continuously into `L^∞(ℝ³)`.  In the BKM assembly the
relevant case is `s = 3 > 3/2 = n/2`: the `H³` norm controls the velocity
pointwise, which is the `control_dominates_velocity` field of `LogBKMControl`.

## Certified here (no sorry)

* `sobolevH3NormSq_dominates_lower` — each derivative-order `n ≤ 3` summand of
  the `H³` norm is dominated by the full `H³` norm (Sobolev norm monotonicity).
* `sobolevH3NormSq_dominates_L2` — the `L²` norm is dominated by the `H³` norm.

## Certified assembly (no sorry)

* `sobolev_domination_of_intermediate` — the intermediate-majorant assembly:
  a Fourier-side majorant `Q` with `‖u‖_∞ ≤ C₁·√(Q u)` and `Q u ≤ C₂·‖u‖²_{H³}`
  yields `‖u‖_∞ ≤ C·√Ms`, purely by monotonicity of `√`.  Unconditional in `Q`.

## Honest residual

* `exists_sobolev_intermediate` — the analytic core: existence of the Fourier
  majorant with both bounds (Fourier inversion + Cauchy–Schwarz against the
  integrable weight `(1+4π²|ξ|²)^{-3}` + Plancherel).
  `sobolevEmbeddingDomination_H3` is then assembled from it kernel-cleanly
  (ProvedModulo this one named leaf)

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}` for certified decls.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Navier.Analysis.SobolevEmbedding

open Navier
open Navier.Analysis.BealeKatoMajda

/-!
## Sobolev norm monotonicity (certified)
-/

/-- **Each derivative summand of the `H³` norm is dominated by the full norm.**
For `n ≤ 3`, `∫ ‖D^n u‖² ≤ sobolevH3NormSq u` — the inclusion `H³ ⊆ Hⁿ` for
`n ≤ 3`.  This is the trivial direction of Sobolev norm monotonicity. -/
theorem sobolevH3NormSq_dominates_lower {n : ℕ} (hn : n < 4) (u : SchwartzVelocity) :
    (∫ x : Space, ‖iteratedFDeriv ℝ n (⇑u) x‖ ^ 2) ≤ sobolevH3NormSq u := by
  have hn' : n ∈ Finset.range 4 := Finset.mem_range.mpr hn
  have hnn : ∀ k ∈ Finset.range 4,
      0 ≤ (∫ x : Space, ‖iteratedFDeriv ℝ k (⇑u) x‖ ^ 2) :=
    fun k _ => integral_nonneg (fun x => sq_nonneg _)
  exact Finset.single_le_sum hnn hn'

/-- **The `L²` norm (`n = 0` summand) is dominated by the `H³` norm.** -/
theorem sobolevH3NormSq_dominates_L2 (u : SchwartzVelocity) :
    (∫ x : Space, ‖iteratedFDeriv ℝ 0 (⇑u) x‖ ^ 2) ≤ sobolevH3NormSq u :=
  sobolevH3NormSq_dominates_lower (n := 0) (by norm_num) u

/-- **The `H¹` norm (`n = 1` summand) is dominated by the `H³` norm.** -/
theorem sobolevH3NormSq_dominates_H1 (u : SchwartzVelocity) :
    (∫ x : Space, ‖iteratedFDeriv ℝ 1 (⇑u) x‖ ^ 2) ≤ sobolevH3NormSq u :=
  sobolevH3NormSq_dominates_lower (n := 1) (by norm_num) u

/-- **The `H²` norm (`n = 2` summand) is dominated by the `H³` norm.** -/
theorem sobolevH3NormSq_dominates_H2 (u : SchwartzVelocity) :
    (∫ x : Space, ‖iteratedFDeriv ℝ 2 (⇑u) x‖ ^ 2) ≤ sobolevH3NormSq u :=
  sobolevH3NormSq_dominates_lower (n := 2) (by norm_num) u

/-!
## The Sobolev embedding theorem (honest residual)
-/

/-- **The intermediate-majorant assembly (certified, no sorry).**  If a
Fourier-side majorant functional `Q` dominates the sup norm
(`‖u x‖ ≤ C₁·√(Q u)`) and is itself dominated by the physical `H³` norm
(`Q u ≤ C₂·sobolevH3NormSq u`), then the sup norm is dominated by `√Ms` for any
`H³`-majorant `Ms`, with composite constant `C₁·√C₂`.

This is the logical skeleton of the Sobolev embedding proof: it turns the two
analytic domination bounds into the embedding statement purely by monotonicity
of `√` and the identity `√(C₂·Ms) = √C₂·√Ms`.  Unconditional in `Q`. -/
theorem sobolev_domination_of_intermediate
    {Q : SchwartzVelocity → ℝ}
    {C₁ : ℝ} (hC₁ : 0 < C₁)
    (h1 : ∀ (u : SchwartzVelocity) (x : Space), ‖(⇑u) x‖ ≤ C₁ * Real.sqrt (Q u))
    {C₂ : ℝ} (hC₂ : 0 < C₂)
    (h2 : ∀ u : SchwartzVelocity, Q u ≤ C₂ * sobolevH3NormSq u) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (Ms : ℝ), sobolevH3NormSq u ≤ Ms →
        ∀ x : Space, ‖(⇑u) x‖ ≤ C * Real.sqrt Ms := by
  refine ⟨C₁ * Real.sqrt C₂, mul_pos hC₁ (Real.sqrt_pos.mpr hC₂), ?_⟩
  intro u Ms hMs x
  have hQMs : Q u ≤ C₂ * Ms :=
    le_trans (h2 u) (mul_le_mul_of_nonneg_left hMs (le_of_lt hC₂))
  calc ‖(⇑u) x‖ ≤ C₁ * Real.sqrt (Q u) := h1 u x
    _ ≤ C₁ * Real.sqrt (C₂ * Ms) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQMs) (le_of_lt hC₁)
    _ = C₁ * Real.sqrt C₂ * Real.sqrt Ms := by
        rw [Real.sqrt_mul (le_of_lt hC₂), mul_assoc]

/-- **[RESIDUAL — analytic core of the Sobolev embedding `H³(ℝ³) ↪ L^∞`;
Agmon; Stein III.2; Majda–Bertozzi Lemma 3.2; est ~250 LOC.]**  There is a
Fourier-side majorant functional `Q` (classically the Bessel-potential norm
`Q u = ∫ ‖û(ξ)‖²·(1+4π²|ξ|²)³ dξ`) together with positive constants `C₁, C₂`
for which two analytic bounds hold:

* **(sup ≤ Fourier-L²)** `‖u x‖ ≤ C₁·√(Q u)` — Fourier inversion
  (`SchwartzMap.fourier_inversion`) writes `u(x) = ∫ û(ξ)·e^{2πi⟨ξ,x⟩} dξ`, so
  `|u(x)| ≤ ∫‖û‖`; Cauchy–Schwarz against the weight `(1+4π²|ξ|²)^{-3}`
  (integrable on `ℝ³` for `s = 3 > 3/2`; sibling `sobWeight_integrable`) gives
  `∫‖û‖ ≤ √(∫weight)·√(Q u)`, so `C₁ = √(∫weight)`.
* **(Fourier-L² ≤ physical H³)** `Q u ≤ C₂·sobolevH3NormSq u` — Plancherel
  identifies `∫‖û(ξ)‖²·|ξ|^{2n} dξ` with `∫‖D^n u‖²` up to constants, so the
  binomial-weighted Fourier norm is controlled by `∑_{n≤3}∫‖D^n u‖²`.

Mathlib-absent pieces: (i) the vector-valued Schwartz Fourier–Plancherel
identity relating `iteratedFDeriv` operator norms to Fourier multipliers, and
(ii) the weight integrability (sibling `WeightIntegrability.sobWeight_integrable`).
Feeding this residual through `sobolev_domination_of_intermediate` closes the
embedding. -/
theorem exists_sobolev_intermediate :
    ∃ (Q : SchwartzVelocity → ℝ) (C₁ C₂ : ℝ),
      0 < C₁ ∧ 0 < C₂ ∧
      (∀ (u : SchwartzVelocity) (x : Space), ‖(⇑u) x‖ ≤ C₁ * Real.sqrt (Q u)) ∧
      (∀ u : SchwartzVelocity, Q u ≤ C₂ * sobolevH3NormSq u) := by
  sorry

/-- **Sobolev embedding `H³(ℝ³) ↪ L^∞` for the BKM assembly.**  The sup norm of
a Schwartz velocity field is dominated by the square root of its `H³` Sobolev
norm: `‖u‖_∞ ≤ C·√(sobolevH3NormSq u)`.

Reduced to its analytic core: the logical assembly is the certified
`sobolev_domination_of_intermediate`; the sole remaining analytic content is the
named residual `exists_sobolev_intermediate` (Fourier inversion + Cauchy–Schwarz
against the integrable weight + Plancherel). -/
theorem sobolevEmbeddingDomination_H3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (Ms : ℝ), sobolevH3NormSq u ≤ Ms →
        ∀ x : Space, ‖(⇑u) x‖ ≤ C * Real.sqrt Ms := by
  obtain ⟨Q, C₁, C₂, hC₁, hC₂, h1, h2⟩ := exists_sobolev_intermediate
  exact sobolev_domination_of_intermediate hC₁ h1 hC₂ h2

end Navier.Analysis.SobolevEmbedding

