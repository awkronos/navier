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

## Honest residual

* `sobolevEmbeddingDomination_H3` — the full embedding theorem.  Closure route:
  Fourier inversion (`fourierInv_fourier_eq`, present in Mathlib) +
  Cauchy–Schwarz against `(1+4π²|ξ|²)^{-3}` (integrable for `3 > 3/2`) +
  Plancherel.  The key Mathlib-absent piece is the weight-integrability
  computation.

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

/-- **[SKELETON — Sobolev embedding `H³(ℝ³) ↪ L^∞`; Agmon, Stein III.2;
est ~250 LOC.]**  The sup norm of a Schwartz velocity field is dominated by
the square root of its `H³` Sobolev norm: `‖u‖_∞ ≤ C·√(sobolevH3NormSq u)`.

Closure route: Fourier inversion (`fourierInv_fourier_eq` for `SchwartzMap`,
present in Mathlib's `Distribution.SchwartzSpace.Fourier`) gives
`u(x) = ∫ û(ξ) e^{2πi⟨ξ,x⟩} dξ`; Cauchy–Schwarz against the weight
`(1+4π²|ξ|²)^{-3}` (integrable for `s = 3 > 3/2 = n/2`; the finiteness is
unconditional) bounds `|u(x)|` by the Fourier-weighted `L²` norm; Plancherel
identifies this with the physical `H³` norm.

The key Mathlib-absent piece is the weight-integrability computation
`∫_{ℝ³} (1+|ξ|²)^{-3} dξ < ∞` (polar coordinates: `4π ∫_0^∞ r²/(1+r²)³ dr`,
convergent at infinity since `2 - 6 = -4 < -1`; the `Γ`-function evaluation
gives `π^{3/2}Γ(3/2)/Γ(3)`).  All other pieces (Fourier inversion, Plancherel)
are present in Mathlib v4.31.0. -/
theorem sobolevEmbeddingDomination_H3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : SchwartzVelocity) (Ms : ℝ), sobolevH3NormSq u ≤ Ms →
        ∀ x : Space, ‖(⇑u) x‖ ≤ C * Real.sqrt Ms := by
  sorry

end Navier.Analysis.SobolevEmbedding
