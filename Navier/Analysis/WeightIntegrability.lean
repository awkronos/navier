import Navier.Analysis.Vorticity
import Navier.Analysis.OfficialABEncoding
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Weight integrability for the Sobolev embedding

The key analytic input for the Fourier-analytic Sobolev embedding `H³(ℝ³) ↪ L^∞`
is the integrability of the Cauchy–Schwarz weight `(1+|ξ|²)^{-3}` on `ℝ³`.  This
converges because `3 > 3/2 = n/2`.

## Certified here (no sorry)

* `prod_le_sumCubed` — the algebraic AM-GM core:
  `(1+a)(1+b)(1+c) ≤ (1+a+b+c)³` for `a,b,c ≥ 0`.
* `sobWeight_le_prod_inv` — the pointwise weight bound:
  `(1+|ξ|²)^{-3} ≤ (1+ξ₀²)^{-1}·(1+ξ₁²)^{-1}·(1+ξ₂²)^{-1}`.
* `sobWeight_nonneg`, `sobWeight_pos` — sign properties.
* `sobWeight_integrable` — full integrability on `ℝ³`.  The pointwise bound
  `sobWeight_le_prod_inv` dominates the weight by `∏ᵢ (1+ξᵢ²)^{-1}`; each factor
  is integrable via `integrable_inv_one_add_sq`, the product is integrable w.r.t.
  the product measure via `Integrable.fintype_prod`, `volume_pi` identifies
  `volume` on `Fin 3 → ℝ` with that product measure, and `Integrable.mono'`
  closes it (Fubini/product-measure assembly).

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}` for certified decls.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.WeightIntegrability

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding

/-!
## The algebraic AM-GM bound
-/

/-- **AM-GM for three nonneg reals:** `(1+a)(1+b)(1+c) ≤ (1+a+b+c)³`.

This follows from expanding both sides: RHS − LHS is a sum of nonneg terms
(AM-GM via the arithmetic mean `((3+s)/3)` bounding the geometric mean, plus
`1+s ≥ 1+s/3`). -/
theorem prod_le_sumCubed {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (1 + a) * (1 + b) * (1 + c) ≤ (1 + a + b + c) ^ 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    ha, hb, hc, sq_nonneg (1 + a + b + c),
    mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

/-!
## The Sobolev weight
-/

/-- The Cauchy–Schwarz weight `(1+|ξ|²)^{-3}` for the Sobolev embedding `s = 3`.
Here `|ξ|² = ξ₀² + ξ₁² + ξ₂²` as an explicit triple sum. -/
def sobWeight (ξ : Space) : ℝ :=
  (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)⁻¹ ^ 3

/-- The weight is nonnegative. -/
theorem sobWeight_nonneg (ξ : Space) : 0 ≤ sobWeight ξ := by
  have h : 0 < (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 : ℝ) := by positivity
  exact pow_nonneg (inv_nonneg.mpr (le_of_lt h)) 3

/-- The weight is positive. -/
theorem sobWeight_pos (ξ : Space) : 0 < sobWeight ξ := by
  have h : 0 < (1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 : ℝ) := by positivity
  exact pow_pos (inv_pos.mpr h) 3

/-- **The pointwise weight bound via AM-GM.**
`(1+|ξ|²)^{-3} ≤ (1+ξ₀²)^{-1}·(1+ξ₁²)^{-1}·(1+ξ₂²)^{-1}`.

This is the key comparison: the weight is dominated by a product of three
1D-integrable factors, each `(1+t²)^{-1}`. -/
theorem sobWeight_le_prod_inv (ξ : Space) :
    sobWeight ξ ≤ (1 + ξ 0 ^ 2)⁻¹ * ((1 + ξ 1 ^ 2)⁻¹ * (1 + ξ 2 ^ 2)⁻¹) := by
  have hn0 : 0 ≤ ξ 0 ^ 2 := sq_nonneg _
  have hn1 : 0 ≤ ξ 1 ^ 2 := sq_nonneg _
  have hn2 : 0 ≤ ξ 2 ^ 2 := sq_nonneg _
  have hkey := prod_le_sumCubed hn0 hn1 hn2
  rw [sobWeight, inv_pow]
  have hA : (0 : ℝ) < 1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by nlinarith [hn0, hn1, hn2]
  have hB : (0 : ℝ) < (1 + ξ 0 ^ 2) * (1 + ξ 1 ^ 2) * (1 + ξ 2 ^ 2) := by positivity
  have hRHS : (1 + ξ 0 ^ 2)⁻¹ * ((1 + ξ 1 ^ 2)⁻¹ * (1 + ξ 2 ^ 2)⁻¹) =
      ((1 + ξ 0 ^ 2) * (1 + ξ 1 ^ 2) * (1 + ξ 2 ^ 2))⁻¹ := by
    field_simp
  rw [hRHS]
  exact (inv_le_inv₀ (pow_pos hA 3) hB).mpr hkey

/-!
## Integrability (honest residual)
-/

/-- **The weight `(1+|ξ|²)^{-3}` is integrable on `ℝ³`.**

Closure route: the pointwise bound `sobWeight_le_prod_inv` reduces to
`∏ᵢ (1+ξᵢ²)^{-1}`, where each factor is integrable on `ℝ` by
`integrable_inv_one_add_sq`.  The product is integrable on `ℝ³` by Fubini on
the product measure `volume = Measure.pi (fun _ => volume)` on `Fin 3 → ℝ`.
The weight follows by `Integrable.mono`.

The remaining formalization step is the Fubini/product-measure assembly on
`Fin 3 → ℝ`, connecting `integrable_inv_one_add_sq` (a 1D result) to the 3D
product measure. -/
theorem sobWeight_integrable :
    Integrable sobWeight volume := by
  -- Each 1D factor `(1+t²)⁻¹` is integrable on `ℝ`.
  have hg : ∀ _ : Fin 3, Integrable (fun t : ℝ => (1 + t ^ 2)⁻¹) volume :=
    fun _ => integrable_inv_one_add_sq
  -- The product `∏ᵢ (1+ξᵢ²)⁻¹` is integrable w.r.t. the product measure on `Fin 3 → ℝ`
  -- (the Fubini/product-measure assembly).
  have hprod : Integrable (fun ξ : Space => ∏ i : Fin 3, (1 + ξ i ^ 2)⁻¹)
      (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) :=
    Integrable.fintype_prod hg
  -- `volume` on `Fin 3 → ℝ` is the product Lebesgue measure.
  rw [volume_pi]
  -- `sobWeight` is continuous (denominator ≥ 1 > 0), hence a.e.-strongly-measurable.
  have hcont : Continuous sobWeight := by
    have hd : Continuous (fun ξ : Space => 1 + ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) := by fun_prop
    exact (hd.inv₀ (fun ξ => by positivity)).pow 3
  -- Dominate `sobWeight` by the integrable product via the pointwise AM-GM bound.
  refine hprod.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (sobWeight_nonneg ξ), Fin.prod_univ_three]
  have h := sobWeight_le_prod_inv ξ
  rw [← mul_assoc] at h
  exact h

end Navier.Analysis.WeightIntegrability
