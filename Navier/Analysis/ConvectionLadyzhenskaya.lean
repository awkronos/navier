import Navier.Analysis.ConvectionTrilinear
import Navier.Analysis.SobolevGNS
import Navier.Analysis.DivFreeGradientEnstrophy

/-!
# The Ladyzhenskaya bound on the projected convection operator

This is the assembly of the three certified halves:

* `ConvectionTrilinear.abs_convectionOperator_inner_le` — the off-diagonal
  Hölder estimate `|⟨B(a), b⟩| ≤ √3 · ‖u_a‖²_{L⁴} · ‖∇u_b‖_{L²}`;
* `Ladyzhenskaya.integral_pow_four_le_sqrt` — the `L⁴`/`L²`/`L⁶`
  interpolation, Cauchy–Schwarz with constant `1`;
* `SobolevGNS.exists_gns_six` — the Gagliardo–Nirenberg–Sobolev endpoint
  `‖u‖_{L⁶(ℝ³)} ≤ C‖∇u‖_{L²}` for Schwartz fields.

Composed, they give the estimate that the Galerkin compactness chain actually
consumes,

`|⟨B(a), b⟩| ≤ C · ‖u_a‖^{1/2}_{L²} · ‖∇u_a‖^{3/2}_{L²} · ‖∇u_b‖_{L²}`,

stated here in its fourth power so that every exponent is a natural number:

`|⟨B(a), b⟩|⁴ ≤ C · (∫|u_a|²) · (∫‖Du_a‖²)³ · (∫‖Du_b‖²)²`.

## Certified here (no sorry)

* `abs_convectionOperator_inner_pow_four_le` — the display above.
* `abs_convectionOperator_inner_pow_four_le_enstrophy` — the same estimate with
  every spatial quantity eliminated:
  `|⟨B(a), b⟩|⁴ ≤ C · ‖a‖² · Ω(a)³ · Ω(b)²` with `Ω = W.coefficientEnstrophy`.
  This is the form `galerkinCoefficientFlow_timeEquicontinuous` consumes: its
  `henst` hypothesis budgets exactly `Ω`, and `‖a‖` is the coefficient energy.
  The passage from `∫‖Du‖²` to `Ω` is the already-certified
  `DivFreeGradientEnstrophy.integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree`.

Degree check (the reason the exponents are forced): `B` is quadratic in `a`
and linear in `b`, so the left side has degree `8` in `u_a` and `4` in `u_b`.
On the right, `(∫|u_a|²)(∫‖Du_a‖²)³` has degree `2 + 6 = 8` and
`(∫‖Du_b‖²)²` has degree `4`.  Both sides are also invariant under the
scaling `u ↦ λ u(·/s)` that makes the underlying Ladyzhenskaya inequality
scale-invariant.  Endpoint `a = 0`: both sides `0`; `m = 0`: both sides `0`.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.

References: Temam, *Navier–Stokes Equations* III §3 (3.4); Robinson–Rodrigo–
Sadowski, *The Three-Dimensional Navier–Stokes Equations*, Lemma 1.30;
Constantin–Foias, *Navier–Stokes Equations*, Ch. 9.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory

namespace Navier.Analysis.ConvectionLadyzhenskaya

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.GalerkinBasis
open Navier.Analysis.ConvectionTrilinear
open Navier.Analysis.SobolevGNS
open Navier.Analysis.DivFreeGradientEnstrophy

/-- **The Ladyzhenskaya bound on the projected convection operator (certified,
no `sorry`).**

`|⟨B(a), b⟩|⁴ ≤ C · (∫|u_a|²) · (∫‖Du_a‖²)³ · (∫‖Du_b‖²)²`,

with `u_a = W.coefficientField a`; taking fourth roots this is
`|⟨B(a), b⟩| ≤ C^{1/4} ‖u_a‖^{1/2}_{L²} ‖∇u_a‖^{3/2}_{L²} ‖∇u_b‖_{L²}`, the
estimate that closes the convective half of the Aubin–Lions time-equicontinuity
argument for the Galerkin scheme.

The constant is uniform in the mode count `m` and in the basis family `W` — it
comes from the Sobolev constant of `ℝ³` alone.  That uniformity is the whole
point: a bound whose constant depended on `m` would carry no compactness
content, exactly as the `∀ m, ∃ δ` weakening of
`galerkinCoefficientFlow_timeEquicontinuous` carries none.

Note that on the diagonal `b = a` this is strictly weaker than
`convectionOperator_inner_self`, which gives exact vanishing; the two are
complementary, not competing. -/
theorem abs_convectionOperator_inner_pow_four_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : GalerkinBasisFamily) (m : ℕ) (a b : EuclideanSpace ℝ (Fin m)),
        |inner ℝ (W.convectionOperator m a) b| ^ 4 ≤
          C * (∫ x : Space, officialEuclideanNorm ((⇑(W.coefficientField a)) x) ^ 2) *
            (∫ x : Space, ‖fderiv ℝ (⇑(W.coefficientField a)) x‖ ^ 2) ^ 3 *
            (∫ x : Space, ‖fderiv ℝ (⇑(W.coefficientField b)) x‖ ^ 2) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_ladyzhenskaya_official
  refine ⟨9 * C, by positivity, fun W m a b => ?_⟩
  set ua : SchwartzVelocity := W.coefficientField a with hua
  set ub : SchwartzVelocity := W.coefficientField b with hub
  set X : ℝ := ∫ x : Space, officialEuclideanNorm ((⇑ua) x) ^ 4 with hX
  set Y : ℝ := ∫ x : Space, ‖fderiv ℝ (⇑ub) x‖ ^ 2 with hY
  have hX0 : 0 ≤ X := integral_nonneg fun x => by positivity
  have hY0 : 0 ≤ Y := integral_nonneg fun x => by positivity
  -- the Hölder estimate, with the two equal `L⁴` factors merged
  have hbase : |inner ℝ (W.convectionOperator m a) b| ≤
      Real.sqrt 3 * (X ^ (1/2 : ℝ) * Y ^ (1/2 : ℝ)) := by
    refine (abs_convectionOperator_inner_le W m a b).trans ?_
    have hmerge : X ^ (1/4 : ℝ) * Y ^ (1/2 : ℝ) * X ^ (1/4 : ℝ) =
        X ^ (1/2 : ℝ) * Y ^ (1/2 : ℝ) := by
      have h : X ^ (1/4 : ℝ) * X ^ (1/4 : ℝ) = X ^ (1/2 : ℝ) := by
        rw [← Real.rpow_add' hX0 (by norm_num)]
        norm_num
      calc X ^ (1/4 : ℝ) * Y ^ (1/2 : ℝ) * X ^ (1/4 : ℝ)
          = (X ^ (1/4 : ℝ) * X ^ (1/4 : ℝ)) * Y ^ (1/2 : ℝ) := by ring
        _ = X ^ (1/2 : ℝ) * Y ^ (1/2 : ℝ) := by rw [h]
    rw [hmerge]
  -- raise to the fourth power
  have hfour : |inner ℝ (W.convectionOperator m a) b| ^ 4 ≤ 9 * (X ^ 2 * Y ^ 2) := by
    refine (pow_le_pow_left₀ (abs_nonneg _) hbase 4).trans ?_
    have hsx : (X ^ (1/2 : ℝ)) ^ 4 = X ^ 2 := by
      rw [← Real.rpow_natCast (X ^ (1/2 : ℝ)) 4, ← Real.rpow_mul hX0]
      norm_num
    have hsy : (Y ^ (1/2 : ℝ)) ^ 4 = Y ^ 2 := by
      rw [← Real.rpow_natCast (Y ^ (1/2 : ℝ)) 4, ← Real.rpow_mul hY0]
      norm_num
    have hs3 : (Real.sqrt 3) ^ 4 = 9 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [mul_pow, mul_pow, hsx, hsy, hs3]
  -- Ladyzhenskaya on the `L⁴` factor
  have hlady := hC ua
  have hE0 : (0:ℝ) ≤ ∫ x : Space, officialEuclideanNorm ((⇑ua) x) ^ 2 :=
    integral_nonneg fun x => by positivity
  have hG0 : (0:ℝ) ≤ (∫ x : Space, ‖fderiv ℝ (⇑ua) x‖ ^ 2) ^ 3 := by
    have : (0:ℝ) ≤ ∫ x : Space, ‖fderiv ℝ (⇑ua) x‖ ^ 2 :=
      integral_nonneg fun x => by positivity
    positivity
  have hY2 : (0:ℝ) ≤ Y ^ 2 := by positivity
  calc |inner ℝ (W.convectionOperator m a) b| ^ 4
      ≤ 9 * (X ^ 2 * Y ^ 2) := hfour
    _ ≤ 9 * ((C * (∫ x : Space, officialEuclideanNorm ((⇑ua) x) ^ 2) *
          (∫ x : Space, ‖fderiv ℝ (⇑ua) x‖ ^ 2) ^ 3) * Y ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_right hlady hY2
    _ = 9 * C * (∫ x : Space, officialEuclideanNorm ((⇑ua) x) ^ 2) *
          (∫ x : Space, ‖fderiv ℝ (⇑ua) x‖ ^ 2) ^ 3 * Y ^ 2 := by ring

/-!
## The fully coefficient-level form
-/

private theorem coefficientField_divFree (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) : DivergenceFreeInitial (W.coefficientField a) :=
  divergenceFreeInitial_sum_smul Finset.univ (fun i : Fin m => a i)
    (fun i : Fin m => W.w i) (fun i => W.divergence_free i)

private theorem integral_officialNorm_sq_eq (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) :
    (∫ x : Space, officialEuclideanNorm ((⇑(W.coefficientField a)) x) ^ 2) = ‖a‖ ^ 2 := by
  rw [← coefficientField_l2_isometry W a]
  unfold schwartzL2Inner
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [Navier.Analysis.Enstrophy.officialInner_self]

private theorem integral_fderiv_sq_le_enstrophy (W : GalerkinBasisFamily) {m : ℕ}
    (a : EuclideanSpace ℝ (Fin m)) :
    (∫ x : Space, ‖fderiv ℝ (⇑(W.coefficientField a)) x‖ ^ 2) ≤
      3 * W.coefficientEnstrophy a :=
  integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree
    (W.coefficientField a) (coefficientField_divFree W a)

/-- **The convection estimate entirely in coefficient-level quantities
(certified, no `sorry`).**

`|⟨B(a), b⟩|⁴ ≤ C · ‖a‖² · Ω(a)³ · Ω(b)²`, with `Ω = W.coefficientEnstrophy`.

Taking fourth roots this is
`|⟨B(a), b⟩| ≤ C^{1/4} ‖a‖^{1/2} Ω(a)^{3/4} Ω(b)^{1/2}`, i.e. exactly
`|⟨B(u), φ⟩| ≤ C ‖u‖^{1/2}_{L²} ‖u‖^{3/2}_{H¹} ‖φ‖_{H¹}` written in the
coefficient coordinates of the Galerkin scheme.

Every quantity on the right is one the Galerkin ODE already budgets:
`‖a‖` is the coefficient energy (`coefficientField_l2_isometry`) and `Ω` is the
`coefficientEnstrophy` that `galerkinCoefficientFlow_timeEquicontinuous`
carries as its `henst` hypothesis.  No Schwartz field, no spatial integral and
no basis property survives into the statement, and the constant is uniform in
`m` and in `W`.

The route from the spatial estimate is
`integral_fderiv_norm_sq_le_three_mul_curl_sq_of_divFree` (the Dirichlet
energy of a divergence-free Schwartz field is at most three times its
enstrophy), which is why the constant picks up `3³ · 3² = 243`.

Endpoint checks.  `a = 0`: both sides `0`.  `m = 0`: `EuclideanSpace ℝ (Fin 0)`
is trivial and both sides are `0`.  `b = a`: strictly weaker than
`convectionOperator_inner_self`, which gives exact vanishing. -/
theorem abs_convectionOperator_inner_pow_four_le_enstrophy :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (W : GalerkinBasisFamily) (m : ℕ) (a b : EuclideanSpace ℝ (Fin m)),
        |inner ℝ (W.convectionOperator m a) b| ^ 4 ≤
          C * ‖a‖ ^ 2 * (W.coefficientEnstrophy a) ^ 3 *
            (W.coefficientEnstrophy b) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := abs_convectionOperator_inner_pow_four_le
  refine ⟨243 * C, by positivity, fun W m a b => ?_⟩
  set Ga : ℝ := ∫ x : Space, ‖fderiv ℝ (⇑(W.coefficientField a)) x‖ ^ 2 with hGa
  set Gb : ℝ := ∫ x : Space, ‖fderiv ℝ (⇑(W.coefficientField b)) x‖ ^ 2 with hGb
  have hGa0 : 0 ≤ Ga := integral_nonneg fun x => by positivity
  have hGb0 : 0 ≤ Gb := integral_nonneg fun x => by positivity
  have hEa : (0:ℝ) ≤ W.coefficientEnstrophy a :=
    integral_nonneg fun x => by positivity
  have hEb : (0:ℝ) ≤ W.coefficientEnstrophy b :=
    integral_nonneg fun x => by positivity
  have hGaE : Ga ≤ 3 * W.coefficientEnstrophy a := integral_fderiv_sq_le_enstrophy W a
  have hGbE : Gb ≤ 3 * W.coefficientEnstrophy b := integral_fderiv_sq_le_enstrophy W b
  have hstart := hC W m a b
  rw [integral_officialNorm_sq_eq W a] at hstart
  have hna : (0:ℝ) ≤ ‖a‖ ^ 2 := by positivity
  calc |inner ℝ (W.convectionOperator m a) b| ^ 4
      ≤ C * ‖a‖ ^ 2 * Ga ^ 3 * Gb ^ 2 := hstart
    _ ≤ C * ‖a‖ ^ 2 * (3 * W.coefficientEnstrophy a) ^ 3 *
          (3 * W.coefficientEnstrophy b) ^ 2 := by
        have h1 : Ga ^ 3 ≤ (3 * W.coefficientEnstrophy a) ^ 3 :=
          pow_le_pow_left₀ hGa0 hGaE 3
        have h2 : Gb ^ 2 ≤ (3 * W.coefficientEnstrophy b) ^ 2 :=
          pow_le_pow_left₀ hGb0 hGbE 2
        have hc : (0:ℝ) ≤ C * ‖a‖ ^ 2 := by positivity
        calc C * ‖a‖ ^ 2 * Ga ^ 3 * Gb ^ 2
            ≤ C * ‖a‖ ^ 2 * (3 * W.coefficientEnstrophy a) ^ 3 * Gb ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h1 hc) (by positivity)
          _ ≤ C * ‖a‖ ^ 2 * (3 * W.coefficientEnstrophy a) ^ 3 *
                (3 * W.coefficientEnstrophy b) ^ 2 := by
              refine mul_le_mul_of_nonneg_left h2 ?_
              positivity
    _ = 243 * C * ‖a‖ ^ 2 * (W.coefficientEnstrophy a) ^ 3 *
          (W.coefficientEnstrophy b) ^ 2 := by ring

end Navier.Analysis.ConvectionLadyzhenskaya
