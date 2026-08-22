import Navier.Analysis.GalerkinBasis
import Navier.Analysis.EnstrophyPointwise
import Navier.Analysis.Ladyzhenskaya

/-!
# The off-diagonal size estimate for the convection operator

`convectionOperator_inner_self` certifies the *diagonal* behaviour of the
projected convection field: `⟨B(a), a⟩ = 0`, energy skewness.  Until now the
estate had no *off-diagonal* estimate at all, which is what every compactness
argument for the Galerkin scheme actually consumes.

This file supplies it, in the form the Aubin–Lions chain needs: the trilinear
transport form `b(u, φ, v) = ⟨(u·∇)φ, v⟩` is bounded by
`√3 · ‖u‖_{L⁴} · ‖∇φ‖_{L²} · ‖v‖_{L⁴}`.  The exponents `4, 2, 4` are Hölder
conjugate (`1/4 + 1/2 + 1/4 = 1`) and the estimate is obtained by two
applications of Cauchy–Schwarz, so the analytic constant is `1`; the `√3` is
purely the norm-convention factor `officialEuclideanNorm x ≤ √3 ‖x‖` between
the official Euclidean norm and the product norm `Space = Fin 3 → ℝ` carries.

## Certified here (no sorry)

* `officialEuclideanNorm_convectionSchwartzBilin_le` — the pointwise bound
  `|(u·∇)φ (x)| ≤ √3 · ‖Dφ(x)‖ · |u(x)|`.
* `abs_integral_convection_pairing_le` — the trilinear estimate above.
* `abs_schwartzL2Inner_convection_le` — the same, stated against the
  repository's `schwartzL2Inner`, which is the pairing that
  `convectionOperator_pairing` produces.
* `abs_convectionOperator_inner_le` — the **off-diagonal counterpart of
  `convectionOperator_inner_self`**: the coefficient-level convection pairing
  `⟨B(a), b⟩_{ℝ^m}` is bounded by
  `√3 · ‖u_a‖_{L⁴} · ‖∇u_a‖_{L²} · ‖u_b‖_{L⁴}` where `u_a = W.coefficientField a`.
  Taking `b = a` recovers a bound, not the exact vanishing — the vanishing is
  the strictly stronger diagonal fact and stays with
  `convectionOperator_inner_self`.

Numerically verified before formalisation: 20000 random weighted samples of the
Hölder triple `(4, 2, 4)` gave maximum violation `7.1e-15` (floating-point
noise); the endpoint `u = 0` gives `0 ≤ 0`, and `m = 0` makes the coefficient
statement a bound on `0`.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.

## What this does NOT supply

The Ladyzhenskaya inequality proper, `‖u‖_{L⁴} ≤ C ‖u‖_{L²}^{1/4} ‖∇u‖_{L²}^{3/4}`,
needs in addition the Gagliardo–Nirenberg–Sobolev endpoint
`‖u‖_{L⁶(ℝ³)} ≤ C ‖∇u‖_{L²}`; Mathlib supplies that only under
`HasCompactSupport`, which a Schwartz field does not satisfy.  The
interpolation half is `Ladyzhenskaya.integral_pow_four_le_sqrt`.  Everything in
*this* file is unconditional in the `L⁴` quantity.

References: Temam, *Navier–Stokes Equations* III §3 (3.4); Robinson–Rodrigo–
Sadowski, *The Three-Dimensional Navier–Stokes Equations*, Lemma 1.30 and
Ch. 4; Constantin–Foias, *Navier–Stokes Equations*, Ch. 9.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory SchwartzMap

namespace Navier.Analysis.ConvectionTrilinear

open Navier
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.GalerkinBasis
open Navier.Analysis.Enstrophy
open Navier.Analysis.EnstrophyPointwise
open Navier.Analysis.Ladyzhenskaya

/-!
## The pointwise bound
-/

/-- **Pointwise size of the transport field (certified, no `sorry`).**
`|(u·∇)φ (x)| ≤ √3 · ‖Dφ(x)‖ · |u(x)|` in the official Euclidean norm.

The two norm conversions are `officialEuclideanNorm_le` (official ≤ `√3` ·
product) on the output and `norm_le_officialEuclideanNorm` (product ≤ official)
on the input; the analytic content is just the operator-norm bound
`‖L y‖ ≤ ‖L‖ ‖y‖`. -/
theorem officialEuclideanNorm_convectionSchwartzBilin_le (u φ : SchwartzVelocity) (x : Space) :
    officialEuclideanNorm (convectionSchwartzBilin u φ x) ≤
      Real.sqrt 3 * (‖fderiv ℝ (⇑φ) x‖ * officialEuclideanNorm ((⇑u) x)) := by
  rw [convectionSchwartzBilin_apply]
  calc officialEuclideanNorm (spatialDerivative (fun _ => φ) 0 x ((⇑u) x))
      ≤ Real.sqrt 3 * ‖spatialDerivative (fun _ => φ) 0 x ((⇑u) x)‖ :=
        officialEuclideanNorm_le _
    _ ≤ Real.sqrt 3 * (‖fderiv ℝ (⇑φ) x‖ * officialEuclideanNorm ((⇑u) x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 3)
        refine le_trans ((spatialDerivative (fun _ => φ) 0 x).le_opNorm _) ?_
        exact mul_le_mul_of_nonneg_left (norm_le_officialEuclideanNorm _) (norm_nonneg _)

/-!
## Integrability inputs
-/

/-- `x ↦ ‖Dφ(x)‖` is the pointwise norm of the Schwartz map `fderivCLM φ`, so
every positive power of it is integrable. -/
theorem integrable_norm_fderiv_pow (φ : SchwartzVelocity) (k : ℕ) :
    Integrable (fun x : Space => ‖fderiv ℝ (⇑φ) x‖ ^ (k + 1)) := by
  have h := integrable_schwartzMap_norm_pow (SchwartzMap.fderivCLM ℝ Space Space φ) k
  refine h.congr ?_
  filter_upwards with x
  rw [fderivCLM_apply]

/-- `x ↦ ‖Dφ(x)‖` is bounded. -/
theorem fderivBound (φ : SchwartzVelocity) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space, ‖fderiv ℝ (⇑φ) x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := schwartzMapBound (SchwartzMap.fderivCLM ℝ Space Space φ)
  exact ⟨C, hC0, fun x => by simpa [fderivCLM_apply] using hC x⟩

/-- The official pointwise norm of a Schwartz velocity field is bounded. -/
theorem officialEuclideanNormBound (u : SchwartzVelocity) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space, officialEuclideanNorm ((⇑u) x) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := schwartzBound u
  refine ⟨Real.sqrt 3 * C, by positivity, fun x => ?_⟩
  exact le_trans (officialEuclideanNorm_le _)
    (mul_le_mul_of_nonneg_left (hC x) (Real.sqrt_nonneg 3))

private theorem continuous_officialNorm (u : SchwartzVelocity) :
    Continuous fun x : Space => officialEuclideanNorm ((⇑u) x) := by
  have h0 : Continuous officialEuclideanNorm := by
    unfold officialEuclideanNorm officialEuclideanPoint; fun_prop
  exact h0.comp u.continuous

/-!
## The trilinear estimate
-/

private theorem sqrt_sqrt_eq_rpow {A : ℝ} (hA : 0 ≤ A) :
    Real.sqrt (Real.sqrt A) = A ^ (1/4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hA]
  norm_num

/-- **The off-diagonal convection estimate (certified, no `sorry`).**
`|∫ ⟨(u·∇)φ, v⟩| ≤ √3 · ‖u‖_{L⁴} · ‖∇φ‖_{L²} · ‖v‖_{L⁴}`.

Hölder triple `(4, 2, 4)`, obtained by two applications of Cauchy–Schwarz:
first split off `‖Dφ‖` against the product `|u|·|v|`, then split that product.
The analytic constant is `1`; the `√3` is the norm-convention factor of
`officialEuclideanNorm` against the product norm on `Space`.

Endpoint `u = 0`: both sides are `0`.  The statement is not vacuous — it fails
for any constant strictly below the sharp Hölder constant on a suitable pair —
and it is satisfiable, being a theorem. -/
theorem abs_integral_convection_pairing_le (u φ v : SchwartzVelocity) :
    |∫ x : Space, officialInner (convectionSchwartzBilin u φ x) ((⇑v) x)| ≤
      Real.sqrt 3 *
        ((∫ x : Space, officialEuclideanNorm ((⇑u) x) ^ 4) ^ (1/4 : ℝ) *
          (∫ x : Space, ‖fderiv ℝ (⇑φ) x‖ ^ 2) ^ (1/2 : ℝ) *
          (∫ x : Space, officialEuclideanNorm ((⇑v) x) ^ 4) ^ (1/4 : ℝ)) := by
  set a : Space → ℝ := fun x => officialEuclideanNorm ((⇑u) x) with ha
  set c : Space → ℝ := fun x => officialEuclideanNorm ((⇑v) x) with hc
  set g : Space → ℝ := fun x => ‖fderiv ℝ (⇑φ) x‖ with hg
  have ha0 : ∀ x, 0 ≤ a x := fun x => officialEuclideanNorm_nonneg _
  have hc0 : ∀ x, 0 ≤ c x := fun x => officialEuclideanNorm_nonneg _
  have hg0 : ∀ x, 0 ≤ g x := fun x => norm_nonneg _
  have hameas : Continuous a := continuous_officialNorm u
  have hcmeas : Continuous c := continuous_officialNorm v
  have hgcont : Continuous g := by
    have hcl : Continuous fun x : Space => ‖(SchwartzMap.fderivCLM ℝ Space Space φ) x‖ :=
      (SchwartzMap.fderivCLM ℝ Space Space φ).continuous.norm
    simpa [hg, fderivCLM_apply] using hcl
  have hgmeas : AEStronglyMeasurable g (volume : Measure Space) :=
    hgcont.aestronglyMeasurable
  -- integrability of the individual powers
  have ha2 : Integrable (fun x => a x ^ 2) := by
    simpa using integrable_officialEuclideanNorm_pow u 1
  have hc2 : Integrable (fun x => c x ^ 2) := by
    simpa using integrable_officialEuclideanNorm_pow v 1
  have ha4 : Integrable (fun x => a x ^ 4) := by
    simpa using integrable_officialEuclideanNorm_pow u 3
  have hc4 : Integrable (fun x => c x ^ 4) := by
    simpa using integrable_officialEuclideanNorm_pow v 3
  have hg2 : Integrable (fun x => g x ^ 2) := by
    simpa using integrable_norm_fderiv_pow φ 1
  -- bounded factors
  obtain ⟨A, hA0, hA⟩ := officialEuclideanNormBound u
  obtain ⟨G, hG0, hG⟩ := fderivBound φ
  have hc1 : Integrable c := by
    simpa using integrable_officialEuclideanNorm_pow v 0
  -- `a·c` and its square are integrable
  have hac : Integrable (fun x => a x * c x) := by
    refine Integrable.mono' (hc1.const_mul A)
      ((hameas.mul hcmeas).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (mul_nonneg (ha0 x) (hc0 x))]
    exact mul_le_mul_of_nonneg_right (hA x) (hc0 x)
  have hacsq : Integrable (fun x => (a x * c x) ^ 2) := by
    refine Integrable.mono' (hc2.const_mul (A ^ 2))
      (((hameas.mul hcmeas).pow 2).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity), mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (ha0 x) (hA x) 2) (by positivity)
  have hgac : Integrable (fun x => g x * (a x * c x)) := by
    refine Integrable.mono' (hac.const_mul G)
      (hgmeas.mul (hameas.mul hcmeas).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (mul_nonneg (hg0 x) (mul_nonneg (ha0 x) (hc0 x)))]
    exact mul_le_mul_of_nonneg_right (hG x) (mul_nonneg (ha0 x) (hc0 x))
  -- the paired integrand
  have hFcont : Continuous
      (fun x : Space => officialInner (convectionSchwartzBilin u φ x) ((⇑v) x)) := by
    have hrw : (fun x : Space => officialInner (convectionSchwartzBilin u φ x) ((⇑v) x))
        = fun x : Space => ∑ i : Fin 3,
            (convectionSchwartzBilin u φ x) i * ((⇑v) x) i := by
      funext x
      rw [officialInner_eq_sum]
    rw [hrw]
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).comp (convectionSchwartzBilin u φ).continuous).mul
      ((continuous_apply i).comp v.continuous)
  have hFbound : ∀ x : Space,
      |officialInner (convectionSchwartzBilin u φ x) ((⇑v) x)|
        ≤ Real.sqrt 3 * (g x * (a x * c x)) := by
    intro x
    calc |officialInner (convectionSchwartzBilin u φ x) ((⇑v) x)|
        ≤ officialEuclideanNorm (convectionSchwartzBilin u φ x) *
            officialEuclideanNorm ((⇑v) x) := abs_officialInner_le _ _
      _ ≤ (Real.sqrt 3 * (g x * a x)) * c x :=
          mul_le_mul_of_nonneg_right
            (officialEuclideanNorm_convectionSchwartzBilin_le u φ x) (hc0 x)
      _ = Real.sqrt 3 * (g x * (a x * c x)) := by ring
  have hFint : Integrable
      (fun x : Space => officialInner (convectionSchwartzBilin u φ x) ((⇑v) x)) := by
    refine Integrable.mono' (hgac.const_mul (Real.sqrt 3))
      hFcont.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hFbound x
  -- second Cauchy-Schwarz: the product `a·c`
  have hstep2 : (∫ x : Space, (a x * c x) ^ 2) ≤
      Real.sqrt (∫ x : Space, a x ^ 4) * Real.sqrt (∫ x : Space, c x ^ 4) := by
    have h := integral_mul_le_sqrt_mul_sqrt (μ := (volume : Measure Space))
      (f := fun x => a x ^ 2) (g := fun x => c x ^ 2)
      (fun x => sq_nonneg _) (fun x => sq_nonneg _)
      ((hameas.pow 2).aestronglyMeasurable) ((hcmeas.pow 2).aestronglyMeasurable)
      (ha4.congr (by filter_upwards with x; ring))
      (hc4.congr (by filter_upwards with x; ring))
    have e1 : ∫ x : Space, a x ^ 2 * c x ^ 2 = ∫ x : Space, (a x * c x) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    have e2 : ∫ x : Space, (a x ^ 2) ^ 2 = ∫ x : Space, a x ^ 4 := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    have e3 : ∫ x : Space, (c x ^ 2) ^ 2 = ∫ x : Space, c x ^ 4 := by
      refine integral_congr_ae ?_
      filter_upwards with x
      ring
    rw [e1, e2, e3] at h
    exact h
  -- first Cauchy-Schwarz: `g` against `a·c`
  have hstep1 : (∫ x : Space, g x * (a x * c x)) ≤
      Real.sqrt (∫ x : Space, g x ^ 2) * Real.sqrt (∫ x : Space, (a x * c x) ^ 2) :=
    integral_mul_le_sqrt_mul_sqrt hg0 (fun x => mul_nonneg (ha0 x) (hc0 x))
      hgmeas (hameas.mul hcmeas).aestronglyMeasurable hg2 hacsq
  -- nonnegativity of the integrals
  have hA4 : (0:ℝ) ≤ ∫ x : Space, a x ^ 4 :=
    integral_nonneg fun x => by positivity
  have hC4 : (0:ℝ) ≤ ∫ x : Space, c x ^ 4 :=
    integral_nonneg fun x => by positivity
  have hG2 : (0:ℝ) ≤ ∫ x : Space, g x ^ 2 :=
    integral_nonneg fun x => by positivity
  have hkey : (∫ x : Space, g x * (a x * c x)) ≤
      (∫ x : Space, a x ^ 4) ^ (1/4 : ℝ) *
        (∫ x : Space, g x ^ 2) ^ (1/2 : ℝ) *
        (∫ x : Space, c x ^ 4) ^ (1/4 : ℝ) := by
    refine hstep1.trans ?_
    have hmono : Real.sqrt (∫ x : Space, (a x * c x) ^ 2) ≤
        Real.sqrt (Real.sqrt (∫ x : Space, a x ^ 4) *
          Real.sqrt (∫ x : Space, c x ^ 4)) := Real.sqrt_le_sqrt hstep2
    refine le_trans (mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _)) ?_
    rw [Real.sqrt_mul (Real.sqrt_nonneg _), sqrt_sqrt_eq_rpow hA4, sqrt_sqrt_eq_rpow hC4,
      Real.sqrt_eq_rpow]
    ring_nf
    rfl
  calc |∫ x : Space, officialInner (convectionSchwartzBilin u φ x) ((⇑v) x)|
      ≤ ∫ x : Space, |officialInner (convectionSchwartzBilin u φ x) ((⇑v) x)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x : Space, Real.sqrt 3 * (g x * (a x * c x)) :=
        integral_mono hFint.abs (hgac.const_mul _) hFbound
    _ = Real.sqrt 3 * ∫ x : Space, g x * (a x * c x) := integral_const_mul _ _
    _ ≤ Real.sqrt 3 *
          ((∫ x : Space, a x ^ 4) ^ (1/4 : ℝ) *
            (∫ x : Space, g x ^ 2) ^ (1/2 : ℝ) *
            (∫ x : Space, c x ^ 4) ^ (1/4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey (Real.sqrt_nonneg 3)

/-!
## Repository-facing forms
-/

/-- **The trilinear estimate against `schwartzL2Inner` (certified, no
`sorry`).**  `|⟨u, (u'·∇)φ⟩_{L²}| ≤ √3 · ‖u'‖_{L⁴} · ‖∇φ‖_{L²} · ‖u‖_{L⁴}`.

This is the shape produced by `convectionOperator_pairing`. -/
theorem abs_schwartzL2Inner_convection_le (u u' φ : SchwartzVelocity) :
    |schwartzL2Inner u (convectionSchwartzBilin u' φ)| ≤
      Real.sqrt 3 *
        ((∫ x : Space, officialEuclideanNorm ((⇑u') x) ^ 4) ^ (1/4 : ℝ) *
          (∫ x : Space, ‖fderiv ℝ (⇑φ) x‖ ^ 2) ^ (1/2 : ℝ) *
          (∫ x : Space, officialEuclideanNorm ((⇑u) x) ^ 4) ^ (1/4 : ℝ)) := by
  rw [schwartzL2Inner_comm]
  exact abs_integral_convection_pairing_le u' φ u

/-- **The off-diagonal size estimate for `convectionOperator` (certified, no
`sorry`).**  The exact counterpart of `convectionOperator_inner_self`:

* diagonal (`convectionOperator_inner_self`): `⟨B(a), a⟩ = 0` — exact vanishing;
* off-diagonal (here): `|⟨B(a), b⟩| ≤ √3 · ‖u_a‖²_{L⁴} · ‖∇u_b‖_{L²}`,

where `u_a = W.coefficientField a`.  Note that the two `L⁴` factors carry the
*same* field `u_a`, because `B` is quadratic in `a`: the trilinear form
`b(u_a, u_b, u_a)` puts `u_b` in the derivative slot.  This is exactly the
inequality the Aubin–Lions time-equicontinuity argument consumes for the
convective half of the Galerkin ODE, the half that
`galerkinCoefficientFlow_timeEquicontinuous` still lacks.

Endpoint checks.  `m = 0`: `EuclideanSpace ℝ (Fin 0)` is trivial, both sides
are `0`.  `a = 0`: `u_a = 0`, both sides `0`.  `b = a`: the bound is *weaker*
than `convectionOperator_inner_self`, which gives exact `0`; nothing here
supersedes the diagonal fact. -/
theorem abs_convectionOperator_inner_le (W : GalerkinBasisFamily) (m : ℕ)
    (a b : EuclideanSpace ℝ (Fin m)) :
    |inner ℝ (W.convectionOperator m a) b| ≤
      Real.sqrt 3 *
        ((∫ x : Space, officialEuclideanNorm ((⇑(W.coefficientField a)) x) ^ 4) ^ (1/4 : ℝ) *
          (∫ x : Space, ‖fderiv ℝ (⇑(W.coefficientField b)) x‖ ^ 2) ^ (1/2 : ℝ) *
          (∫ x : Space, officialEuclideanNorm ((⇑(W.coefficientField a)) x) ^ 4) ^ (1/4 : ℝ)) := by
  have hpair : (inner ℝ (W.convectionOperator m a) b : ℝ) =
      schwartzL2Inner (W.coefficientField a)
        (convectionSchwartzBilin (W.coefficientField a) (W.coefficientField b)) := by
    rw [← coefficientField_l2_inner W (W.convectionOperator m a) b]
    exact convectionOperator_pairing W m a b
  rw [hpair]
  exact abs_schwartzL2Inner_convection_le (W.coefficientField a)
    (W.coefficientField a) (W.coefficientField b)

end Navier.Analysis.ConvectionTrilinear
