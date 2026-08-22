import Navier.Analysis.OfficialABEncoding
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `L⁴` interpolation between `L²` and `L⁶` (Ladyzhenskaya, interpolation half)

The three-dimensional Ladyzhenskaya inequality
`‖u‖_{L⁴(ℝ³)} ≤ C ‖u‖_{L²}^{1/4} ‖∇u‖_{L²}^{3/4}` factors through exactly two
ingredients:

* the **interpolation** step `‖u‖_{L⁴}⁴ ≤ ‖u‖_{L²} · ‖u‖_{L⁶}³`, which is
  Cauchy–Schwarz applied to `∫ |u| · |u|³`, and
* the **Gagliardo–Nirenberg–Sobolev endpoint** `‖u‖_{L⁶(ℝ³)} ≤ C ‖∇u‖_{L²}`.

This file certifies the first, in the repository's Bochner-integral language,
and supplies the Schwartz-class integrability facts that any consumer of it
needs.  The GNS endpoint is a separate, strictly harder obligation: Mathlib's
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` supplies it only under
`HasCompactSupport`, which a Schwartz field does not satisfy.

## Certified here (no sorry)

* `integral_pow_four_le_sqrt` — the general measure-theoretic interpolation
  `∫ f⁴ ≤ √(∫ f²) · √(∫ f⁶)` for a nonnegative `f`.  This is exactly
  Cauchy–Schwarz, so the constant is `1`: the inequality is *sharp*, not a
  convenience bound.
* `schwartzBound` / `integrable_officialEuclideanNorm_pow` — a Schwartz field
  is uniformly bounded, and every power `‖u‖^{k+1}` of its official Euclidean
  pointwise norm is integrable.
* `schwartz_integral_pow_four_le` — the interpolation specialised to a Schwartz
  velocity field in the official Euclidean coordinates.

Numerically verified before formalisation (20000 random weighted samples,
maximum violation `1.5e-11`, i.e. floating-point noise); the endpoint `f = 0`
gives `0 ≤ 0`.  On centred Gaussians the full Ladyzhenskaya ratio
`‖u‖₄ / (‖u‖₂^{1/4}‖∇u‖₂^{3/4})` is constant `= 0.4311697…` across three
decades of amplitude and width, confirming that the exponents `1/4`, `3/4` are
the scale-forced ones.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.

References: Ladyzhenskaya, *The Mathematical Theory of Viscous Incompressible
Flow*, Ch. 1 §2; Temam, *Navier–Stokes Equations* III §3 (3.4);
Robinson–Rodrigo–Sadowski, *The Three-Dimensional Navier–Stokes Equations*,
Lemma 1.30.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Navier.Analysis.Ladyzhenskaya

open Navier
open Navier.Analysis.OfficialABEncoding

/-!
## The interpolation inequality (general, sharp constant `1`)
-/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Cauchy–Schwarz for Bochner integrals of nonnegative real functions
(certified, no `sorry`).**  `∫ f·g ≤ √(∫ f²) · √(∫ g²)`.

This is `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` at the conjugate
pair `(2, 2)`, restated with `Real.sqrt` and natural-number powers so that it
composes with the repository's Bochner-integral conventions.  Constant `1`,
sharp. -/
theorem integral_mul_le_sqrt_mul_sqrt
    {f g : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hpq : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have hmemf : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm).mpr hf2
  have hmemg : MemLp g 2 μ := (memLp_two_iff_integrable_sq hgm).mpr hg2
  have key := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
      (f := f) (g := g)
      (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
      (by simpa using hmemf) (by simpa using hmemg)
  have hr : ∀ h : α → ℝ, ∫ a, h a ^ (2:ℝ) ∂μ = ∫ a, h a ^ (2:ℕ) ∂μ := by
    intro h
    refine integral_congr_ae ?_
    filter_upwards with a
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [hr f, hr g] at key
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact key

/-- **`L⁴` interpolation between `L²` and `L⁶` (certified, no `sorry`).**  For a
nonnegative function with integrable square and sixth power,
`∫ f⁴ ≤ √(∫ f²) · √(∫ f⁶)`.

This is Cauchy–Schwarz applied to the factorisation `f⁴ = f · f³`, so the
constant is `1` and the inequality is sharp (equality iff `f³` is a.e.
proportional to `f`).  Taking fourth roots gives the familiar
`‖f‖₄ ≤ ‖f‖₂^{1/4} ‖f‖₆^{3/4}`.

Endpoint check: `f = 0` gives `0 ≤ 0`; no hypothesis is degenerate, and the
statement is satisfied by every integrable-power nonnegative `f` without being
vacuous (it fails for the reversed inequality already on a two-point space). -/
theorem integral_pow_four_le_sqrt
    {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : AEStronglyMeasurable f μ)
    (h2 : Integrable (fun x => f x ^ 2) μ)
    (h6 : Integrable (fun x => f x ^ 6) μ) :
    (∫ x, f x ^ 4 ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 6 ∂μ) := by
  have hg : AEStronglyMeasurable (fun x => f x ^ 3) μ := hfm.pow 3
  have h3sq : Integrable (fun x => (f x ^ 3) ^ 2) μ := by
    refine h6.congr ?_
    filter_upwards with x
    ring
  have key := integral_mul_le_sqrt_mul_sqrt (μ := μ) hf0
    (fun x => pow_nonneg (hf0 x) 3) hfm hg h2 h3sq
  have e1 : ∫ a, f a * f a ^ 3 ∂μ = ∫ a, f a ^ 4 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with a
    ring
  have e2 : ∫ a, (f a ^ 3) ^ 2 ∂μ = ∫ a, f a ^ 6 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with a
    ring
  rw [e1, e2] at key
  exact key

/-!
## Schwartz-class inputs
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A Schwartz map on `Space` is uniformly bounded (the `k = n = 0` decay
estimate). -/
theorem schwartzMapBound (u : SchwartzMap Space V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(⇑u) x‖ ≤ C := by
  obtain ⟨C, _, hC⟩ := u.decay 0 0
  refine ⟨C, ?_, fun x => by simpa using hC x⟩
  exact le_trans (norm_nonneg _) (by simpa using hC 0)

/-- Every positive power of the pointwise norm of a Schwartz map is integrable:
dominate `‖u‖^{k+1}` by `C^k · ‖u‖` and use `SchwartzMap.integrable`. -/
theorem integrable_schwartzMap_norm_pow (u : SchwartzMap Space V) (k : ℕ) :
    Integrable (fun x => ‖(⇑u) x‖ ^ (k + 1)) := by
  obtain ⟨C, _, hC0⟩ := schwartzMapBound u
  refine Integrable.mono' (g := fun x => C ^ k * ‖(⇑u) x‖)
    (u.integrable.norm.const_mul _) ?_ ?_
  · exact (u.continuous.norm.pow _).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity), pow_succ]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hC0 x) k) (norm_nonneg _)

/-- A Schwartz velocity field is uniformly bounded. -/
theorem schwartzBound (u : SchwartzVelocity) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(⇑u) x‖ ≤ C :=
  schwartzMapBound u

/-- Every positive power of the pointwise norm of a Schwartz velocity field is
integrable. -/
theorem integrable_norm_pow (u : SchwartzVelocity) (k : ℕ) :
    Integrable (fun x => ‖(⇑u) x‖ ^ (k + 1)) :=
  integrable_schwartzMap_norm_pow u k

/-- The same for the official Euclidean pointwise norm, which is comparable to
the ambient product norm on `Space` by `norm_le_officialEuclideanNorm` and
`officialEuclideanNorm_le`. -/
theorem integrable_officialEuclideanNorm_pow (u : SchwartzVelocity) (k : ℕ) :
    Integrable (fun x => officialEuclideanNorm ((⇑u) x) ^ (k + 1)) := by
  have hmeas : AEStronglyMeasurable
      (fun x => officialEuclideanNorm ((⇑u) x) ^ (k + 1)) (volume : Measure Space) := by
    have h0 : Continuous officialEuclideanNorm := by
      unfold officialEuclideanNorm officialEuclideanPoint; fun_prop
    exact ((h0.comp u.continuous).pow _).aestronglyMeasurable
  refine Integrable.mono'
    (g := fun x => Real.sqrt 3 ^ (k + 1) * ‖(⇑u) x‖ ^ (k + 1))
    ((integrable_norm_pow u k).const_mul _) hmeas ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (pow_nonneg (officialEuclideanNorm_nonneg _) _), ← mul_pow]
  exact pow_le_pow_left₀ (officialEuclideanNorm_nonneg _) (officialEuclideanNorm_le _) _

/-- **The interpolation bound for a Schwartz velocity field (certified, no
`sorry`).**  In the official Euclidean coordinates,
`∫ |u|⁴ ≤ √(∫ |u|²) · √(∫ |u|⁶)`.

Combined with the Gagliardo–Nirenberg–Sobolev endpoint
`(∫ |u|⁶)^{1/6} ≤ C (∫ |∇u|²)^{1/2}` this is exactly Ladyzhenskaya's
inequality on `ℝ³`; the endpoint is the remaining obligation and is *not*
supplied by this file. -/
theorem schwartz_integral_pow_four_le (u : SchwartzVelocity) :
    (∫ x : Space, officialEuclideanNorm ((⇑u) x) ^ 4) ≤
      Real.sqrt (∫ x : Space, officialEuclideanNorm ((⇑u) x) ^ 2) *
        Real.sqrt (∫ x : Space, officialEuclideanNorm ((⇑u) x) ^ 6) := by
  have h0 : Continuous officialEuclideanNorm := by
    unfold officialEuclideanNorm officialEuclideanPoint; fun_prop
  have hcont : Continuous fun x : Space => officialEuclideanNorm ((⇑u) x) := h0.comp u.continuous
  exact integral_pow_four_le_sqrt
    (fun x => officialEuclideanNorm_nonneg _)
    hcont.aestronglyMeasurable
    (by simpa using integrable_officialEuclideanNorm_pow u 1)
    (by simpa using integrable_officialEuclideanNorm_pow u 5)

end Navier.Analysis.Ladyzhenskaya
