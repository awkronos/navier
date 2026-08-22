import Navier.Analysis.Ladyzhenskaya
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The Gagliardo–Nirenberg–Sobolev endpoint on `ℝ³` for Schwartz fields

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` supplies the
Gagliardo–Nirenberg–Sobolev inequality only for **compactly supported** `C¹`
fields.  A Schwartz field is not compactly supported, so the estate could not
use it directly; this file removes that restriction by the standard
cutoff-and-limit argument and lands the endpoint in the repository's
Bochner-integral language:

`∫ ‖u‖⁶ ≤ C · (∫ ‖Du‖²)³`

which is `‖u‖_{L⁶(ℝ³)} ≤ C^{1/6} ‖∇u‖_{L²}` in sixth-power form.  Together with
`Ladyzhenskaya.integral_pow_four_le_sqrt` this gives the full three-dimensional
Ladyzhenskaya inequality, and hence turns the `L⁴` factors of
`ConvectionTrilinear.abs_convectionOperator_inner_le` into enstrophy.

## The argument

Fix the reference bump `bmp` (equal to `1` on the closed unit ball, supported in
the ball of radius `2`) and set `cut R x = bmp (R⁻¹ • x)`.  Then `cut R` is
smooth, takes values in `[0, 1]`, is `1` on `‖x‖ ≤ R`, has compact support, and
`‖D(cut R) x‖ ≤ K / R` for a fixed `K` — this last bound is the reason the
cutoff error vanishes and is obtained from `fderiv_comp_smul` plus a uniform
bound on `‖D bmp‖` (continuous with compact support).

Applying GNS to `trunc u R = (cut R) • u` and using
`(a + b)² ≤ 2a² + 2b²` on the product rule gives, for every `R ≥ 1`,

`∫ ‖trunc u R‖⁶ ≤ C₀⁶ · (2 ∫‖Du‖² + 2 (K/R)² ∫‖u‖²)³`,

where `C₀` is Mathlib's GNS constant.  Letting `R = n + 1 → ∞`, dominated
convergence (dominating function `‖u‖⁶`, integrable because `u` is Schwartz)
sends the left side to `∫‖u‖⁶` and the right side to `8 C₀⁶ (∫‖Du‖²)³`.

## Certified here (no sorry)

* `exists_gns_six` — `∃ C ≥ 0, ∀ u : SchwartzVelocity, ∫ ‖u‖⁶ ≤ C (∫ ‖Du‖²)³`.
* `exists_ladyzhenskaya` — the full Ladyzhenskaya inequality in the form
  `(∫ ‖u‖⁴)² ≤ C · (∫ ‖u‖²) · (∫ ‖Du‖²)³`, obtained by squaring the certified
  interpolation and substituting the endpoint.  Squaring keeps every exponent a
  natural number, so no `rpow` appears in the statement.

Step 0, before formalisation.  Both statements are scale-invariant, which is
the only way an inequality of this shape can be true: on centred Gaussians
`A exp(-|x|²/2s²)` the ratio `∫|u|⁶ / (∫|∇u|²)³` is constant `0.00183905502…`
across three decades of amplitude `A` and width `s`, and the Ladyzhenskaya
ratio `‖u‖₄/(‖u‖₂^{1/4}‖∇u‖₂^{3/4})` is constant `0.4311697…` on the same
family.  A wrong exponent would have broken the invariance immediately.
Endpoint `u = 0`: both sides `0`.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.

References: Evans, *Partial Differential Equations* §5.6.1 Thm 1 (GNS) and the
cutoff extension in §5.5; Ladyzhenskaya, *The Mathematical Theory of Viscous
Incompressible Flow* Ch. 1 §2; Mathlib
`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Navier.Analysis.SobolevGNS

open Navier
open Navier.Analysis.Ladyzhenskaya

/-!
## The cutoff family
-/

/-- The reference bump: `1` on the closed unit ball, supported in the ball of
radius `2`. -/
private def bmp : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, by norm_num⟩

/-- `‖D bmp‖` is bounded: it is continuous with compact support. -/
private theorem exists_bmp_fderiv_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Space, ‖fderiv ℝ (⇑bmp) x‖ ≤ K := by
  have hc : Continuous (fderiv ℝ (⇑bmp)) :=
    (bmp.contDiff (n := 2)).continuous_fderiv (by norm_num)
  have hcs : HasCompactSupport (fderiv ℝ (⇑bmp)) := bmp.hasCompactSupport.fderiv ℝ
  obtain ⟨K, hK⟩ := hcs.exists_bound_of_continuous hc
  exact ⟨max K 0, le_max_right _ _, fun x => (hK x).trans (le_max_left _ _)⟩

/-- The rescaled cutoff `χ_R (x) = bmp (x / R)`. -/
private def cut (R : ℝ) : Space → ℝ := fun x => bmp (R⁻¹ • x)

private theorem cut_contDiff (R : ℝ) : ContDiff ℝ 2 (cut R) :=
  (bmp.contDiff).comp (contDiff_const_smul _)

private theorem cut_nonneg (R : ℝ) (x : Space) : 0 ≤ cut R x := bmp.nonneg

private theorem cut_le_one (R : ℝ) (x : Space) : cut R x ≤ 1 := bmp.le_one

private theorem cut_hasCompactSupport {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (cut R) :=
  bmp.hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (R⁻¹) (inv_ne_zero hR))

private theorem cut_eq_one {R : ℝ} (hR : 0 < R) {x : Space} (hx : ‖x‖ ≤ R) :
    cut R x = 1 := by
  refine bmp.one_of_mem_closedBall ?_
  simp only [Metric.mem_closedBall, dist_zero_right]
  show ‖R⁻¹ • x‖ ≤ bmp.rIn
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  show R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR]
  simpa using hx

/-- **The scaling bound on the cutoff derivative.**  `‖D(χ_R) x‖ ≤ K / R`; this
is what makes the cutoff error vanish as `R → ∞`. -/
private theorem cut_fderiv_norm_le {K : ℝ} (hK : ∀ x : Space, ‖fderiv ℝ (⇑bmp) x‖ ≤ K)
    {R : ℝ} (hR : 0 < R) (x : Space) : ‖fderiv ℝ (cut R) x‖ ≤ K / R := by
  have hd : fderiv ℝ (cut R) x = R⁻¹ • fderiv ℝ (⇑bmp) (R⁻¹ • x) := fderiv_comp_smul _
  rw [hd, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hK _) (by positivity)

/-!
## The truncated field
-/

/-- The compactly supported truncation of a Schwartz field. -/
private def trunc (u : SchwartzVelocity) (R : ℝ) : Space → Space :=
  fun x => cut R x • (⇑u) x

private theorem trunc_contDiff (u : SchwartzVelocity) (R : ℝ) :
    ContDiff ℝ 2 (trunc u R) :=
  (cut_contDiff R).smul (u.smooth 2)

private theorem trunc_hasCompactSupport (u : SchwartzVelocity) {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (trunc u R) := by
  have h : HasCompactSupport ((cut R) • (⇑u : Space → Space)) :=
    HasCompactSupport.smul_right (cut_hasCompactSupport hR)
  exact h

private theorem trunc_norm_le (u : SchwartzVelocity) (R : ℝ) (x : Space) :
    ‖trunc u R x‖ ≤ ‖(⇑u) x‖ := by
  show ‖cut R x • (⇑u) x‖ ≤ ‖(⇑u) x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg R x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (cut_le_one R x)

/-- The product rule bound: `‖D(χ_R u)‖ ≤ ‖Du‖ + (K/R)‖u‖`. -/
private theorem trunc_fderiv_norm_le (u : SchwartzVelocity)
    {K : ℝ} (hK : ∀ x : Space, ‖fderiv ℝ (⇑bmp) x‖ ≤ K)
    {R : ℝ} (hR : 0 < R) (x : Space) :
    ‖fderiv ℝ (trunc u R) x‖ ≤ ‖fderiv ℝ (⇑u) x‖ + (K / R) * ‖(⇑u) x‖ := by
  have hc : DifferentiableAt ℝ (cut R) x :=
    ((cut_contDiff R).differentiable (by norm_num)).differentiableAt
  have hu : DifferentiableAt ℝ (⇑u) x :=
    (u.smooth 1).differentiable (by norm_num) |>.differentiableAt
  have hd : fderiv ℝ (trunc u R) x =
      cut R x • fderiv ℝ (⇑u) x + (fderiv ℝ (cut R) x).smulRight ((⇑u) x) :=
    fderiv_smul hc hu
  rw [hd]
  refine (norm_add_le _ _).trans ?_
  gcongr
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg R x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cut_le_one R x)
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (cut_fderiv_norm_le hK hR x) (norm_nonneg _)

/-!
## The compactly supported endpoint, in Bochner form
-/

/-- Mathlib's GNS constant for `E = F = Space`, `p = 2`. -/
private def gnsConst : ℝ≥0 :=
  MeasureTheory.SNormLESNormFDerivOfEqConst Space (volume : Measure Space) ((2 : ℝ≥0) : ℝ)

private theorem rpow_inv_pow {X : ℝ} (hX : 0 ≤ X) {r : ℝ} (hr : r ≠ 0) (n : ℕ)
    (hn : (n : ℝ) * r = 1) : (X ^ r) ^ n = X := by
  rw [← Real.rpow_natCast (X ^ r) n, ← Real.rpow_mul hX, mul_comm r (n : ℝ), hn,
    Real.rpow_one]

/-- **GNS for a compactly supported `C²` field on `ℝ³`, in Bochner form.**
`(∫ ‖v‖⁶)^{1/6} ≤ C₀ · (∫ ‖Dv‖²)^{1/2}`. -/
private theorem gns_of_hasCompactSupport {v : Space → Space}
    (hv : ContDiff ℝ 2 v) (h2v : HasCompactSupport v) :
    (∫ x : Space, ‖v x‖ ^ 6) ^ (1/6 : ℝ) ≤
      (gnsConst : ℝ) * (∫ x : Space, ‖fderiv ℝ v x‖ ^ 2) ^ (1/2 : ℝ) := by
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hdcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hmem6 : MemLp v 6 (volume : Measure Space) :=
    hv1.continuous.memLp_of_hasCompactSupport h2v
  have hmem2 : MemLp (fderiv ℝ v) 2 (volume : Measure Space) :=
    hdcont.memLp_of_hasCompactSupport (h2v.fderiv ℝ)
  have hgns := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
      (volume : Measure Space) hv1 h2v (p := 2) (p' := 6) (by norm_num)
      (by simp [Space])
      (by rw [show Module.finrank ℝ Space = 3 from by simp [Space]]; norm_num)
  simp only [ENNReal.coe_ofNat] at hgns
  rw [hmem6.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    hmem2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hgns
  have hI6 : (0:ℝ) ≤ ∫ x : Space, ‖v x‖ ^ 6 := integral_nonneg fun x => by positivity
  have hI2 : (0:ℝ) ≤ ∫ x : Space, ‖fderiv ℝ v x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hQ : (0:ℝ) ≤ (∫ x : Space, ‖fderiv ℝ v x‖ ^ 2) ^ (1/2 : ℝ) := Real.rpow_nonneg hI2 _
  have hnum6 : ((6:ℝ≥0∞).toReal) = 6 := by norm_num
  have hnum2 : ((2:ℝ≥0∞).toReal) = 2 := by norm_num
  rw [hnum6, hnum2] at hgns
  rw [show (MeasureTheory.SNormLESNormFDerivOfEqConst Space (volume : Measure Space)
        ((2 : ℝ≥0) : ℝ) : ℝ≥0∞) = ENNReal.ofReal (gnsConst : ℝ) from
      ENNReal.ofReal_coe_nnreal.symm,
    ← ENNReal.ofReal_mul (by positivity)] at hgns
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hgns
  simpa [one_div] using this

/-!
## Removing compact support
-/

/-- The truncated-derivative energy is controlled by the field's own energy,
uniformly in `R`, with an error that vanishes like `R⁻²`. -/
private theorem trunc_fderiv_sq_integral_le (u : SchwartzVelocity)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x : Space, ‖fderiv ℝ (⇑bmp) x‖ ≤ K)
    {R : ℝ} (hR : 0 < R) :
    (∫ x : Space, ‖fderiv ℝ (trunc u R) x‖ ^ 2) ≤
      2 * (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) +
        2 * (K / R) ^ 2 * (∫ x : Space, ‖(⇑u) x‖ ^ 2) := by
  have hdu : Integrable (fun x : Space => ‖fderiv ℝ (⇑u) x‖ ^ 2) := by
    have h : Integrable
        (fun x : Space => ‖(SchwartzMap.fderivCLM ℝ Space Space u) x‖ ^ 2) := by
      simpa using integrable_schwartzMap_norm_pow (SchwartzMap.fderivCLM ℝ Space Space u) 1
    refine h.congr ?_
    filter_upwards with x
    rw [SchwartzMap.fderivCLM_apply]
  have hu2 : Integrable (fun x : Space => ‖(⇑u) x‖ ^ 2) := by
    simpa using integrable_norm_pow u 1
  have hdt : Continuous (fderiv ℝ (trunc u R)) :=
    (trunc_contDiff u R).continuous_fderiv (by norm_num)
  have hmaj : Integrable (fun x : Space =>
      2 * ‖fderiv ℝ (⇑u) x‖ ^ 2 + 2 * (K / R) ^ 2 * ‖(⇑u) x‖ ^ 2) :=
    (hdu.const_mul 2).add (hu2.const_mul (2 * (K / R) ^ 2))
  have hptwise : ∀ x : Space, ‖fderiv ℝ (trunc u R) x‖ ^ 2 ≤
      2 * ‖fderiv ℝ (⇑u) x‖ ^ 2 + 2 * (K / R) ^ 2 * ‖(⇑u) x‖ ^ 2 := by
    intro x
    have h1 : ‖fderiv ℝ (trunc u R) x‖ ^ 2 ≤
        (‖fderiv ℝ (⇑u) x‖ + (K / R) * ‖(⇑u) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (trunc_fderiv_norm_le u hK hR x) 2
    nlinarith [sq_nonneg (‖fderiv ℝ (⇑u) x‖ - (K / R) * ‖(⇑u) x‖)]
  have hdtint : Integrable (fun x : Space => ‖fderiv ℝ (trunc u R) x‖ ^ 2) := by
    refine Integrable.mono' hmaj ((hdt.norm.pow 2).aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity)]
    exact hptwise x
  calc (∫ x : Space, ‖fderiv ℝ (trunc u R) x‖ ^ 2)
      ≤ ∫ x : Space, (2 * ‖fderiv ℝ (⇑u) x‖ ^ 2 + 2 * (K / R) ^ 2 * ‖(⇑u) x‖ ^ 2) :=
        integral_mono hdtint hmaj hptwise
    _ = 2 * (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) +
          2 * (K / R) ^ 2 * (∫ x : Space, ‖(⇑u) x‖ ^ 2) := by
        rw [integral_add (hdu.const_mul 2) (hu2.const_mul (2 * (K / R) ^ 2)),
          integral_const_mul, integral_const_mul]

/-!
## The endpoint for Schwartz fields
-/

/-- **The Gagliardo–Nirenberg–Sobolev endpoint on `ℝ³` for Schwartz fields
(certified, no `sorry`).**  `∫ ‖u‖⁶ ≤ C · (∫ ‖Du‖²)³`, i.e.
`‖u‖_{L⁶} ≤ C^{1/6} ‖∇u‖_{L²}`, with a single constant valid for every Schwartz
velocity field.

Mathlib's GNS needs compact support; the cutoff `χ_R` removes that hypothesis.
The `L²` energy of `u` enters only through the cutoff error `K/R`, which is why
it disappears in the limit and the final constant depends on nothing but the
dimension.

Endpoint `u = 0`: `0 ≤ 0`.  The statement is scale-invariant (both sides scale
as `A⁶s³` under `u ↦ A u(·/s)`), which is what forces the exponent `3` on the
right and is the check that would have caught a wrong exponent. -/
theorem exists_gns_six :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SchwartzVelocity,
      (∫ x : Space, ‖(⇑u) x‖ ^ 6) ≤ C * (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3 := by
  obtain ⟨K, hK0, hK⟩ := exists_bmp_fderiv_bound
  refine ⟨8 * (gnsConst : ℝ) ^ 6, by positivity, fun u => ?_⟩
  set B : ℝ := ∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2 with hB
  set D : ℝ := ∫ x : Space, ‖(⇑u) x‖ ^ 2 with hD
  have hB0 : 0 ≤ B := integral_nonneg fun x => by positivity
  have hD0 : 0 ≤ D := integral_nonneg fun x => by positivity
  -- the truncated bound, for every positive `R`
  have hstep : ∀ R : ℝ, 0 < R →
      (∫ x : Space, ‖trunc u R x‖ ^ 6) ≤
        (gnsConst : ℝ) ^ 6 * (2 * B + 2 * (K / R) ^ 2 * D) ^ 3 := by
    intro R hR
    have hgns := gns_of_hasCompactSupport (trunc_contDiff u R)
      (trunc_hasCompactSupport u (ne_of_gt hR))
    have hQ0 : (0:ℝ) ≤ ∫ x : Space, ‖fderiv ℝ (trunc u R) x‖ ^ 2 :=
      integral_nonneg fun x => by positivity
    have hM0 : (0:ℝ) ≤ 2 * B + 2 * (K / R) ^ 2 * D := by positivity
    have hmono : (∫ x : Space, ‖fderiv ℝ (trunc u R) x‖ ^ 2) ^ (1/2 : ℝ) ≤
        (2 * B + 2 * (K / R) ^ 2 * D) ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow hQ0 (trunc_fderiv_sq_integral_le u hK0 hK hR) (by norm_num)
    have hchain : (∫ x : Space, ‖trunc u R x‖ ^ 6) ^ (1/6 : ℝ) ≤
        (gnsConst : ℝ) * (2 * B + 2 * (K / R) ^ 2 * D) ^ (1/2 : ℝ) :=
      hgns.trans (mul_le_mul_of_nonneg_left hmono (NNReal.coe_nonneg gnsConst))
    have hS0 : (0:ℝ) ≤ ∫ x : Space, ‖trunc u R x‖ ^ 6 :=
      integral_nonneg fun x => by positivity
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hS0 _) hchain 6
    rw [rpow_inv_pow hS0 (r := (1/6 : ℝ)) (by norm_num) 6 (by norm_num), mul_pow] at hpow
    calc (∫ x : Space, ‖trunc u R x‖ ^ 6)
        ≤ (gnsConst : ℝ) ^ 6 * (((2 * B + 2 * (K / R) ^ 2 * D) ^ (1/2 : ℝ)) ^ 6) := hpow
      _ = (gnsConst : ℝ) ^ 6 * (2 * B + 2 * (K / R) ^ 2 * D) ^ 3 := by
          congr 1
          rw [show (6:ℕ) = 2 * 3 from rfl, pow_mul,
            rpow_inv_pow hM0 (r := (1/2 : ℝ)) (by norm_num) 2 (by norm_num)]
  -- pass to the limit along `R = n + 1`
  have hdom : Integrable (fun x : Space => ‖(⇑u) x‖ ^ 6) := by
    simpa using integrable_norm_pow u 5
  have hlhs : Tendsto (fun n : ℕ => ∫ x : Space, ‖trunc u ((n : ℝ) + 1) x‖ ^ 6) atTop
      (𝓝 (∫ x : Space, ‖(⇑u) x‖ ^ 6)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖(⇑u) x‖ ^ 6) ?_ hdom ?_ ?_
    · intro n
      exact (((trunc_contDiff u ((n : ℝ) + 1)).continuous.norm).pow 6).aestronglyMeasurable
    · intro n
      filter_upwards with x
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (trunc_norm_le u _ x) 6
    · filter_upwards with x
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
      have hxle : ‖x‖ ≤ (n : ℝ) + 1 := by
        have h1 : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈‖x‖⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
        linarith
      have : trunc u ((n : ℝ) + 1) x = (⇑u) x := by
        show cut ((n : ℝ) + 1) x • (⇑u) x = (⇑u) x
        rw [cut_eq_one (by positivity) hxle, one_smul]
      rw [this]
  have hKR : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) K
  have hrhs : Tendsto
      (fun n : ℕ => (gnsConst : ℝ) ^ 6 * (2 * B + 2 * (K / ((n : ℝ) + 1)) ^ 2 * D) ^ 3)
      atTop (𝓝 ((gnsConst : ℝ) ^ 6 * (2 * B + 2 * (0:ℝ) ^ 2 * D) ^ 3)) :=
    ((((hKR.pow 2).const_mul 2).mul_const D).const_add (2 * B)).pow 3 |>.const_mul _
  have hfinal := le_of_tendsto_of_tendsto' hlhs hrhs
    (fun n => hstep ((n : ℝ) + 1) (by positivity))
  calc (∫ x : Space, ‖(⇑u) x‖ ^ 6)
      ≤ (gnsConst : ℝ) ^ 6 * (2 * B + 2 * (0:ℝ) ^ 2 * D) ^ 3 := hfinal
    _ = 8 * (gnsConst : ℝ) ^ 6 * B ^ 3 := by ring

/-!
## The Ladyzhenskaya inequality
-/

/-- **The three-dimensional Ladyzhenskaya inequality (certified, no `sorry`).**
`(∫ ‖u‖⁴)² ≤ C · (∫ ‖u‖²) · (∫ ‖Du‖²)³`, which is
`‖u‖_{L⁴} ≤ C^{1/8} ‖u‖_{L²}^{1/4} ‖∇u‖_{L²}^{3/4}` after taking eighth roots.

Squaring the interpolation keeps every exponent a natural number, so the
statement carries no `rpow`.  Assembled from the two certified halves:
`Ladyzhenskaya.integral_pow_four_le_sqrt` (Cauchy–Schwarz, constant `1`) and
`exists_gns_six` (the Sobolev endpoint).

Step 0: on centred Gaussians the ratio
`‖u‖₄/(‖u‖₂^{1/4}‖∇u‖₂^{3/4})` is constant `0.4311697…` across three decades of
amplitude and width — the scale invariance that forces these exponents. -/
theorem exists_ladyzhenskaya :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SchwartzVelocity,
      (∫ x : Space, ‖(⇑u) x‖ ^ 4) ^ 2 ≤
        C * (∫ x : Space, ‖(⇑u) x‖ ^ 2) * (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := exists_gns_six
  refine ⟨C, hC0, fun u => ?_⟩
  have hcont : Continuous fun x : Space => ‖(⇑u) x‖ := u.continuous.norm
  have h2 : Integrable (fun x : Space => ‖(⇑u) x‖ ^ 2) := by
    simpa using integrable_norm_pow u 1
  have h6 : Integrable (fun x : Space => ‖(⇑u) x‖ ^ 6) := by
    simpa using integrable_norm_pow u 5
  have hinterp := integral_pow_four_le_sqrt (μ := (volume : Measure Space))
    (f := fun x => ‖(⇑u) x‖) (fun x => norm_nonneg _) hcont.aestronglyMeasurable h2 h6
  have hP0 : (0:ℝ) ≤ ∫ x : Space, ‖(⇑u) x‖ ^ 2 := integral_nonneg fun x => by positivity
  have hQ0 : (0:ℝ) ≤ ∫ x : Space, ‖(⇑u) x‖ ^ 6 := integral_nonneg fun x => by positivity
  have hX0 : (0:ℝ) ≤ ∫ x : Space, ‖(⇑u) x‖ ^ 4 := integral_nonneg fun x => by positivity
  have hsq := pow_le_pow_left₀ hX0 hinterp 2
  rw [mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt hQ0] at hsq
  refine hsq.trans ?_
  calc (∫ x : Space, ‖(⇑u) x‖ ^ 2) * (∫ x : Space, ‖(⇑u) x‖ ^ 6)
      ≤ (∫ x : Space, ‖(⇑u) x‖ ^ 2) *
          (C * (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3) :=
        mul_le_mul_of_nonneg_left (hC u) hP0
    _ = C * (∫ x : Space, ‖(⇑u) x‖ ^ 2) *
          (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3 := by ring

/-- **Ladyzhenskaya in the repository's official Euclidean coordinates.**  The
conversion is `‖x‖ ≤ officialEuclideanNorm x ≤ √3 ‖x‖`, which costs `3² = 9` on
each `L⁴` factor and is free on the `L²` factor.  This is the form that
converts the `L⁴` factors of
`ConvectionTrilinear.abs_convectionOperator_inner_le` into energy and
derivative energy. -/
theorem exists_ladyzhenskaya_official :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SchwartzVelocity,
      (∫ x : Space, Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 4) ^ 2 ≤
        C * (∫ x : Space,
              Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 2) *
          (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_ladyzhenskaya
  refine ⟨81 * C, by positivity, fun u => ?_⟩
  have h4 : Integrable (fun x : Space => ‖(⇑u) x‖ ^ 4) := by
    simpa using integrable_norm_pow u 3
  have h4o : Integrable (fun x : Space =>
      Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 4) := by
    simpa using integrable_officialEuclideanNorm_pow u 3
  have h2 : Integrable (fun x : Space => ‖(⇑u) x‖ ^ 2) := by
    simpa using integrable_norm_pow u 1
  have h2o : Integrable (fun x : Space =>
      Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 2) := by
    simpa using integrable_officialEuclideanNorm_pow u 1
  -- the L⁴ side costs 9
  have hup : (∫ x : Space,
      Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 4) ≤
      9 * ∫ x : Space, ‖(⇑u) x‖ ^ 4 := by
    rw [← integral_const_mul]
    refine integral_mono h4o (h4.const_mul 9) fun x => ?_
    have hle := Navier.Analysis.OfficialABEncoding.officialEuclideanNorm_le ((⇑u) x)
    have h := pow_le_pow_left₀
      (Navier.Analysis.OfficialABEncoding.officialEuclideanNorm_nonneg _) hle 4
    calc Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 4
        ≤ (Real.sqrt 3 * ‖(⇑u) x‖) ^ 4 := h
      _ = 9 * ‖(⇑u) x‖ ^ 4 := by
          rw [mul_pow, show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]
          norm_num
  -- the L² side is free
  have hdown : (∫ x : Space, ‖(⇑u) x‖ ^ 2) ≤
      ∫ x : Space, Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 2 := by
    refine integral_mono h2 h2o fun x => ?_
    exact pow_le_pow_left₀ (norm_nonneg _)
      (Navier.Analysis.OfficialABEncoding.norm_le_officialEuclideanNorm _) 2
  have hX0 : (0:ℝ) ≤ ∫ x : Space, ‖(⇑u) x‖ ^ 4 := integral_nonneg fun x => by positivity
  have hO0 : (0:ℝ) ≤ ∫ x : Space,
      Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 4 :=
    integral_nonneg fun x => by positivity
  have hG0 : (0:ℝ) ≤ (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3 := by
    have : (0:ℝ) ≤ ∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2 := integral_nonneg fun x => by positivity
    positivity
  calc (∫ x : Space,
      Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 4) ^ 2
      ≤ (9 * ∫ x : Space, ‖(⇑u) x‖ ^ 4) ^ 2 := pow_le_pow_left₀ hO0 hup 2
    _ = 81 * ((∫ x : Space, ‖(⇑u) x‖ ^ 4) ^ 2) := by ring
    _ ≤ 81 * (C * (∫ x : Space, ‖(⇑u) x‖ ^ 2) *
          (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3) := by
        exact mul_le_mul_of_nonneg_left (hC u) (by norm_num)
    _ ≤ 81 * (C * (∫ x : Space,
          Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 2) *
          (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3) := by
        have : C * (∫ x : Space, ‖(⇑u) x‖ ^ 2) ≤
            C * (∫ x : Space,
              Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 2) :=
          mul_le_mul_of_nonneg_left hdown hC0
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right this hG0) (by norm_num)
    _ = 81 * C * (∫ x : Space,
          Navier.Analysis.OfficialABEncoding.officialEuclideanNorm ((⇑u) x) ^ 2) *
          (∫ x : Space, ‖fderiv ℝ (⇑u) x‖ ^ 2) ^ 3 := by ring

end Navier.Analysis.SobolevGNS
