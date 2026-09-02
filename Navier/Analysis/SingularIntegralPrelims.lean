import Navier.Analysis.BiotSavartKernel
import Navier.Analysis.Vorticity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Singular-integral preliminaries: log optimization and the BKM shape reduction

This file builds the algebraic infrastructure that reduces the Biot–Savart log
inequality (the hardest Mathlib-absent input of the Beale–Kato–Majda criterion)
to its genuinely deep core: the Calderón–Zygmund near-field cancellation bound.

## Certified here (no sorry)

* `log_subadditive_prod` — `log(1+ab) ≤ log(1+a) + log(1+b)`, the key
  log-subadditivity governing how the cutoff optimization introduces the `log⁺`.
* `sqrt_le_one_add_self` — `√s ≤ 1+s`, absorbing the root into the linear term.
* `log_absorption` — `1 + M(1+log(1+L)) ≤ (1+M)(1+log(1+L))`, the constant
  absorption step used in the BKM assembly chain.
* `bkm_shape_absorption` — the three-term version with `√M₂`, the exact algebraic
  step from `logBKMControl_of_schwartzSliced` extracted as a named lemma.
* `sobolev_root_absorption` — `C·√Ms ≤ C·(1+Ms)`.

## The `p = 2` Calderón–Zygmund layer (certified here, no sorry)

* `l2_multiplier_bound` — **`L²` boundedness of every bounded Fourier
  multiplier**: if `‖m ξ‖ ≤ C` pointwise and `𝓕 g = m · 𝓕 f` a.e., then
  `‖g‖₂ ≤ C ‖f‖₂`.  Proof: Plancherel (`MeasureTheory.Lp.fourierTransformₗᵢ`,
  present in the pinned Mathlib `v4.31.0` at `Mathlib/Analysis/Fourier/LpSpace.lean`)
  plus the pointwise domination lemma `MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul`.
* `exists_l2_multiplier_apply` — the operator **exists**: for a measurable
  bounded `m` and any `f ∈ L²`, there is a `g ∈ L²` with `𝓕 g = m · 𝓕 f` a.e.
  and `‖g‖ ≤ C ‖f‖`.  Without this the bound above would be a statement about a
  possibly empty hypothesis set.
* `rieszMultiplier` / `doubleRieszMultiplier` — the symbols `-i ξⱼ/|ξ|` and
  `-ξᵢξⱼ/|ξ|²` of `Rⱼ` and `RᵢRⱼ`, with `‖·‖ ≤ 1` everywhere
  (`norm_rieszMultiplier_le_one`, `norm_doubleRieszMultiplier_le_one`) and
  measurability.
* `riesz_l2_bound`, `doubleRiesz_l2_bound` — `‖Rⱼ f‖₂ ≤ ‖f‖₂`,
  `‖RᵢRⱼ f‖₂ ≤ ‖f‖₂`.
* `pressure_l2_bound_of_doubleRiesz_representation` — the consumer shape of
  the Navier–Stokes pressure: if `p = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` in `L²(ℝ³)`, then
  `‖p‖₂ ≤ Σᵢⱼ ‖uᵢuⱼ‖₂`.  This is the `p = 2` half of blocker (b) of
  `ConditionalRegularity.prodiSerrin_interior_outerRegion_bounded`.

Scope, stated once and travelling with every claim above: this is the
**`p = 2`** theory only.  It is exactly the Hilbert-space/Plancherel case and
uses no Calderón–Zygmund decomposition, no weak-`(1,1)` bound and no
Marcinkiewicz interpolation.  The domain carrier is `EuclideanSpace ℝ (Fin 3)`
(Plancherel needs a real inner-product structure), not the estate's
`Space = Fin 3 → ℝ`; transporting along the measure-preserving coordinate
equivalence is a separate step and is *not* performed here.

## Honest residual

The `L^r` theory for `r ≠ 2` — weak-`(1,1)` via the Calderón–Zygmund
decomposition, Marcinkiewicz interpolation, `L^∞ → BMO` for homogeneous
kernels on `ℝ³` (Stein, *Singular Integrals* 1970 Ch. II §4; Grafakos §4.3;
genuinely Mathlib-absent) — is named in `BealeKatoMajda.lean` as
`BKMAnalyticResidual.biotSavartLogInequality`.

Axiom set: `⊆ {propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace Navier.Analysis.SingularIntegralPrelims

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BiotSavartKernel

/-!
## Elementary log inequalities
-/

/-- **Log-subadditivity on products.**  For `a, b ≥ 0`,
`log(1 + a·b) ≤ log(1 + a) + log(1 + b)`.

Follows from `1 + ab ≤ (1+a)(1+b)` and the monotonicity of `log`. -/
theorem log_subadditive_prod {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.log (1 + a * b) ≤ Real.log (1 + a) + Real.log (1 + b) := by
  have h1 : (0 : ℝ) < 1 + a * b := by nlinarith
  have h2 : (0 : ℝ) < 1 + a := by nlinarith
  have h3 : (0 : ℝ) < 1 + b := by nlinarith
  have hkey : 1 + a * b ≤ (1 + a) * (1 + b) := by nlinarith
  have hlog := Real.log_le_log h1 hkey
  rwa [Real.log_mul (ne_of_gt h2) (ne_of_gt h3)] at hlog

/-- **`log` is nonnegative on `[1, ∞)`.** -/
theorem log_nonneg_of_ge_one {Y : ℝ} (hY : 1 ≤ Y) :
    0 ≤ Real.log Y :=
  Real.log_nonneg hY

/-- **Square-root domination.**  For `s ≥ 0`, `√s ≤ 1 + s`. -/
theorem sqrt_le_one_add_self {s : ℝ} (hs : 0 ≤ s) :
    Real.sqrt s ≤ 1 + s := by
  nlinarith [sq_nonneg (1 - Real.sqrt s), Real.sq_sqrt hs,
    Real.sqrt_nonneg s]

/-- **The log-absorption (constant bookkeeping) lemma.**  For `M, L ≥ 0`,
`1 + M·(1 + log(1+L)) ≤ (1+M)·(1 + log(1+L))`. -/
theorem log_absorption {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) :
    1 + M * (1 + Real.log (1 + L)) ≤
      (1 + M) * (1 + Real.log (1 + L)) := by
  have hlog : 0 ≤ Real.log (1 + L) :=
    Real.log_nonneg (by nlinarith)
  nlinarith

/-!
## The BKM shape absorption (assembly-chain algebra)
-/

/-- **The BKM three-term absorption lemma.**  For `Mω, L, M₂ ≥ 0`,

  `1 + Mω·(1 + log(1+L)) + √M₂ ≤ (1 + Mω + √M₂)·(1 + log(1+L))`.

This is the exact algebraic step (proven inline via `nlinarith` in
`logBKMControl_of_schwartzSliced`, line 458 of `BKMLogBootstrap.lean`) that
absorbs the Biot–Savart additive bound into the multiplicative log-linear
Grönwall rate.  Extracted as a named, reusable lemma. -/
theorem bkm_shape_absorption {Mω L M₂ : ℝ}
    (hMω : 0 ≤ Mω) (hL : 0 ≤ L) (hM₂ : 0 ≤ M₂) :
    1 + Mω * (1 + Real.log (1 + L)) + Real.sqrt M₂ ≤
      (1 + Mω + Real.sqrt M₂) * (1 + Real.log (1 + L)) := by
  have hlog : 0 ≤ Real.log (1 + L) :=
    Real.log_nonneg (by nlinarith)
  have hsqrt : 0 ≤ Real.sqrt M₂ := Real.sqrt_nonneg _
  nlinarith

/-- **Sobolev root absorption.**  `C·√Ms ≤ C·(1+Ms)` for `Ms, C ≥ 0` —
absorbs the Sobolev root into the linear control term (velocity-domination
step of the BKM assembly). -/
theorem sobolev_root_absorption {Ms C : ℝ} (hMs : 0 ≤ Ms) (hC : 0 ≤ C) :
    C * Real.sqrt Ms ≤ C * (1 + Ms) := by
  exact mul_le_mul_of_nonneg_left (sqrt_le_one_add_self hMs) hC

/-!
## The `L²` Fourier-multiplier layer

Plancherel is available in the pinned Mathlib (`v4.31.0`) as
`MeasureTheory.Lp.fourierTransformₗᵢ`, a linear isometry equivalence of
`L²(E, F)` for `E` a finite-dimensional real inner-product space and `F` a
complex inner-product space.  That makes the whole `p = 2` singular-integral
theory a two-line consequence: an operator whose Fourier symbol is bounded by
`C` is bounded on `L²` with the same constant.

Measured 2026-09-02: the estate's residual notes recorded Plancherel as absent
from the pinned Mathlib.  That is false — `Mathlib/Analysis/Fourier/LpSpace.lean`
carries it, in the vector-valued form.  Only the `r ≠ 2` theory is absent.
-/

section L2Multiplier

open MeasureTheory

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **`L²` boundedness of a bounded Fourier multiplier.**  If the symbol `m`
satisfies `‖m ξ‖ ≤ C` for every frequency `ξ`, and `g` is a function whose
Fourier transform is `m · 𝓕 f` almost everywhere, then `‖g‖₂ ≤ C ‖f‖₂`.

This is the `p = 2` Calderón–Zygmund theorem.  Its proof is Plancherel on both
sides of the pointwise symbol bound; no decomposition or interpolation is
involved, which is precisely why `p = 2` is Mathlib-reachable and `p ≠ 2` is
not. -/
theorem l2_multiplier_bound
    (C : ℝ) (m : E → ℂ) (f g : Lp (α := E) F 2)
    (hm : ∀ ξ : E, ‖m ξ‖ ≤ C)
    (hmul : ∀ᵐ ξ : E,
      (MeasureTheory.Lp.fourierTransformₗᵢ E F g) ξ
        = m ξ • (MeasureTheory.Lp.fourierTransformₗᵢ E F f) ξ) :
    ‖g‖ ≤ C * ‖f‖ := by
  have h1 : ‖MeasureTheory.Lp.fourierTransformₗᵢ E F g‖
      ≤ C * ‖MeasureTheory.Lp.fourierTransformₗᵢ E F f‖ := by
    refine MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hmul] with ξ hξ
    rw [hξ, norm_smul]
    exact mul_le_mul_of_nonneg_right (hm ξ) (norm_nonneg _)
  rwa [(MeasureTheory.Lp.fourierTransformₗᵢ E F).norm_map,
    (MeasureTheory.Lp.fourierTransformₗᵢ E F).norm_map] at h1

/-- **The multiplier operator exists.**  For a measurable symbol bounded by
`C` and any `f ∈ L²`, there is an actual `g ∈ L²` realising `𝓕 g = m · 𝓕 f`,
with `‖g‖ ≤ C ‖f‖`.

This is the satisfiability half of `l2_multiplier_bound`: without it that
theorem could be about an empty hypothesis set.  Construction: `m · 𝓕 f` is in
`L²` by domination against `C • 𝓕 f`, and `g` is its inverse Fourier
transform. -/
theorem exists_l2_multiplier_apply
    (C : ℝ) (m : E → ℂ) (hmeas : AEStronglyMeasurable m (volume : Measure E))
    (hm : ∀ ξ : E, ‖m ξ‖ ≤ C) (f : Lp (α := E) F 2) :
    ∃ g : Lp (α := E) F 2,
      (∀ᵐ ξ : E, (MeasureTheory.Lp.fourierTransformₗᵢ E F g) ξ
        = m ξ • (MeasureTheory.Lp.fourierTransformₗᵢ E F f) ξ) ∧
      ‖g‖ ≤ C * ‖f‖ := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hm 0)
  set h : Lp (α := E) F 2 := MeasureTheory.Lp.fourierTransformₗᵢ E F f with hh
  have hmem : MemLp (fun ξ : E => m ξ • h ξ) 2 (volume : Measure E) := by
    refine MemLp.of_le (g := fun ξ : E => (C : ℂ) • h ξ)
      ((Lp.memLp h).const_smul (C : ℂ)) (hmeas.smul (Lp.aestronglyMeasurable h)) ?_
    filter_upwards with ξ
    rw [norm_smul, norm_smul]
    have hCn : ‖(C : ℂ)‖ = C := by simp [Complex.norm_real, abs_of_nonneg hC]
    rw [hCn]
    exact mul_le_mul_of_nonneg_right (hm ξ) (norm_nonneg _)
  refine ⟨(MeasureTheory.Lp.fourierTransformₗᵢ E F).symm (hmem.toLp _), ?_, ?_⟩
  · rw [LinearIsometryEquiv.apply_symm_apply]
    filter_upwards [hmem.coeFn_toLp] with ξ hξ using hξ
  · rw [LinearIsometryEquiv.norm_map]
    refine le_trans (MeasureTheory.Lp.norm_le_mul_norm_of_ae_le_mul
      (c := C) (g := h) ?_) ?_
    · filter_upwards [hmem.coeFn_toLp] with ξ hξ
      rw [hξ, norm_smul]
      exact mul_le_mul_of_nonneg_right (hm ξ) (norm_nonneg _)
    · rw [hh, LinearIsometryEquiv.norm_map]

/-- **Finite sums of multiplier operators.**  A function that decomposes as a
finite sum of multiplier images obeys the sum of the individual bounds.  This
is the shape the Navier–Stokes pressure representation
`p = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)` consumes. -/
theorem l2_multiplier_sum_bound {ι : Type*} (s : Finset ι)
    (C : ι → ℝ) (m : ι → E → ℂ) (f h : ι → Lp (α := E) F 2)
    (g : Lp (α := E) F 2)
    (hm : ∀ k ∈ s, ∀ ξ : E, ‖m k ξ‖ ≤ C k)
    (hh : ∀ k ∈ s, ∀ᵐ ξ : E,
      (MeasureTheory.Lp.fourierTransformₗᵢ E F (h k)) ξ
        = m k ξ • (MeasureTheory.Lp.fourierTransformₗᵢ E F (f k)) ξ)
    (hg : g = ∑ k ∈ s, h k) :
    ‖g‖ ≤ ∑ k ∈ s, C k * ‖f k‖ := by
  rw [hg]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k hk => ?_)
  exact l2_multiplier_bound (C k) (m k) (f k) (h k) (hm k hk) (hh k hk)

end L2Multiplier

/-!
## The Riesz transforms on `ℝ³` and the `L²` pressure bound
-/

section Riesz

open MeasureTheory

/-- The Plancherel-compatible carrier for `ℝ³`.  Plancherel needs a real
inner-product structure, which `Space = Fin 3 → ℝ` (sup norm) does not carry;
transport along the measure-preserving coordinate equivalence is a separate
step and is not performed in this file. -/
abbrev FourierSpace := EuclideanSpace ℝ (Fin 3)

/-- Coordinate domination on `EuclideanSpace ℝ (Fin 3)`. -/
theorem abs_coord_le_norm (j : Fin 3) (ξ : FourierSpace) : |ξ j| ≤ ‖ξ‖ := by
  simpa using PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) ξ j

/-- **The Riesz-transform symbol** `-i ξⱼ / |ξ|`.  Lean's `x / 0 = 0`
convention gives the value `0` at the origin, a null set. -/
def rieszMultiplier (j : Fin 3) (ξ : FourierSpace) : ℂ :=
  (-Complex.I) * ((ξ j : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ)

/-- **The double Riesz symbol** `-ξᵢξⱼ / |ξ|²`, the Fourier multiplier of
`RᵢRⱼ` and hence of the Navier–Stokes pressure operator
`p = Σᵢⱼ RᵢRⱼ(uᵢuⱼ)`. -/
def doubleRieszMultiplier (i j : Fin 3) (ξ : FourierSpace) : ℂ :=
  -(((ξ i * ξ j : ℝ) : ℂ) / ((‖ξ‖ ^ 2 : ℝ) : ℂ))

theorem norm_rieszMultiplier_le_one (j : Fin 3) (ξ : FourierSpace) :
    ‖rieszMultiplier j ξ‖ ≤ 1 := by
  rcases eq_or_ne ξ 0 with h | h
  · simp [rieszMultiplier, h]
  · have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr h
    rw [rieszMultiplier, norm_div, norm_mul]
    simp only [Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_neg]
    rw [div_le_one (by simpa [abs_of_pos hpos] using hpos)]
    simpa [abs_of_pos hpos] using abs_coord_le_norm j ξ

theorem norm_doubleRieszMultiplier_le_one (i j : Fin 3) (ξ : FourierSpace) :
    ‖doubleRieszMultiplier i j ξ‖ ≤ 1 := by
  rcases eq_or_ne ξ 0 with h | h
  · simp [doubleRieszMultiplier, h]
  · have hpos : 0 < ‖ξ‖ := norm_pos_iff.mpr h
    have hsq : (0:ℝ) < ‖ξ‖ ^ 2 := by positivity
    rw [doubleRieszMultiplier, norm_neg, norm_div]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_one (by simpa [abs_of_pos hsq] using hsq), abs_of_pos hsq, abs_mul]
    have h1 := abs_coord_le_norm i ξ
    have h2 := abs_coord_le_norm j ξ
    nlinarith [abs_nonneg (ξ i), abs_nonneg (ξ j)]

theorem continuous_coord (j : Fin 3) : Continuous fun ξ : FourierSpace => (ξ j : ℝ) :=
  (EuclideanSpace.proj (𝕜 := ℝ) j).continuous

theorem measurable_rieszMultiplier (j : Fin 3) : Measurable (rieszMultiplier j) := by
  unfold rieszMultiplier
  exact (measurable_const.mul
    (Complex.measurable_ofReal.comp (continuous_coord j).measurable)).div
    (Complex.measurable_ofReal.comp continuous_norm.measurable)

theorem measurable_doubleRieszMultiplier (i j : Fin 3) :
    Measurable (doubleRieszMultiplier i j) := by
  unfold doubleRieszMultiplier
  exact ((Complex.measurable_ofReal.comp
      (((continuous_coord i).mul (continuous_coord j)).measurable)).div
    (Complex.measurable_ofReal.comp ((continuous_norm.pow 2).measurable))).neg

/-- **`L²` boundedness of the Riesz transform** `Rⱼ` on `ℝ³`, with constant
one.  Stated over the realising pair `(f, g)`; `exists_rieszTransform` supplies
the realiser. -/
theorem riesz_l2_bound (j : Fin 3) (f g : Lp (α := FourierSpace) ℂ 2)
    (hmul : ∀ᵐ ξ : FourierSpace,
      (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ g) ξ
        = rieszMultiplier j ξ • (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ f) ξ) :
    ‖g‖ ≤ ‖f‖ := by
  simpa using l2_multiplier_bound 1 (rieszMultiplier j) f g
    (norm_rieszMultiplier_le_one j) hmul

/-- **`L²` boundedness of the double Riesz transform** `RᵢRⱼ`, constant one. -/
theorem doubleRiesz_l2_bound (i j : Fin 3) (f g : Lp (α := FourierSpace) ℂ 2)
    (hmul : ∀ᵐ ξ : FourierSpace,
      (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ g) ξ
        = doubleRieszMultiplier i j ξ •
          (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ f) ξ) :
    ‖g‖ ≤ ‖f‖ := by
  simpa using l2_multiplier_bound 1 (doubleRieszMultiplier i j) f g
    (norm_doubleRieszMultiplier_le_one i j) hmul

/-- **The Riesz transform exists on `L²(ℝ³)`.** -/
theorem exists_rieszTransform (j : Fin 3) (f : Lp (α := FourierSpace) ℂ 2) :
    ∃ g : Lp (α := FourierSpace) ℂ 2,
      (∀ᵐ ξ : FourierSpace,
        (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ g) ξ
          = rieszMultiplier j ξ •
            (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ f) ξ) ∧ ‖g‖ ≤ ‖f‖ := by
  obtain ⟨g, hg, hnorm⟩ := exists_l2_multiplier_apply 1 (rieszMultiplier j)
    (measurable_rieszMultiplier j).aestronglyMeasurable
    (norm_rieszMultiplier_le_one j) f
  exact ⟨g, hg, by simpa using hnorm⟩

/-- **The double Riesz transform exists on `L²(ℝ³)`.** -/
theorem exists_doubleRieszTransform (i j : Fin 3) (f : Lp (α := FourierSpace) ℂ 2) :
    ∃ g : Lp (α := FourierSpace) ℂ 2,
      (∀ᵐ ξ : FourierSpace,
        (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ g) ξ
          = doubleRieszMultiplier i j ξ •
            (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ f) ξ) ∧ ‖g‖ ≤ ‖f‖ := by
  obtain ⟨g, hg, hnorm⟩ := exists_l2_multiplier_apply 1 (doubleRieszMultiplier i j)
    (measurable_doubleRieszMultiplier i j).aestronglyMeasurable
    (norm_doubleRieszMultiplier_le_one i j) f
  exact ⟨g, hg, by simpa using hnorm⟩

/-- **The `L²` pressure bound.**  If the pressure `P` decomposes as
`Σᵢⱼ RᵢRⱼ(wᵢⱼ)` with `wᵢⱼ` the quadratic velocity products `uᵢuⱼ`, then

  `‖P‖₂ ≤ Σᵢⱼ ‖wᵢⱼ‖₂`.

This is the `p = 2` half of blocker (b) of
`ConditionalRegularity.prodiSerrin_interior_outerRegion_bounded`: the local
`L²` bound on the normalized pressure that
`PressureNormalization.abs_cutoffPressure_le_localL2` consumes as its first
factor.

Scope: the Calderón–Zygmund *representation* `p = Σ RᵢRⱼ(uᵢuⱼ)` itself — the
solution of the pressure Poisson equation `-Δp = Σᵢⱼ ∂ᵢ∂ⱼ(uᵢuⱼ)` — is a
hypothesis here, not a conclusion.  What is certified is that once the
representation holds, the `L²` bound follows as the sum over the nine terms,
each of operator norm one.

Satisfiability (checked, both poles): `hR` is realisable for every `w` by
`exists_doubleRieszTransform`, and `hP` then defines `P`; so the hypothesis
bundle is inhabited and the conclusion is not vacuously true.  It is also not
vacuous in the other direction — the conclusion constrains `‖P‖`. -/
theorem pressure_l2_bound_of_doubleRiesz_representation
    (w R : Fin 3 → Fin 3 → Lp (α := FourierSpace) ℂ 2)
    (P : Lp (α := FourierSpace) ℂ 2)
    (hR : ∀ i j : Fin 3, ∀ᵐ ξ : FourierSpace,
      (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ (R i j)) ξ
        = doubleRieszMultiplier i j ξ •
          (MeasureTheory.Lp.fourierTransformₗᵢ FourierSpace ℂ (w i j)) ξ)
    (hP : P = ∑ i : Fin 3, ∑ j : Fin 3, R i j) :
    ‖P‖ ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖w i j‖ := by
  rw [hP]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
  exact doubleRiesz_l2_bound i j (w i j) (R i j) (hR i j)

end Riesz

/-- The Calderón–Zygmund theorem is the genuinely Mathlib-absent deep input.
Named as a residual so the assembly chain can cite the open leaf precisely. -/
inductive CalderonZygmundResidual where
  | czWeakTypeBound
  | czBMOBound
  deriving DecidableEq, Repr

end Navier.Analysis.SingularIntegralPrelims
