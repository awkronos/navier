import Mathlib

/-!
# Riesz–Fréchet–Kolmogorov: the two engines of the dyadic-average route

Mathlib has Arzelà–Ascoli for `C(K)` and Banach–Alaoglu for weak-* compactness,
but **no** Riesz–Fréchet–Kolmogorov compactness criterion for `L^p`.  It has to be
built, and this module is the general-functional-analysis part of that build:
nothing here mentions Navier–Stokes, so it is reusable anywhere.

## The route

`Navier.Analysis.LerayWeak.exists_subseq_windowCauchy` is the designated consumer.
Rather than mollify-and-Arzelà–Ascoli, the argument taken there is the **dyadic-
average projection**: partition the window into cells of side `h`, let `E_h f` be
the cell-wise average of `f`, and combine

* **Jensen / Cauchy–Schwarz**, which makes `E_h f` close to `f` uniformly over a
  translation-equicontinuous family, via the pointwise oscillation bound
  `‖(⨍_Q f) − f x‖² ≤ ⨍_Q ‖f y − f x‖²` summed over cells into
  `‖E_h f − f‖²_{L²} ≤ 2^d · sup_{|k|_∞ ≤ h} ‖τ_k f − f‖²_{L²}`; and
* **Bolzano–Weierstrass**, which extracts a subsequence along which `E_h f`
  converges — legitimate precisely because `E_h f` lives in the *finite-
  dimensional* span of the finitely many cell indicators, so no compactness in
  an infinite-dimensional space is ever invoked.

Together these give total boundedness of the family, hence an `L²`-Cauchy
subsequence.  This module establishes both engines: `norm_setAverage_sub_sq_le`
with its oscillation form, and `exists_subseq_cauchy_of_bounded_pi`.  The
remaining middle step — converting the cell-oscillation sum into the translation
modulus by Fubini and translation-invariance of Haar measure — is what the
consumer still names as its residual.

## Step-0 record

`experiments/riesz_kolmogorov_dyadic_core.py` checks the route numerically, before
any of it was written.  The Jensen inequality holds with `max(lhs − rhs) = 0` over
20000 random vector-valued trials.  The cell bound holds with worst observed
ratios `0.45` and `0.29` against the bound `2¹` in `d = 1`, and `0.31` and `0.16`
against `2²` in `d = 2`, so the constant `2^d` is safe rather than tight.  The
end-to-end separation is the intended one: an equicontinuous family has modulus
`9e-2 → 2e-5` as `h → 0` and minimum pairwise `L²` distance `4.2e-5`, while an
oscillating family has modulus pinned at `5.6e-1` and pairwise distance bounded
below by `1.7e-1`, hence no Cauchy subsequence.  That second family is the same
phenomenon as the curl-free witness that falsified the original Aubin–Lions
hypothesis list (`experiments/aubin_lions_curlfree_witness.py`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential
  Equations*, Springer 2011, Thm 4.26 (Riesz–Fréchet–Kolmogorov) and Cor 4.27.
* J. Simon, "Compact sets in `L^p(0,T;B)`", *Ann. Mat. Pura Appl.* **146** (1987)
  65–96, Thm 1.
* R. Temam, *Navier–Stokes Equations*, AMS Chelsea 2001, Ch. III §2.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace Navier.Analysis.RieszKolmogorov

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-!
## Engine 1 — the averaging (Jensen) bound
-/

omit [CompleteSpace E] in
/-- The norm of a set-average is at most the set-average of the norm. -/
theorem norm_setAverage_le (f : α → E) (s : Set α) :
    ‖⨍ y in s, f y ∂μ‖ ≤ ⨍ y in s, ‖f y‖ ∂μ := by
  rw [setAverage_eq, setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.mpr measureReal_nonneg)

/-- Cauchy–Schwarz for a set-average: the square of the average is at most the
average of the square.  This is Jensen's inequality for the convex function
`r ↦ r²` against the normalized restriction of `μ` to `s`. -/
theorem sq_setAverage_le {s : Set α} (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤)
    {h : α → ℝ} (hi : IntegrableOn h s μ) (hi2 : IntegrableOn (fun y => h y ^ 2) s μ) :
    (⨍ y in s, h y ∂μ) ^ 2 ≤ ⨍ y in s, h y ^ 2 ∂μ :=
  ConvexOn.map_set_average_le (g := fun r : ℝ => r ^ 2)
    (Even.convexOn_pow (by decide)) (by fun_prop) isClosed_univ h0 hs
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hi hi2

/-- **Engine 1.**  The set-average of `f` over `s` is closer to any point `c` than
the average of the distances to `c`, in the mean-square sense:
`‖(⨍_s f) − c‖² ≤ ⨍_s ‖f y − c‖²`.

Numerically checked to be sharp-or-equal before formalization: over 20000 random
vector-valued trials the maximum of `lhs − rhs` is exactly `0`, attained at the
one-point averages (`experiments/riesz_kolmogorov_dyadic_core.py`, part (J)). -/
theorem norm_setAverage_sub_sq_le {s : Set α} (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤)
    (f : α → E) (c : E) (hfi : IntegrableOn f s μ)
    (hsq : IntegrableOn (fun y => ‖f y - c‖ ^ 2) s μ) :
    ‖(⨍ y in s, f y ∂μ) - c‖ ^ 2 ≤ ⨍ y in s, ‖f y - c‖ ^ 2 ∂μ := by
  have hc : IntegrableOn (fun _ : α => c) s μ := integrableOn_const hs
  have hg : IntegrableOn (fun y => f y - c) s μ := hfi.sub hc
  have h1 : (⨍ y in s, (f y - c) ∂μ) = (⨍ y in s, f y ∂μ) - c := by
    have hstep : (⨍ y in s, (f y - c) ∂μ) = (⨍ y in s, f y ∂μ) - (⨍ _ in s, c ∂μ) := by
      simp only [setAverage_eq, integral_sub hfi hc, smul_sub]
    rw [hstep, setAverage_const h0 hs]
  calc ‖(⨍ y in s, f y ∂μ) - c‖ ^ 2 = ‖⨍ y in s, (f y - c) ∂μ‖ ^ 2 := by rw [h1]
    _ ≤ (⨍ y in s, ‖f y - c‖ ∂μ) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_setAverage_le _ _) 2
    _ ≤ ⨍ y in s, ‖f y - c‖ ^ 2 ∂μ := sq_setAverage_le h0 hs hg.norm hsq

/-- **The cell-oscillation bound.**  Specializing `norm_setAverage_sub_sq_le` at
`c = f x` says: on a cell `s`, the error of replacing `f` by its cell-average is
controlled pointwise by the mean-square oscillation of `f` over that cell.  This
is the pointwise inequality that, summed over the cells of a partition and
converted by Fubini, becomes `‖E_h f − f‖²_{L²} ≤ 2^d sup_{|k|_∞ ≤ h}
‖τ_k f − f‖²_{L²}`. -/
theorem norm_setAverage_sub_apply_sq_le {s : Set α} (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤)
    (f : α → E) (x : α) (hfi : IntegrableOn f s μ)
    (hsq : IntegrableOn (fun y => ‖f y - f x‖ ^ 2) s μ) :
    ‖(⨍ y in s, f y ∂μ) - f x‖ ^ 2 ≤ ⨍ y in s, ‖f y - f x‖ ^ 2 ∂μ :=
  norm_setAverage_sub_sq_le h0 hs f (f x) hfi hsq

/-- **The integrated cell bound.**  Integrating `norm_setAverage_sub_apply_sq_le`
over the cell: replacing `f` by its cell-average costs at most the mean-square
oscillation of `f` on that cell.  Summing this over the cells of a partition of
the window, and converting the right side by Fubini and translation-invariance of
Lebesgue measure, is what produces `‖E_h f − f‖²_{L²} ≤ 2^d sup_{|k|_∞ ≤ h}
‖τ_k f − f‖²_{L²}`.

The integrability side conditions are taken as hypotheses rather than derived:
on the intended cells they are immediate (bounded cell, `f` square-integrable),
and keeping them explicit avoids committing this general lemma to any one
measurability setup. -/
theorem setIntegral_norm_sub_setAverage_sq_le {s : Set α} (hsm : MeasurableSet s)
    (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤) (f : α → E) (hfi : IntegrableOn f s μ)
    (hslice : ∀ x : α, IntegrableOn (fun y => ‖f y - f x‖ ^ 2) s μ)
    (hlhs : IntegrableOn (fun x => ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2) s μ)
    (hrhs : IntegrableOn (fun x => ⨍ y in s, ‖f y - f x‖ ^ 2 ∂μ) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ
      ≤ ∫ x in s, (⨍ y in s, ‖f y - f x‖ ^ 2 ∂μ) ∂μ := by
  refine setIntegral_mono_on hlhs hrhs hsm fun x _ => ?_
  rw [show ‖f x - ⨍ y in s, f y ∂μ‖ = ‖(⨍ y in s, f y ∂μ) - f x‖ from norm_sub_rev _ _]
  exact norm_setAverage_sub_apply_sq_le h0 hs f x hfi (hslice x)

/-- Cauchy–Schwarz on a **unit-measure** set, where the averaging constant
disappears: `‖∫_s f‖² ≤ ∫_s ‖f‖²`.  This is the form the segment estimate below
needs, the segment `[0,1]` having measure one. -/
theorem norm_setIntegral_sq_le_of_measure_one {s : Set α} (h1 : μ s = 1) (f : α → E)
    (hfi : IntegrableOn f s μ) (hsq : IntegrableOn (fun y => ‖f y‖ ^ 2) s μ) :
    ‖∫ y in s, f y ∂μ‖ ^ 2 ≤ ∫ y in s, ‖f y‖ ^ 2 ∂μ := by
  have hr : μ.real s = 1 := by simp [Measure.real, h1]
  have hA : ∀ g : α → E, (⨍ y in s, g y ∂μ) = ∫ y in s, g y ∂μ := by
    intro g; rw [setAverage_eq, hr]; simp
  have hA' : (⨍ y in s, ‖f y‖ ^ 2 ∂μ) = ∫ y in s, ‖f y‖ ^ 2 ∂μ := by
    rw [setAverage_eq, hr]; simp
  have h0 : μ s ≠ 0 := by rw [h1]; exact one_ne_zero
  have ht : μ s ≠ ⊤ := by rw [h1]; exact ENNReal.one_ne_top
  have hmain := norm_setAverage_sub_sq_le h0 ht f 0 hfi (by simpa using hsq)
  simpa [hA, hA', sub_zero] using hmain

/-!
## The translation modulus from a derivative bound (Brezis Prop. 9.3, pointwise)

`‖τ_y f − f‖_{L²} ≤ ‖y‖ · ‖∇f‖_{L²}` is how a family with a uniform `H¹` bound is
shown to satisfy the spatial-translation equicontinuity that
Riesz–Fréchet–Kolmogorov requires — and it is also how the Galerkin approximants
discharge `SpaceEquicontinuous`.  Its pointwise half is established here.

The route deliberately avoids Minkowski's integral inequality (absent from
Mathlib in the needed form): apply Cauchy–Schwarz on the unit segment *first*,
so only `norm_setIntegral_sq_le_of_measure_one` above and the fundamental theorem
of calculus are needed.  What remains for the `L²` statement is integrating in
`x` and using Fubini plus translation-invariance of Lebesgue measure.
-/

/-- **Segment estimate.**  Along the segment from `x` to `x + y`, the squared
increment of `f` is at most the mean-square of the directional derivative:
`‖f(x+y) − f(x)‖² ≤ ∫₀¹ ‖Df(x+sy)·y‖² ds`.  Fundamental theorem of calculus for
`s ↦ f(x + s·y)`, then Cauchy–Schwarz on the unit-measure segment. -/
theorem norm_sub_sq_le_segment {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : G → F) (hf : Differentiable ℝ f) (x y : G)
    (hi : IntervalIntegrable (fun s : ℝ => fderiv ℝ f (x + s • y) y) volume 0 1)
    (hsq : IntervalIntegrable (fun s : ℝ => ‖fderiv ℝ f (x + s • y) y‖ ^ 2) volume 0 1) :
    ‖f (x + y) - f x‖ ^ 2 ≤ ∫ s in (0:ℝ)..1, ‖fderiv ℝ f (x + s • y) y‖ ^ 2 := by
  have hd : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => f (x + r • y)) (fderiv ℝ f (x + s • y) y) s := by
    intro s _
    have hline : HasDerivAt (fun r : ℝ => x + r • y) y s := by
      simpa using ((hasDerivAt_id s).smul_const y).const_add x
    exact (hf (x + s • y)).hasFDerivAt.comp_hasDerivAt s hline
  have hftc : (∫ s in (0:ℝ)..1, fderiv ℝ f (x + s • y) y) = f (x + y) - f x := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  exact norm_setIntegral_sq_le_of_measure_one (by simp) _
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hsq)

/-- **Brezis Prop. 9.3, pointwise form.**  Replacing the directional derivative by
the operator norm: `‖f(x+y) − f(x)‖² ≤ ‖y‖² ∫₀¹ ‖Df(x+sy)‖² ds`.  Integrating this
in `x` and using translation-invariance gives
`‖τ_y f − f‖_{L²} ≤ ‖y‖ · ‖∇f‖_{L²}`. -/
theorem norm_sub_sq_le_segment_opNorm {G F : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : G → F) (hf : Differentiable ℝ f) (x y : G)
    (hi : IntervalIntegrable (fun s : ℝ => fderiv ℝ f (x + s • y) y) volume 0 1)
    (hsq : IntervalIntegrable (fun s : ℝ => ‖fderiv ℝ f (x + s • y) y‖ ^ 2) volume 0 1)
    (hop : IntervalIntegrable (fun s : ℝ => ‖fderiv ℝ f (x + s • y)‖ ^ 2) volume 0 1) :
    ‖f (x + y) - f x‖ ^ 2 ≤ ‖y‖ ^ 2 * ∫ s in (0:ℝ)..1, ‖fderiv ℝ f (x + s • y)‖ ^ 2 := by
  refine le_trans (norm_sub_sq_le_segment f hf x y hi hsq) ?_
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one hsq (hop.const_mul _) fun s _ => ?_
  have hle : ‖fderiv ℝ f (x + s • y) y‖ ≤ ‖fderiv ℝ f (x + s • y)‖ * ‖y‖ :=
    (fderiv ℝ f (x + s • y)).le_opNorm y
  nlinarith [norm_nonneg (fderiv ℝ f (x + s • y) y), norm_nonneg y,
    norm_nonneg (fderiv ℝ f (x + s • y))]

/-!
## Translation-invariance: a cell integral becomes a displacement integral

The middle step of the dyadic route converts the cell-oscillation sum into the
translation modulus.  Its per-cell half is the change of variables `y = x + k`:
because Haar measure is translation-invariant, integrating over the cell `A` at
base point `x` is the same as integrating over the displacement set `A − x`.  The
*partition* is not translation-covariant — a translate of a cell straddles its
neighbours — which is exactly why the resulting bound is stated against the full
displacement ball rather than against a single cell, and where the `2^d` overshoot
comes from.  `experiments/riesz_kolmogorov_dyadic_core.py` part (C) measured that
overshoot as safe rather than tight (worst ratios `0.45 / 0.29` against `2¹`,
`0.31 / 0.16` against `2²`), so the simple bookkeeping below is taken in
preference to the sharp one.
-/

/-- **Cell integral ≤ displacement-ball integral.**  If every point of `A` is
within `h` of the base point `x`, then a nonnegative integrand's integral over the
cell is at most its integral over the ball of displacements of radius `h`, after
the change of variables `y = x + k`.

Translation-invariance enters exactly once, as `integral_add_left_eq_self`; the
rest is the pointwise indicator comparison, which is where the non-covariance of
the partition is absorbed. -/
theorem setIntegral_le_translate_ball {G : Type*} [MeasurableSpace G]
    [NormedAddCommGroup G] [MeasurableAdd G] [OpensMeasurableSpace G]
    {ν : Measure G} [ν.IsAddLeftInvariant]
    (A : Set G) (hA : MeasurableSet A) (h : ℝ) (x : G)
    (hAx : ∀ y ∈ A, ‖y - x‖ ≤ h)
    (g : G → ℝ) (hg : ∀ z, 0 ≤ g z)
    (hiA : Integrable (Set.indicator A g) ν)
    (hiB : Integrable (Set.indicator (Metric.closedBall (0:G) h) fun k => g (x + k)) ν) :
    ∫ y in A, g y ∂ν ≤ ∫ k in Metric.closedBall (0:G) h, g (x + k) ∂ν := by
  have hiA' : Integrable (fun k => Set.indicator A g (x + k)) ν := hiA.comp_add_left x
  calc ∫ y in A, g y ∂ν
      = ∫ y, Set.indicator A g y ∂ν := (integral_indicator hA).symm
    _ = ∫ k, Set.indicator A g (x + k) ∂ν := (integral_add_left_eq_self _ x).symm
    _ ≤ ∫ k, Set.indicator (Metric.closedBall (0:G) h) (fun k => g (x + k)) k ∂ν := by
        refine integral_mono hiA' hiB fun k => ?_
        by_cases hk : x + k ∈ A
        · have hmem : k ∈ Metric.closedBall (0:G) h := by
            have hb := hAx (x + k) hk
            simpa [Metric.mem_closedBall, dist_zero_right, add_sub_cancel_left] using hb
          simp [Set.indicator_of_mem hk, Set.indicator_of_mem hmem]
        · simp only [Set.indicator_of_notMem hk]
          exact Set.indicator_nonneg (fun z _ => hg _) k
    _ = ∫ k in Metric.closedBall (0:G) h, g (x + k) ∂ν :=
        integral_indicator measurableSet_closedBall

/-- **The per-cell oscillation bound against the translation modulus.**  Combining
the previous lemma with the cell-average bound: on a cell of radius `h` about `x`,
the mean-square oscillation of `f` is controlled by the displacement integral of
`‖f(x+k) − f(x)‖²` over the ball `‖k‖ ≤ h`.  Summing this over the cells of a
partition and bounding each displacement integral by `‖τ_k f − f‖²_{L²}` is the
remaining step of the criterion. -/
theorem setIntegral_oscillation_le_translate_ball {G : Type*} [MeasurableSpace G]
    [NormedAddCommGroup G] [MeasurableAdd G] [OpensMeasurableSpace G]
    {ν : Measure G} [ν.IsAddLeftInvariant]
    {F : Type*} [NormedAddCommGroup F]
    (A : Set G) (hA : MeasurableSet A) (h : ℝ) (x : G)
    (hAx : ∀ y ∈ A, ‖y - x‖ ≤ h) (f : G → F)
    (hiA : Integrable (Set.indicator A fun y => ‖f y - f x‖ ^ 2) ν)
    (hiB : Integrable
      (Set.indicator (Metric.closedBall (0:G) h) fun k => ‖f (x + k) - f x‖ ^ 2) ν) :
    ∫ y in A, ‖f y - f x‖ ^ 2 ∂ν
      ≤ ∫ k in Metric.closedBall (0:G) h, ‖f (x + k) - f x‖ ^ 2 ∂ν :=
  setIntegral_le_translate_ball A hA h x hAx _ (fun _ => by positivity) hiA hiB

/-- **Brezis Prop. 9.3, `L²` form.**  `‖τ_y f − f‖²_{L²} ≤ ‖y‖² · ‖∇f‖²_{L²}`.

This is the half of the translation modulus that turns a uniform `H¹` bound into
the spatial-translation equicontinuity that Riesz–Fréchet–Kolmogorov requires, and
it is what lets the Galerkin approximants discharge `SpaceEquicontinuous`.

Integrating the pointwise segment estimate in `x` and exchanging the order,
translation-invariance makes every slice `∫ ‖Df(x + s·y)‖² dx` equal to
`∫ ‖Df(x)‖² dx`, so the `s`-integral over the unit segment contributes exactly
`1`.  Integrability is taken as hypotheses rather than derived: on the intended
inputs (compactly supported smooth modes) each is immediate, and keeping them
explicit avoids committing a general lemma to one decay class. -/
theorem integral_norm_sub_sq_le_mul_integral_fderiv_sq {G F : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [MeasurableAdd G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ν : Measure G} [SFinite ν] [ν.IsAddRightInvariant]
    (f : G → F) (hf : Differentiable ℝ f) (y : G)
    (hi : ∀ x : G, IntervalIntegrable (fun s : ℝ => fderiv ℝ f (x + s • y) y) volume 0 1)
    (hsq : ∀ x : G, IntervalIntegrable (fun s : ℝ => ‖fderiv ℝ f (x + s • y) y‖ ^ 2) volume 0 1)
    (hop : ∀ x : G, IntervalIntegrable (fun s : ℝ => ‖fderiv ℝ f (x + s • y)‖ ^ 2) volume 0 1)
    (hlhs : Integrable (fun x => ‖f (x + y) - f x‖ ^ 2) ν)
    (hmid : Integrable (fun x => ∫ s in Set.Ioc (0:ℝ) 1, ‖fderiv ℝ f (x + s • y)‖ ^ 2) ν)
    (hprod : Integrable
      (Function.uncurry fun (x : G) (s : ℝ) => ‖fderiv ℝ f (x + s • y)‖ ^ 2)
      (ν.prod (volume.restrict (Set.Ioc (0:ℝ) 1)))) :
    ∫ x, ‖f (x + y) - f x‖ ^ 2 ∂ν ≤ ‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν := by
  have hpt : ∀ x : G, ‖f (x + y) - f x‖ ^ 2
      ≤ ‖y‖ ^ 2 * ∫ s in Set.Ioc (0:ℝ) 1, ‖fderiv ℝ f (x + s • y)‖ ^ 2 := by
    intro x
    have hseg := norm_sub_sq_le_segment_opNorm f hf x y (hi x) (hsq x) (hop x)
    rwa [intervalIntegral.integral_of_le zero_le_one] at hseg
  calc ∫ x, ‖f (x + y) - f x‖ ^ 2 ∂ν
      ≤ ∫ x, ‖y‖ ^ 2 * (∫ s in Set.Ioc (0:ℝ) 1, ‖fderiv ℝ f (x + s • y)‖ ^ 2) ∂ν :=
        integral_mono hlhs (hmid.const_mul _) hpt
    _ = ‖y‖ ^ 2 * ∫ x, (∫ s in Set.Ioc (0:ℝ) 1, ‖fderiv ℝ f (x + s • y)‖ ^ 2) ∂ν :=
        MeasureTheory.integral_const_mul _ _
    _ = ‖y‖ ^ 2 * ∫ s in Set.Ioc (0:ℝ) 1, (∫ x, ‖fderiv ℝ f (x + s • y)‖ ^ 2 ∂ν) := by
        rw [integral_integral_swap hprod]
    _ = ‖y‖ ^ 2 * ∫ _s in Set.Ioc (0:ℝ) 1, (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
        exact integral_add_right_eq_self (fun x => ‖fderiv ℝ f x‖ ^ 2) (s • y)
    _ = ‖y‖ ^ 2 * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂ν := by
        rw [setIntegral_const]; simp

/-!
## Aggregation over the partition

Two purely measure-theoretic steps, with no group structure and no analysis left
in them.  `sum_setIntegral_le_integral_of_disjoint` is where the disjointness of
the cells is spent: the cell integrals of a nonnegative integrand add up to an
integral over their union, hence are dominated by the integral over the whole
space — which for the displacement integrand is `‖τ_k f − f‖²_{L²}`.
`setIntegral_le_measureReal_mul_const` is the last line of the criterion,
integrating the displacement variable `k` over the ball to turn a supremum into
the factor `ν(B_h) = (2h)^d`, which against the cell measure `h^d` is the `2^d`.
-/

/-- **Tonelli swap, in set-integral form.**  Exchanging the cell variable `x` with
the displacement variable `k`.  A thin wrapper on `integral_integral_swap`, stated
with set integrals so the consumer never has to juggle restricted product
measures: `(μ.restrict A).prod (ν.restrict B)` is exactly the measure the
integrability hypothesis needs. -/
theorem setIntegral_setIntegral_swap {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SFinite μ] [SFinite ν] (A : Set α) (B : Set β) (F : α → β → ℝ)
    (hint : Integrable (Function.uncurry F) ((μ.restrict A).prod (ν.restrict B))) :
    ∫ x in A, (∫ k in B, F x k ∂ν) ∂μ = ∫ k in B, (∫ x in A, F x k ∂μ) ∂ν :=
  integral_integral_swap hint

/-- **Disjointness step.**  Cell integrals of a nonnegative integrand sum to at
most the integral over the whole space. -/
theorem sum_setIntegral_le_integral_of_disjoint {N : ℕ} (A : Fin N → Set α)
    (hm : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A))
    (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) (hint : Integrable F μ) :
    ∑ i, ∫ x in A i, F x ∂μ ≤ ∫ x, F x ∂μ := by
  have hUnion : ∫ x in ⋃ i, A i, F x ∂μ = ∑' i, ∫ x in A i, F x ∂μ :=
    integral_iUnion hm hd hint.integrableOn
  calc ∑ i, ∫ x in A i, F x ∂μ = ∑' i, ∫ x in A i, F x ∂μ := (tsum_fintype _).symm
    _ = ∫ x in ⋃ i, A i, F x ∂μ := hUnion.symm
    _ ≤ ∫ x, F x ∂μ :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall hF)

/-- **Last line of the criterion.**  A bound `M` on a finite-measure set turns its
integral into `ν(S)·M`; applied to `k ↦ ‖τ_k f − f‖²_{L²}` over the displacement
ball this is what converts the integral in `k` into a supremum. -/
theorem setIntegral_le_measureReal_mul_const {S : Set α} (hS : MeasurableSet S)
    (hSfin : μ S ≠ ⊤) (g : α → ℝ) (M : ℝ) (hb : ∀ k ∈ S, g k ≤ M)
    (hint : IntegrableOn g S μ) :
    ∫ k in S, g k ∂μ ≤ μ.real S * M := by
  have hmono := setIntegral_mono_on hint (integrableOn_const hSfin) hS hb
  simpa [setIntegral_const, smul_eq_mul] using hmono

/-- **Per-cell assembly.**  Chaining the three landed steps — the cell-average
bound, the per-base-point translation to the displacement ball, and Tonelli — the
error of replacing `f` by its average on a cell of radius `h` is controlled by the
displacement integral over the ball `‖k‖ ≤ h`:

`∫_A ‖f − ⨍_A f‖² ≤ ν(A)⁻¹ ∫_{‖k‖≤h} ∫_A ‖f(x+k) − f(x)‖² dx dk`.

Summing this over a disjoint partition, the inner integral becomes
`‖τ_k f − f‖²_{L²}` (`sum_setIntegral_le_integral_of_disjoint`) and the outer one
becomes `ν(B_h)·sup` (`setIntegral_le_measureReal_mul_const`); against `ν(A) = h^d`
that is the `2^d`. -/
theorem setIntegral_cellError_le_displacement {G : Type*} [MeasurableSpace G]
    [NormedAddCommGroup G] [MeasurableAdd G] [OpensMeasurableSpace G]
    {ν : Measure G} [ν.IsAddLeftInvariant] [SFinite ν]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : Set G) (hA : MeasurableSet A) (h : ℝ) (f : G → F)
    (h0 : ν A ≠ 0) (hfin : ν A ≠ ⊤)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ ≤ h)
    (hfi : IntegrableOn f A ν)
    (hslice : ∀ x : G, IntegrableOn (fun y => ‖f y - f x‖ ^ 2) A ν)
    (hlhs : IntegrableOn (fun x => ‖f x - ⨍ y in A, f y ∂ν‖ ^ 2) A ν)
    (hrhs : IntegrableOn (fun x => ⨍ y in A, ‖f y - f x‖ ^ 2 ∂ν) A ν)
    (hiA : ∀ x : G, Integrable (Set.indicator A fun y => ‖f y - f x‖ ^ 2) ν)
    (hiB : ∀ x : G, Integrable
      (Set.indicator (Metric.closedBall (0:G) h) fun k => ‖f (x + k) - f x‖ ^ 2) ν)
    (hball : IntegrableOn
      (fun x => ∫ k in Metric.closedBall (0:G) h, ‖f (x + k) - f x‖ ^ 2 ∂ν) A ν)
    (hprod : Integrable (Function.uncurry fun (x k : G) => ‖f (x + k) - f x‖ ^ 2)
      ((ν.restrict A).prod (ν.restrict (Metric.closedBall (0:G) h)))) :
    ∫ x in A, ‖f x - ⨍ y in A, f y ∂ν‖ ^ 2 ∂ν
      ≤ (ν.real A)⁻¹ * ∫ k in Metric.closedBall (0:G) h,
          (∫ x in A, ‖f (x + k) - f x‖ ^ 2 ∂ν) ∂ν := by
  have hstep1 := setIntegral_norm_sub_setAverage_sq_le hA h0 hfin f hfi hslice hlhs hrhs
  have hstep2 : ∫ x in A, (⨍ y in A, ‖f y - f x‖ ^ 2 ∂ν) ∂ν
      ≤ (ν.real A)⁻¹ * ∫ x in A,
          (∫ k in Metric.closedBall (0:G) h, ‖f (x + k) - f x‖ ^ 2 ∂ν) ∂ν := by
    have hpull : ∀ x : G, (⨍ y in A, ‖f y - f x‖ ^ 2 ∂ν)
        = (ν.real A)⁻¹ * ∫ y in A, ‖f y - f x‖ ^ 2 ∂ν := by
      intro x; rw [setAverage_eq, smul_eq_mul]
    have hmono : ∫ x in A, (⨍ y in A, ‖f y - f x‖ ^ 2 ∂ν) ∂ν
        ≤ ∫ x in A, (ν.real A)⁻¹ *
            (∫ k in Metric.closedBall (0:G) h, ‖f (x + k) - f x‖ ^ 2 ∂ν) ∂ν := by
      refine setIntegral_mono_on hrhs (hball.const_mul _) hA fun x hx => ?_
      rw [hpull x]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr measureReal_nonneg)
      exact setIntegral_oscillation_le_translate_ball A hA h x
        (fun y hy => hdiam x hx y hy) f (hiA x) (hiB x)
    rwa [MeasureTheory.integral_const_mul] at hmono
  refine le_trans hstep1 (le_trans hstep2 ?_)
  rw [setIntegral_setIntegral_swap A (Metric.closedBall (0:G) h) _ hprod]

/-!
## The cell grid

The cells the criterion is summed over: half-open axis-parallel cubes of side `h`
indexed by an integer multi-index, on a finite-dimensional coordinate space
`ι → ℝ`.  Half-open (`Ico`) is what makes the grid an exact partition — closed
cubes would overlap on faces and open ones would miss them.

**Mathlib query, recorded either way.**  `MeasureTheory/Covering/` (Vitali,
Besicovitch, VitaliFamily) does not serve here: `Vitali.exists_disjoint_covering_ae`
produces an a.e.-cover by balls drawn from a family satisfying a Vitali condition,
with no control on the cells' common measure, whereas the criterion needs cells of
*known equal* measure `h^d` and diameter `≤ h` so that `ν(B_h)/ν(A) = 2^d`.
`ZSpan.exist_unique_vadd_mem_fundamentalDomain` does give a genuine lattice tiling
and would work, at the cost of carrying a basis and its `ZSpan.repr` coordinates
through every estimate.  For an axis-parallel grid the direct construction below is
shorter and its measure is `volume_pi_pi` in one line, so it is hand-rolled.

Per the standing advice, no attempt is made to tile the window exactly: cells are
indexed over all of `ι → ℤ` and intersected with the window where needed.  Boundary
cells then stick out, which is harmless — the criterion needs only disjointness and
covering, and the `2^d` slack absorbs partial cells.
-/

section GridCell

variable {ι : Type*} [Fintype ι]

/-- The half-open grid cell of side `h` at integer multi-index `j`. -/
def gridCell (h : ℝ) (j : ι → ℤ) : Set (ι → ℝ) :=
  Set.univ.pi fun i => Set.Ico (h * j i) (h * (j i + 1))

theorem measurableSet_gridCell (h : ℝ) (j : ι → ℤ) : MeasurableSet (gridCell h j) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

/-- Every grid cell has measure `h^{|ι|}`. -/
theorem volume_gridCell {h : ℝ} (hh : 0 ≤ h) (j : ι → ℤ) :
    volume (gridCell h j) = ENNReal.ofReal (h ^ Fintype.card ι) := by
  rw [gridCell, volume_pi_pi]
  have hEach : ∀ i : ι, volume (Set.Ico (h * j i) (h * (j i + 1))) = ENNReal.ofReal h := by
    intro i; rw [Real.volume_Ico]; ring_nf
  simp only [hEach, Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.ofReal_pow hh]

omit [Fintype ι] in
/-- Distinct multi-indices give disjoint cells. -/
theorem gridCell_disjoint {h : ℝ} (hh : 0 < h) {j j' : ι → ℤ} (hne : j ≠ j') :
    Disjoint (gridCell h j) (gridCell h j') := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have h1 := hx i (Set.mem_univ i)
  have h2 := hx' i (Set.mem_univ i)
  simp only [Set.mem_Ico] at h1 h2
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have : (j i : ℝ) + 1 ≤ (j' i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    nlinarith [h1.2, h2.1]
  · have : (j' i : ℝ) + 1 ≤ (j i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
    nlinarith [h2.2, h1.1]

/-- A grid cell has diameter at most `h` in the supremum norm of `ι → ℝ`. -/
theorem norm_sub_le_of_mem_gridCell {h : ℝ} (hh : 0 ≤ h) {j : ι → ℤ} {x y : ι → ℝ}
    (hx : x ∈ gridCell h j) (hy : y ∈ gridCell h j) : ‖x - y‖ ≤ h := by
  refine (pi_norm_le_iff_of_nonneg hh).mpr fun i => ?_
  have h1 := hx i (Set.mem_univ i)
  have h2 := hy i (Set.mem_univ i)
  simp only [Set.mem_Ico] at h1 h2
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> [nlinarith [h1.1, h2.2]; nlinarith [h1.2, h2.1]]

omit [Fintype ι] in
/-- **The grid covers**: every point lies in the cell of its coordinatewise floor. -/
theorem mem_gridCell_floor {h : ℝ} (hh : 0 < h) (x : ι → ℝ) :
    x ∈ gridCell h fun i => ⌊x i / h⌋ := by
  intro i _
  have hfl := Int.floor_le (x i / h)
  have hlt := Int.lt_floor_add_one (x i / h)
  constructor
  · rw [← le_div_iff₀' hh]; exact hfl
  · rw [← div_lt_iff₀' hh]; exact hlt

end GridCell

/-!
## Engine 2 — Bolzano–Weierstrass in the finite-dimensional cell space
-/

/-- **Engine 2.**  A norm-bounded sequence in `Fin N → ℝ` has a Cauchy
subsequence.  This is the step that makes the dyadic-average route elementary:
the cell-average vector of a member of the family is a point of `Fin N → ℝ` with
`N` the number of cells meeting the window, so no infinite-dimensional
compactness is ever needed — only Heine–Borel in a proper space.

Stated in the "extract from any sequence" shape the diagonal argument consumes:
apply it to `fun k => v (τ k)` to refine a given subsequence `τ`. -/
theorem exists_subseq_cauchy_of_bounded_pi {N : ℕ} (v : ℕ → Fin N → ℝ) (M : ℝ)
    (hb : ∀ k : ℕ, ‖v k‖ ≤ M) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ j k : ℕ, K ≤ j → K ≤ k →
        ‖v (ρ j) - v (ρ k)‖ < ε := by
  obtain ⟨b, -, ρ, hρ, hconv⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : Fin N → ℝ)) (r := M))
      (fun k => by simpa [Metric.mem_closedBall, dist_zero_right] using hb k)
  refine ⟨ρ, hρ, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq ε hε
  exact ⟨K, fun j k hj hk => by simpa [dist_eq_norm] using hK j hj k hk⟩

end Navier.Analysis.RieszKolmogorov








