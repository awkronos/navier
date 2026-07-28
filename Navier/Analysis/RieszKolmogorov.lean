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
    (hslice : ∀ x ∈ s, IntegrableOn (fun y => ‖f y - f x‖ ^ 2) s μ)
    (hlhs : IntegrableOn (fun x => ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2) s μ)
    (hrhs : IntegrableOn (fun x => ⨍ y in s, ‖f y - f x‖ ^ 2 ∂μ) s μ) :
    ∫ x in s, ‖f x - ⨍ y in s, f y ∂μ‖ ^ 2 ∂μ
      ≤ ∫ x in s, (⨍ y in s, ‖f y - f x‖ ^ 2 ∂μ) ∂μ := by
  refine setIntegral_mono_on hlhs hrhs hsm fun x hx => ?_
  rw [show ‖f x - ⨍ y in s, f y ∂μ‖ = ‖(⨍ y in s, f y ∂μ) - f x‖ from norm_sub_rev _ _]
  exact norm_setAverage_sub_apply_sq_le h0 hs f x hfi (hslice x hx)

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

/-!
### Translate domination

Obligations (6)–(8) of the cell data involve `f(x + k)` for `x` in the cell and
`‖k‖ ≤ h`, so local `L²` on the cell is not enough — they need `L²` on an **enlarged**
window `W ⊇ A + B_h`.  These two lemmas are the transfer.  `hAB` is load-bearing in
exactly one place: it is what makes the indicator of `W`, evaluated at the *translated*
point, majorize the translate on `B`.  The inclusion does not transfer under the
translation by itself.
-/

/-- If `x + B ⊆ W`, then `L¹` on `W` transfers to the translate on `B`. -/
theorem integrableOn_translate_of_mapsTo {G : Type*} [MeasurableSpace G]
    [NormedAddCommGroup G] [MeasurableAdd G] {ν : Measure G} [ν.IsAddLeftInvariant]
    (B W : Set G) (hB : MeasurableSet B) (hW : MeasurableSet W) (x : G)
    (hAB : ∀ k ∈ B, x + k ∈ W) (g : G → ℝ) (hg : ∀ z, 0 ≤ g z)
    (hmeas : AEStronglyMeasurable (fun k => g (x + k)) ν) (hiW : IntegrableOn g W ν) :
    IntegrableOn (fun k => g (x + k)) B ν := by
  have hmaj : Integrable (fun k => Set.indicator W g (x + k)) ν :=
    ((integrable_indicator_iff hW).mpr hiW).comp_add_left x
  refine (integrable_indicator_iff hB).mp ?_
  refine Integrable.mono' hmaj (hmeas.indicator hB) (Filter.Eventually.of_forall fun k => ?_)
  by_cases hk : k ∈ B
  · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (hAB k hk), Real.norm_eq_abs,
      abs_of_nonneg (hg _)]
  · rw [Set.indicator_of_notMem hk, norm_zero]
    exact Set.indicator_nonneg (fun z _ => hg z) (x + k)

/-- If `x + B ⊆ W`, the translated integral over `B` is dominated by the integral over
`W`.  Translation-invariance enters once, as `integral_add_left_eq_self`. -/
theorem setIntegral_translate_le_setIntegral {G : Type*} [MeasurableSpace G]
    [NormedAddCommGroup G] [MeasurableAdd G] {ν : Measure G} [ν.IsAddLeftInvariant]
    (B W : Set G) (hB : MeasurableSet B) (hW : MeasurableSet W) (x : G)
    (hAB : ∀ k ∈ B, x + k ∈ W) (g : G → ℝ) (hg : ∀ z, 0 ≤ g z)
    (hmeas : AEStronglyMeasurable (fun k => g (x + k)) ν) (hiW : IntegrableOn g W ν) :
    ∫ k in B, g (x + k) ∂ν ≤ ∫ z in W, g z ∂ν := by
  have hmaj : Integrable (fun k => Set.indicator W g (x + k)) ν :=
    ((integrable_indicator_iff hW).mpr hiW).comp_add_left x
  have hiB := integrableOn_translate_of_mapsTo B W hB hW x hAB g hg hmeas hiW
  calc ∫ k in B, g (x + k) ∂ν = ∫ k, Set.indicator B (fun k => g (x + k)) k ∂ν :=
        (integral_indicator hB).symm
    _ ≤ ∫ k, Set.indicator W g (x + k) ∂ν := by
        refine integral_mono ((integrable_indicator_iff hB).mpr hiB) hmaj fun k => ?_
        by_cases hk : k ∈ B
        · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (hAB k hk)]
        · rw [Set.indicator_of_notMem hk]
          exact Set.indicator_nonneg (fun z _ => hg z) (x + k)
    _ = ∫ z, Set.indicator W g z ∂ν := integral_add_left_eq_self _ x
    _ = ∫ z in W, g z ∂ν := integral_indicator hW

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

/-- Finset-indexed form of the disjointness step, so a cell family indexed by
multi-indices needs no reindexing through `Fin N`. -/
theorem sum_finset_setIntegral_le_integral_of_disjoint {κ : Type*} (S : Finset κ)
    (A : κ → Set α) (hm : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Function.onFun Disjoint A))
    (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) (hint : Integrable F μ) :
    ∑ i ∈ S, ∫ x in A i, F x ∂μ ≤ ∫ x, F x ∂μ := by
  classical
  have hdS : Pairwise (Function.onFun Disjoint fun i : ↥S => A i) := by
    intro i i' hne
    exact hd (Subtype.coe_injective.ne hne)
  have hUnion : ∫ x in ⋃ i : ↥S, A i, F x ∂μ = ∑' i : ↥S, ∫ x in A i, F x ∂μ :=
    integral_iUnion (fun i => hm i) hdS hint.integrableOn
  calc ∑ i ∈ S, ∫ x in A i, F x ∂μ
      = ∑ i : ↥S, ∫ x in A i, F x ∂μ := (Finset.sum_coe_sort S _).symm
    _ = ∑' i : ↥S, ∫ x in A i, F x ∂μ := (tsum_fintype _).symm
    _ = ∫ x in ⋃ i : ↥S, A i, F x ∂μ := hUnion.symm
    _ ≤ ∫ x, F x ∂μ := setIntegral_le_integral hint (Filter.Eventually.of_forall hF)

/-- **Disjointness step, localized to a bounded window.**  Bounds the cell sum by the
integral over any measurable set containing the cells, rather than over the whole
space.

This weaker form is the one a Navier–Stokes bundle can actually supply.
`sum_finset_setIntegral_le_integral_of_disjoint` requires `Integrable F` over the
*whole* space; a Leray/Galerkin bundle controls its field only on bounded windows
`(0,T] × B̄(0,R)` and says nothing whatsoever for `t < 0`, so that hypothesis is
strictly stronger than any consumer here can discharge.  Since the cells of a finite
family always sit inside a bounded window, nothing is lost. -/
theorem sum_finset_setIntegral_le_setIntegral_of_disjoint {κ : Type*} (S : Finset κ)
    (A : κ → Set α) (W : Set α) (hsub : ∀ i ∈ S, A i ⊆ W)
    (hm : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A))
    (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) (hint : IntegrableOn F W μ) :
    ∑ i ∈ S, ∫ x in A i, F x ∂μ ≤ ∫ x in W, F x ∂μ := by
  classical
  have hUsub : (⋃ i : ↥S, A i) ⊆ W := Set.iUnion_subset fun i => hsub i i.2
  have hdS : Pairwise (Function.onFun Disjoint fun i : ↥S => A i) :=
    fun i i' hne => hd (Subtype.coe_injective.ne hne)
  have hUnion : ∫ x in ⋃ i : ↥S, A i, F x ∂μ = ∑' i : ↥S, ∫ x in A i, F x ∂μ :=
    integral_iUnion (fun i => hm i) hdS (hint.mono_set hUsub)
  calc ∑ i ∈ S, ∫ x in A i, F x ∂μ
      = ∑ i : ↥S, ∫ x in A i, F x ∂μ := (Finset.sum_coe_sort S _).symm
    _ = ∑' i : ↥S, ∫ x in A i, F x ∂μ := (tsum_fintype _).symm
    _ = ∫ x in ⋃ i : ↥S, A i, F x ∂μ := hUnion.symm
    _ ≤ ∫ x in W, F x ∂μ :=
        setIntegral_mono_set hint (Filter.Eventually.of_forall hF)
          (HasSubset.Subset.eventuallyLE hUsub)

/-- **Last line of the criterion.**  A bound `M` on a finite-measure set turns its
integral into `ν(S)·M`; applied to `k ↦ ‖τ_k f − f‖²_{L²}` over the displacement
ball this is what converts the integral in `k` into a supremum. -/
theorem setIntegral_le_measureReal_mul_const {S : Set α} (hS : MeasurableSet S)
    (hSfin : μ S ≠ ⊤) (g : α → ℝ) (M : ℝ) (hb : ∀ k ∈ S, g k ≤ M)
    (hint : IntegrableOn g S μ) :
    ∫ k in S, g k ∂μ ≤ μ.real S * M := by
  have hmono := setIntegral_mono_on hint (integrableOn_const hSfin) hS hb
  simpa [setIntegral_const, smul_eq_mul] using hmono

/-!
### Uniform integrability of the cell data

`setIntegral_cellError_le_displacement` below takes eight integrability hypotheses,
stated per cell.  Instantiating it over a *family* of cells therefore needs them to
hold **uniformly in the cell index**, which is a quantifier order that is painful to
discover halfway through a transport argument.  So the uniform statement is hoisted
here and proved standalone: for a bounded measurable field every one of the eight
follows from the single global bound `‖f‖ ≤ M` plus finiteness of the cell and the
displacement ball, and a global bound is uniform in the cell by construction.
-/

/-- A bounded a.e.-measurable real function is integrable on any finite-measure set. -/
theorem integrableOn_of_bound {s : Set α} (hs : μ s ≠ ⊤) {g : α → ℝ}
    (hmeas : AEStronglyMeasurable g μ) {M : ℝ} (hb : ∀ x, |g x| ≤ M) :
    IntegrableOn g s μ :=
  MeasureTheory.Measure.integrableOn_of_bounded hs hmeas (M := M)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

omit [CompleteSpace E] in
/-- A set-average inherits any global bound on the function.  No measurability
hypothesis: the bound goes through `norm_setIntegral_le_of_norm_le_const`, which
needs only finiteness of the set and an a.e. bound. -/
theorem norm_setAverage_le_of_bound {s : Set α} (h0 : μ s ≠ 0) (hs : μ s ≠ ⊤)
    (f : α → E) {M : ℝ} (hb : ∀ z, ‖f z‖ ≤ M) : ‖⨍ y in s, f y ∂μ‖ ≤ M := by
  have hpos : 0 < μ.real s := ENNReal.toReal_pos h0 hs
  have hnorm : ‖∫ y in s, f y ∂μ‖ ≤ M * μ.real s :=
    norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr hs) fun x _ => hb x
  rw [setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr measureReal_nonneg)]
  calc (μ.real s)⁻¹ * ‖∫ y in s, f y ∂μ‖ ≤ (μ.real s)⁻¹ * (M * μ.real s) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = M := by field_simp

/-!
### From local `L²` to the cell-data integrability

The `_of_bounded` corollary below assumes `‖f‖ ≤ M`, which is the *convenient* bound
and not the one a Leray field has: `UniformKineticBound` is `∫ ‖u(t)‖² ≤ C`, an `L²`
bound, and a Leray field is genuinely not uniformly bounded.  Demanding `L^∞` of it
would be a hypothesis satisfied by none of the intended objects — the
satisfied-by-nothing pole — so the corollary is kept and *supplemented* rather than
edited.

These two atoms are what make the `L²` route mechanical.  Both turn on the cell having
**finite measure**, which is exactly where that hypothesis is load-bearing: it is what
makes a constant integrable on the cell, and every step below is `‖f‖²` plus a
constant.  Neither needs `Memℒp` or Hölder — `2a ≤ 1 + a²` and
`‖a − c‖² ≤ 2‖a‖² + 2‖c‖²` suffice. -/

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- On a **finite-measure** set, square-integrability gives integrability, by the
elementary `2a ≤ 1 + a²`.  Needs only a normed group on the codomain. -/
theorem integrableOn_norm_of_sq {s : Set α} (hs : μ s ≠ ⊤) {f : α → E}
    (hmeas : AEStronglyMeasurable (fun z => ‖f z‖) μ)
    (hsq : IntegrableOn (fun z => ‖f z‖ ^ 2) s μ) :
    IntegrableOn (fun z => ‖f z‖) s μ := by
  refine Integrable.mono' (((integrableOn_const hs (C := (1:ℝ))).add hsq).div_const 2)
    hmeas.restrict (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [Pi.add_apply]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [sq_nonneg (‖f z‖ - 1)]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Square-integrability survives subtracting a constant, on a **finite-measure** set:
`‖f − c‖² ≤ 2‖f‖² + 2‖c‖²`, and the constant term is integrable precisely because the
set is finite. -/
theorem integrableOn_norm_sub_const_sq {s : Set α} (hs : μ s ≠ ⊤) {f : α → E} (c : E)
    (hmeas : AEStronglyMeasurable (fun z => ‖f z - c‖ ^ 2) μ)
    (hsq : IntegrableOn (fun z => ‖f z‖ ^ 2) s μ) :
    IntegrableOn (fun z => ‖f z - c‖ ^ 2) s μ := by
  refine Integrable.mono'
    ((hsq.const_mul 2).add (integrableOn_const hs (C := 2 * ‖c‖ ^ 2)))
    hmeas.restrict (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply]
  nlinarith [norm_nonneg (f z - c), norm_sub_le (f z) c, norm_nonneg (f z), norm_nonneg c,
    sq_nonneg (‖f z‖ - ‖c‖)]

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
    (hslice : ∀ x ∈ A, IntegrableOn (fun y => ‖f y - f x‖ ^ 2) A ν)
    (hlhs : IntegrableOn (fun x => ‖f x - ⨍ y in A, f y ∂ν‖ ^ 2) A ν)
    (hrhs : IntegrableOn (fun x => ⨍ y in A, ‖f y - f x‖ ^ 2 ∂ν) A ν)
    (hiA : ∀ x ∈ A, Integrable (Set.indicator A fun y => ‖f y - f x‖ ^ 2) ν)
    (hiB : ∀ x ∈ A, Integrable
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
        (fun y hy => hdiam x hx y hy) f (hiA x hx) (hiB x hx)
    rwa [MeasureTheory.integral_const_mul] at hmono
  refine le_trans hstep1 (le_trans hstep2 ?_)
  rw [setIntegral_setIntegral_swap A (Metric.closedBall (0:G) h) _ hprod]

/-- **Per-cell bound for a bounded measurable field.**  Same conclusion as
`setIntegral_cellError_le_displacement`, with all eight integrability hypotheses
replaced by one global bound `‖f‖ ≤ M`, measurability, and finiteness of the cell
and the displacement ball.

This is the form a family of cells can be instantiated at: `M` does not depend on
the cell, so the hypotheses are uniform in the cell index by construction, which is
the quantifier order the per-cell version cannot supply. -/
theorem setIntegral_cellError_le_displacement_of_bounded {G : Type*} [MeasurableSpace G]
    [NormedAddCommGroup G] [MeasurableAdd G] [MeasurableAdd₂ G] [OpensMeasurableSpace G]
    {ν : Measure G} [ν.IsAddLeftInvariant] [SFinite ν]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (A : Set G) (hA : MeasurableSet A) (h : ℝ) (f : G → F)
    (hmeas : Measurable f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (h0 : ν A ≠ 0) (hfin : ν A ≠ ⊤) (hBfin : ν (Metric.closedBall (0:G) h) ≠ ⊤)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, ‖y - x‖ ≤ h) :
    ∫ x in A, ‖f x - ⨍ y in A, f y ∂ν‖ ^ 2 ∂ν
      ≤ (ν.real A)⁻¹ * ∫ k in Metric.closedBall (0:G) h,
          (∫ x in A, ‖f (x + k) - f x‖ ^ 2 ∂ν) ∂ν := by
  classical
  set B := Metric.closedBall (0:G) h with hBdef
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  -- the uniform bound on every oscillation integrand
  have hbd : ∀ a b : F, ‖a‖ ≤ M → ‖b‖ ≤ M → ‖a - b‖ ^ 2 ≤ 4 * M ^ 2 := by
    intro a b ha hb
    nlinarith [norm_nonneg (a - b), norm_sub_le a b, norm_nonneg a, norm_nonneg b]
  -- joint measurability of the two oscillation kernels
  have hj1 : Measurable fun z : G × G => ‖f z.2 - f z.1‖ ^ 2 :=
    (((hmeas.comp measurable_snd).sub (hmeas.comp measurable_fst)).norm).pow_const 2
  have hj2 : Measurable fun z : G × G => ‖f (z.1 + z.2) - f z.1‖ ^ 2 :=
    (((hmeas.comp (measurable_fst.add measurable_snd)).sub
      (hmeas.comp measurable_fst)).norm).pow_const 2
  -- (1) `f` itself
  have hfi : IntegrableOn f A ν :=
    MeasureTheory.Measure.integrableOn_of_bounded hfin hmeas.aestronglyMeasurable
      (M := M) (Filter.Eventually.of_forall fun x => hM x)
  -- (2) the oscillation at a fixed base point, on the cell
  have hslice : ∀ x ∈ A, IntegrableOn (fun y => ‖f y - f x‖ ^ 2) A ν := fun x _ =>
    integrableOn_of_bound hfin
      (((hmeas.sub measurable_const).norm.pow_const 2)).aestronglyMeasurable
      (M := 4 * M ^ 2) fun y => by
        rw [abs_of_nonneg (by positivity)]; exact hbd _ _ (hM y) (hM x)
  -- (3) the cell-average error, using that the average inherits the bound
  have havg : ‖⨍ y in A, f y ∂ν‖ ≤ M := norm_setAverage_le_of_bound h0 hfin f hM
  have hlhs : IntegrableOn (fun x => ‖f x - ⨍ y in A, f y ∂ν‖ ^ 2) A ν :=
    integrableOn_of_bound hfin
      (((hmeas.sub measurable_const).norm.pow_const 2)).aestronglyMeasurable
      (M := 4 * M ^ 2) fun x => by
        rw [abs_of_nonneg (by positivity)]; exact hbd _ _ (hM x) havg
  -- (4) the averaged oscillation, measurable by `integral_prod_right'`
  haveI : SFinite (ν.restrict A) := inferInstance
  have hsmA : StronglyMeasurable fun x : G => ∫ y in A, ‖f y - f x‖ ^ 2 ∂ν :=
    hj1.stronglyMeasurable.integral_prod_right' (ν := ν.restrict A)
  have hrhs : IntegrableOn (fun x => ⨍ y in A, ‖f y - f x‖ ^ 2 ∂ν) A ν := by
    refine integrableOn_of_bound hfin ?_ (M := 4 * M ^ 2) fun x => ?_
    · simp only [setAverage_eq, smul_eq_mul]
      exact (hsmA.const_mul _).aestronglyMeasurable
    · have := norm_setAverage_le_of_bound (E := ℝ) h0 hfin
        (fun y => ‖f y - f x‖ ^ 2) (M := 4 * M ^ 2) fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact hbd _ _ (hM y) (hM x)
      simpa [Real.norm_eq_abs] using this
  -- (5)(6) indicator forms
  have hiA : ∀ x ∈ A, Integrable (Set.indicator A fun y => ‖f y - f x‖ ^ 2) ν :=
    fun x hx => (integrable_indicator_iff hA).mpr (hslice x hx)
  have hiB : ∀ x ∈ A, Integrable (Set.indicator B fun k => ‖f (x + k) - f x‖ ^ 2) ν := by
    intro x _
    refine (integrable_indicator_iff measurableSet_closedBall).mpr ?_
    refine integrableOn_of_bound hBfin
      ((((hmeas.comp (measurable_const_add x)).sub measurable_const).norm.pow_const
        2)).aestronglyMeasurable (M := 4 * M ^ 2) fun k => ?_
    rw [abs_of_nonneg (by positivity)]; exact hbd _ _ (hM _) (hM x)
  -- (7) the displacement integral as a function of the base point
  haveI : SFinite (ν.restrict B) := inferInstance
  have hsmB : StronglyMeasurable fun x : G => ∫ k in B, ‖f (x + k) - f x‖ ^ 2 ∂ν :=
    hj2.stronglyMeasurable.integral_prod_right' (ν := ν.restrict B)
  have hballInt : IntegrableOn (fun x => ∫ k in B, ‖f (x + k) - f x‖ ^ 2 ∂ν) A ν := by
    refine integrableOn_of_bound hfin hsmB.aestronglyMeasurable
      (M := (4 * M ^ 2) * ν.real B) fun x => ?_
    have hnn : 0 ≤ ∫ k in B, ‖f (x + k) - f x‖ ^ 2 ∂ν :=
      setIntegral_nonneg measurableSet_closedBall fun k _ => by positivity
    rw [abs_of_nonneg hnn]
    have hb := setIntegral_le_measureReal_mul_const (μ := ν) measurableSet_closedBall hBfin
      (fun k => ‖f (x + k) - f x‖ ^ 2) (4 * M ^ 2)
      (fun k _ => hbd _ _ (hM _) (hM x))
      (integrableOn_of_bound hBfin
        ((((hmeas.comp (measurable_const_add x)).sub measurable_const).norm.pow_const
          2)).aestronglyMeasurable (M := 4 * M ^ 2) fun k => by
            rw [abs_of_nonneg (by positivity)]; exact hbd _ _ (hM _) (hM x))
    linarith [hb, mul_comm (ν.real B) (4 * M ^ 2)]
  -- (8) the product integrand
  haveI : IsFiniteMeasure (ν.restrict A) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  haveI : IsFiniteMeasure (ν.restrict B) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have hprod : Integrable (Function.uncurry fun (x k : G) => ‖f (x + k) - f x‖ ^ 2)
      ((ν.restrict A).prod (ν.restrict B)) := by
    refine Integrable.mono' (integrable_const (4 * M ^ 2))
      (hj2.aestronglyMeasurable) (Filter.Eventually.of_forall fun z => ?_)
    have hz : Function.uncurry (fun (x k : G) => ‖f (x + k) - f x‖ ^ 2) z
        = ‖f (z.1 + z.2) - f z.1‖ ^ 2 := rfl
    rw [hz, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbd _ _ (hM _) (hM _)
  exact setIntegral_cellError_le_displacement A hA h f h0 hfin hdiam hfi hslice hlhs hrhs
    hiA hiB hballInt hprod

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

**Spacetime shape.**  The Navier–Stokes window lives in `ℝ × (Fin 3 → ℝ)`, not in a
pi type, so instantiating this grid there goes through
`MeasurableEquiv.piFinSuccAbove` (`Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:562`),
which at `n = 3`, `i = 0` is `(Fin 4 → ℝ) ≃ᵐ ℝ × (Fin 3 → ℝ)`, together with
`MeasureTheory.volume_preserving_piFinSuccAbove`
(`Mathlib/MeasureTheory/Constructions/Pi.lean:813`) — the measure-preserving
statement, which is the property the estimates need rather than the bijection alone.
`volume_preserving_piEquivPiSubtypeProd` (same file, `:721`) is the coarser split if
one is ever wanted.

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

/-- **Only finitely many cells meet a bounded window.**  If `gridCell h j` meets
`B̄(0,R)` then each coordinate index `j i` lies in a fixed integer interval, so the
index set embeds in a finite product. -/
theorem finite_gridIndices {h : ℝ} (hh : 0 < h) (R : ℝ) :
    {j : ι → ℤ | (gridCell h j ∩ Metric.closedBall (0 : ι → ℝ) R).Nonempty}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.Finite.pi fun _ : ι => Set.finite_Icc ⌈(-R / h) - 1⌉ ⌊R / h⌋) ?_
  rintro j ⟨x, hxj, hxB⟩
  intro i _
  have hxi : |x i| ≤ R := by
    have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    have h2 : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hxB
    simpa [Real.norm_eq_abs] using h1.trans h2
  have hmem := hxj i (Set.mem_univ i)
  simp only [Set.mem_Ico] at hmem
  obtain ⟨hlo, hhi⟩ := abs_le.mp hxi
  refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
  · have hdiv : -R / h < (j i : ℝ) + 1 := by
      rw [div_lt_iff₀ hh]; linarith [hmem.2]
    linarith
  · rw [le_div_iff₀ hh]; linarith [hmem.1]

/-- **The finitely many cells meeting a ball cover it.** -/
theorem closedBall_subset_biUnion_gridCell {h : ℝ} (hh : 0 < h) (R : ℝ) :
    Metric.closedBall (0 : ι → ℝ) R ⊆
      ⋃ j ∈ {j : ι → ℤ | (gridCell h j ∩ Metric.closedBall (0 : ι → ℝ) R).Nonempty},
        gridCell h j := fun x hx =>
  Set.mem_biUnion ⟨x, mem_gridCell_floor hh x, hx⟩ (mem_gridCell_floor hh x)

end GridCell

/-!
### Spacetime cells

The Navier–Stokes window lives in `ℝ × (ι → ℝ)`, not in a pi type.  **Route chosen,
and why.**  `MeasurableEquiv.piFinSuccAbove` with
`MeasureTheory.volume_preserving_piFinSuccAbove` transports `(Fin 4 → ℝ)` to
`ℝ × (Fin 3 → ℝ)` and would carry the *measure* facts across — but the cell
hypothesis `hdiam` is about the **norm**, and Mathlib records no
norm-preservation or isometry statement for that equivalence (searched: the only
`piFinSuccAbove` results are the measurable-equiv definition and the two
measure-preserving lemmas).  Transporting would therefore need an isometry lemma
proved from scratch on top of the equivalence.

Building the product cell directly needs no such lemma, because
`Prod.norm_mk : ‖(x, y)‖ = max ‖x‖ ‖y‖` gives the diameter bound immediately from
the two factor bounds.  So the product is taken directly and the transport is not
used.  Every fact below mirrors its `gridCell` counterpart.
-/

section ProdGridCell

variable {ι : Type*} [Fintype ι]

/-- A spacetime cell: a time interval of length `h` times a spatial grid cell. -/
def prodGridCell (h : ℝ) (m : ℤ) (j : ι → ℤ) : Set (ℝ × (ι → ℝ)) :=
  Set.Ico (h * m) (h * (m + 1)) ×ˢ gridCell h j

theorem measurableSet_prodGridCell (h : ℝ) (m : ℤ) (j : ι → ℤ) :
    MeasurableSet (prodGridCell h m j) :=
  measurableSet_Ico.prod (measurableSet_gridCell h j)

/-- A spacetime cell has measure `h^{|ι|+1}`: the `h⁴` of the criterion when
`|ι| = 3`. -/
theorem volume_prodGridCell {h : ℝ} (hh : 0 ≤ h) (m : ℤ) (j : ι → ℤ) :
    volume (prodGridCell h m j) = ENNReal.ofReal (h ^ (Fintype.card ι + 1)) := by
  rw [prodGridCell, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    volume_gridCell hh j, Real.volume_Ico]
  rw [show h * (m + 1) - h * m = h by ring, ← ENNReal.ofReal_mul hh]
  congr 1
  rw [pow_succ]
  ring

omit [Fintype ι] in
theorem prodGridCell_disjoint {h : ℝ} (hh : 0 < h) {m m' : ℤ} {j j' : ι → ℤ}
    (hne : (m, j) ≠ (m', j')) : Disjoint (prodGridCell h m j) (prodGridCell h m' j') := by
  refine Set.disjoint_left.mpr fun z hz hz' => ?_
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hz1', hz2'⟩ := hz'
  by_cases hm : m = m'
  · subst hm
    have hj : j ≠ j' := fun hj => hne (by rw [hj])
    exact (Set.disjoint_left.mp (gridCell_disjoint hh hj)) hz2 hz2'
  · simp only [Set.mem_Ico] at hz1 hz1'
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · have : (m : ℝ) + 1 ≤ (m' : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
      nlinarith [hz1.2, hz1'.1]
    · have : (m' : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
      nlinarith [hz1'.2, hz1.1]

/-- A spacetime cell has diameter at most `h`.  This is `Prod.norm_mk`: the product
norm is the max of the factor norms, so the two factor bounds combine with no
isometry argument. -/
theorem norm_sub_le_of_mem_prodGridCell {h : ℝ} (hh : 0 ≤ h) {m : ℤ} {j : ι → ℤ}
    {z w : ℝ × (ι → ℝ)} (hz : z ∈ prodGridCell h m j) (hw : w ∈ prodGridCell h m j) :
    ‖z - w‖ ≤ h := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  rw [show z - w = (z.1 - w.1, z.2 - w.2) from rfl, Prod.norm_mk]
  refine max_le ?_ (norm_sub_le_of_mem_gridCell hh hz2 hw2)
  simp only [Set.mem_Ico] at hz1 hw1
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> [nlinarith [hz1.1, hw1.2]; nlinarith [hz1.2, hw1.1]]

omit [Fintype ι] in
/-- **The spacetime grid covers.** -/
theorem mem_prodGridCell_floor {h : ℝ} (hh : 0 < h) (z : ℝ × (ι → ℝ)) :
    z ∈ prodGridCell h ⌊z.1 / h⌋ fun i => ⌊z.2 i / h⌋ := by
  refine ⟨?_, mem_gridCell_floor hh z.2⟩
  constructor
  · rw [← le_div_iff₀' hh]; exact Int.floor_le (z.1 / h)
  · rw [← div_lt_iff₀' hh]; exact Int.lt_floor_add_one (z.1 / h)

/-- The one-dimensional index bound shared by the spatial and time factors: a cell
of side `h` meeting `[-R, R]` has its index in a fixed integer interval. -/
theorem mem_Icc_of_mem_Ico_of_abs_le {h : ℝ} (hh : 0 < h) {R : ℝ} {m : ℤ} {t : ℝ}
    (ht : t ∈ Set.Ico (h * m) (h * (m + 1))) (htR : |t| ≤ R) :
    m ∈ Set.Icc ⌈(-R / h) - 1⌉ ⌊R / h⌋ := by
  simp only [Set.mem_Ico] at ht
  obtain ⟨hlo, hhi⟩ := abs_le.mp htR
  refine ⟨Int.ceil_le.mpr ?_, Int.le_floor.mpr ?_⟩
  · have hdiv : -R / h < (m : ℝ) + 1 := by rw [div_lt_iff₀ hh]; linarith [ht.2]
    linarith
  · rw [le_div_iff₀ hh]; linarith [ht.1]

/-- **Only finitely many spacetime cells meet a bounded spacetime window.** -/
theorem finite_prodGridIndices {h : ℝ} (hh : 0 < h) (R : ℝ) :
    {p : ℤ × (ι → ℤ) | (prodGridCell h p.1 p.2 ∩
        Metric.closedBall (0 : ℝ × (ι → ℝ)) R).Nonempty}.Finite := by
  classical
  refine Set.Finite.subset
    (Set.Finite.prod (Set.finite_Icc ⌈(-R / h) - 1⌉ ⌊R / h⌋) (finite_gridIndices hh R)) ?_
  rintro ⟨m, j⟩ ⟨z, ⟨hz1, hz2⟩, hzB⟩
  have hnB : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hzB
  rw [Prod.norm_def] at hnB
  have h1 : |z.1| ≤ R := by
    have hle := le_trans (le_max_left ‖z.1‖ ‖z.2‖) hnB
    simpa [Real.norm_eq_abs] using hle
  have h2 : ‖z.2‖ ≤ R := le_trans (le_max_right ‖z.1‖ ‖z.2‖) hnB
  refine ⟨mem_Icc_of_mem_Ico_of_abs_le hh hz1 h1, ⟨z.2, hz2, ?_⟩⟩
  simpa [Metric.mem_closedBall, dist_zero_right] using h2

/-- **The finitely many spacetime cells meeting a ball cover it.** -/
theorem closedBall_subset_biUnion_prodGridCell {h : ℝ} (hh : 0 < h) (R : ℝ) :
    Metric.closedBall (0 : ℝ × (ι → ℝ)) R ⊆
      ⋃ p ∈ {p : ℤ × (ι → ℤ) | (prodGridCell h p.1 p.2 ∩
          Metric.closedBall (0 : ℝ × (ι → ℝ)) R).Nonempty}, prodGridCell h p.1 p.2 :=
  fun z hz =>
    Set.mem_biUnion (x := (⌊z.1 / h⌋, fun i => ⌊z.2 i / h⌋))
      ⟨z, mem_prodGridCell_floor hh z, hz⟩ (mem_prodGridCell_floor hh z)

/-- **The Navier–Stokes window sits inside a spacetime ball.**  `(0,T] × B̄(0,R)` has
spacetime norm at most `max T R`, because the product norm is the max.  This is how a
time-times-space window enters the cell machinery. -/
theorem window_subset_closedBall {T R : ℝ} :
    Set.Ioc (0:ℝ) T ×ˢ Metric.closedBall (0 : ι → ℝ) R
      ⊆ Metric.closedBall (0 : ℝ × (ι → ℝ)) (max T R) := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  simp only [Set.mem_Ioc] at ht
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs, abs_of_pos ht.1]
    exact le_trans ht.2 (le_max_left T R)
  · exact le_trans (by simpa [Metric.mem_closedBall, dist_zero_right] using hx) (le_max_right T R)

/-- **The criterion's arithmetic.**  Summing the per-cell bound over a finite family
of spacetime cells of side `h`: the total cell-average error is controlled by the
translation modulus, with the constant `ν(B_h)/h^{d}` — which for the sup-norm ball
is `(2h)^d/h^d = 2^d`, independent of `h`.  That `h`-independence is the whole point:
it lets `h → 0` drive the error to zero uniformly over an equicontinuous family.

Integrability of the displacement integrals is taken as hypotheses, per the module's
convention; `hglob` is the genuinely new requirement — the disjointness step needs
`‖τ_k f − f‖²` integrable over the *whole* space, which a bound on `‖f‖` alone cannot
give, and which a decaying (Schwartz, or compactly supported) field does. -/
theorem sum_cellError_le_modulus {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {h : ℝ} (hh : 0 < h) (S : Finset (ℤ × (ι → ℤ)))
    (f : ℝ × (ι → ℝ) → F) (hmeas : Measurable f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (Mmod : ℝ)
    (hmod : ∀ k ∈ Metric.closedBall (0 : ℝ × (ι → ℝ)) h,
      (∫ x, ‖f (x + k) - f x‖ ^ 2) ≤ Mmod)
    (hglob : ∀ k, Integrable fun x => ‖f (x + k) - f x‖ ^ 2)
    (hFp : ∀ p ∈ S, IntegrableOn
      (fun k => ∫ x in prodGridCell h p.1 p.2, ‖f (x + k) - f x‖ ^ 2)
      (Metric.closedBall (0 : ℝ × (ι → ℝ)) h))
    (hG : IntegrableOn (fun k => ∫ x, ‖f (x + k) - f x‖ ^ 2)
      (Metric.closedBall (0 : ℝ × (ι → ℝ)) h)) :
    ∑ p ∈ S, (∫ x in prodGridCell h p.1 p.2,
        ‖f x - ⨍ y in prodGridCell h p.1 p.2, f y‖ ^ 2)
      ≤ (h ^ (Fintype.card ι + 1))⁻¹ *
          (volume.real (Metric.closedBall (0 : ℝ × (ι → ℝ)) h) * Mmod) := by
  classical
  -- `volume` on `ℝ × (ι → ℝ)` is the product measure, hence translation-invariant
  haveI : (volume : Measure (ℝ × (ι → ℝ))).IsAddLeftInvariant := by
    rw [MeasureTheory.Measure.volume_eq_prod]; infer_instance
  set B := Metric.closedBall (0 : ℝ × (ι → ℝ)) h with hBdef
  set d := Fintype.card ι + 1 with hddef
  have hdpos : (0:ℝ) < h ^ d := by positivity
  have hvolcell : ∀ p : ℤ × (ι → ℤ), volume (prodGridCell h p.1 p.2)
      = ENNReal.ofReal (h ^ d) := fun p => volume_prodGridCell hh.le p.1 p.2
  have hne : ∀ p : ℤ × (ι → ℤ), volume (prodGridCell h p.1 p.2) ≠ 0 := by
    intro p; rw [hvolcell p, Ne, ENNReal.ofReal_eq_zero]; exact not_le.mpr hdpos
  have hfin : ∀ p : ℤ × (ι → ℤ), volume (prodGridCell h p.1 p.2) ≠ ⊤ := by
    intro p; rw [hvolcell p]; exact ENNReal.ofReal_ne_top
  have hreal : ∀ p : ℤ × (ι → ℤ), volume.real (prodGridCell h p.1 p.2) = h ^ d := by
    intro p
    rw [Measure.real, hvolcell p, ENNReal.toReal_ofReal hdpos.le]
  have hBfin : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  -- per-cell bound, with the cell measure evaluated
  have hcell : ∀ p ∈ S, (∫ x in prodGridCell h p.1 p.2,
      ‖f x - ⨍ y in prodGridCell h p.1 p.2, f y‖ ^ 2)
      ≤ (h ^ d)⁻¹ * ∫ k in B, (∫ x in prodGridCell h p.1 p.2,
          ‖f (x + k) - f x‖ ^ 2) := by
    intro p _
    have hres := setIntegral_cellError_le_displacement_of_bounded
      (prodGridCell h p.1 p.2) (measurableSet_prodGridCell h p.1 p.2) h f hmeas hM
      (hne p) (hfin p) hBfin
      (fun x hx y hy => norm_sub_le_of_mem_prodGridCell hh.le hy hx)
    rwa [hreal p] at hres
  -- the finite sum, the interchange, and the disjointness step
  calc ∑ p ∈ S, (∫ x in prodGridCell h p.1 p.2,
          ‖f x - ⨍ y in prodGridCell h p.1 p.2, f y‖ ^ 2)
      ≤ ∑ p ∈ S, (h ^ d)⁻¹ * ∫ k in B, (∫ x in prodGridCell h p.1 p.2,
          ‖f (x + k) - f x‖ ^ 2) := Finset.sum_le_sum hcell
    _ = (h ^ d)⁻¹ * ∑ p ∈ S, ∫ k in B, (∫ x in prodGridCell h p.1 p.2,
          ‖f (x + k) - f x‖ ^ 2) := by rw [← Finset.mul_sum]
    _ = (h ^ d)⁻¹ * ∫ k in B, (∑ p ∈ S, ∫ x in prodGridCell h p.1 p.2,
          ‖f (x + k) - f x‖ ^ 2) := by
        rw [MeasureTheory.integral_finsetSum S hFp]
    _ ≤ (h ^ d)⁻¹ * ∫ k in B, (∫ x, ‖f (x + k) - f x‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine setIntegral_mono_on (integrable_finsetSum S hFp) hG
          measurableSet_closedBall fun k _ => ?_
        exact sum_finset_setIntegral_le_integral_of_disjoint S
          (fun p => prodGridCell h p.1 p.2)
          (fun p => measurableSet_prodGridCell h p.1 p.2)
          (fun p q hpq => prodGridCell_disjoint hh (by
            simpa [Prod.ext_iff] using hpq))
          _ (fun x => by positivity) (hglob k)
    _ ≤ (h ^ d)⁻¹ * (volume.real B * Mmod) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_le_measureReal_mul_const measurableSet_closedBall hBfin
          _ Mmod (fun k hk => hmod k hk) hG

end ProdGridCell

/-!
## Subsequence combinatorics

Pure `ℕ`-level extraction, with no measure theory and no Navier–Stokes content: the
nested Cantor diagonal over a countable family of subsequence predicates, and its
specialization to an array of error functionals.  These lived downstream until the
compactness criterion needed them, which made them unreachable from here; they belong
at this level on the merits.
-/

/-- **Cantor diagonal extraction over a countable family of subsequence
predicates.**  If `Q n` is stable under passing to a further subsequence
(`hsub`) and under dropping a finite head (`htail`), and if from *every*
strictly monotone `τ` one can extract a refinement satisfying `Q n` (`hstep`),
then a single strictly monotone `σ` satisfies `Q n` for **every** `n`.

This is the extraction step of the Aubin–Lions–Simon argument over a countable
exhaustion; Mathlib has `Filter.extraction_forall_of_frequently`, which produces
`P n (φ n)` rather than a subsequence good for all `n` simultaneously, so this
nested form is absent.  Construction: nested extractors `Ψ 0 = id`,
`Ψ (j+1) = Ψ j ∘ ρ j`, diagonal `σ k = Ψ (k+1) k`; the ranges `Set.range (Ψ j)` are
antitone, which places every tail of `σ` inside `Set.range (Ψ (n+1))`.

[J.-L. Lions, *Quelques méthodes de résolution des problèmes aux limites non
linéaires*, Dunod 1969, Ch. 1 §5; J. Simon, "Compact sets in `L^p(0,T;B)`",
*Ann. Mat. Pura Appl.* **146** (1987) 65–96; R. Temam, *Navier–Stokes
Equations*, AMS Chelsea 2001, Ch. III §2.3.] -/
theorem exists_diagonal_subseq (Q : ℕ → (ℕ → ℕ) → Prop)
    (hsub : ∀ (n : ℕ) (τ ρ : ℕ → ℕ), Q n τ → StrictMono ρ → Q n (τ ∘ ρ))
    (htail : ∀ (n N : ℕ) (τ : ℕ → ℕ), Q n (fun k => τ (k + N)) → Q n τ)
    (hstep : ∀ (n : ℕ) (τ : ℕ → ℕ), StrictMono τ → ∃ ρ, StrictMono ρ ∧ Q n (τ ∘ ρ)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, Q n σ := by
  classical
  choose ρ hρmono hρQ using hstep
  let Ψ : ℕ → {f : ℕ → ℕ // StrictMono f} := fun n =>
    Nat.rec (motive := fun _ => {f : ℕ → ℕ // StrictMono f})
      ⟨id, strictMono_id⟩
      (fun j p => ⟨p.1 ∘ ρ j p.1 p.2, p.2.comp (hρmono j p.1 p.2)⟩) n
  have hΨsucc : ∀ j, (Ψ (j+1)).1 = (Ψ j).1 ∘ ρ j (Ψ j).1 (Ψ j).2 := fun _ => rfl
  have hmono : ∀ n, StrictMono (Ψ n).1 := fun n => (Ψ n).2
  have hQ : ∀ j, Q j (Ψ (j+1)).1 := by
    intro j
    have h := hρQ j (Ψ j).1 (Ψ j).2
    simpa [hΨsucc j] using h
  have hrange : ∀ j, Set.range (Ψ (j+1)).1 ⊆ Set.range (Ψ j).1 := by
    intro j; rw [hΨsucc j]; exact Set.range_comp_subset_range _ _
  have hrange' : ∀ a b, a ≤ b → Set.range (Ψ b).1 ⊆ Set.range (Ψ a).1 := by
    intro a b hab
    induction b with
    | zero => simp_all
    | succ b ih =>
      rcases Nat.lt_or_ge a (b+1) with h | h
      · exact (hrange b).trans (ih (Nat.lt_succ_iff.mp h))
      · have he : a = b + 1 := le_antisymm hab h
        subst he; exact subset_rfl
  set σ : ℕ → ℕ := fun k => (Ψ (k+1)).1 k with hσdef
  have hσmono : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 : σ (k+1) = (Ψ (k+1)).1 (ρ (k+1) (Ψ (k+1)).1 (Ψ (k+1)).2 (k+1)) := by
      show (Ψ (k+2)).1 (k+1) = _
      rw [hΨsucc (k+1)]; rfl
    rw [h1]
    exact (hmono (k+1)) (lt_of_lt_of_le (Nat.lt_succ_self k) ((hρmono (k+1) _ _).le_apply))
  refine ⟨σ, hσmono, ?_⟩
  intro n
  have hmem : ∀ j : ℕ, σ (j + n) ∈ Set.range (Ψ (n+1)).1 := by
    intro j; exact hrange' (n+1) (j+n+1) (by omega) ⟨j + n, rfl⟩
  choose ψ hψ using hmem
  have hψmono : StrictMono ψ := by
    intro a b hab
    have h1 : σ (a + n) < σ (b + n) := hσmono (by omega)
    rw [← hψ a, ← hψ b] at h1
    exact (hmono (n+1)).lt_iff_lt.mp h1
  have hQn : Q n ((Ψ (n+1)).1 ∘ ψ) := hsub n _ _ (hQ n) hψmono
  have heq : ((Ψ (n+1)).1 ∘ ψ) = fun j => σ (j + n) := by funext j; exact hψ j
  rw [heq] at hQn
  exact htail n n σ hQn

/-- **Diagonal extraction, specialized to a countable array of error
functionals.**  `F n m` is the error of member `m` on window `n`.  If every
window can be handled along a further refinement of any given subsequence, one
subsequence drives every window to `0`.  This is the form consumed by the
`T = R = n` exhaustion of `StrongL2LocLimit`. -/
theorem exists_subseq_forall_window_tendsto (F : ℕ → ℕ → ℝ)
    (hstep : ∀ (n : ℕ) (τ : ℕ → ℕ), StrictMono τ →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
        Filter.Tendsto (fun k => F n (τ (ρ k))) Filter.atTop (nhds 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ n, Filter.Tendsto (fun k => F n (σ k)) Filter.atTop (nhds 0) := by
  refine exists_diagonal_subseq
    (fun n τ => Filter.Tendsto (fun k => F n (τ k)) Filter.atTop (nhds 0)) ?_ ?_ hstep
  · intro n τ ρ hQ hρ
    exact hQ.comp hρ.tendsto_atTop
  · intro n N τ hQ
    exact (Filter.tendsto_add_atTop_iff_nat (f := fun k => F n (τ k)) N).mp hQ

/-!
## Engine 2 — Bolzano–Weierstrass in the finite-dimensional cell space
-/

/-- **Engine 2, vector-valued.**  A norm-bounded sequence in `Fin N → F` with `F`
finite-dimensional over `ℝ` has a Cauchy subsequence.

This is the form the criterion actually needs: the cell-average vector of a member of
the family has one entry per cell, and each entry is an average of `f`, so it is
`F`-valued rather than real.  `Fin N → F` is finite-dimensional, hence proper, so
Heine–Borel applies exactly as in the scalar case — no infinite-dimensional
compactness anywhere. -/
theorem exists_subseq_cauchy_of_bounded_pi_finiteDim {N : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (v : ℕ → Fin N → F) (M : ℝ) (hb : ∀ k : ℕ, ‖v k‖ ≤ M) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ j k : ℕ, K ≤ j → K ≤ k →
        ‖v (ρ j) - v (ρ k)‖ < ε := by
  haveI : ProperSpace (Fin N → F) := FiniteDimensional.proper_real (Fin N → F)
  obtain ⟨b, -, ρ, hρ, hconv⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : Fin N → F)) (r := M))
      (fun k => by simpa [Metric.mem_closedBall, dist_zero_right] using hb k)
  refine ⟨ρ, hρ, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq ε hε
  exact ⟨K, fun j k hj hk => by simpa [dist_eq_norm] using hK j hj k hk⟩

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




















