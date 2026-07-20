import Navier.Analysis.SeeleyMoments
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Seeley reflection series — the analytic extension operator

This leaf constructs Seeley's linear extension operator
(`E g)(t, x) = ∑' k, seeleyA k · φ(−2^k t) • g(−2^k t, x)`  (t < 0)
for the half-space, following

  R. T. Seeley, "Extension of C^∞ functions defined in a half space",
  Proc. Amer. Math. Soc. 15 (1964), 625–626.

`SeriesData V` packages one summand family `(c k · ψ(−2^k t)) • h(−2^k t, x)`
with the exact hypotheses the uniform-convergence arguments consume:
* `h` within-smooth on the closed right half-space (no completeness of `V`);
* `ψ` smooth, supported in `|s − 1| ≤ 2`, all iterated derivatives bounded;
* `|c k| · 2^{km}` summable for every `m` (super-polynomial decay).

Main results of this file:
* `summable_term` — termwise summability everywhere (finite support off the
  boundary; a convergent scalar series on the boundary) — no completeness;
* `series_zero_fst` — boundary value `series (0, x) = (∑' c) · ψ 0 • h(0,x)`;
* `continuousOn_series` — the series is continuous on the closed left
  half-space (uniform tail + finite-head ε-split).
-/

noncomputable section

namespace Navier.Analysis.HalfSpaceSmoothnessBridge.SeeleyReflection

open Set Filter Topology
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The closed left half-space `t ≤ 0` in `ℝ × Space`. -/
abbrev leftHalf : Set (ℝ × Space) := Set.Iic 0 ×ˢ Set.univ

/-- The closed right half-space `0 ≤ t` in `ℝ × Space`. -/
abbrev rightHalf : Set (ℝ × Space) := Set.Ici 0 ×ˢ Set.univ

theorem uniqueDiffOn_leftHalf : UniqueDiffOn ℝ leftHalf :=
  (uniqueDiffOn_Iic 0).prod uniqueDiffOn_univ

theorem uniqueDiffOn_rightHalf : UniqueDiffOn ℝ rightHalf := uniqueDiffOn_halfSpace

/-!
## The smooth cutoff `seeleyPhi`

`seeleyPhi` is `1` on the closed ball `|s − 1| ≤ 1` (in particular at `0`,
where the reflected arguments land at the boundary `t = 0`) and `0` off the
open ball `|s − 1| < 2`.  All its iterated derivatives vanish at `0` because
it is locally constant there.
-/

/-- The Seeley cutoff: a `C^∞` bump equal to `1` on `|s − 1| ≤ 1` and
supported in `|s − 1| ≤ 2`. -/
def seeleyPhi : ℝ → ℝ := (⟨1, 2, zero_lt_one, one_lt_two⟩ : ContDiffBump (1 : ℝ))

theorem seeleyPhi_one {s : ℝ} (hs : |s - 1| ≤ 1) : seeleyPhi s = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  exact hs

theorem seeleyPhi_zero {s : ℝ} (hs : 2 ≤ |s - 1|) : seeleyPhi s = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  exact hs

theorem seeleyPhi_contDiff : ContDiff ℝ ∞ seeleyPhi :=
  ContDiffBump.contDiff _

theorem seeleyPhi_nonneg (s : ℝ) : 0 ≤ seeleyPhi s := ContDiffBump.nonneg _

theorem seeleyPhi_le_one (s : ℝ) : seeleyPhi s ≤ 1 := ContDiffBump.le_one _

theorem seeleyPhi_eq_one_on {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 2) : seeleyPhi s = 1 := by
  apply seeleyPhi_one
  rcases hs with ⟨h0, h2⟩
  rw [abs_le]
  constructor <;> linarith

/-- Every nontrivial iterated derivative of the cutoff vanishes on the open
interval `(0, 2)`, where the cutoff is locally `1`. -/
theorem iteratedDeriv_seeleyPhi_eqOn_Ioo (n : ℕ) (hn : 1 ≤ n) :
    EqOn (iteratedDeriv n seeleyPhi) (fun _ : ℝ => (0 : ℝ)) (Set.Ioo (0 : ℝ) 2) := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro s hs
    rw [iteratedDeriv_one]
    show deriv seeleyPhi s = 0
    have hEq : seeleyPhi =ᶠ[𝓝 s] fun _ => (1 : ℝ) :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs) (fun t ht => seeleyPhi_eq_one_on ht)
    rw [hEq.deriv_eq, deriv_const]
  | succ n hn ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    show deriv (iteratedDeriv n seeleyPhi) s = 0
    have hEq : iteratedDeriv n seeleyPhi =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs) (fun t ht => ih ht)
    rw [hEq.deriv_eq, deriv_const]

/-- Every nontrivial iterated derivative of the cutoff vanishes at `0`
(continuity from the right, where it is locally `1`). -/
theorem iteratedDeriv_seeleyPhi_zero {n : ℕ} (hn : 1 ≤ n) :
    iteratedDeriv n seeleyPhi 0 = 0 := by
  have hseq : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmem : ∀ j : ℕ, (1 : ℝ) / (j + 1) ∈ Set.Ioo (0 : ℝ) 2 := by
    intro j
    have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    refine ⟨by positivity, lt_of_le_of_lt (by
      rw [div_le_one hpos]; exact le_add_of_nonneg_left (by positivity)) one_lt_two⟩
  have hval : ∀ j : ℕ, iteratedDeriv n seeleyPhi ((1 : ℝ) / (j + 1)) = 0 :=
    fun j => iteratedDeriv_seeleyPhi_eqOn_Ioo n hn (hmem j)
  have hcont : Continuous (iteratedDeriv n seeleyPhi) :=
    seeleyPhi_contDiff.continuous_iteratedDeriv n (by exact_mod_cast le_top)
  have hlim : Tendsto (fun j : ℕ => iteratedDeriv n seeleyPhi ((1 : ℝ) / (j + 1)))
      atTop (𝓝 (iteratedDeriv n seeleyPhi 0)) :=
    Filter.Tendsto.comp hcont.continuousAt hseq
  simp_rw [hval] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-!
## The `SeriesData` package
-/

/-- One reflection-series family: terms `(c k · ψ(−2^k t)) • h(−2^k t, x)`.
The class is designed to be closed under one application of the Fréchet
derivative, so that smoothness of the series at all orders follows from the
base hypotheses by induction. -/
structure SeriesData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- The reflected field, within-smooth on the closed right half-space. -/
  h : (ℝ × Space) → V
  /-- Within-smoothness of the reflected field. -/
  hh : ContDiffOn ℝ ∞ h rightHalf
  /-- The scalar cutoff. -/
  ψ : ℝ → ℝ
  /-- Smoothness of the cutoff. -/
  hψ : ContDiff ℝ ∞ ψ
  /-- Support of the cutoff in `|s − 1| ≤ 2`. -/
  hψsupp : ∀ s : ℝ, 2 ≤ |s - 1| → ψ s = 0
  /-- Every iterated derivative of the cutoff is bounded. -/
  hψb : ∀ n : ℕ, ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv n ψ t| ≤ C
  /-- The reflection coefficients. -/
  c : ℕ → ℝ
  /-- Super-polynomial decay of the coefficients. -/
  hc : ∀ m : ℕ, Summable fun k => |c k| * (2 : ℝ) ^ (k * m)

namespace SeriesData

/-- The `k`-th summand of the reflection series. -/
def term (D : SeriesData V) (k : ℕ) (z : ℝ × Space) : V :=
  (D.c k * D.ψ (-(2 : ℝ) ^ k * z.1)) • D.h (-(2 : ℝ) ^ k * z.1, z.2)

/-- The reflection series of one `SeriesData` package. -/
def series (D : SeriesData V) (z : ℝ × Space) : V := ∑' k, D.term k z

/-- Terms whose reflected argument escapes the cutoff support vanish. -/
theorem term_eq_zero_of_two_le (D : SeriesData V) {k : ℕ} {z : ℝ × Space}
    (hs : 2 ≤ |-(2 : ℝ) ^ k * z.1 - 1|) : D.term k z = 0 := by
  rw [term, D.hψsupp _ hs, mul_zero, zero_smul]

/-- `|c|` is summable (the `m = 0` decay). -/
theorem summable_abs_c (D : SeriesData V) : Summable fun k => |D.c k| := by
  have := D.hc 0
  simpa using this

/-- `c` is summable. -/
theorem summable_c (D : SeriesData V) : Summable fun k => D.c k :=
  Summable.of_norm (by simpa [Real.norm_eq_abs] using D.summable_abs_c)

/-- Termwise summability: finite support away from the boundary, a convergent
scalar series on the boundary.  No completeness of `V` is needed. -/
theorem summable_term (D : SeriesData V) (z : ℝ × Space) :
    Summable fun k => D.term k z := by
  by_cases hz1 : z.1 = 0
  · have h2 : Summable fun k => D.c k * D.ψ 0 := D.summable_c.mul_right _
    have hterm : (fun k => D.term k z) = fun k =>
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (D.h (0, z.2)))
          (D.c k * D.ψ 0) := by
      funext k
      simp [term, hz1]
    rw [hterm]
    exact (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) _).summable h2
  · obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (3 / |z.1|) one_lt_two
    apply summable_of_ne_finset_zero (s := Finset.range K)
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    apply term_eq_zero_of_two_le
    have hpos : (0 : ℝ) < |z.1| := abs_pos.mpr hz1
    have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h2k : (3 : ℝ) < (2 : ℝ) ^ k * |z.1| := by
      calc (3 : ℝ) = 3 / |z.1| * |z.1| := by field_simp
        _ < (2 : ℝ) ^ K * |z.1| := mul_lt_mul_of_pos_right hK hpos
        _ ≤ (2 : ℝ) ^ k * |z.1| := mul_le_mul_of_nonneg_right hpow hpos.le
    have hu : |-(2 : ℝ) ^ k * z.1| = (2 : ℝ) ^ k * |z.1| := by
      rw [abs_mul, abs_neg, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hbig : (3 : ℝ) < |-(2 : ℝ) ^ k * z.1| := hu ▸ h2k
    have h := abs_sub_abs_le_abs_sub (-(2 : ℝ) ^ k * z.1) (1 : ℝ)
    rw [abs_one] at h
    linarith

/-- The boundary value of the series: at `t = 0` every reflected argument is
`0`, so the series collapses to `(∑' c) · ψ 0 • h(0, x)`. -/
theorem series_zero_fst (D : SeriesData V) (x : Space) :
    D.series (0, x) = ((∑' k, D.c k) * D.ψ 0) • D.h (0, x) := by
  have hterm : ∀ k : ℕ, D.term k (0, x) = (D.c k * D.ψ 0) • D.h (0, x) := by
    intro k
    simp [term]
  have h2 : Summable fun k => D.c k * D.ψ 0 := D.summable_c.mul_right _
  have hL : (∑' k, (D.c k * D.ψ 0) • D.h (0, x)) =
      (∑' k, D.c k * D.ψ 0) • D.h (0, x) := by
    have hmap := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (D.h (0, x))).map_tsum h2
    have hφ : ∀ a : ℝ,
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (D.h (0, x))) a =
          a • D.h (0, x) := fun a => by simp
    simp_rw [hφ] at hmap
    exact hmap.symm
  rw [series, tsum_congr hterm, hL, tsum_mul_right]

/-- A uniform norm bound for `h` on the compact strip
`[0, 3] × closedBall x₀ 1`, where all active reflected arguments live. -/
theorem exists_h_bound (D : SeriesData V) (x₀ : Space) :
    ∃ Ch : ℝ, ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall x₀ 1, ‖D.h w‖ ≤ Ch := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall x₀ 1) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hsub : Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall x₀ 1 ⊆ rightHalf :=
    Set.prod_mono Set.Icc_subset_Ici_self (Set.subset_univ _)
  have hcont : ContinuousOn D.h (Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall x₀ 1) :=
    D.hh.continuousOn.mono hsub
  exact hK.exists_bound_of_continuousOn hcont

/-- Uniform term bound on the left half-space near `z₀`: either the term
vanishes (reflected argument outside the cutoff support) or the reflected
argument lies in the compact strip and the bounds apply. -/
theorem term_norm_le {D : SeriesData V} {z₀ z : ℝ × Space} (hzA : z ∈ leftHalf)
    (hz2 : z.2 ∈ Metric.closedBall z₀.2 1) {Cψ Ch : ℝ}
    (hCψ : ∀ t : ℝ, |D.ψ t| ≤ Cψ)
    (hCh : ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1, ‖D.h w‖ ≤ Ch)
    (k : ℕ) : ‖D.term k z‖ ≤ |D.c k| * (Cψ * Ch) := by
  have hCψnn : 0 ≤ Cψ := le_trans (abs_nonneg _) (hCψ 0)
  have hChnn : 0 ≤ Ch :=
    le_trans (norm_nonneg _)
      (hCh (1, z₀.2) (Set.mem_prod.mpr
        ⟨Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩,
          Metric.mem_closedBall_self one_pos.le⟩))
  by_cases hsupp : 2 ≤ |-(2 : ℝ) ^ k * z.1 - 1|
  · rw [term_eq_zero_of_two_le D hsupp, norm_zero]
    exact mul_nonneg (abs_nonneg _) (mul_nonneg hCψnn hChnn)
  · rw [not_le] at hsupp
    have hz1 : z.1 ≤ 0 := hzA.1
    have ht1 : (0 : ℝ) ≤ -(2 : ℝ) ^ k * z.1 := by
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
      have h3 : (2 : ℝ) ^ k * z.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 hz1
      rw [neg_mul]
      exact neg_nonneg.mpr h3
    have ht2 : -(2 : ℝ) ^ k * z.1 ≤ 3 := by
      have hlt := abs_lt.mp hsupp
      linarith [hlt.2]
    have hw : (-(2 : ℝ) ^ k * z.1, z.2) ∈
        Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1 :=
      Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨ht1, ht2⟩, hz2⟩
    have hh := hCh _ hw
    have h1 : |D.c k * D.ψ (-(2 : ℝ) ^ k * z.1)| ≤ |D.c k| * Cψ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCψ _) (abs_nonneg _)
    rw [term, norm_smul, Real.norm_eq_abs]
    calc |D.c k * D.ψ (-(2 : ℝ) ^ k * z.1)| * ‖D.h (-(2 : ℝ) ^ k * z.1, z.2)‖
        ≤ |D.c k| * Cψ * Ch :=
          mul_le_mul h1 hh (norm_nonneg _) (mul_nonneg (abs_nonneg _) hCψnn)
      _ = |D.c k| * (Cψ * Ch) := by ring

/-- The tail of the series is dominated by the tail of the (summable) bound
`|c| · Cψ · Ch`, uniformly on the left half-space near `z₀`. -/
theorem series_tail_norm_le {D : SeriesData V} {z₀ z : ℝ × Space} (hzA : z ∈ leftHalf)
    (hz2 : z.2 ∈ Metric.closedBall z₀.2 1) {Cψ Ch : ℝ}
    (hCψ : ∀ t : ℝ, |D.ψ t| ≤ Cψ)
    (hCh : ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1, ‖D.h w‖ ≤ Ch)
    (K : ℕ) :
    ‖∑' k, D.term (k + K) z‖ ≤ ∑' k, |D.c (k + K)| * (Cψ * Ch) := by
  have hgsum : Summable fun k => |D.c (k + K)| * (Cψ * Ch) :=
    ((summable_nat_add_iff K).2 D.summable_abs_c).mul_right _
  have hsum1 : Summable fun k => ‖D.term (k + K) z‖ :=
    Summable.of_norm_bounded hgsum fun k => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact term_norm_le hzA hz2 hCψ hCh (k + K)
  calc ‖∑' k, D.term (k + K) z‖ ≤ ∑' k, ‖D.term (k + K) z‖ :=
        norm_tsum_le_tsum_norm hsum1
    _ ≤ ∑' k, |D.c (k + K)| * (Cψ * Ch) :=
        Summable.tsum_le_tsum (fun k => term_norm_le hzA hz2 hCψ hCh (k + K))
          hsum1 hgsum

/-- Tails of a summable real series are eventually small. -/
theorem exists_tail_small {f : ℕ → ℝ} (hf : Summable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ‖∑' k, f (k + K)‖ < ε := by
  have hlim : Tendsto (fun K => ∑' k, f (k + K)) atTop (𝓝 0) := by
    have hkey : ∀ K : ℕ, ∑' k, f (k + K) =
        ∑' k, f k - ∑ k ∈ Finset.range K, f k := by
      intro K
      rw [← hf.sum_add_tsum_nat_add K]
      abel
    simp_rw [hkey]
    have h2 : Tendsto (fun K => ∑' k, f k - ∑ k ∈ Finset.range K, f k) atTop
        (𝓝 ((∑' k, f k) - ∑' k, f k)) :=
      tendsto_const_nhds.sub hf.hasSum.tendsto_sum_nat
    simpa using h2
  have hev := hlim.eventually (Metric.ball_mem_nhds 0 hε)
  rcases hev.exists with ⟨K, hK⟩
  exact ⟨K, by rwa [dist_zero_right] at hK⟩

/-- Each term is continuous within the left half-space. -/
theorem term_continuousWithinAt (D : SeriesData V) (k : ℕ) (z₀ : ℝ × Space)
    (hz₀ : z₀ ∈ leftHalf) : ContinuousWithinAt (D.term k) leftHalf z₀ := by
  have hmap : ContinuousWithinAt
      (fun z : ℝ × Space => (-(2 : ℝ) ^ k * z.1, z.2)) leftHalf z₀ :=
    ((continuous_const.mul continuous_fst).continuousWithinAt).prodMk
      (continuous_snd.continuousWithinAt)
  have hto : Set.MapsTo (fun z : ℝ × Space => (-(2 : ℝ) ^ k * z.1, z.2))
      leftHalf rightHalf := by
    intro z hz
    have hz1 : z.1 ≤ 0 := hz.1
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    have h3 : (2 : ℝ) ^ k * z.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 hz1
    refine ⟨?_, Set.mem_univ _⟩
    show 0 ≤ -(2 : ℝ) ^ k * z.1
    rw [neg_mul]
    exact neg_nonneg.mpr h3
  have hh : ContinuousWithinAt D.h rightHalf (-(2 : ℝ) ^ k * z₀.1, z₀.2) :=
    D.hh.continuousOn _ (hto hz₀)
  have hcomp : ContinuousWithinAt
      (D.h ∘ fun z : ℝ × Space => (-(2 : ℝ) ^ k * z.1, z.2)) leftHalf z₀ :=
    ContinuousWithinAt.comp (f := fun z : ℝ × Space => (-(2 : ℝ) ^ k * z.1, z.2))
      hh hmap hto
  have hsc : ContinuousWithinAt
      (fun z : ℝ × Space => D.c k * D.ψ (-(2 : ℝ) ^ k * z.1)) leftHalf z₀ :=
    continuousWithinAt_const.mul
      ((D.hψ.continuous.comp (continuous_const.mul continuous_fst)).continuousWithinAt)
  have : D.term k = fun z : ℝ × Space =>
      (D.c k * D.ψ (-(2 : ℝ) ^ k * z.1)) • D.h (-(2 : ℝ) ^ k * z.1, z.2) := rfl
  rw [this]
  exact hsc.smul hcomp

/-- Finite head sums of terms are continuous within the left half-space. -/
theorem finsum_term_continuousWithinAt (D : SeriesData V) (K : ℕ) (z₀ : ℝ × Space)
    (hz₀ : z₀ ∈ leftHalf) :
    ContinuousWithinAt (fun z => ∑ k ∈ Finset.range K, D.term k z) leftHalf z₀ := by
  induction K with
  | zero => simp [continuousWithinAt_const]
  | succ n ih =>
    have hsum : (fun z => ∑ k ∈ Finset.range (n + 1), D.term k z) =
        fun z => (∑ k ∈ Finset.range n, D.term k z) + D.term n z :=
      funext fun z => Finset.sum_range_succ _ _
    rw [hsum]
    exact ih.add (D.term_continuousWithinAt n z₀ hz₀)

/-- **Continuity of the reflection series** on the closed left half-space:
uniform tail bound plus finite-head continuity. -/
theorem continuousOn_series (D : SeriesData V) : ContinuousOn D.series leftHalf := by
  intro z₀ hz₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨Cψ, hCψ⟩ := D.hψb 0
  have hCψ' : ∀ t : ℝ, |D.ψ t| ≤ Cψ := by simpa [iteratedDeriv_zero] using hCψ
  obtain ⟨Ch, hCh⟩ := D.exists_h_bound z₀.2
  have hCψnn : 0 ≤ Cψ := le_trans (abs_nonneg _) (hCψ' 0)
  have hChnn : 0 ≤ Ch :=
    le_trans (norm_nonneg _)
      (hCh (1, z₀.2) ⟨⟨by norm_num, by norm_num⟩,
        Metric.mem_closedBall_self one_pos.le⟩)
  have hbsum : Summable fun k => |D.c k| * (Cψ * Ch) := D.summable_abs_c.mul_right _
  obtain ⟨K, hK⟩ := exists_tail_small hbsum (show 0 < ε / 4 by positivity)
  have htail_nn : 0 ≤ ∑' k, |D.c (k + K)| * (Cψ * Ch) :=
    tsum_nonneg fun k => mul_nonneg (abs_nonneg _) (mul_nonneg hCψnn hChnn)
  have htail_lt : ∑' k, |D.c (k + K)| * (Cψ * Ch) < ε / 4 := by
    have := hK
    rwa [Real.norm_of_nonneg htail_nn] at this
  have hsum_cts : ContinuousWithinAt
      (fun z => ∑ k ∈ Finset.range K, D.term k z) leftHalf z₀ :=
    D.finsum_term_continuousWithinAt K z₀ hz₀
  obtain ⟨δ₁, hδ₁, hδhead⟩ :=
    (Metric.continuousWithinAt_iff.mp hsum_cts) (ε / 4) (by positivity)
  refine ⟨min δ₁ 1, lt_min hδ₁ one_pos, ?_⟩
  intro z hzA hzd
  have hzhead : dist (∑ k ∈ Finset.range K, D.term k z)
      (∑ k ∈ Finset.range K, D.term k z₀) < ε / 4 :=
    hδhead hzA (lt_of_lt_of_le hzd (min_le_left _ _))
  have hzball : z.2 ∈ Metric.closedBall z₀.2 1 := by
    rw [Metric.mem_closedBall]
    have hle : dist z.2 z₀.2 ≤ dist z z₀ := by
      have h3 := le_max_right (dist z.1 z₀.1) (dist z.2 z₀.2)
      rwa [← Prod.dist_eq] at h3
    exact le_trans hle (le_trans hzd.le (min_le_right _ _))
  rw [dist_eq_norm] at hzhead ⊢
  have hsplit : ∀ w : ℝ × Space, D.series w =
      (∑ k ∈ Finset.range K, D.term k w) + ∑' k, D.term (k + K) w :=
    fun w => ((D.summable_term w).sum_add_tsum_nat_add K).symm
  rw [hsplit z, hsplit z₀]
  have htz := series_tail_norm_le hzA hzball hCψ' hCh K
  have htz0 := series_tail_norm_le hz₀
    (Metric.mem_closedBall_self one_pos.le) hCψ' hCh K
  have htz_lt : ‖∑' k, D.term (k + K) z‖ < ε / 4 := lt_of_le_of_lt htz htail_lt
  have htz0_lt : ‖∑' k, D.term (k + K) z₀‖ < ε / 4 := lt_of_le_of_lt htz0 htail_lt
  calc ‖(∑ k ∈ Finset.range K, D.term k z) + ∑' k, D.term (k + K) z -
        ((∑ k ∈ Finset.range K, D.term k z₀) + ∑' k, D.term (k + K) z₀)‖
      ≤ ‖(∑ k ∈ Finset.range K, D.term k z) - (∑ k ∈ Finset.range K, D.term k z₀)‖
          + ‖∑' k, D.term (k + K) z‖ + ‖∑' k, D.term (k + K) z₀‖ := by
        have hsplit2 :
            (∑ k ∈ Finset.range K, D.term k z) + ∑' k, D.term (k + K) z -
              ((∑ k ∈ Finset.range K, D.term k z₀) + ∑' k, D.term (k + K) z₀)
            = ((∑ k ∈ Finset.range K, D.term k z) - (∑ k ∈ Finset.range K, D.term k z₀))
              + ((∑' k, D.term (k + K) z) - (∑' k, D.term (k + K) z₀)) := by abel
        rw [hsplit2]
        refine le_trans (norm_add_le _ _) ?_
        rw [add_assoc]
        exact add_le_add le_rfl (norm_sub_le _ _)
    _ < ε / 4 + ε / 4 + ε / 4 := by
        exact add_lt_add (add_lt_add hzhead htz_lt) htz0_lt
    _ < ε := by linarith

/-!
## W3 — per-term first jets

The derivative of `term k z = (c k · ψ(−2^k z.1)) • h(−2^k z.1, z.2)` is the
Leibniz sum of the `ψ'`-piece and the `h`-jet piece; both carry a `2^k`
chain factor, absorbed by the super-polynomial decay of `c`.
-/

/-- The linear reflection map `z ↦ (−2^k z.1, z.2)` as a continuous linear
map. -/
def reflCLM (k : ℕ) : (ℝ × Space) →L[ℝ] (ℝ × Space) :=
  ((-(2 : ℝ) ^ k) • ContinuousLinearMap.fst ℝ ℝ Space).prod
    (ContinuousLinearMap.snd ℝ ℝ Space)

theorem reflCLM_apply (k : ℕ) (z : ℝ × Space) :
    reflCLM k z = (-(2 : ℝ) ^ k * z.1, z.2) := by
  ext <;> simp [reflCLM, smul_eq_mul]

theorem mapsTo_reflCLM_leftHalf (k : ℕ) :
    Set.MapsTo (reflCLM k) leftHalf rightHalf := by
  intro z hz
  have hz1 : z.1 ≤ 0 := hz.1
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
  have h3 : (2 : ℝ) ^ k * z.1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 hz1
  have h4 : (0 : ℝ) ≤ -(2 : ℝ) ^ k * z.1 := by rw [neg_mul]; exact neg_nonneg.mpr h3
  rw [reflCLM_apply]
  exact Set.mem_prod.mpr ⟨h4, Set.mem_univ _⟩

theorem reflCLM_norm_le (k : ℕ) : ‖reflCLM k‖ ≤ (2 : ℝ) ^ k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hz1 : ‖-(2 : ℝ) ^ k * z.1‖ = (2 : ℝ) ^ k * ‖z.1‖ := by
    rw [norm_mul, norm_neg, norm_pow, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc ‖reflCLM k z‖ = max ‖-(2 : ℝ) ^ k * z.1‖ ‖z.2‖ := by
        rw [reflCLM_apply]
        exact Prod.norm_def _
    _ ≤ max ((2 : ℝ) ^ k * ‖z‖) ((2 : ℝ) ^ k * ‖z‖) := by
        apply max_le_max
        · rw [hz1]
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        · exact le_trans (le_max_right _ _)
            (le_mul_of_one_le_left (le_max_of_le_left (norm_nonneg z.1))
              (one_le_pow₀ (by norm_num)))
    _ = (2 : ℝ) ^ k * ‖z‖ := max_self _

/-- The scalar coefficient of term `k`. -/
def scalarFun (D : SeriesData V) (k : ℕ) (z : ℝ × Space) : ℝ :=
  D.c k * D.ψ (reflCLM k z).1

/-- The jet of `scalarFun k` at `z`: multiplication by
`c k · (−2^k) · ψ'(−2^k z.1)` on the first coordinate. -/
def scalarJet (D : SeriesData V) (k : ℕ) (z : ℝ × Space) : (ℝ × Space) →L[ℝ] ℝ :=
  (D.c k * (-(2 : ℝ) ^ k) * deriv D.ψ (reflCLM k z).1) •
    ContinuousLinearMap.fst ℝ ℝ Space

theorem hasFDerivAt_scalarFun (D : SeriesData V) (k : ℕ) (z : ℝ × Space) :
    HasFDerivAt (D.scalarFun k) (D.scalarJet k z) z := by
  have hdψ : Differentiable ℝ D.ψ := D.hψ.differentiable (by simp)
  have hinner : HasFDerivAt (fun z : ℝ × Space => (reflCLM k z).1)
      ((-(2 : ℝ) ^ k) • ContinuousLinearMap.fst ℝ ℝ Space) z := by
    have hL := (ContinuousLinearMap.fst ℝ ℝ Space).hasFDerivAt.comp z
      (reflCLM k).hasFDerivAt
    have hfst : (ContinuousLinearMap.fst ℝ ℝ Space).comp (reflCLM k) =
        (-(2 : ℝ) ^ k) • ContinuousLinearMap.fst ℝ ℝ Space := by
      apply ContinuousLinearMap.ext
      intro v
      rw [ContinuousLinearMap.comp_apply, reflCLM_apply]
      simp [smul_eq_mul]
    rw [hfst] at hL
    have hrw : (fun z : ℝ × Space => (reflCLM k z).1) =
        (ContinuousLinearMap.fst ℝ ℝ Space) ∘ (reflCLM k) := rfl
    rw [hrw]
    exact hL
  have hψd : HasDerivAt D.ψ (deriv D.ψ ((reflCLM k z).1)) ((reflCLM k z).1) :=
    (hdψ _).hasDerivAt
  have hcomp := hψd.hasFDerivAt.comp z hinner
  have hjet : (ContinuousLinearMap.toSpanSingleton ℝ
        (deriv D.ψ ((reflCLM k z).1))).comp
      ((-(2 : ℝ) ^ k) • ContinuousLinearMap.fst ℝ ℝ Space) =
      (deriv D.ψ ((reflCLM k z).1) * (-(2 : ℝ) ^ k)) •
        ContinuousLinearMap.fst ℝ ℝ Space := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.comp_apply]
    simp [smul_eq_mul, mul_comm, mul_assoc]
  rw [hjet] at hcomp
  have hcm := hcomp.const_mul (D.c k)
  have hsmul : (D.c k) • ((deriv D.ψ ((reflCLM k z).1) * (-(2 : ℝ) ^ k)) •
        ContinuousLinearMap.fst ℝ ℝ Space) =
      (D.c k * (deriv D.ψ ((reflCLM k z).1) * (-(2 : ℝ) ^ k))) •
        ContinuousLinearMap.fst ℝ ℝ Space := smul_smul _ _ _
  rw [hsmul] at hcm
  have hr : D.c k * (deriv D.ψ ((reflCLM k z).1) * (-(2 : ℝ) ^ k)) =
      D.c k * (-(2 : ℝ) ^ k) * deriv D.ψ ((reflCLM k z).1) := by ring
  rw [hr] at hcm
  exact hcm

/-- The `h`-part of the term jet. -/
theorem hasFDerivWithinAt_h_comp_refl (D : SeriesData V) (k : ℕ) (z : ℝ × Space)
    (hz : z ∈ leftHalf) :
    HasFDerivWithinAt (D.h ∘ reflCLM k)
      ((fderivWithin ℝ D.h rightHalf (reflCLM k z)).comp (reflCLM k)) leftHalf z := by
  have hd : DifferentiableOn ℝ D.h rightHalf := D.hh.differentiableOn (by simp)
  have hw : reflCLM k z ∈ rightHalf := mapsTo_reflCLM_leftHalf k hz
  have hh : HasFDerivWithinAt D.h (fderivWithin ℝ D.h rightHalf (reflCLM k z))
      rightHalf (reflCLM k z) := (hd _ hw).hasFDerivWithinAt
  exact HasFDerivWithinAt.comp (f := ⇑(reflCLM k)) (s := leftHalf) (t := rightHalf)
    (x := z) hh (reflCLM k).hasFDerivAt.hasFDerivWithinAt
    (mapsTo_reflCLM_leftHalf k)

/-- The first jet of term `k` at `z`: Leibniz sum of the `ψ'`-piece and the
`h`-jet piece. -/
def termJet (D : SeriesData V) (k : ℕ) (z : ℝ × Space) : (ℝ × Space) →L[ℝ] V :=
  (D.c k * D.ψ (reflCLM k z).1) •
      ((fderivWithin ℝ D.h rightHalf (reflCLM k z)).comp (reflCLM k)) +
    (D.scalarJet k z).smulRight (D.h (reflCLM k z))

theorem hasFDerivWithinAt_term (D : SeriesData V) (k : ℕ) (z : ℝ × Space)
    (hz : z ∈ leftHalf) :
    HasFDerivWithinAt (D.term k) (D.termJet k z) leftHalf z := by
  have hsc : HasFDerivWithinAt (D.scalarFun k) (D.scalarJet k z) leftHalf z :=
    (D.hasFDerivAt_scalarFun k z).hasFDerivWithinAt
  have hh := D.hasFDerivWithinAt_h_comp_refl k z hz
  have hsmul := hsc.smul hh
  have hterm : D.term k = fun z : ℝ × Space => D.scalarFun k z • D.h (reflCLM k z) := by
    funext w
    simp [term, scalarFun, reflCLM_apply]
  rw [hterm]
  exact hsmul

/-- If the reflected argument is strictly outside the cutoff support, the
term jet vanishes (`ψ` and `ψ'` both vanish there). -/
theorem termJet_eq_zero_of_two_lt (D : SeriesData V) {k : ℕ} {z : ℝ × Space}
    (hs : 2 < |(reflCLM k z).1 - 1|) : D.termJet k z = 0 := by
  have hψ0 : D.ψ (reflCLM k z).1 = 0 := D.hψsupp _ hs.le
  have hdψ0 : deriv D.ψ (reflCLM k z).1 = 0 := by
    have hEq : D.ψ =ᶠ[𝓝 ((reflCLM k z).1)] fun _ : ℝ => (0 : ℝ) := by
      have hopen : IsOpen {s : ℝ | 2 < |s - 1|} :=
        isOpen_lt continuous_const (by fun_prop)
      have hmem : {s : ℝ | 2 < |s - 1|} ∈ 𝓝 ((reflCLM k z).1) :=
        hopen.mem_nhds hs
      exact eventuallyEq_of_mem hmem fun s hs2 => D.hψsupp s hs2.le
    rw [hEq.deriv_eq]
    simp
  rw [termJet, scalarJet, hψ0, hdψ0, mul_zero, mul_zero, zero_smul]
  simp

/-- Termwise jet summability: finite support off the boundary; an explicit
scalar-series decomposition on the boundary (no completeness of `V`). -/
theorem summable_termJet (D : SeriesData V) (z : ℝ × Space) :
    Summable fun k => D.termJet k z := by
  by_cases hz1 : z.1 = 0
  · -- boundary: three scalar-series pieces
    have hcs : Summable fun k => D.c k * (2 : ℝ) ^ k := by
      apply Summable.of_norm
      have h1 := D.hc 1
      simp only [Nat.mul_one] at h1
      simpa [Real.norm_eq_abs, abs_mul] using h1
    set w : ℝ × Space := (0, z.2) with hw_def
    have hw1 : w.1 = 0 := rfl
    set L₁ : (ℝ × Space) →L[ℝ] V :=
      (ContinuousLinearMap.fst ℝ ℝ Space).smulRight
        (fderivWithin ℝ D.h rightHalf w ((1 : ℝ), (0 : Space))) with L₁_def
    set L₂ : (ℝ × Space) →L[ℝ] V :=
      ((fderivWithin ℝ D.h rightHalf w).comp (ContinuousLinearMap.inr ℝ ℝ Space)).comp
        (ContinuousLinearMap.snd ℝ ℝ Space) with L₂_def
    set L₃ : (ℝ × Space) →L[ℝ] V :=
      (ContinuousLinearMap.fst ℝ ℝ Space).smulRight (D.h w) with L₃_def
    have hsA : Summable fun k => D.c k * D.ψ 0 * (-(2 : ℝ) ^ k) := by
      have : (fun k => D.c k * D.ψ 0 * (-(2 : ℝ) ^ k)) =
          fun k => (-D.ψ 0) * (D.c k * (2 : ℝ) ^ k) := by
        funext k; ring
      rw [this]
      exact hcs.mul_left _
    have hsB : Summable fun k => D.c k * D.ψ 0 := D.summable_c.mul_right _
    have hsC : Summable fun k => D.c k * (-(2 : ℝ) ^ k) * deriv D.ψ 0 := by
      have : (fun k => D.c k * (-(2 : ℝ) ^ k) * deriv D.ψ 0) =
          fun k => (-deriv D.ψ 0) * (D.c k * (2 : ℝ) ^ k) := by
        funext k; ring
      rw [this]
      exact hcs.mul_left _
    have hdecomp : (fun k => D.termJet k z) = fun k =>
        (D.c k * D.ψ 0 * (-(2 : ℝ) ^ k)) • L₁ + (D.c k * D.ψ 0) • L₂ +
          (D.c k * (-(2 : ℝ) ^ k) * deriv D.ψ 0) • L₃ := by
      funext k
      have hGL : reflCLM k z = w := by
        rw [reflCLM_apply, hz1, mul_zero]
      have hcomp : ∀ v : ℝ × Space,
          ((fderivWithin ℝ D.h rightHalf w).comp (reflCLM k)) v =
            (-(2 : ℝ) ^ k) • (L₁ v) + L₂ v := by
        intro v
        have hsplit : (-(2 : ℝ) ^ k * v.1, v.2) =
            (-(2 : ℝ) ^ k * v.1) • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), v.2) := by
          ext <;> simp
        rw [ContinuousLinearMap.comp_apply, reflCLM_apply, hsplit, map_add, map_smul]
        have hL₁ : L₁ v = v.1 • fderivWithin ℝ D.h rightHalf w ((1 : ℝ), (0 : Space)) := by
          simp [L₁_def]
        have hL₂ : L₂ v = (fderivWithin ℝ D.h rightHalf w) ((0 : ℝ), v.2) := by
          simp [L₂_def]
        rw [hL₁, hL₂, smul_smul]
      have hsJ : D.scalarJet k z = (D.c k * (-(2 : ℝ) ^ k) * deriv D.ψ 0) •
          ContinuousLinearMap.fst ℝ ℝ Space := by rw [scalarJet, hGL, hw1]
      rw [termJet, hGL, hw1]
      have hcsm : (D.scalarJet k z).smulRight (D.h w) =
          (D.c k * (-(2 : ℝ) ^ k) * deriv D.ψ 0) • L₃ := by
        rw [hsJ]
        apply ContinuousLinearMap.ext
        intro v
        simp only [ContinuousLinearMap.smulRight_apply, FunLike.coe_smul,
          Pi.smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul]
        rw [show L₃ v = v.1 • D.h w from by simp [L₃_def]]
        rw [smul_smul]
      rw [hcsm]
      apply ContinuousLinearMap.ext
      intro v
      simp only [add_apply, FunLike.coe_smul, Pi.smul_apply]
      rw [hcomp v, smul_add, smul_smul]
    rw [hdecomp]
    exact ((ContinuousLinearMap.lsmul ℝ ℝ).flip L₁).summable hsA |>.add
      (((ContinuousLinearMap.lsmul ℝ ℝ).flip L₂).summable hsB) |>.add
      (((ContinuousLinearMap.lsmul ℝ ℝ).flip L₃).summable hsC)
  · -- interior: finite support
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (3 / |z.1|) one_lt_two
    apply summable_of_ne_finset_zero (s := Finset.range K)
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    apply D.termJet_eq_zero_of_two_lt
    have hpos : (0 : ℝ) < |z.1| := abs_pos.mpr hz1
    have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
    have h2k : (3 : ℝ) < (2 : ℝ) ^ k * |z.1| := by
      calc (3 : ℝ) = 3 / |z.1| * |z.1| := by field_simp
        _ < (2 : ℝ) ^ K * |z.1| := mul_lt_mul_of_pos_right hK hpos
        _ ≤ (2 : ℝ) ^ k * |z.1| := mul_le_mul_of_nonneg_right hpow hpos.le
    have hu : |(reflCLM k z).1| = (2 : ℝ) ^ k * |z.1| := by
      rw [reflCLM_apply]
      show |-(2 : ℝ) ^ k * z.1| = (2 : ℝ) ^ k * |z.1|
      rw [abs_mul, abs_neg, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hbig : (3 : ℝ) < |(reflCLM k z).1| := by rw [hu]; exact h2k
    have h := abs_sub_abs_le_abs_sub ((reflCLM k z).1) (1 : ℝ)
    rw [abs_one] at h
    linarith

/-- Uniform jet bound near `z₀`: on the compact strip each term jet is
bounded by `|c k| · 2^k · (C0·Ch1 + C1·Ch0)`. -/
theorem termJet_norm_le {D : SeriesData V} {z₀ z : ℝ × Space} (hzA : z ∈ leftHalf)
    (hz2 : z.2 ∈ Metric.closedBall z₀.2 1) {C0 C1 Ch0 Ch1 : ℝ}
    (hC0 : ∀ t : ℝ, |D.ψ t| ≤ C0) (hC1 : ∀ t : ℝ, |deriv D.ψ t| ≤ C1)
    (hCh0 : ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1, ‖D.h w‖ ≤ Ch0)
    (hCh1 : ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1,
      ‖fderivWithin ℝ D.h rightHalf w‖ ≤ Ch1)
    (hC0nn : 0 ≤ C0) (hC1nn : 0 ≤ C1) (hCh0nn : 0 ≤ Ch0) (hCh1nn : 0 ≤ Ch1)
    (k : ℕ) :
    ‖D.termJet k z‖ ≤ |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1 + C1 * Ch0) := by
  by_cases hs : 2 < |(reflCLM k z).1 - 1|
  · rw [D.termJet_eq_zero_of_two_lt hs, norm_zero]
    positivity
  · rw [not_lt] at hs
    have h1 : (0 : ℝ) ≤ (reflCLM k z).1 := (mapsTo_reflCLM_leftHalf k hzA).1
    have h3 : (reflCLM k z).1 ≤ 3 := by
      have h := abs_sub_abs_le_abs_sub ((reflCLM k z).1) (1 : ℝ)
      rw [abs_one] at h
      have ha : |(reflCLM k z).1| ≤ |(reflCLM k z).1 - 1| + 1 := by linarith
      rw [abs_of_nonneg h1] at ha
      linarith
    have hmem : reflCLM k z ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1 :=
      Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨h1, h3⟩,
        by rw [reflCLM_apply]; exact hz2⟩
    have hp1 : ‖(D.c k * D.ψ (reflCLM k z).1) •
          ((fderivWithin ℝ D.h rightHalf (reflCLM k z)).comp (reflCLM k))‖
        ≤ |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1) := by
      calc ‖(D.c k * D.ψ (reflCLM k z).1) •
            ((fderivWithin ℝ D.h rightHalf (reflCLM k z)).comp (reflCLM k))‖
          = |D.c k| * |D.ψ (reflCLM k z).1| *
            ‖(fderivWithin ℝ D.h rightHalf (reflCLM k z)).comp (reflCLM k)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul]
        _ ≤ |D.c k| * C0 * (Ch1 * (2 : ℝ) ^ k) := by
            have hcomp' : ‖(fderivWithin ℝ D.h rightHalf (reflCLM k z)).comp (reflCLM k)‖
                ≤ Ch1 * (2 : ℝ) ^ k :=
              le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
                (mul_le_mul (hCh1 _ hmem) (reflCLM_norm_le k) (by positivity) hCh1nn)
            have h3 : |D.c k| * |D.ψ (reflCLM k z).1| ≤ |D.c k| * C0 :=
              mul_le_mul_of_nonneg_left (hC0 _) (abs_nonneg _)
            exact mul_le_mul h3 hcomp' (norm_nonneg _)
              (mul_nonneg (abs_nonneg _) hC0nn)
        _ = |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1) := by ring
    have hp2 : ‖(D.scalarJet k z).smulRight (D.h (reflCLM k z))‖
        ≤ |D.c k| * (2 : ℝ) ^ k * (C1 * Ch0) := by
      have hfst : ‖ContinuousLinearMap.fst ℝ ℝ Space‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
          rw [one_mul]
          exact le_max_left _ _
      have hsj : ‖D.scalarJet k z‖ ≤
          |D.c k| * (2 : ℝ) ^ k * |deriv D.ψ (reflCLM k z).1| := by
        rw [scalarJet, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
          abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc |D.c k| * (2 : ℝ) ^ k * |deriv D.ψ (reflCLM k z).1| *
              ‖ContinuousLinearMap.fst ℝ ℝ Space‖
            ≤ |D.c k| * (2 : ℝ) ^ k * |deriv D.ψ (reflCLM k z).1| * 1 :=
              mul_le_mul_of_nonneg_left hfst (by positivity)
          _ = |D.c k| * (2 : ℝ) ^ k * |deriv D.ψ (reflCLM k z).1| := mul_one _
      calc ‖(D.scalarJet k z).smulRight (D.h (reflCLM k z))‖
          = ‖D.scalarJet k z‖ * ‖D.h (reflCLM k z)‖ :=
            ContinuousLinearMap.norm_smulRight_apply _ _
        _ ≤ (|D.c k| * (2 : ℝ) ^ k * |deriv D.ψ (reflCLM k z).1|) * Ch0 :=
            mul_le_mul hsj (hCh0 _ hmem) (norm_nonneg _) (by positivity)
        _ ≤ (|D.c k| * (2 : ℝ) ^ k * C1) * Ch0 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hC1 _) (by positivity)) hCh0nn
        _ = |D.c k| * (2 : ℝ) ^ k * (C1 * Ch0) := by ring
    rw [termJet]
    calc ‖(D.c k * D.ψ (reflCLM k z).1) •
            ((fderivWithin ℝ D.h rightHalf (reflCLM k z)).comp (reflCLM k)) +
          (D.scalarJet k z).smulRight (D.h (reflCLM k z))‖
        ≤ ‖(D.c k * D.ψ (reflCLM k z).1) •
            ((fderivWithin ℝ D.h rightHalf (reflCLM k z)).comp (reflCLM k))‖ +
          ‖(D.scalarJet k z).smulRight (D.h (reflCLM k z))‖ := norm_add_le _ _
      _ ≤ |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1) +
            |D.c k| * (2 : ℝ) ^ k * (C1 * Ch0) := add_le_add hp1 hp2
      _ = |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1 + C1 * Ch0) := by ring

/-- A uniform operator-norm bound for `fderivWithin ℝ D.h rightHalf` on the
compact strip `[0, 3] × closedBall x₀ 1`, mirroring `exists_h_bound`. -/
theorem exists_hjet_bound (D : SeriesData V) (x₀ : Space) :
    ∃ Ch : ℝ, ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall x₀ 1,
      ‖fderivWithin ℝ D.h rightHalf w‖ ≤ Ch := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall x₀ 1) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hsub : Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall x₀ 1 ⊆ rightHalf :=
    Set.prod_mono Set.Icc_subset_Ici_self (Set.subset_univ _)
  have hcont : ContinuousOn (fderivWithin ℝ D.h rightHalf)
      (Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall x₀ 1) :=
    (D.hh.continuousOn_fderivWithin uniqueDiffOn_rightHalf (by simp)).mono hsub
  exact hK.exists_bound_of_continuousOn hcont

/-- On the convex set `leftHalf ∩ closedBall z₀ 1`, a finite block of
consecutive term jets (starting at index `N`) differs from the same block at
`z₀` by at most twice the tail-jet weight sum `∑' i, |c (i+N)| 2^(i+N) J`. -/
theorem termJet_tail_jet_bound (D : SeriesData V) {z₀ : ℝ × Space}
    (hz₀ : z₀ ∈ leftHalf) {C0 C1 Ch0 Ch1 : ℝ}
    (hC0 : ∀ t : ℝ, |D.ψ t| ≤ C0) (hC1 : ∀ t : ℝ, |deriv D.ψ t| ≤ C1)
    (hCh0 : ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1, ‖D.h w‖ ≤ Ch0)
    (hCh1 : ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1,
      ‖fderivWithin ℝ D.h rightHalf w‖ ≤ Ch1)
    (hC0nn : 0 ≤ C0) (hC1nn : 0 ≤ C1) (hCh0nn : 0 ≤ Ch0) (hCh1nn : 0 ≤ Ch1)
    (N : ℕ)
    (hq_tail : Summable fun k => |D.c (k + N)| * (2 : ℝ) ^ (k + N) *
      (C0 * Ch1 + C1 * Ch0))
    (M : ℕ) (w : ℝ × Space) (hw : w ∈ leftHalf ∩ Metric.closedBall z₀ 1) :
    ‖(∑ k ∈ Finset.range M, D.termJet (k + N) w)
      - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀)‖
      ≤ 2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0)) := by
  have hqnn : ∀ k, 0 ≤ |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1 + C1 * Ch0) := fun k =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num) _))
      (add_nonneg (mul_nonneg hC0nn hCh1nn) (mul_nonneg hC1nn hCh0nn))
  have h2ball : w.2 ∈ Metric.closedBall z₀.2 1 := by
    have hww := Set.inter_subset_right hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hww
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖w.2 - z₀.2‖ = ‖(w - z₀).2‖ := rfl
      _ ≤ ‖w - z₀‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ 1 := hww
  have hjetw : ∀ k, ‖D.termJet k w‖ ≤ |D.c k| * (2 : ℝ) ^ k *
      (C0 * Ch1 + C1 * Ch0) := fun k =>
    D.termJet_norm_le (Set.inter_subset_left hw) h2ball hC0 hC1 hCh0 hCh1
      hC0nn hC1nn hCh0nn hCh1nn k
  have hz₀j : ∀ k, ‖D.termJet k z₀‖ ≤ |D.c k| * (2 : ℝ) ^ k *
      (C0 * Ch1 + C1 * Ch0) := fun k =>
    D.termJet_norm_le hz₀ (Metric.mem_closedBall_self (by norm_num)) hC0 hC1
      hCh0 hCh1 hC0nn hC1nn hCh0nn hCh1nn k
  have h1 : ‖∑ k ∈ Finset.range M, D.termJet (k + N) w‖
      ≤ ∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0) := by
    calc ‖∑ k ∈ Finset.range M, D.termJet (k + N) w‖
        ≤ ∑ k ∈ Finset.range M, ‖D.termJet (k + N) w‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range M, |D.c (k + N)| * (2 : ℝ) ^ (k + N) *
          (C0 * Ch1 + C1 * Ch0) := Finset.sum_le_sum fun k _ => hjetw (k + N)
      _ ≤ ∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0) :=
          sum_le_hasSum _ (fun i _ => hqnn (i + N)) hq_tail.hasSum
  have h2 : ‖∑ k ∈ Finset.range M, D.termJet (k + N) z₀‖
      ≤ ∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0) := by
    calc ‖∑ k ∈ Finset.range M, D.termJet (k + N) z₀‖
        ≤ ∑ k ∈ Finset.range M, ‖D.termJet (k + N) z₀‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range M, |D.c (k + N)| * (2 : ℝ) ^ (k + N) *
          (C0 * Ch1 + C1 * Ch0) := Finset.sum_le_sum fun k _ => hz₀j (k + N)
      _ ≤ ∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0) :=
          sum_le_hasSum _ (fun i _ => hqnn (i + N)) hq_tail.hasSum
  calc ‖(∑ k ∈ Finset.range M, D.termJet (k + N) w)
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀)‖
      ≤ ‖∑ k ∈ Finset.range M, D.termJet (k + N) w‖
        + ‖∑ k ∈ Finset.range M, D.termJet (k + N) z₀‖ := norm_sub_le _ _
    _ ≤ (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0))
        + (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0)) :=
        add_le_add h1 h2
    _ = 2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0)) :=
        (two_mul _).symm

/-- A finite partial tail of the Seeley series, minus its jet at `z₀` applied,
is Fréchet differentiable on `leftHalf ∩ closedBall z₀ 1` with the expected
jet difference. -/
theorem hasFDerivWithinAt_term_tail_partial (D : SeriesData V) (z₀ : ℝ × Space)
    (N M : ℕ) (w : ℝ × Space) (hw : w ∈ leftHalf ∩ Metric.closedBall z₀ 1) :
    HasFDerivWithinAt
      (fun u => (∑ k ∈ Finset.range M, D.term (k + N)) u
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) u)
      ((∑ k ∈ Finset.range M, D.termJet (k + N) w)
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀))
      (leftHalf ∩ Metric.closedBall z₀ 1) w := by
  apply HasFDerivWithinAt.sub
  · exact (HasFDerivWithinAt.sum (fun k _ =>
      D.hasFDerivWithinAt_term (k + N) w (Set.inter_subset_left hw))).mono
      Set.inter_subset_left
  · exact (∑ k ∈ Finset.range M,
      D.termJet (k + N) z₀).hasFDerivAt.hasFDerivWithinAt

/-- The mean value theorem applied to a finite partial tail of the Seeley
series on the convex set `leftHalf ∩ closedBall z₀ 1`: the partial tail minus
its jet at `z₀` is Lipschitz with the supplied jet-difference bound. The
differentiability and jet-bound facts are taken as hypotheses so this
declaration carries no large unification obligations of its own. -/
theorem series_tail_res_partial_le (D : SeriesData V) (z₀ : ℝ × Space) (N M : ℕ)
    (S : ℝ) (z : ℝ × Space)
    (hf : ∀ w ∈ leftHalf ∩ Metric.closedBall z₀ 1,
      HasFDerivWithinAt
        (fun u => (∑ k ∈ Finset.range M, D.term (k + N)) u
          - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) u)
        ((∑ k ∈ Finset.range M, D.termJet (k + N) w)
          - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀))
        (leftHalf ∩ Metric.closedBall z₀ 1) w)
    (hb : ∀ w ∈ leftHalf ∩ Metric.closedBall z₀ 1,
      ‖(∑ k ∈ Finset.range M, D.termJet (k + N) w)
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀)‖ ≤ S)
    (hz₀B : z₀ ∈ leftHalf ∩ Metric.closedBall z₀ 1)
    (hzB : z ∈ leftHalf ∩ Metric.closedBall z₀ 1) :
    ‖((∑ k ∈ Finset.range M, D.term (k + N)) z
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) z)
      - ((∑ k ∈ Finset.range M, D.term (k + N)) z₀
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) z₀)‖
      ≤ S * ‖z - z₀‖ := by
  have hconvB : Convex ℝ (leftHalf ∩ Metric.closedBall z₀ 1) :=
    ((convex_Iic (0 : ℝ)).prod convex_univ).inter (convex_closedBall z₀ 1)
  exact hconvB.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hb hz₀B hzB

/-- The finite partial tails of the Seeley series minus the tail jet at
`z₀`, evaluated at a fixed point `u`, converge to the difference of the
infinite tail and the infinite tail jet applied at `u`. -/
theorem series_tail_tendsto_apply (D : SeriesData V) (N : ℕ) (z₀ u : ℝ × Space) :
    Tendsto (fun M => (∑ k ∈ Finset.range M, D.term (k + N)) u
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) u)
      atTop (𝓝 ((∑' k, D.term (k + N) u)
        - (∑' k, D.termJet (k + N) z₀) u)) := by
  have hs1 : Summable fun k => D.term (k + N) u :=
    (summable_nat_add_iff N).mpr (D.summable_term u)
  have hs2 : Summable fun k => D.termJet (k + N) z₀ :=
    (summable_nat_add_iff N).mpr (D.summable_termJet z₀)
  have h1 : Tendsto (fun M => (∑ k ∈ Finset.range M, D.term (k + N)) u) atTop
      (𝓝 (∑' k, D.term (k + N) u)) :=
    (hs1.hasSum.tendsto_sum_nat).congr fun M => (Finset.sum_apply _ _ _).symm
  have h2 : Tendsto (fun M => (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) u)
      atTop (𝓝 ((∑' k, D.termJet (k + N) z₀) u)) := by
    have h := ((ContinuousLinearMap.apply ℝ V u).continuous.tendsto
        (∑' k, D.termJet (k + N) z₀)).comp hs2.hasSum.tendsto_sum_nat
    rw [ContinuousLinearMap.apply_apply] at h
    exact h
  exact h1.sub h2

/-- The tail of the Seeley series past index `N` satisfies a Lipschitz-type
residual bound against the tail jet, with constant twice the tail-jet weight
sum. Proved by passing the finite partial bound
`series_tail_res_partial_le` to the limit `M → ∞`. -/
theorem series_tail_res_le (D : SeriesData V) {z₀ : ℝ × Space}
    (hz₀ : z₀ ∈ leftHalf) {C0 C1 Ch0 Ch1 : ℝ}
    (hC0 : ∀ t : ℝ, |D.ψ t| ≤ C0) (hC1 : ∀ t : ℝ, |deriv D.ψ t| ≤ C1)
    (hCh0 : ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1, ‖D.h w‖ ≤ Ch0)
    (hCh1 : ∀ w ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1,
      ‖fderivWithin ℝ D.h rightHalf w‖ ≤ Ch1)
    (hC0nn : 0 ≤ C0) (hC1nn : 0 ≤ C1) (hCh0nn : 0 ≤ Ch0) (hCh1nn : 0 ≤ Ch1)
    (N : ℕ)
    (hq_tail : Summable fun k => |D.c (k + N)| * (2 : ℝ) ^ (k + N) *
      (C0 * Ch1 + C1 * Ch0))
    (z : ℝ × Space) (hzB : z ∈ leftHalf ∩ Metric.closedBall z₀ 1) :
    ‖(∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
      - (∑' k, D.termJet (k + N) z₀) (z - z₀)‖
      ≤ (2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0)))
        * ‖z - z₀‖ := by
  have hMVT : ∀ M, ‖((∑ k ∈ Finset.range M, D.term (k + N)) z
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) z)
      - ((∑ k ∈ Finset.range M, D.term (k + N)) z₀
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) z₀)‖
      ≤ (2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0)))
        * ‖z - z₀‖ := fun M =>
    D.series_tail_res_partial_le z₀ N M
      (2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0))) z
      (fun w hw => D.hasFDerivWithinAt_term_tail_partial z₀ N M w hw)
      (fun w hw => D.termJet_tail_jet_bound hz₀ hC0 hC1 hCh0 hCh1
        hC0nn hC1nn hCh0nn hCh1nn N hq_tail M w hw)
      ⟨hz₀, Metric.mem_closedBall_self (by norm_num)⟩ hzB
  have hlimz : Tendsto (fun M => (∑ k ∈ Finset.range M, D.term (k + N)) z
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) z)
      atTop (𝓝 ((∑' k, D.term (k + N) z)
        - (∑' k, D.termJet (k + N) z₀) z)) :=
    D.series_tail_tendsto_apply N z₀ z
  have hlimz₀ : Tendsto (fun M => (∑ k ∈ Finset.range M, D.term (k + N)) z₀
        - (∑ k ∈ Finset.range M, D.termJet (k + N) z₀) z₀)
      atTop (𝓝 ((∑' k, D.term (k + N) z₀)
        - (∑' k, D.termJet (k + N) z₀) z₀)) :=
    D.series_tail_tendsto_apply N z₀ z₀
  have hnorm := (hlimz.sub hlimz₀).norm
  have hT_le := le_of_tendsto_of_tendsto hnorm tendsto_const_nhds
    (Filter.Eventually.of_forall hMVT)
  have hT_eq : ((∑' k, D.term (k + N) z) - (∑' k, D.termJet (k + N) z₀) z)
      - ((∑' k, D.term (k + N) z₀) - (∑' k, D.termJet (k + N) z₀) z₀)
      = (∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
        - (∑' k, D.termJet (k + N) z₀) (z - z₀) := by
    rw [ContinuousLinearMap.map_sub]; abel
  rwa [hT_eq] at hT_le

/-- The Seeley reflection series has a Fréchet derivative within the left
half-space at every point of it, given by the termwise jet series. Proof:
split the series at an index `N` chosen so the tail-jet weight sum is `< ε/8`;
the finite head contributes a little-`o` head residual by
`hasFDerivWithinAt_term`; the tail residual is bounded by `2·S·‖z − z₀‖` via
`series_tail_res_le`. -/
theorem hasFDerivWithinAt_series (D : SeriesData V) {z₀ : ℝ × Space}
    (hz₀ : z₀ ∈ leftHalf) :
    HasFDerivWithinAt D.series (∑' k, D.termJet k z₀) leftHalf z₀ := by
  obtain ⟨C0, hC0i⟩ := D.hψb 0
  have hC0 : ∀ t : ℝ, |D.ψ t| ≤ C0 := by simpa [iteratedDeriv_zero] using hC0i
  obtain ⟨C1, hC1i⟩ := D.hψb 1
  have hC1 : ∀ t : ℝ, |deriv D.ψ t| ≤ C1 := by simpa [iteratedDeriv_one] using hC1i
  obtain ⟨Ch0, hCh0⟩ := D.exists_h_bound z₀.2
  obtain ⟨Ch1, hCh1⟩ := D.exists_hjet_bound z₀.2
  have hC0nn : 0 ≤ C0 := le_trans (abs_nonneg _) (hC0 0)
  have hC1nn : 0 ≤ C1 := le_trans (abs_nonneg _) (hC1 0)
  have hw₀ : ((1 : ℝ), z₀.2) ∈ Set.Icc (0 : ℝ) 3 ×ˢ Metric.closedBall z₀.2 1 :=
    ⟨⟨by norm_num, by norm_num⟩, Metric.mem_closedBall_self (by norm_num)⟩
  have hCh0nn : 0 ≤ Ch0 := le_trans (norm_nonneg _) (hCh0 _ hw₀)
  have hCh1nn : 0 ≤ Ch1 := le_trans (norm_nonneg _) (hCh1 _ hw₀)
  have hJnn : 0 ≤ C0 * Ch1 + C1 * Ch0 :=
    add_nonneg (mul_nonneg hC0nn hCh1nn) (mul_nonneg hC1nn hCh0nn)
  have hqnn : ∀ k, 0 ≤ |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1 + C1 * Ch0) := fun k =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num) _)) hJnn
  have hbase : Summable fun k => |D.c k| * (2 : ℝ) ^ k := by simpa using D.hc 1
  have hq : Summable fun k => |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1 + C1 * Ch0) :=
    hbase.mul_right _
  have hS : Tendsto
      (fun K => ∑' i, |D.c (i + K)| * (2 : ℝ) ^ (i + K) * (C0 * Ch1 + C1 * Ch0))
      atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun k => |D.c k| * (2 : ℝ) ^ k * (C0 * Ch1 + C1 * Ch0))
  rw [hasFDerivWithinAt_iff_tendsto, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hS (ε / 8) (by positivity)
  have hSnn : 0 ≤ ∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0) :=
    tsum_nonneg fun i => hqnn (i + N)
  have hKN : ∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0)
      < ε / 8 := by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hSnn] at h
  have hHead : HasFDerivWithinAt (∑ k ∈ Finset.range N, D.term k)
      (∑ k ∈ Finset.range N, D.termJet k z₀) leftHalf z₀ :=
    HasFDerivWithinAt.sum (fun k _ => D.hasFDerivWithinAt_term k z₀ hz₀)
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (hasFDerivWithinAt_iff_tendsto.mp hHead) (ε / 2) (by positivity)
  have hq_tail : Summable fun k => |D.c (k + N)| * (2 : ℝ) ^ (k + N) *
      (C0 * Ch1 + C1 * Ch0) := (summable_nat_add_iff N).mpr hq
  refine ⟨min δ₁ 1, lt_min hδ₁ one_pos, ?_⟩
  intro z hz hdist
  have hdist₁ : dist z z₀ < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hzB : z ∈ leftHalf ∩ Metric.closedBall z₀ 1 :=
    ⟨hz, Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hdist
      (min_le_right _ _)))⟩
  by_cases hzz : z = z₀
  · subst hzz
    simp only [sub_self, norm_zero, inv_zero, zero_mul, dist_self]
    exact hε
  · have hnorm_pos : 0 < ‖z - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
    have hjet_id : (∑' k, D.termJet k z₀)
        = (∑ k ∈ Finset.range N, D.termJet k z₀) + ∑' k, D.termJet (k + N) z₀ :=
      ((D.summable_termJet z₀).sum_add_tsum_nat_add N).symm
    have hJ0 : (∑' k, D.termJet k z₀) (z - z₀)
        = (∑ k ∈ Finset.range N, D.termJet k z₀) (z - z₀)
          + (∑' k, D.termJet (k + N) z₀) (z - z₀) := by
      rw [hjet_id, add_apply]
    have hsum_id : ∀ u, D.series u = (∑ k ∈ Finset.range N, D.term k u)
        + ∑' k, D.term (k + N) u := fun u =>
      ((D.summable_term u).sum_add_tsum_nat_add N).symm
    have hR : D.series z - D.series z₀ - (∑' k, D.termJet k z₀) (z - z₀)
        = ((∑ k ∈ Finset.range N, D.term k) z - (∑ k ∈ Finset.range N, D.term k) z₀
            - (∑ k ∈ Finset.range N, D.termJet k z₀) (z - z₀))
          + ((∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
            - (∑' k, D.termJet (k + N) z₀) (z - z₀)) := by
      rw [Finset.sum_apply, Finset.sum_apply, hJ0, hsum_id z, hsum_id z₀]; abel
    have hh2 : ‖z - z₀‖⁻¹ * ‖(∑ k ∈ Finset.range N, D.term k) z
        - (∑ k ∈ Finset.range N, D.term k) z₀
        - (∑ k ∈ Finset.range N, D.termJet k z₀) (z - z₀)‖ < ε / 2 := by
      have h := hδ₁' hz hdist₁
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg
        (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))] at h
    have ht2 : ‖z - z₀‖⁻¹ * ‖(∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
        - (∑' k, D.termJet (k + N) z₀) (z - z₀)‖
        ≤ 2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) * (C0 * Ch1 + C1 * Ch0)) := by
      have h := D.series_tail_res_le hz₀ hC0 hC1 hCh0 hCh1 hC0nn hC1nn hCh0nn
        hCh1nn N hq_tail z hzB
      calc ‖z - z₀‖⁻¹ * ‖(∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
            - (∑' k, D.termJet (k + N) z₀) (z - z₀)‖
          ≤ ‖z - z₀‖⁻¹ * ((2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) *
            (C0 * Ch1 + C1 * Ch0))) * ‖z - z₀‖) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))
        _ = 2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) *
            (C0 * Ch1 + C1 * Ch0)) := by
            rw [mul_comm (2 * (∑' i, |D.c (i + N)| * (2 : ℝ) ^ (i + N) *
              (C0 * Ch1 + C1 * Ch0))) _, ← mul_assoc,
              inv_mul_cancel₀ (ne_of_gt hnorm_pos), one_mul]
    have hquot : ‖z - z₀‖⁻¹ * ‖D.series z - D.series z₀
        - (∑' k, D.termJet k z₀) (z - z₀)‖
        ≤ ‖z - z₀‖⁻¹ * ‖(∑ k ∈ Finset.range N, D.term k) z
            - (∑ k ∈ Finset.range N, D.term k) z₀
            - (∑ k ∈ Finset.range N, D.termJet k z₀) (z - z₀)‖
          + ‖z - z₀‖⁻¹ * ‖(∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
            - (∑' k, D.termJet (k + N) z₀) (z - z₀)‖ := by
      rw [hR]
      calc ‖z - z₀‖⁻¹ * ‖((∑ k ∈ Finset.range N, D.term k) z
              - (∑ k ∈ Finset.range N, D.term k) z₀
              - (∑ k ∈ Finset.range N, D.termJet k z₀) (z - z₀))
            + ((∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
              - (∑' k, D.termJet (k + N) z₀) (z - z₀))‖
          ≤ ‖z - z₀‖⁻¹ * (‖(∑ k ∈ Finset.range N, D.term k) z
              - (∑ k ∈ Finset.range N, D.term k) z₀
              - (∑ k ∈ Finset.range N, D.termJet k z₀) (z - z₀)‖
            + ‖(∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
              - (∑' k, D.termJet (k + N) z₀) (z - z₀)‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _)
              (inv_nonneg.mpr (norm_nonneg _))
        _ = ‖z - z₀‖⁻¹ * ‖(∑ k ∈ Finset.range N, D.term k) z
              - (∑ k ∈ Finset.range N, D.term k) z₀
              - (∑ k ∈ Finset.range N, D.termJet k z₀) (z - z₀)‖
            + ‖z - z₀‖⁻¹ * ‖(∑' k, D.term (k + N) z) - (∑' k, D.term (k + N) z₀)
              - (∑' k, D.termJet (k + N) z₀) (z - z₀)‖ := mul_add _ _ _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
    linarith [hquot, hh2, ht2, hKN, hε]

/-! ### W5: class-closure — the series is within-smooth at every order

The termwise jet series reassembles into the series of three *derived*
packages (`derived₁`: the derivative cutoff with scaled coefficients on the
same field; `derived₂`: the `(1,0)`-directional jet values with the same
cutoff and scaled coefficients; `derived₃`: the inr-composed jet values with
the same cutoff and coefficients), each of which is again a `SeriesData`.
Induction on the smoothness order then gives `ContDiffOn ℝ ∞ D.series
leftHalf`. -/

/-- The derivative of the cutoff inherits the support vanishing: `ψ'`
vanishes wherever `2 ≤ |s − 1|`. -/
theorem hψsupp_deriv (D : SeriesData V) (s : ℝ) (hs : 2 ≤ |s - 1|) :
    deriv D.ψ s = 0 := by
  have hdψ : Differentiable ℝ D.ψ := D.hψ.differentiable (by simp)
  rcases lt_or_eq_of_le hs with h | h
  · have hop : IsOpen {t : ℝ | (2:ℝ) < |t - 1|} :=
      isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
    have hev : ∀ᶠ t in 𝓝 s, D.ψ t = 0 := by
      filter_upwards [hop.eventually_mem h] with t ht
      exact D.hψsupp t (le_of_lt ht)
    have heq : D.ψ =ᶠ[𝓝 s] (0 : ℝ → ℝ) := hev
    rw [heq.deriv_eq]
    show deriv (fun _ => (0:ℝ)) s = 0
    exact deriv_const _ _
  · rcases lt_or_ge (s - 1) 0 with hsgn | hsgn
    · rw [abs_of_neg hsgn] at h
      have hs1 : s = -1 := by linarith
      subst hs1
      have heq : D.ψ =ᶠ[𝓝[Set.Iic (-1)] (-1)] (0 : ℝ → ℝ) := by
        apply eventuallyEq_nhdsWithin_of_eqOn
        intro t ht
        simp only [Set.mem_Iic] at ht
        exact D.hψsupp t (by rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]; linarith)
      have hdw : derivWithin D.ψ (Set.Iic (-1)) (-1) =
          derivWithin (0 : ℝ → ℝ) (Set.Iic (-1)) (-1) :=
        heq.derivWithin_eq (D.hψsupp (-1) (by norm_num))
      have hd0 : derivWithin (0 : ℝ → ℝ) (Set.Iic (-1)) (-1) = 0 := by simp
      rw [← (hdψ (-1)).derivWithin (uniqueDiffWithinAt_Iic (-1)), hdw, hd0]
    · rw [abs_of_nonneg hsgn] at h
      have hs3 : s = 3 := by linarith
      subst hs3
      have heq : D.ψ =ᶠ[𝓝[Set.Ici 3] 3] (0 : ℝ → ℝ) := by
        apply eventuallyEq_nhdsWithin_of_eqOn
        intro t ht
        simp only [Set.mem_Ici] at ht
        exact D.hψsupp t (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - 1)]; linarith)
      have hdw : derivWithin D.ψ (Set.Ici 3) 3 = derivWithin (0 : ℝ → ℝ) (Set.Ici 3) 3 :=
        heq.derivWithin_eq (D.hψsupp 3 (by norm_num))
      have hd0 : derivWithin (0 : ℝ → ℝ) (Set.Ici 3) 3 = 0 := by simp
      rw [← (hdψ 3).derivWithin (uniqueDiffWithinAt_Ici 3), hdw, hd0]

/-- The derivative of the cutoff is smooth. -/
theorem hψ_deriv_contDiff (D : SeriesData V) : ContDiff ℝ ∞ (deriv D.ψ) := by
  rw [← iteratedDeriv_one]
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [iteratedDeriv_one, ← iteratedDeriv_succ']
  exact D.hψ.differentiable_iteratedDeriv (m+1) (by exact_mod_cast WithTop.coe_lt_top (m+1))

/-- Every iterated derivative of `deriv ψ` is bounded (shift of `hψb`). -/
theorem hψb_deriv (D : SeriesData V) (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv n (deriv D.ψ) t| ≤ C := by
  rw [← iteratedDeriv_succ']
  exact D.hψb (n+1)

/-- The scaled coefficients `k ↦ (−2^k) · c k` inherit super-polynomial
decay. -/
theorem hc_smul_pow (D : SeriesData V) (m : ℕ) :
    Summable fun k => |(-(2:ℝ)^k) * D.c k| * (2:ℝ)^(k*m) := by
  have h := D.hc (m + 1)
  have heq : (fun k => |(-(2:ℝ)^k) * D.c k| * (2:ℝ)^(k*m)) =
      fun k => |D.c k| * (2:ℝ)^(k*(m+1)) := by
    funext k
    rw [abs_mul, abs_neg, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      show k*(m+1) = k*m + k from by ring, pow_add]
    ring
  rwa [heq]

/-- First derived package: same field, derivative cutoff, scaled
coefficients.  Its series carries the `ψ'`-piece of the termwise jets. -/
def derived₁ (D : SeriesData V) : SeriesData V where
  h := D.h
  hh := D.hh
  ψ := deriv D.ψ
  hψ := D.hψ_deriv_contDiff
  hψsupp := D.hψsupp_deriv
  hψb := D.hψb_deriv
  c := fun k => (-(2:ℝ)^k) * D.c k
  hc := fun m => D.hc_smul_pow m

/-- Second derived package: the `(1,0)`-directional jet values, same cutoff,
scaled coefficients.  Its series carries the first-coordinate reflection
piece of the termwise jets. -/
def derived₂ (D : SeriesData V) : SeriesData V where
  h := fun w => (fderivWithin ℝ D.h rightHalf w) ((1:ℝ), (0:Space))
  hh := by
    have hfd : ContDiffOn ℝ ∞ (fderivWithin ℝ D.h rightHalf) rightHalf :=
      D.hh.fderivWithin uniqueDiffOn_rightHalf (by simp)
    exact hfd.clm_apply contDiffOn_const
  ψ := D.ψ
  hψ := D.hψ
  hψsupp := D.hψsupp
  hψb := D.hψb
  c := fun k => (-(2:ℝ)^k) * D.c k
  hc := fun m => D.hc_smul_pow m

/-- Third derived package: the inr-composed jet values, same cutoff and
coefficients.  Its series carries the spatial-direction piece of the
termwise jets. -/
def derived₃ (D : SeriesData V) : SeriesData (Space →L[ℝ] V) where
  h := fun w => (fderivWithin ℝ D.h rightHalf w).comp (ContinuousLinearMap.inr ℝ ℝ Space)
  hh := by
    have hfd : ContDiffOn ℝ ∞ (fderivWithin ℝ D.h rightHalf) rightHalf :=
      D.hh.fderivWithin uniqueDiffOn_rightHalf (by simp)
    exact hfd.clm_comp contDiffOn_const
  ψ := D.ψ
  hψ := D.hψ
  hψsupp := D.hψsupp
  hψb := D.hψb
  c := D.c
  hc := D.hc

/-- The termwise jet splits across the three derived packages, term by
term. -/
theorem termJet_eq_derived (D : SeriesData V) (k : ℕ) (z u : ℝ × Space) :
    D.termJet k z u =
      u.1 • D.derived₁.term k z +
        (u.1 • D.derived₂.term k z + D.derived₃.term k z u.2) := by
  have hfu : (ContinuousLinearMap.fst ℝ ℝ Space) u = u.1 := rfl
  have hsu : (ContinuousLinearMap.snd ℝ ℝ Space) u = u.2 := rfl
  have hdecomp : (-(2:ℝ)^k * u.1, u.2) = (-(2:ℝ)^k * u.1) • ((1:ℝ), (0:Space)) +
      ((0:ℝ), u.2) := by
    ext <;> simp
  have h1 : D.derived₁.term k z =
      ((-(2:ℝ)^k) * D.c k * deriv D.ψ (-(2:ℝ)^k * z.1)) •
        D.h (-(2:ℝ)^k * z.1, z.2) := rfl
  have h2 : D.derived₂.term k z =
      ((-(2:ℝ)^k) * D.c k * D.ψ (-(2:ℝ)^k * z.1)) •
        (fderivWithin ℝ D.h rightHalf (-(2:ℝ)^k * z.1, z.2)) ((1:ℝ), (0:Space)) := rfl
  have h3 : D.derived₃.term k z =
      (D.c k * D.ψ (-(2:ℝ)^k * z.1)) •
        (fderivWithin ℝ D.h rightHalf (-(2:ℝ)^k * z.1, z.2)).comp
          (ContinuousLinearMap.inr ℝ ℝ Space) := rfl
  rw [h1, h2, h3]
  simp only [termJet, scalarJet, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, reflCLM_apply, smul_apply, hfu, smul_eq_mul,
    add_apply, ContinuousLinearMap.inr_apply]
  rw [hdecomp, map_add, map_smul]
  generalize D.h (-(2:ℝ)^k * z.1, z.2) = hw
  generalize (fderivWithin ℝ D.h rightHalf (-(2:ℝ)^k * z.1, z.2)) ((1:ℝ), (0:Space)) = J10
  generalize (fderivWithin ℝ D.h rightHalf (-(2:ℝ)^k * z.1, z.2)) ((0:ℝ), u.2) = J02
  generalize D.c k = c'
  generalize D.ψ (-(2:ℝ)^k * z.1) = q
  generalize deriv D.ψ (-(2:ℝ)^k * z.1) = q'
  module

/-- Applying a tsum of continuous linear maps pointwise commutes with the
tsum. Stated with an opaque summand so elaboration never unfolds the
(concrete, large) summand during higher-order unification. -/
theorem tsum_apply_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → E →L[ℝ] V} (hF : Summable F) (x : E) :
    (∑' k, F k) x = ∑' k, F k x :=
  (ContinuousLinearMap.apply ℝ V x).map_tsum hF

/-- Pointwise summability of a summable family of continuous linear maps. -/
theorem summable_apply_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → E →L[ℝ] V} (hF : Summable F) (x : E) :
    Summable fun k => F k x :=
  (ContinuousLinearMap.apply ℝ V x).summable hF

/-- Constant scalar multiples preserve summability. -/
theorem summable_smul_const {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℕ → W} (hF : Summable F) (b : ℝ) :
    Summable fun k => b • F k :=
  hF.const_smul b

/-- A constant scalar pulls out of a tsum. -/
theorem tsum_smul_const {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℕ → W} (hF : Summable F) (b : ℝ) :
    ∑' k, b • F k = b • ∑' k, F k :=
  hF.tsum_const_smul b

/-- Tsums add termwise for summable families. -/
theorem tsum_add' {W : Type*} [NormedAddCommGroup W] {F G : ℕ → W}
    (hF : Summable F) (hG : Summable G) :
    ∑' k, (F k + G k) = ∑' k, F k + ∑' k, G k :=
  hF.tsum_add hG

/-- The termwise jet series reassembles into the three derived series. -/
theorem tsum_termJet (D : SeriesData V) (z : ℝ × Space) :
    ∑' k, D.termJet k z =
      (ContinuousLinearMap.fst ℝ ℝ Space).smulRight (D.derived₁.series z) +
        ((ContinuousLinearMap.fst ℝ ℝ Space).smulRight (D.derived₂.series z) +
          (D.derived₃.series z).comp (ContinuousLinearMap.snd ℝ ℝ Space)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hfu : (ContinuousLinearMap.fst ℝ ℝ Space) u = u.1 := rfl
  have hsu : (ContinuousLinearMap.snd ℝ ℝ Space) u = u.2 := rfl
  have happly : (∑' k, D.termJet k z) u = ∑' k, D.termJet k z u :=
    tsum_apply_clm (D.summable_termJet z) u
  have happly3 : (∑' k, D.derived₃.term k z) u.2 = ∑' k, D.derived₃.term k z u.2 :=
    tsum_apply_clm (D.derived₃.summable_term z) u.2
  have hf1 : Summable fun k => u.1 • D.derived₁.term k z :=
    summable_smul_const (D.derived₁.summable_term z) u.1
  have hf2 : Summable fun k => u.1 • D.derived₂.term k z :=
    summable_smul_const (D.derived₂.summable_term z) u.1
  have hf3 : Summable fun k => D.derived₃.term k z u.2 :=
    summable_apply_clm (D.derived₃.summable_term z) u.2
  have step1 : (∑' k, D.termJet k z) u =
      ∑' k, (u.1 • D.derived₁.term k z +
        (u.1 • D.derived₂.term k z + D.derived₃.term k z u.2)) := by
    rw [happly]
    exact tsum_congr fun k => D.termJet_eq_derived k z u
  have step2 : ∑' k, (u.1 • D.derived₁.term k z +
        (u.1 • D.derived₂.term k z + D.derived₃.term k z u.2)) =
      u.1 • ∑' k, D.derived₁.term k z +
        (u.1 • ∑' k, D.derived₂.term k z + ∑' k, D.derived₃.term k z u.2) := by
    rw [tsum_add' hf1 (hf2.add hf3), tsum_add' hf2 hf3,
      tsum_smul_const (D.derived₁.summable_term z) u.1,
      tsum_smul_const (D.derived₂.summable_term z) u.1]
  have step3 : u.1 • ∑' k, D.derived₁.term k z +
        (u.1 • ∑' k, D.derived₂.term k z + ∑' k, D.derived₃.term k z u.2) =
      ((ContinuousLinearMap.fst ℝ ℝ Space).smulRight (D.derived₁.series z) +
        ((ContinuousLinearMap.fst ℝ ℝ Space).smulRight (D.derived₂.series z) +
          (D.derived₃.series z).comp (ContinuousLinearMap.snd ℝ ℝ Space))) u := by
    rw [← happly3]
    show u.1 • D.derived₁.series z +
        (u.1 • D.derived₂.series z + (D.derived₃.series z) u.2) = _
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, hfu, hsu]
  exact (step1.trans step2).trans step3


/-- The assembled jet function: the series of the termwise jets, packaged
via the three derived series. -/
def seriesJet (D : SeriesData V) (z : ℝ × Space) : (ℝ × Space) →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ ℝ Space).smulRight (D.derived₁.series z) +
    ((ContinuousLinearMap.fst ℝ ℝ Space).smulRight (D.derived₂.series z) +
      (D.derived₃.series z).comp (ContinuousLinearMap.snd ℝ ℝ Space))

/-- The within-derivative of the series is the assembled jet. -/
theorem fderivWithin_series_eq_seriesJet (D : SeriesData V) {z : ℝ × Space}
    (hz : z ∈ leftHalf) :
    fderivWithin ℝ D.series leftHalf z = D.seriesJet z := by
  rw [(D.hasFDerivWithinAt_series hz).fderivWithin (uniqueDiffOn_leftHalf z hz)]
  exact D.tsum_termJet z

/-- The assembled jet is within-`C^n` whenever the three derived series
are. -/
theorem contDiffOn_seriesJet (D : SeriesData V) (n : ℕ)
    (ih1 : ContDiffOn ℝ n D.derived₁.series leftHalf)
    (ih2 : ContDiffOn ℝ n D.derived₂.series leftHalf)
    (ih3 : ContDiffOn ℝ n D.derived₃.series leftHalf) :
    ContDiffOn ℝ n D.seriesJet leftHalf := by
  show ContDiffOn ℝ n (fun z => (ContinuousLinearMap.fst ℝ ℝ Space).smulRight
      (D.derived₁.series z) +
    ((ContinuousLinearMap.fst ℝ ℝ Space).smulRight (D.derived₂.series z) +
      (D.derived₃.series z).comp (ContinuousLinearMap.snd ℝ ℝ Space))) leftHalf
  exact (contDiffOn_const.smulRight ih1).add
    ((contDiffOn_const.smulRight ih2).add (ih3.clm_comp contDiffOn_const))

/-- The reflection series is within-`C^n` on the left half-space at every
finite order, by induction on the order over the derived packages. -/
theorem contDiffOn_series_nat (n : ℕ) :
    ∀ {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (D : SeriesData V),
      ContDiffOn ℝ n D.series leftHalf := by
  induction n with
  | zero =>
    intro V _ _ D
    exact contDiffOn_zero.mpr D.continuousOn_series
  | succ n ih =>
    intro V _ _ D
    have hdiff : DifferentiableOn ℝ D.series leftHalf :=
      fun z hz => (D.hasFDerivWithinAt_series hz).differentiableWithinAt
    have hct : ContDiffOn ℝ n (fderivWithin ℝ D.series leftHalf) leftHalf :=
      (D.contDiffOn_seriesJet n (ih D.derived₁) (ih D.derived₂) (ih D.derived₃)).congr
        fun z hz => D.fderivWithin_series_eq_seriesJet hz
    have hcast : ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by push_cast; ring
    rw [hcast]
    exact (contDiffOn_succ_iff_fderivWithin uniqueDiffOn_leftHalf).mpr
      ⟨hdiff, by simp, hct⟩

/-- The reflection series is within-smooth on the left half-space. -/
theorem contDiffOn_series_leftHalf (D : SeriesData V) :
    ContDiffOn ℝ ∞ D.series leftHalf :=
  contDiffOn_infty.mpr fun n => contDiffOn_series_nat n D

end SeriesData

end Navier.Analysis.HalfSpaceSmoothnessBridge.SeeleyReflection
