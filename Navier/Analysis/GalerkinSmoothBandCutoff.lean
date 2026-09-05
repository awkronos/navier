import Navier.Analysis.GalerkinAnnularApproximation
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Smooth even cutoffs converging to the indicator of an actual Fourier band. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff SchwartzMap

namespace Navier.Analysis.GalerkinSmoothBandCutoff

open DivFreeGradientEnstrophy

/-- Symmetrizing a smooth function with support exactly an even open set
preserves that support because both summands are nonnegative. -/
theorem exists_even_smooth_band_function (B : Set EuclSpace) (hB : IsOpen B)
    (hneg : ∀ ξ, -ξ ∈ B ↔ ξ ∈ B) :
    ∃ f : EuclSpace → ℝ, ContDiff ℝ ∞ f ∧ Function.support f = B ∧
      (∀ ξ, 0 ≤ f ξ ∧ f ξ ≤ 1) ∧ (∀ ξ, f (-ξ) = f ξ) := by
  obtain ⟨g, hgs, hgd, hgr⟩ := hB.exists_contDiff_support_eq (n := ⊤)
  have hg (ξ : EuclSpace) : 0 ≤ g ξ ∧ g ξ ≤ 1 := hgr (Set.mem_range_self ξ)
  refine ⟨fun ξ => (g ξ + g (-ξ)) / 2,
    (hgd.add (hgd.comp contDiff_neg)).div_const 2, ?_, ?_, ?_⟩
  · ext ξ
    simp only [Function.mem_support]
    constructor
    · intro hf
      by_contra hout
      have hz : g ξ = 0 := by
        have h : ξ ∉ Function.support g := by simpa only [hgs] using hout
        simpa only [Function.mem_support, not_not] using h
      have hnz : g (-ξ) = 0 := by
        have h : -ξ ∉ Function.support g := by simpa only [hgs, hneg] using hout
        simpa only [Function.mem_support, not_not] using h
      exact hf (by rw [hz, hnz]; norm_num)
    · intro hξ
      have hne : g ξ ≠ 0 := by
        change ξ ∈ Function.support g
        rwa [hgs]
      have hpos := lt_of_le_of_ne (hg ξ).1 hne.symm
      have hn := (hg (-ξ)).1
      linarith
  · intro ξ
    constructor <;> linarith [(hg ξ).1, (hg ξ).2, (hg (-ξ)).1, (hg (-ξ)).2]
  · intro ξ
    simp [add_comm]

/-- Actual smooth, compactly supported, even band cutoffs, bounded between
zero and one and converging pointwise to the band indicator.  Flatness at the
band boundary follows from the smooth support construction. -/
theorem exists_smooth_band_cutoffs (B : Set EuclSpace) (hB : IsOpen B)
    (hcompact : IsCompact (closure B)) (hneg : ∀ ξ, -ξ ∈ B ↔ ξ ∈ B) :
    ∃ χ : ℕ → EuclSpace → ℝ,
      (∀ n, ContDiff ℝ ∞ (χ n)) ∧
      (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n ξ, 0 ≤ χ n ξ ∧ χ n ξ ≤ 1) ∧
      (∀ n ξ, ξ ∉ B → χ n ξ = 0) ∧
      (∀ n ξ, χ n (-ξ) = χ n ξ) ∧
      ∀ ξ, Tendsto (fun n => χ n ξ) atTop (𝓝 (B.indicator (fun _ => 1) ξ)) := by
  obtain ⟨f, hfd, hfs, hfr, hfe⟩ := exists_even_smooth_band_function B hB hneg
  have hfzero (ξ : EuclSpace) (hξ : ξ ∉ B) : f ξ = 0 := by
    have h : ξ ∉ Function.support f := by simpa only [hfs] using hξ
    simpa only [Function.mem_support, not_not] using h
  let χ : ℕ → EuclSpace → ℝ := fun n ξ => 1 - (1 - f ξ) ^ n
  have hzero (n : ℕ) (ξ : EuclSpace) (hξ : ξ ∉ B) : χ n ξ = 0 := by
    simp [χ, hfzero ξ hξ]
  refine ⟨χ, ?_, ?_, ?_, hzero, ?_, ?_⟩
  · intro n
    exact contDiff_const.sub ((contDiff_const.sub hfd).pow n)
  · intro n
    have hs : Function.support (χ n) ⊆ B := by
      intro ξ hξ
      by_contra hout
      exact hξ (hzero n ξ hout)
    exact hcompact.of_isClosed_subset isClosed_closure (closure_mono hs)
  · intro n ξ
    have h0 : 0 ≤ 1 - f ξ := sub_nonneg.mpr (hfr ξ).2
    have h1 : 1 - f ξ ≤ 1 := by linarith [(hfr ξ).1]
    have hp := pow_le_one₀ h0 h1 (n := n)
    have hn := pow_nonneg h0 n
    dsimp only [χ]
    constructor <;> linarith
  · intro n ξ
    simp only [χ, hfe]
  · intro ξ
    by_cases hξ : ξ ∈ B
    · have hp : 0 < f ξ := by
        have hne : f ξ ≠ 0 := by change ξ ∈ Function.support f; rwa [hfs]
        exact lt_of_le_of_ne (hfr ξ).1 hne.symm
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
        (sub_nonneg.mpr (hfr ξ).2) (show 1 - f ξ < 1 by linarith)
      simpa [χ, hξ] using tendsto_const_nhds.sub ht
    · simpa only [Set.indicator_of_notMem hξ] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr
          (fun n => (hzero n ξ hξ).symm)

/-- The cutoff error tends to zero against every integrable nonnegative
density. This supplies both the unweighted and curl-weighted Fourier errors.
The integrals exist by domination by the given integrable density. -/
theorem tendsto_integral_cutoff_error (B : Set EuclSpace) (hB : MeasurableSet B)
    (χ : ℕ → EuclSpace → ℝ) (hχ : ∀ n, Continuous (χ n))
    (hχrange : ∀ n ξ, 0 ≤ χ n ξ ∧ χ n ξ ≤ 1)
    (hχlim : ∀ ξ, Tendsto (fun n => χ n ξ) atTop
      (𝓝 (B.indicator (fun _ => 1) ξ)))
    {a : EuclSpace → ℝ} (ha : Integrable a) (ha0 : ∀ ξ, 0 ≤ a ξ) :
    Tendsto (fun n => ∫ ξ, (χ n ξ - B.indicator (fun _ => 1) ξ) ^ 2 * a ξ)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) (ξ : EuclSpace) :
      ‖(χ n ξ - B.indicator (fun _ => 1) ξ) ^ 2 * a ξ‖ ≤ a ξ := by
    have he : (χ n ξ - B.indicator (fun _ => 1) ξ) ^ 2 ≤ 1 := by
      by_cases h : ξ ∈ B
      · simp only [Set.indicator_of_mem h]
        nlinarith [(hχrange n ξ).1, (hχrange n ξ).2]
      · simp only [Set.indicator_of_notMem h, sub_zero]
        nlinarith [(hχrange n ξ).1, (hχrange n ξ).2]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (ha0 ξ))]
    exact (mul_le_mul_of_nonneg_right he (ha0 ξ)).trans_eq (one_mul _)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun ξ => (χ n ξ - B.indicator (fun _ => 1) ξ) ^ 2 * a ξ) := by
    exact (((hχ n).aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator hB)).pow 2).mul ha.aestronglyMeasurable
  have hlim : ∀ᵐ ξ : EuclSpace, Tendsto
      (fun n => (χ n ξ - B.indicator (fun _ => 1) ξ) ^ 2 * a ξ) atTop (𝓝 0) := by
    filter_upwards [] with ξ
    have hc : Tendsto (fun _ : ℕ => B.indicator (fun _ => (1 : ℝ)) ξ)
        atTop (𝓝 (B.indicator (fun _ => 1) ξ)) := tendsto_const_nhds
    simpa using (((hχlim ξ).sub hc).pow 2).mul_const (a ξ)
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (bound := a) hmeas ha
    (fun n => Filter.Eventually.of_forall (hbound n)) hlim

/-- Multiplication by the constructed cutoff produces an actual Schwartz
map. Compact support and smoothness justify the construction. -/
def cutoffSchwartz {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (χ : EuclSpace → ℝ) (hχc : HasCompactSupport χ) (hχd : ContDiff ℝ ∞ χ)
    (g : 𝓢(EuclSpace, H)) : 𝓢(EuclSpace, H) :=
  (hχc.smul_right (f' := (g : EuclSpace → H))).toSchwartzMap
    (hχd.smul (g.smooth ⊤))

@[simp] theorem cutoffSchwartz_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (χ : EuclSpace → ℝ) (hχc : HasCompactSupport χ) (hχd : ContDiff ℝ ∞ χ)
    (g : 𝓢(EuclSpace, H)) (ξ : EuclSpace) :
    cutoffSchwartz χ hχc hχd g ξ = χ ξ • g ξ := rfl

/-- Smooth compactly supported band approximations converge in every
integrable weighted `L²` norm. The approximants are constructed Schwartz maps,
and the limiting object is the actual sharp Fourier-band restriction. -/
theorem exists_schwartz_band_approximation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : Set EuclSpace) (hB : IsOpen B) (hc : IsCompact (closure B))
    (hneg : ∀ ξ, -ξ ∈ B ↔ ξ ∈ B) (g : 𝓢(EuclSpace, H)) :
    ∃ v : ℕ → 𝓢(EuclSpace, H),
      (∀ n ξ, ξ ∉ B → v n ξ = 0) ∧
      ∀ w : EuclSpace → ℝ, (∀ ξ, 0 ≤ w ξ) →
        Integrable (fun ξ => w ξ * ‖g ξ‖ ^ 2) →
        Tendsto (fun n => ∫ ξ, w ξ * ‖v n ξ - B.indicator g ξ‖ ^ 2)
          atTop (𝓝 0) := by
  obtain ⟨χ, hχd, hχc, hχrange, hχzero, _hχeven, hχlim⟩ :=
    exists_smooth_band_cutoffs B hB hc hneg
  let v : ℕ → 𝓢(EuclSpace, H) := fun n => cutoffSchwartz (χ n) (hχc n) (hχd n) g
  refine ⟨v, ?_, ?_⟩
  · intro n ξ hξ
    simp [v, hχzero n ξ hξ]
  · intro w hw hwi
    have ht := tendsto_integral_cutoff_error B hB.measurableSet χ
      (fun n => (hχd n).continuous) hχrange hχlim hwi
      (fun ξ => mul_nonneg (hw ξ) (sq_nonneg _))
    have heq (n : ℕ) (ξ : EuclSpace) :
        w ξ * ‖v n ξ - B.indicator g ξ‖ ^ 2 =
          (χ n ξ - B.indicator (fun _ => 1) ξ) ^ 2 * (w ξ * ‖g ξ‖ ^ 2) := by
      have hid : B.indicator g ξ = B.indicator (fun _ => (1 : ℝ)) ξ • g ξ := by
        by_cases hξ : ξ ∈ B <;> simp [hξ]
      rw [hid]
      change w ξ * ‖χ n ξ • g ξ - B.indicator (fun _ => (1 : ℝ)) ξ • g ξ‖ ^ 2 = _
      rw [← sub_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    simpa only [heq] using ht

/-- For each actual dyadic band and each Schwartz Fourier field, the smooth
band approximation converges with weight `1 + |ξ|²`, simultaneously controlling
velocity and first-derivative energy. All integrability inputs follow from
Schwartz decay. -/
theorem exists_dyadic_schwartz_graph_approximation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (k : ℤ) (g : 𝓢(EuclSpace, H)) :
    ∃ v : ℕ → 𝓢(EuclSpace, H),
      (∀ n ξ, ξ ∉ GalerkinAnnularApproximation.dyadicAnnulus k → v n ξ = 0) ∧
      Tendsto (fun n => ∫ ξ, (1 + ‖ξ‖ ^ 2) *
        ‖v n ξ - (GalerkinAnnularApproximation.dyadicAnnulus k).indicator g ξ‖ ^ 2)
        atTop (𝓝 0) := by
  let B := GalerkinAnnularApproximation.dyadicAnnulus k
  have hc : IsCompact (closure B) := by
    apply (isCompact_closedBall (0 : EuclSpace) ((2 : ℝ) ^ (k + 1))).of_isClosed_subset
      isClosed_closure
    apply closure_minimal _ Metric.isClosed_closedBall
    intro ξ hξ
    simpa only [Metric.mem_closedBall, dist_zero_right] using hξ.2.le
  have hneg : ∀ ξ, -ξ ∈ B ↔ ξ ∈ B := by
    intro ξ
    simp [B, GalerkinAnnularApproximation.dyadicAnnulus]
  obtain ⟨v, hv, happ⟩ := exists_schwartz_band_approximation B
    (GalerkinAnnularApproximation.dyadicAnnulus_isOpen k) hc hneg g
  refine ⟨v, hv, happ (fun ξ => 1 + ‖ξ‖ ^ 2) (fun ξ => by positivity) ?_⟩
  have h0 : Integrable (fun ξ => ‖g ξ‖ ^ 2) := by
    simpa using GalerkinDisjointBands.integrable_weighted_normSq g 0
  have h2 := GalerkinDisjointBands.integrable_weighted_normSq g 2
  have heq : (fun ξ => (1 + ‖ξ‖ ^ 2) * ‖g ξ‖ ^ 2) =
      (fun ξ => ‖g ξ‖ ^ 2 + ‖ξ‖ ^ 2 * ‖g ξ‖ ^ 2) := by
    funext ξ
    ring
  rw [heq]
  exact h0.add h2

end Navier.Analysis.GalerkinSmoothBandCutoff
