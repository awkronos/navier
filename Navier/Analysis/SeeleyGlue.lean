import Navier.Analysis.SeeleyReflection
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Seeley glue — the cutoff and the extension data

`seeleyPhi` is Seeley's cutoff: smooth, identically 1 on a neighborhood of
`0`, supported in `|s - 1| ≤ 2`, with every iterated derivative bounded.
Together with Seeley's coefficient sequence `seeleyA` it packages a
half-space-smooth field into `SeriesData`, the input of the reflection-series
machinery of `SeeleyReflection.lean`.

Reference: R. T. Seeley, "Extension of C^∞ functions defined in a half
space", Proc. Amer. Math. Soc. 15 (1964), 625–626.
-/

noncomputable section

namespace Navier.Analysis.HalfSpaceSmoothnessBridge.SeeleyGlue

open Metric Filter Topology
open scoped ContDiff
open Navier.Analysis.HalfSpaceSmoothnessBridge
open Navier.Analysis.HalfSpaceSmoothnessBridge.SeeleyCoeff
open Navier.Analysis.HalfSpaceSmoothnessBridge.SeeleyReflection

/-- The bump function underlying Seeley's cutoff: center `1`, inner radius
`3 / 2`, outer radius `2`.  Since `3 / 2 > 1`, the bump is identically `1` on
`closedBall 1 (3 / 2)`, a two-sided neighborhood of `0` — this is what gives
the flat jet of the cutoff at `0`. -/
def seeleyBump : ContDiffBump (1 : ℝ) := ⟨3 / 2, 2, by norm_num, by norm_num⟩

/-- Seeley's cutoff. -/
def seeleyPhi : ℝ → ℝ := ⇑seeleyBump

/-- The cutoff is smooth. -/
theorem seeleyPhi_contDiff : ContDiff ℝ ∞ seeleyPhi :=
  ContDiff.contDiffBump (c := fun _ => (1 : ℝ)) (g := id) (f := fun _ => seeleyBump)
    contDiff_const contDiff_const contDiff_const contDiff_id

/-- The cutoff takes the value `1` at `0`. -/
theorem seeleyPhi_zero : seeleyPhi 0 = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [mem_closedBall, dist_comm, Real.dist_eq]
  norm_num [seeleyBump]

/-- The cutoff is identically `1` on a neighborhood of `0`. -/
theorem seeleyPhi_eq_one_near : seeleyPhi =ᶠ[𝓝 0] 1 := by
  apply ContDiffBump.eventuallyEq_one_of_mem_ball
  rw [mem_ball, dist_comm, Real.dist_eq]
  norm_num [seeleyBump]

/-- The cutoff is supported in `|s - 1| < 2`. -/
theorem seeleyPhi_support (s : ℝ) (hs : 2 ≤ |s - 1|) : seeleyPhi s = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [Real.dist_eq]
  exact hs

/-- Flat jet at `0`: every positive-order iterated derivative vanishes. -/
theorem seeleyPhi_iteratedDeriv_zero (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n seeleyPhi 0 = 0 := by
  have h : iteratedDeriv n seeleyPhi =ᶠ[𝓝 0] iteratedDeriv n (1 : ℝ → ℝ) :=
    seeleyPhi_eq_one_near.iteratedDeriv n
  rw [h.eq_of_nhds, show (1 : ℝ → ℝ) = fun _ => (1 : ℝ) from rfl, iteratedDeriv_const]
  exact if_neg (Nat.one_le_iff_ne_zero.mp hn)

/-- Every iterated derivative of the cutoff is bounded: compactly supported,
hence bounded on the support interval and zero outside. -/
theorem seeleyPhi_iteratedDeriv_bounded (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv n seeleyPhi t| ≤ C := by
  have hcont : Continuous fun t => |iteratedDeriv n seeleyPhi t| :=
    (seeleyPhi_contDiff.continuous_iteratedDeriv n
      (WithTop.coe_le_coe.mpr le_top)).abs
  have hzero_of_lt (t : ℝ) (ht : t < -1) : iteratedDeriv n seeleyPhi t = 0 := by
    have h1 : seeleyPhi =ᶠ[𝓝 t] (0 : ℝ → ℝ) := by
      have hop : IsOpen {s : ℝ | s < -1} := isOpen_gt' _
      filter_upwards [hop.eventually_mem ht] with s hs
      exact seeleyPhi_support s (by rw [abs_of_neg (by linarith)]; linarith)
    rw [(h1.iteratedDeriv n).eq_of_nhds]
    simp
  have hzero_of_gt (t : ℝ) (ht : 3 < t) : iteratedDeriv n seeleyPhi t = 0 := by
    have h1 : seeleyPhi =ᶠ[𝓝 t] (0 : ℝ → ℝ) := by
      have hop : IsOpen {s : ℝ | (3 : ℝ) < s} := isOpen_lt' _
      filter_upwards [hop.eventually_mem ht] with s hs
      exact seeleyPhi_support s (by rw [abs_of_pos (by linarith)]; linarith)
    rw [(h1.iteratedDeriv n).eq_of_nhds]
    simp
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-1) 3
  · exact le_trans (by simpa using hC t ht) (le_max_left C 0)
  · by_cases h1 : t < -1
    · rw [hzero_of_lt t h1]; simp
    · have hge : (-1 : ℝ) ≤ t := le_of_not_gt h1
      have h3 : 3 < t := lt_of_not_ge fun hc => ht (Set.mem_Icc.mpr ⟨hge, hc⟩)
      rw [hzero_of_gt t h3]; simp

/-- Packaging: a half-space-smooth field, Seeley's coefficients, and the
cutoff assemble into the `SeriesData` consumed by the reflection-series
machinery. -/
def topData {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') (hg : HalfSpaceSmooth g) : SeriesData E' where
  h := jointMap g
  hh := hg
  ψ := seeleyPhi
  hψ := seeleyPhi_contDiff
  hψsupp := seeleyPhi_support
  hψb := seeleyPhi_iteratedDeriv_bounded
  c := seeleyA
  hc := summable_seeleyA_abs_pow

/-- Boundary value: the reflection series matches the field at `t = 0`, since
`∑' seeleyA = 1` and `seeleyPhi 0 = 1`. -/
theorem topData_series_boundary {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') (hg : HalfSpaceSmooth g) (x : Space) :
    (topData g hg).series (0, x) = g 0 x := by
  rw [SeriesData.series_zero_fst]
  show ((∑' k, seeleyA k) * seeleyPhi 0) • jointMap g (0, x) = g 0 x
  rw [seeley_moment_zero, seeleyPhi_zero]
  simp [jointMap]

/-- The Seeley coefficients against the first power of the reflection
factor: `∑' k, -(2^k) * seeleyA k = 1` (the first moment identity). -/
theorem tsum_neg_two_pow_mul_seeleyA : ∑' k, (-(2 : ℝ) ^ k) * seeleyA k = 1 := by
  have h := seeley_moment 1
  rw [← h]
  refine tsum_congr fun k => ?_
  rw [pow_one, mul_comm]

/-- The `derived₁` series of `topData` vanishes at the boundary: it carries
a factor `deriv seeleyPhi 0 = 0` (the flat jet of the cutoff). -/
theorem derived₁_series_boundary {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') (hg : HalfSpaceSmooth g) (x : Space) :
    (topData g hg).derived₁.series (0, x) = 0 := by
  rw [SeriesData.series_zero_fst]
  show ((∑' k, (-(2 : ℝ) ^ k) * seeleyA k) * deriv seeleyPhi 0) • jointMap g (0, x) = 0
  have hψ : deriv seeleyPhi 0 = 0 := by
    rw [← iteratedDeriv_one]
    exact seeleyPhi_iteratedDeriv_zero 1 (le_refl 1)
  rw [hψ, mul_zero, zero_smul]

/-- The `derived₂` series of `topData` at the boundary is the field's
`(1, 0)`-directional jet value: the first Seeley moment collapses the
coefficient sum to `1`. -/
theorem derived₂_series_boundary {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') (hg : HalfSpaceSmooth g) (x : Space) :
    (topData g hg).derived₂.series (0, x) =
      (fderivWithin ℝ (jointMap g) rightHalf (0, x)) ((1 : ℝ), (0 : Space)) := by
  rw [SeriesData.series_zero_fst]
  show ((∑' k, (-(2 : ℝ) ^ k) * seeleyA k) * seeleyPhi 0) •
    (fderivWithin ℝ (jointMap g) rightHalf (0, x)) ((1 : ℝ), (0 : Space)) = _
  rw [tsum_neg_two_pow_mul_seeleyA, seeleyPhi_zero, one_mul, one_smul]

/-- The `derived₃` series of `topData` at the boundary is the field's jet
precomposed with `inr`: the zeroth Seeley moment collapses the coefficient
sum to `1`. -/
theorem derived₃_series_boundary {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') (hg : HalfSpaceSmooth g) (x : Space) :
    (topData g hg).derived₃.series (0, x) =
      (fderivWithin ℝ (jointMap g) rightHalf (0, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space) := by
  rw [SeriesData.series_zero_fst]
  show ((∑' k, seeleyA k) * seeleyPhi 0) •
    (fderivWithin ℝ (jointMap g) rightHalf (0, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) = _
  rw [seeley_moment_zero, seeleyPhi_zero, one_mul, one_smul]

/-- **First-jet matching** (`m = 1` Seeley): the reflection series'
within-derivative from the left at `(0, x)` equals the field's
within-derivative from the right.  The three derived packages collapse via
the flat jet of the cutoff (`derived₁` dies) and the first two Seeley
moment identities. -/
theorem fderivWithin_series_boundary {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') (hg : HalfSpaceSmooth g) (x : Space) :
    fderivWithin ℝ (topData g hg).series leftHalf (0, x) =
      fderivWithin ℝ (jointMap g) rightHalf (0, x) := by
  have hz : (0, x) ∈ leftHalf := by simp
  rw [SeriesData.fderivWithin_series_eq_seriesJet _ hz]
  rw [SeriesData.seriesJet, derived₁_series_boundary g hg x,
    derived₂_series_boundary g hg x, derived₃_series_boundary g hg x]
  apply ContinuousLinearMap.ext
  intro u
  have hu : u = u.1 • ((1 : ℝ), (0 : Space)) +
      ContinuousLinearMap.inr ℝ ℝ Space u.2 := by
    ext
    · simp
    · simp [ContinuousLinearMap.inr_apply]
  show u.1 • (0 : E') + (u.1 • (fderivWithin ℝ (jointMap g) rightHalf (0, x)) ((1 : ℝ), (0 : Space)) +
      ((fderivWithin ℝ (jointMap g) rightHalf (0, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space)) u.2) =
    (fderivWithin ℝ (jointMap g) rightHalf (0, x)) u
  rw [smul_zero, zero_add]
  conv_rhs => rw [hu]
  rw [map_add, map_smul, ContinuousLinearMap.comp_apply]

/-! ## Glueing across the time-zero hyperplane

A `GluedData V` packages two fields, within-smooth on the right and left
closed half-spaces respectively, whose iterated jets agree at every boundary
point.  The master theorem `contDiff_glued` shows the glued field is smooth
on all of spacetime: continuity from the closed-union argument, the `C^1`
step from the mean-value theorem on each closed convex half, and the full
induction through the derived data. -/

/-- Glueing data for the extension across `{0} × Space`: fields smooth on
each closed half-space with all boundary jets matching. -/
structure GluedData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- The right-half field. -/
  f₁ : (ℝ × Space) → V
  /-- The left-half field. -/
  f₂ : (ℝ × Space) → V
  /-- Within-smoothness of the right field. -/
  h₁ : ContDiffOn ℝ ∞ f₁ rightHalf
  /-- Within-smoothness of the left field. -/
  h₂ : ContDiffOn ℝ ∞ f₂ leftHalf
  /-- Values agree at the boundary. -/
  hval : ∀ x : Space, f₁ (0, x) = f₂ (0, x)
  /-- All iterated jets agree at the boundary. -/
  hjet : ∀ (m : ℕ) (x : Space),
    iteratedFDerivWithin ℝ m f₁ rightHalf (0, x) =
      iteratedFDerivWithin ℝ m f₂ leftHalf (0, x)

namespace GluedData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The glued field: the right field on `0 ≤ t`, the left field on `t < 0`. -/
def glued (G : GluedData V) : (ℝ × Space) → V :=
  fun z => if 0 ≤ z.1 then G.f₁ z else G.f₂ z

/-- The first-jet match rephrased at the level of within-derivatives. -/
theorem fderivWithin_boundary_eq (G : GluedData V) (x : Space) :
    fderivWithin ℝ G.f₁ rightHalf (0, x) = fderivWithin ℝ G.f₂ leftHalf (0, x) := by
  apply ContinuousLinearMap.ext
  intro v
  have hzR : (0, x) ∈ rightHalf := by simp
  have hzL : (0, x) ∈ leftHalf := by simp
  have happ : (iteratedFDerivWithin ℝ 1 G.f₁ rightHalf (0, x)) (fun _ => v) =
      (iteratedFDerivWithin ℝ 1 G.f₂ leftHalf (0, x)) (fun _ => v) := by
    rw [G.hjet 1 x]
  rwa [iteratedFDerivWithin_one_apply (uniqueDiffOn_rightHalf _ hzR),
    iteratedFDerivWithin_one_apply (uniqueDiffOn_leftHalf _ hzL)] at happ

/-- The mean-value boundary estimate: on a closed convex half containing the
boundary point, the field minus the boundary linear map is `ε`-Lipschitz
close near the boundary, by continuity of the within-derivative. -/
theorem mvt_boundary_estimate {f : (ℝ × Space) → V} {s : Set (ℝ × Space)}
    (hconv : Convex ℝ s) {x : Space} (hs₀ : (0, x) ∈ s)
    (hf : DifferentiableOn ℝ f s) (hfc : ContinuousOn (fderivWithin ℝ f s) s)
    (L : (ℝ × Space) →L[ℝ] V) (hL : L = fderivWithin ℝ f s (0, x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℝ × Space, dist z (0, x) < δ → z ∈ s →
      ‖f z - f (0, x) - L (z - (0, x))‖ ≤ ε * ‖z - (0, x)‖ := by
  have hcont := hfc (0, x) hs₀
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont ε hε
  refine ⟨δ, hδ, fun z hzδ hzs => ?_⟩
  have hcv : Convex ℝ (s ∩ Metric.ball (0, x) δ) := hconv.inter (convex_ball _ _)
  have hfw : ∀ w ∈ s ∩ Metric.ball (0, x) δ,
      HasFDerivWithinAt (fun w => f w - L w) (fderivWithin ℝ f s w - L)
        (s ∩ Metric.ball (0, x) δ) w := by
    intro w hw
    have h1 : HasFDerivWithinAt f (fderivWithin ℝ f s w) s w :=
      (hf w hw.1).hasFDerivWithinAt
    have h2 : HasFDerivWithinAt (fun w => L w) L s w := L.hasFDerivAt.hasFDerivWithinAt
    exact (h1.sub h2).mono Set.inter_subset_left
  have hb : ∀ w ∈ s ∩ Metric.ball (0, x) δ, ‖fderivWithin ℝ f s w - L‖ ≤ ε := by
    intro w hw
    have h3 : dist (fderivWithin ℝ f s w) (fderivWithin ℝ f s (0, x)) < ε := hδ' hw.1 hw.2
    rw [← hL] at h3
    rw [← dist_eq_norm]
    exact le_of_lt h3
  have hmem₀ : (0, x) ∈ s ∩ Metric.ball (0, x) δ := ⟨hs₀, Metric.mem_ball_self hδ⟩
  have hmemz : z ∈ s ∩ Metric.ball (0, x) δ := ⟨hzs, hzδ⟩
  have hmvt := hcv.norm_image_sub_le_of_norm_hasFDerivWithin_le hfw hb hmem₀ hmemz
  have heq : f z - f (0, x) - L (z - (0, x)) = (f z - L z) - (f (0, x) - L (0, x)) := by
    rw [map_sub]
    abel
  rw [heq]
  exact hmvt

/-- The glued field is differentiable at boundary points, with derivative
the common within-derivative. -/
theorem hasFDerivAt_glued_boundary (G : GluedData V) (x : Space) :
    HasFDerivAt G.glued (fderivWithin ℝ G.f₁ rightHalf (0, x)) (0, x) := by
  set L := fderivWithin ℝ G.f₁ rightHalf (0, x) with hL
  have hL2 : L = fderivWithin ℝ G.f₂ leftHalf (0, x) := G.fderivWithin_boundary_eq x
  have hd₁ : DifferentiableOn ℝ G.f₁ rightHalf := G.h₁.differentiableOn (by simp)
  have hd₂ : DifferentiableOn ℝ G.f₂ leftHalf := G.h₂.differentiableOn (by simp)
  have hc₁ : ContinuousOn (fderivWithin ℝ G.f₁ rightHalf) rightHalf :=
    G.h₁.continuousOn_fderivWithin uniqueDiffOn_rightHalf (by simp)
  have hc₂ : ContinuousOn (fderivWithin ℝ G.f₂ leftHalf) leftHalf :=
    G.h₂.continuousOn_fderivWithin uniqueDiffOn_leftHalf (by simp)
  have hz₁ : (0, x) ∈ rightHalf := by simp
  have hz₂ : (0, x) ∈ leftHalf := by simp
  have hcv₁ : Convex ℝ rightHalf := (convex_Ici _).prod convex_univ
  have hcv₂ : Convex ℝ leftHalf := (convex_Iic _).prod convex_univ
  rw [hasFDerivAt_iff_tendsto, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hest₁⟩ := mvt_boundary_estimate hcv₁ hz₁ hd₁ hc₁ L hL (half_pos hε)
  obtain ⟨δ₂, hδ₂, hest₂⟩ := mvt_boundary_estimate hcv₂ hz₂ hd₂ hc₂ L hL2 (half_pos hε)
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds _ (lt_min hδ₁ hδ₂)) ?_
  intro z hz
  simp only [dist_zero_right, norm_mul, norm_inv, norm_norm]
  by_cases hz₀ : z = (0, x)
  · subst hz₀
    simp [map_zero, hε]
  · have hzz : (0:ℝ) < ‖z - (0, x)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz₀)
    have hne : ‖z - (0, x)‖ ≠ 0 := hzz.ne'
    by_cases h : 0 ≤ z.1
    · have hgl : G.glued z = G.f₁ z := if_pos h
      have hgl₀ : G.glued (0, x) = G.f₁ (0, x) := if_pos (le_refl 0)
      have hzR : z ∈ rightHalf := ⟨h, Set.mem_univ _⟩
      have hzδ₁ : dist z (0, x) < δ₁ := lt_of_lt_of_le hz (min_le_left _ _)
      have he := hest₁ z hzδ₁ hzR
      calc ‖z - (0, x)‖⁻¹ * ‖G.glued z - G.glued (0, x) - L (z - (0, x))‖
          = ‖z - (0, x)‖⁻¹ * ‖G.f₁ z - G.f₁ (0, x) - L (z - (0, x))‖ := by rw [hgl, hgl₀]
        _ ≤ ‖z - (0, x)‖⁻¹ * ((ε / 2) * ‖z - (0, x)‖) :=
            mul_le_mul_of_nonneg_left he (by positivity)
        _ = ε / 2 := by
            rw [mul_comm (‖z - (0, x)‖⁻¹) ((ε / 2) * ‖z - (0, x)‖), mul_assoc,
              mul_inv_cancel₀ hne, mul_one]
        _ < ε := half_lt_self hε
    · have hlt : z.1 < 0 := lt_of_not_ge h
      have hgl : G.glued z = G.f₂ z := if_neg (not_le.mpr hlt)
      have hgl₀ : G.glued (0, x) = G.f₁ (0, x) := if_pos (le_refl 0)
      have hzL : z ∈ leftHalf := ⟨le_of_lt hlt, Set.mem_univ _⟩
      have hzδ₂ : dist z (0, x) < δ₂ := lt_of_lt_of_le hz (min_le_right _ _)
      have he := hest₂ z hzδ₂ hzL
      have hval0 : G.f₁ (0, x) = G.f₂ (0, x) := G.hval x
      calc ‖z - (0, x)‖⁻¹ * ‖G.glued z - G.glued (0, x) - L (z - (0, x))‖
          = ‖z - (0, x)‖⁻¹ * ‖G.f₂ z - G.f₂ (0, x) - L (z - (0, x))‖ := by
            rw [hgl, hgl₀, hval0]
        _ ≤ ‖z - (0, x)‖⁻¹ * ((ε / 2) * ‖z - (0, x)‖) :=
            mul_le_mul_of_nonneg_left he (by positivity)
        _ = ε / 2 := by
            rw [mul_comm (‖z - (0, x)‖⁻¹) ((ε / 2) * ‖z - (0, x)‖), mul_assoc,
              mul_inv_cancel₀ hne, mul_one]
        _ < ε := half_lt_self hε

/-- The glued field is everywhere differentiable. -/
theorem differentiable_glued (G : GluedData V) : Differentiable ℝ G.glued := by
  intro z
  by_cases h0 : z.1 = 0
  · have hz : z = (0, z.2) := Prod.ext h0 rfl
    rw [hz]
    exact (G.hasFDerivAt_glued_boundary z.2).differentiableAt
  · by_cases h : 0 < z.1
    · have hop : IsOpen {w : ℝ × Space | 0 < w.1} :=
        isOpen_Ioi.preimage (Continuous.fst continuous_id)
      have hnhds : rightHalf ∈ 𝓝 z :=
        Filter.mem_of_superset (hop.mem_nhds h) fun w hw => ⟨Set.mem_Ici.mpr (le_of_lt hw), Set.mem_univ _⟩
      have heq : G.glued =ᶠ[𝓝 z] G.f₁ := by
        filter_upwards [hop.mem_nhds h] with w hw
        exact if_pos (le_of_lt hw)
      exact (heq.differentiableAt_iff).mpr
        ((G.h₁.differentiableOn (by simp)).differentiableAt hnhds)
    · have hlt : z.1 < 0 := lt_of_le_of_ne (le_of_not_gt h) h0
      have hop : IsOpen {w : ℝ × Space | w.1 < 0} :=
        isOpen_Iio.preimage (Continuous.fst continuous_id)
      have hnhds : leftHalf ∈ 𝓝 z :=
        Filter.mem_of_superset (hop.mem_nhds hlt) fun w hw => ⟨Set.mem_Iic.mpr (le_of_lt hw), Set.mem_univ _⟩
      have heq : G.glued =ᶠ[𝓝 z] G.f₂ := by
        filter_upwards [hop.mem_nhds hlt] with w hw
        exact if_neg (not_le.mpr hw)
      exact (heq.differentiableAt_iff).mpr
        ((G.h₂.differentiableOn (by simp)).differentiableAt hnhds)

/-- The glued field is continuous: it agrees with a continuous-on-a-closed-set
field on each of two closed half-spaces covering spacetime. -/
theorem continuous_glued (G : GluedData V) : Continuous G.glued := by
  have hcon₁ : ContinuousOn G.glued rightHalf :=
    (G.h₁.continuousOn).congr fun w hw => if_pos hw.1
  have hcon₂ : ContinuousOn G.glued leftHalf := by
    apply (G.h₂.continuousOn).congr
    intro w hw
    by_cases hc : w.1 = 0
    · have : w = (0, w.2) := Prod.ext hc rfl
      rw [this]
      exact (if_pos (le_refl 0)).trans (G.hval w.2)
    · exact if_neg (not_le.mpr (lt_of_le_of_ne hw.1 hc))
  have hunion : rightHalf ∪ leftHalf = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases le_total z.1 0 with h | h
    · exact Or.inr ⟨h, Set.mem_univ _⟩
    · exact Or.inl ⟨h, Set.mem_univ _⟩
  have := hcon₁.union_of_isClosed hcon₂ (isClosed_Ici.prod isClosed_univ)
    (isClosed_Iic.prod isClosed_univ)
  rw [hunion] at this
  exact continuousOn_univ.mp this

/-- The derived glueing data: the within-derivatives on each half, which
inherit the full jet match. -/
def derived (G : GluedData V) : GluedData ((ℝ × Space) →L[ℝ] V) where
  f₁ := fderivWithin ℝ G.f₁ rightHalf
  f₂ := fderivWithin ℝ G.f₂ leftHalf
  h₁ := G.h₁.fderivWithin uniqueDiffOn_rightHalf (by simp)
  h₂ := G.h₂.fderivWithin uniqueDiffOn_leftHalf (by simp)
  hval := fun x => G.fderivWithin_boundary_eq x
  hjet := fun m x => by
    have hzR : (0, x) ∈ rightHalf := by simp
    have hzL : (0, x) ∈ leftHalf := by simp
    have e1 := iteratedFDerivWithin_succ_eq_comp_right uniqueDiffOn_rightHalf hzR
      (f := G.f₁) (n := m)
    have e2 := iteratedFDerivWithin_succ_eq_comp_right uniqueDiffOn_leftHalf hzL
      (f := G.f₂) (n := m)
    rw [G.hjet (m + 1) x] at e1
    rw [e2] at e1
    simp only [Function.comp_apply] at e1
    exact ((continuousMultilinearCurryRightEquiv' ℝ m (ℝ × Space) V).symm.injective e1).symm

/-- The derivative of the glued field is the glued derived field. -/
theorem fderiv_glued (G : GluedData V) : fderiv ℝ G.glued = G.derived.glued := by
  funext z
  by_cases h0 : z.1 = 0
  · have hz : z = (0, z.2) := Prod.ext h0 rfl
    rw [hz, (G.hasFDerivAt_glued_boundary z.2).fderiv]
    show fderivWithin ℝ G.f₁ rightHalf (0, z.2) =
      (if 0 ≤ (0 : ℝ) then fderivWithin ℝ G.f₁ rightHalf (0, z.2)
        else fderivWithin ℝ G.f₂ leftHalf (0, z.2))
    rw [if_pos (le_refl 0)]
  · by_cases h : 0 < z.1
    · have hop : IsOpen {w : ℝ × Space | 0 < w.1} :=
        isOpen_Ioi.preimage (Continuous.fst continuous_id)
      have hnhds : rightHalf ∈ 𝓝 z :=
        Filter.mem_of_superset (hop.mem_nhds h) fun w hw => ⟨Set.mem_Ici.mpr (le_of_lt hw), Set.mem_univ _⟩
      have heq : G.glued =ᶠ[𝓝 z] G.f₁ := by
        filter_upwards [hop.mem_nhds h] with w hw
        exact if_pos (le_of_lt hw)
      calc fderiv ℝ G.glued z = fderiv ℝ G.f₁ z := heq.fderiv_eq
        _ = fderivWithin ℝ G.f₁ rightHalf z := (fderivWithin_of_mem_nhds hnhds).symm
        _ = G.derived.glued z := (if_pos (le_of_lt h)).symm
    · have hlt : z.1 < 0 := lt_of_le_of_ne (le_of_not_gt h) h0
      have hop : IsOpen {w : ℝ × Space | w.1 < 0} :=
        isOpen_Iio.preimage (Continuous.fst continuous_id)
      have hnhds : leftHalf ∈ 𝓝 z :=
        Filter.mem_of_superset (hop.mem_nhds hlt) fun w hw => ⟨Set.mem_Iic.mpr (le_of_lt hw), Set.mem_univ _⟩
      have heq : G.glued =ᶠ[𝓝 z] G.f₂ := by
        filter_upwards [hop.mem_nhds hlt] with w hw
        exact if_neg (not_le.mpr hw)
      calc fderiv ℝ G.glued z = fderiv ℝ G.f₂ z := heq.fderiv_eq
        _ = fderivWithin ℝ G.f₂ leftHalf z := (fderivWithin_of_mem_nhds hnhds).symm
        _ = G.derived.glued z := (if_neg (not_le.mpr hlt)).symm

/-- The glueing induction: the glued field is `C^n` for every finite `n`. -/
theorem contDiff_glued_nat : ∀ (n : ℕ) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : GluedData V), ContDiff ℝ n G.glued := by
  intro n
  induction n with
  | zero =>
      intro V _ _ G
      simpa using (contDiff_zero (𝕜 := ℝ)).mpr G.continuous_glued
  | succ n ih =>
      intro V _ _ G
      have hcast : ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by push_cast; ring
      rw [hcast, contDiff_succ_iff_fderiv]
      refine ⟨G.differentiable_glued, ?_, ?_⟩
      · intro hω
        simp at hω
      · rw [G.fderiv_glued]
        exact ih G.derived

/-- **Glueing theorem**: fields within-smooth on each closed half-space whose
iterated jets match at the boundary glue to a smooth field on all of
spacetime. -/
theorem contDiff_glued (G : GluedData V) : ContDiff ℝ ∞ G.glued :=
  contDiff_infty.mpr fun n => contDiff_glued_nat n G

end GluedData


/-! ## Boundary jet matching at all orders (Seeley W6b)

The remaining analytic content of Seeley's argument: the iterated jets of
the reflection series at the boundary equal the field's jets, at every
order.  One unified induction `series_jet_boundary` carries the scalar
`D.ψ 0` on the right-hand side so the `derived₁` (cutoff-derivative)
branch dies automatically via `deriv ψ 0 = 0`. -/

section JetBoundary

/-- Jet-flatness of a cutoff at the origin. -/
def FlatAtZero (ψ : ℝ → ℝ) : Prop := ∀ n : ℕ, 1 ≤ n → iteratedDeriv n ψ 0 = 0

/-- The full tower of Seeley moment identities for a coefficient family. -/
def AllMoments (c : ℕ → ℝ) : Prop := ∀ j : ℕ, ∑' k : ℕ, c k * (-(2:ℝ)^k)^j = 1

theorem AllMoments.tsum {c : ℕ → ℝ} (hm : AllMoments c) : ∑' k : ℕ, c k = 1 := by
  simpa using hm 0

/-- The moment tower survives coefficient scaling by the reflection factor. -/
theorem AllMoments.shift {c : ℕ → ℝ} (hm : AllMoments c) :
    AllMoments (fun k => (-(2:ℝ)^k) * c k) := by
  intro j
  rw [← hm (j + 1)]
  refine tsum_congr fun k => ?_
  rw [pow_succ']
  ring

/-- Jet-flatness passes to the derivative. -/
theorem FlatAtZero.deriv {ψ : ℝ → ℝ} (h : FlatAtZero ψ) : FlatAtZero (_root_.deriv ψ) := by
  intro n hn
  rw [← iteratedDeriv_succ']
  exact h (n + 1) (Nat.le_trans hn (Nat.le_succ n))

/-- A jet-flat cutoff has vanishing first derivative at the origin. -/
theorem FlatAtZero.deriv_apply_zero {ψ : ℝ → ℝ} (h : FlatAtZero ψ) : _root_.deriv ψ 0 = 0 := by
  rw [← iteratedDeriv_one]
  exact h 1 (le_refl 1)

/-- The Seeley cutoff is jet-flat at the origin. -/
theorem flatAtZero_seeleyPhi : FlatAtZero seeleyPhi := seeleyPhi_iteratedDeriv_zero

/-- Seeley's coefficients satisfy the full moment tower. -/
theorem allMoments_seeleyA : AllMoments seeleyA := seeley_moment

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Post-composition with the first projection, as a CLM in the value. -/
noncomputable def jetL1 : V →L[ℝ] ((ℝ × Space) →L[ℝ] V) :=
  ContinuousLinearMap.smulRightL ℝ (ℝ × Space) V (ContinuousLinearMap.fst ℝ ℝ Space)

@[simp] theorem jetL1_apply (w : V) (u : ℝ × Space) : jetL1 w u = u.1 • w := by
  simp [jetL1, ContinuousLinearMap.smulRightL_apply_apply]

/-- Pre-composition with the second projection, as a CLM in the operator. -/
noncomputable def jetL3 : (Space →L[ℝ] V) →L[ℝ] ((ℝ × Space) →L[ℝ] V) :=
  ContinuousLinearMap.flip
    (ContinuousLinearMap.compSL (ℝ × Space) Space V (RingHom.id ℝ) (RingHom.id ℝ))
    (ContinuousLinearMap.snd ℝ ℝ Space)

@[simp] theorem jetL3_apply (M : Space →L[ℝ] V) (u : ℝ × Space) : jetL3 M u = M u.2 := by
  simp [jetL3, ContinuousLinearMap.flip_apply]

/-- Scalar multiplication passes through post-composition by a CLM. -/
private theorem compCMM_smul {m : ℕ} {V₁ W : Type*} [NormedAddCommGroup V₁]
    [NormedSpace ℝ V₁] [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V₁ →L[ℝ] W) (a : ℝ)
    (J : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × Space) V₁) :
    L.compContinuousMultilinearMap (a • J) = a • L.compContinuousMultilinearMap J := by
  rw [← ContinuousLinearMap.compContinuousMultilinearMapL_apply,
    ← ContinuousLinearMap.compContinuousMultilinearMapL_apply]
  exact map_smul _ _ _

/-- Post-composition by a CLM kills the zero multilinear map. -/
private theorem compCMM_zero {m : ℕ} {V₁ W : Type*} [NormedAddCommGroup V₁]
    [NormedSpace ℝ V₁] [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V₁ →L[ℝ] W) :
    L.compContinuousMultilinearMap
      (0 : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × Space) V₁) = 0 := by
  rw [← ContinuousLinearMap.compContinuousMultilinearMapL_apply]
  exact map_zero _

set_option maxHeartbeats 1600000 in
/-- **Boundary jet matching, all orders.**  For any series data whose cutoff
is jet-flat at the origin and whose coefficients satisfy the full Seeley
moment tower, the `m`-th iterated jet of the reflection series at `(0, x)`
equals `ψ 0` times the `m`-th jet of the field.  Induction on `m` over the
derived packages: the cutoff-derivative branch carries the factor
`deriv ψ 0 = 0` and dies; the other two branches are reassembled into the
jet of the field by splitting each tangent direction along `(1, 0)` and the
spatial inclusion. -/
theorem series_jet_boundary : ∀ (m : ℕ) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (D : SeriesData V), FlatAtZero D.ψ → AllMoments D.c → ∀ x : Space,
    iteratedFDerivWithin ℝ m D.series leftHalf (0, x) =
      D.ψ 0 • iteratedFDerivWithin ℝ m D.h rightHalf (0, x) := by
  intro m
  induction m with
  | zero =>
      intro V _ _ D hflat hm x
      ext v
      rw [ContinuousMultilinearMap.smul_apply, iteratedFDerivWithin_zero_apply,
        iteratedFDerivWithin_zero_apply, SeriesData.series_zero_fst, hm.tsum, one_mul]
  | succ m ih =>
      intro V _ _ D hflat hm x
      have hz₀ : (0, x) ∈ leftHalf := by simp
      have hzR : (0, x) ∈ rightHalf := by simp
      have hu : UniqueDiffOn ℝ leftHalf := uniqueDiffOn_leftHalf
      have hur : UniqueDiffOn ℝ rightHalf := uniqueDiffOn_rightHalf
      have hle : (m : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
      have hC1 : ContDiffWithinAt ℝ ∞ D.derived₁.series leftHalf (0, x) :=
        (SeriesData.contDiffOn_series_leftHalf D.derived₁).contDiffWithinAt hz₀
      have hC2 : ContDiffWithinAt ℝ ∞ D.derived₂.series leftHalf (0, x) :=
        (SeriesData.contDiffOn_series_leftHalf D.derived₂).contDiffWithinAt hz₀
      have hC3 : ContDiffWithinAt ℝ ∞ D.derived₃.series leftHalf (0, x) :=
        (SeriesData.contDiffOn_series_leftHalf D.derived₃).contDiffWithinAt hz₀
      have hA1 : ContDiffWithinAt ℝ (m : ℕ∞ω) (jetL1 ∘ D.derived₁.series) leftHalf (0, x) :=
        (jetL1.contDiff.comp_contDiffWithinAt hC1).of_le hle
      have hA2 : ContDiffWithinAt ℝ (m : ℕ∞ω) (jetL1 ∘ D.derived₂.series) leftHalf (0, x) :=
        (jetL1.contDiff.comp_contDiffWithinAt hC2).of_le hle
      have hA3 : ContDiffWithinAt ℝ (m : ℕ∞ω) (jetL3 ∘ D.derived₃.series) leftHalf (0, x) :=
        (jetL3.contDiff.comp_contDiffWithinAt hC3).of_le hle
      have hD2 : ContDiffWithinAt ℝ ∞ D.derived₂.h rightHalf (0, x) :=
        D.derived₂.hh.contDiffWithinAt hzR
      have hD3 : ContDiffWithinAt ℝ ∞ D.derived₃.h rightHalf (0, x) :=
        D.derived₃.hh.contDiffWithinAt hzR
      have hA23 : ContDiffWithinAt ℝ (m : ℕ∞ω)
          ((jetL1 ∘ D.derived₂.series) + (jetL3 ∘ D.derived₃.series)) leftHalf (0, x) :=
        hA2.add hA3
      have hB2 : ContDiffWithinAt ℝ (m : ℕ∞ω) (jetL1 ∘ D.derived₂.h) rightHalf (0, x) :=
        (jetL1.contDiff.comp_contDiffWithinAt hD2).of_le hle
      have hB3 : ContDiffWithinAt ℝ (m : ℕ∞ω) (jetL3 ∘ D.derived₃.h) rightHalf (0, x) :=
        (jetL3.contDiff.comp_contDiffWithinAt hD3).of_le hle
      have ih1 : iteratedFDerivWithin ℝ m D.derived₁.series leftHalf (0, x) = 0 := by
        have h : iteratedFDerivWithin ℝ m D.derived₁.series leftHalf (0, x) =
            _root_.deriv D.ψ 0 • iteratedFDerivWithin ℝ m D.derived₁.h rightHalf (0, x) :=
          ih D.derived₁ (FlatAtZero.deriv hflat) (AllMoments.shift hm) x
        rwa [FlatAtZero.deriv_apply_zero hflat, zero_smul] at h
      have ih2 : iteratedFDerivWithin ℝ m D.derived₂.series leftHalf (0, x) =
          D.ψ 0 • iteratedFDerivWithin ℝ m D.derived₂.h rightHalf (0, x) :=
        ih D.derived₂ hflat (AllMoments.shift hm) x
      have ih3 : iteratedFDerivWithin ℝ m D.derived₃.series leftHalf (0, x) =
          D.ψ 0 • iteratedFDerivWithin ℝ m D.derived₃.h rightHalf (0, x) :=
        ih D.derived₃ hflat hm x
      have ES : Set.EqOn (fun y => fderivWithin ℝ D.series leftHalf y)
          (jetL1 ∘ D.derived₁.series + (jetL1 ∘ D.derived₂.series + jetL3 ∘ D.derived₃.series))
          leftHalf := by
        intro z hz
        show fderivWithin ℝ D.series leftHalf z =
          (jetL1 ∘ D.derived₁.series + (jetL1 ∘ D.derived₂.series + jetL3 ∘ D.derived₃.series)) z
        rw [SeriesData.fderivWithin_series_eq_seriesJet D hz]
        apply ContinuousLinearMap.ext
        intro u
        simp [SeriesData.seriesJet, Function.comp_apply, Pi.add_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply]
      have EH : Set.EqOn (fun y => fderivWithin ℝ D.h rightHalf y)
          (jetL1 ∘ D.derived₂.h + jetL3 ∘ D.derived₃.h) rightHalf := by
        intro z hz
        apply ContinuousLinearMap.ext
        intro u
        have hu' : u = u.1 • ((1 : ℝ), (0 : Space)) +
            ContinuousLinearMap.inr ℝ ℝ Space u.2 := by
          ext
          · simp
          · simp [ContinuousLinearMap.inr_apply]
        show (fderivWithin ℝ D.h rightHalf z) u =
          u.1 • ((fderivWithin ℝ D.h rightHalf z) ((1 : ℝ), (0 : Space))) +
            ((fderivWithin ℝ D.h rightHalf z).comp (ContinuousLinearMap.inr ℝ ℝ Space)) u.2
        conv_lhs => rw [hu']
        rw [map_add, map_smul, ContinuousLinearMap.comp_apply]
      have stepC : iteratedFDerivWithin ℝ m
            (jetL1 ∘ D.derived₁.series + (jetL1 ∘ D.derived₂.series + jetL3 ∘ D.derived₃.series))
            leftHalf (0, x) =
          jetL1.compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ m D.derived₁.series leftHalf (0, x)) +
          (jetL1.compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ m D.derived₂.series leftHalf (0, x)) +
           jetL3.compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ m D.derived₃.series leftHalf (0, x))) := by
        rw [iteratedFDerivWithin_add_apply hA1 hA23 hu hz₀,
          iteratedFDerivWithin_add_apply hA2 hA3 hu hz₀,
          jetL1.iteratedFDerivWithin_comp_left hC1 hu hz₀ hle,
          jetL1.iteratedFDerivWithin_comp_left hC2 hu hz₀ hle,
          jetL3.iteratedFDerivWithin_comp_left hC3 hu hz₀ hle]
      have stepF : iteratedFDerivWithin ℝ m (fun y => fderivWithin ℝ D.h rightHalf y)
            rightHalf (0, x) =
          jetL1.compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ m D.derived₂.h rightHalf (0, x)) +
          jetL3.compContinuousMultilinearMap
            (iteratedFDerivWithin ℝ m D.derived₃.h rightHalf (0, x)) := by
        rw [iteratedFDerivWithin_congr EH hzR m,
          iteratedFDerivWithin_add_apply hB2 hB3 hur hzR,
          jetL1.iteratedFDerivWithin_comp_left hD2 hur hzR hle,
          jetL3.iteratedFDerivWithin_comp_left hD3 hur hzR hle]
      have e1 : iteratedFDerivWithin ℝ (m + 1) D.series leftHalf (0, x) =
          (continuousMultilinearCurryRightEquiv' ℝ m (ℝ × Space) V).symm
            (iteratedFDerivWithin ℝ m (fun y => fderivWithin ℝ D.series leftHalf y)
              leftHalf (0, x)) := by
        have h := iteratedFDerivWithin_succ_eq_comp_right uniqueDiffOn_leftHalf hz₀
          (f := D.series) (n := m)
        rwa [Function.comp_apply] at h
      have e2 : iteratedFDerivWithin ℝ (m + 1) D.h rightHalf (0, x) =
          (continuousMultilinearCurryRightEquiv' ℝ m (ℝ × Space) V).symm
            (iteratedFDerivWithin ℝ m (fun y => fderivWithin ℝ D.h rightHalf y)
              rightHalf (0, x)) := by
        have h := iteratedFDerivWithin_succ_eq_comp_right uniqueDiffOn_rightHalf hzR
          (f := D.h) (n := m)
        rwa [Function.comp_apply] at h
      rw [e1, e2, iteratedFDerivWithin_congr ES hz₀ m, stepC, ih1, ih2, ih3, stepF]
      ext v
      simp [smul_add]

end JetBoundary

/-- **Seeley jet match**: at every boundary point and every order, the
field's right-half iterated jet equals the reflection series' left-half
iterated jet.  Specialization of `series_jet_boundary` to the Seeley data;
the cutoff value `seeleyPhi 0 = 1` collapses the scalar. -/
theorem seeley_jet_match {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') (hg : HalfSpaceSmooth g) (m : ℕ) (x : Space) :
    iteratedFDerivWithin ℝ m (jointMap g) rightHalf (0, x) =
      iteratedFDerivWithin ℝ m (topData g hg).series leftHalf (0, x) := by
  have h : iteratedFDerivWithin ℝ m (topData g hg).series leftHalf (0, x) =
      seeleyPhi 0 • iteratedFDerivWithin ℝ m (jointMap g) rightHalf (0, x) :=
    series_jet_boundary m (topData g hg) flatAtZero_seeleyPhi allMoments_seeleyA x
  rw [seeleyPhi_zero, one_smul] at h
  exact h.symm

/-- **Seeley's extension theorem** (half-space, spacetime form): every
within-smooth field on the closed nonnegative-time half-space admits a
globally smooth extension agreeing with it on nonnegative times. -/
theorem seeley_extension {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (g : ℝ → Space → E') (hg : HalfSpaceSmooth g) :
    Nonempty (HalfSpaceSmoothExtension g) := by
  refine ⟨⟨GluedData.glued ⟨jointMap g, (topData g hg).series, hg,
      SeriesData.contDiffOn_series_leftHalf _, fun x => (topData_series_boundary g hg x).symm,
      fun m x => seeley_jet_match g hg m x⟩, GluedData.contDiff_glued _, fun t ht x => ?_⟩⟩
  show (if (0 : ℝ) ≤ t then jointMap g (t, x) else (topData g hg).series (t, x)) = g t x
  rw [if_pos ht]
  rfl

end Navier.Analysis.HalfSpaceSmoothnessBridge.SeeleyGlue
