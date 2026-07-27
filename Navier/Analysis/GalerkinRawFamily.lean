import Navier.Analysis.GalerkinBasis

/-!
# A countable independent divergence-free family (strictly-lower sub-lemma)

**Status**: this file closes the `divergence_free` and `independent` fields of
`RawDivFreeFamily` (`Navier.Analysis.GalerkinBasis`) for an EXPLICIT family —
pairwise-disjoint-support translates of the already-certified curl-of-bump
field `phiSchwartz` (`Navier.Analysis.LerayWeak`).  It does **not** close
`exists_rawDivFreeFamily`: that theorem's `dense_span` obligation needs a
family whose finite spans are `L²`-dense in the FULL divergence-free Schwartz
class, and a family of translates of ONE fixed shape at pairwise-disjoint
supports provably cannot be dense-spanning (a finite combination is supported
on a bounded union of disjoint balls, so it cannot `L²`-approximate a
divergence-free Schwartz datum whose mass lies outside every one of those
balls — e.g. a bump at a location none of the `v_j` reach). Density needs a
genuinely different route: EITHER a translate family at a DENSE set of
centers plus a Wiener-type "closed span of translates = whole space iff the
generator's Fourier transform is a.e. nonzero" theorem, OR a Helmholtz/Leray
vector-potential representation (`u = curl A`) combined with an `H¹`-dense
(not just `L²`-dense) scalar potential family — both genuinely
Mathlib-absent and each individually deep.  This file's contribution is the
two fields that ARE closable now, isolated as a fresh, independently
checkable leaf so future dense-span work only has one obligation left.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace Navier.Analysis.GalerkinBasis

open Navier
open Navier.Analysis.Enstrophy
open Navier.Analysis.LerayWeak
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.Vorticity

open scoped ContDiff

/-!
## A translate of the certified curl-of-bump field
-/

/-- `phiSchwartz`, recentred at `c` (raw function level). -/
def shiftPhi (c : Space) : Space → Space := fun y => phiSchwartz (y - c)

/-- Translation invariance of the Fréchet derivative: `d/dy[f(y-c)]|_x = f'(x-c)`. -/
theorem fderiv_shiftPhi (c x : Space) :
    fderiv ℝ (shiftPhi c) x = fderiv ℝ (⇑phiSchwartz) (x - c) := by
  have hg : HasFDerivAt (⇑phiSchwartz) (fderiv ℝ (⇑phiSchwartz) (x - c)) (x - c) :=
    (phiSchwartz.smooth 1).differentiable (by norm_num) |>.differentiableAt.hasFDerivAt
  have hl := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const c
  have hcomp := hg.comp x hl
  exact hcomp.fderiv

theorem shiftPhi_smooth (c : Space) : ContDiff ℝ (⊤ : ℕ∞) (shiftPhi c) :=
  (phiSchwartz.smooth (⊤ : ℕ∞)).comp (contDiff_id.sub contDiff_const)

theorem shiftPhi_continuous (c : Space) : Continuous (shiftPhi c) :=
  phiSchwartz.continuous.comp (continuous_id.sub continuous_const)

theorem phiSchwartz_coe_hasCompactSupport :
    HasCompactSupport (⇑phiSchwartz : Space → Space) := by
  have heq : (⇑phiSchwartz : Space → Space) = phifun := by
    funext x; exact phiSchwartz_apply x
  rw [heq]; exact phifun_supp

theorem shiftPhi_hasCompactSupport (c : Space) : HasCompactSupport (shiftPhi c) :=
  phiSchwartz_coe_hasCompactSupport.comp_homeomorph (Homeomorph.subRight c)

/-- The recentred field, bundled as a Schwartz map. -/
def shiftSchwartz (c : Space) : SchwartzVelocity :=
  (shiftPhi_hasCompactSupport c).toSchwartzMap (shiftPhi_smooth c)

theorem shiftSchwartz_apply (c x : Space) : shiftSchwartz c x = shiftPhi c x := rfl

/-- Every recentred copy of `phiSchwartz` is still divergence-free: divergence
is a spatial-derivative functional, and translation of the argument by a
constant only re-evaluates the base point (`fderiv_shiftPhi`). -/
theorem shiftSchwartz_divFree (c : Space) : DivergenceFreeInitial (shiftSchwartz c) := by
  intro x
  show staticDivergence (fun y => shiftSchwartz c y) x = 0
  have hcoe : (fun y => shiftSchwartz c y) = shiftPhi c := by
    funext y; exact shiftSchwartz_apply c y
  rw [hcoe]
  unfold staticDivergence
  have hstep : ∀ i : Fin 3, fderiv ℝ (shiftPhi c) x (basisVector i) =
      fderiv ℝ (⇑phiSchwartz) (x - c) (basisVector i) := by
    intro i; rw [fderiv_shiftPhi]
  simp only [hstep]
  have hzero := phiSchwartz_divfree (x - c)
  simpa [staticDivergence] using hzero

/-- No recentred copy of `phiSchwartz` is the zero field. -/
theorem shiftSchwartz_ne_zero (c : Space) : shiftSchwartz c ≠ 0 := by
  intro h
  have hfun0 : (⇑(shiftSchwartz c) : Space → Space) = (⇑(0 : SchwartzVelocity) : Space → Space) :=
    congrArg (fun f : SchwartzVelocity => (⇑f : Space → Space)) h
  have hfun : (fun y : Space => phiSchwartz (y - c)) = (0 : Space → Space) := by
    funext y
    have := congrFun hfun0 y
    simpa [shiftSchwartz_apply, shiftPhi] using this
  apply phiSchwartz_ne_zero
  have hfun2 : (⇑phiSchwartz : Space → Space) = 0 := by
    funext y
    have := congrFun hfun (y + c)
    simpa using this
  exact DFunLike.coe_injective hfun2

/-!
## Far-support vanishing and disjointness
-/

/-- A radius outside which the certified bump field vanishes. -/
theorem exists_phiSchwartz_support_radius :
    ∃ R0 : ℝ, 0 ≤ R0 ∧
      tsupport (⇑phiSchwartz : Space → Space) ⊆ Metric.closedBall (0 : Space) R0 := by
  obtain ⟨R, hR⟩ := phiSchwartz_coe_hasCompactSupport.isBounded.subset_closedBall (0 : Space)
  exact ⟨max R 0, le_max_right _ _, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩

theorem shiftPhi_eq_zero_of_far (c x : Space) (R0 : ℝ)
    (hR0 : tsupport (⇑phiSchwartz : Space → Space) ⊆ Metric.closedBall (0 : Space) R0)
    (hx : R0 < dist x c) : shiftPhi c x = 0 := by
  show phiSchwartz (x - c) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hb := hR0 hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  rw [dist_eq_norm] at hx
  linarith

/-!
## Orthogonality and positivity for far-apart centres
-/

theorem shiftSchwartz_orthogonal_of_far (c d : Space) (R0 : ℝ)
    (hR0 : tsupport (⇑phiSchwartz : Space → Space) ⊆ Metric.closedBall (0 : Space) R0)
    (hfar : 2 * R0 < dist c d) :
    schwartzL2Inner (shiftSchwartz c) (shiftSchwartz d) = 0 := by
  unfold schwartzL2Inner
  have hzero : (fun x : Space => officialInner (shiftSchwartz c x) (shiftSchwartz d x)) = fun _ => 0 := by
    funext x
    by_cases h1 : dist x c ≤ R0
    · have hxd : R0 < dist x d := by
        have htri : dist c d ≤ dist c x + dist x d := dist_triangle c x d
        rw [dist_comm x c] at h1
        linarith
      rw [shiftSchwartz_apply, shiftSchwartz_apply, shiftPhi_eq_zero_of_far d x R0 hR0 hxd]
      rw [officialInner_comm]; exact officialInner_zero_left _
    · rw [shiftSchwartz_apply, shiftSchwartz_apply,
        shiftPhi_eq_zero_of_far c x R0 hR0 (not_le.mp h1)]
      exact officialInner_zero_left _
  rw [hzero, integral_zero]

theorem shiftSchwartz_self_pos (c : Space) :
    0 < schwartzL2Inner (shiftSchwartz c) (shiftSchwartz c) := by
  obtain ⟨x0, hx0⟩ : ∃ x, shiftSchwartz c x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply shiftSchwartz_ne_zero c
    exact DFunLike.coe_injective (by funext y; exact hcon y)
  unfold schwartzL2Inner
  have hcont : Continuous (fun x : Space => officialInner (shiftSchwartz c x) (shiftSchwartz c x)) := by
    simp only [officialInner_eq_sum]
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp (shiftSchwartz c).continuous).mul
        ((continuous_apply i).comp (shiftSchwartz c).continuous))
  have hsupp : HasCompactSupport (fun x : Space => officialInner (shiftSchwartz c x) (shiftSchwartz c x)) := by
    have hs : HasCompactSupport (shiftPhi c) := shiftPhi_hasCompactSupport c
    have hsub : Function.support (fun x : Space => officialInner (shiftSchwartz c x) (shiftSchwartz c x))
        ⊆ Function.support (shiftPhi c) := by
      intro x hx
      rw [Function.mem_support] at hx ⊢
      intro hcon
      apply hx
      have hz : shiftSchwartz c x = 0 := by rw [shiftSchwartz_apply]; exact hcon
      rw [hz, officialInner_zero_left]
    exact hs.mono hsub
  apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcont hsupp
  · intro x
    show 0 ≤ officialInner (shiftSchwartz c x) (shiftSchwartz c x)
    rw [officialInner_self]; positivity
  · show officialInner (shiftSchwartz c x0) (shiftSchwartz c x0) ≠ 0
    rw [officialInner_self]
    intro hcontra
    apply hx0
    have hz : officialEuclideanNorm (shiftSchwartz c x0) = 0 := by
      nlinarith [officialEuclideanNorm_nonneg (shiftSchwartz c x0)]
    exact (officialEuclideanNorm_eq_zero_iff _).mp hz

/-!
## The countable family: centres spaced far enough apart
-/

/-- The `n`-th centre: `(2R0+1)(n+1)` along the first axis, so consecutive
centres are `2R0+1` apart and all pairwise distances exceed `2R0`. -/
def famCentre (R0 : ℝ) (n : ℕ) : Space := ((2 * R0 + 1) * (n + 1)) • basisVector 0

theorem famCentre_dist (R0 : ℝ) (hR0 : 0 ≤ R0) {n m : ℕ} (hnm : n < m) :
    2 * R0 < dist (famCentre R0 n) (famCentre R0 m) := by
  have hb0 : ‖(basisVector 0 : Space)‖ = 1 := by simp [basisVector, Pi.norm_single]
  have h1 : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
    have h2 : n + 1 ≤ m := hnm
    have h3 := (Nat.cast_le (α := ℝ)).mpr h2
    push_cast at h3; linarith
  unfold famCentre
  rw [dist_eq_norm, ← sub_smul, norm_smul, hb0, mul_one]
  have heq : (2 * R0 + 1) * ((n : ℝ) + 1) - (2 * R0 + 1) * ((m : ℝ) + 1)
      = (2 * R0 + 1) * ((n : ℝ) - (m : ℝ)) := by ring
  rw [heq, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by linarith : (0:ℝ) < 2 * R0 + 1)]
  rw [abs_sub_comm]
  have h4 : |(m:ℝ) - (n:ℝ)| = (m:ℝ) - (n:ℝ) := abs_of_pos (by linarith)
  rw [h4]
  nlinarith

/-- The family itself: translates of the certified curl-of-bump field at the
spaced-out centres `famCentre R0 n`. -/
def famV (R0 : ℝ) (n : ℕ) : SchwartzVelocity := shiftSchwartz (famCentre R0 n)

theorem famV_divFree (R0 : ℝ) (n : ℕ) : DivergenceFreeInitial (famV R0 n) :=
  shiftSchwartz_divFree (famCentre R0 n)

theorem famV_orthogonal (R0 : ℝ) (hR0 : 0 ≤ R0)
    (hR0supp : tsupport (⇑phiSchwartz : Space → Space) ⊆ Metric.closedBall (0 : Space) R0)
    {n m : ℕ} (hnm : n ≠ m) :
    schwartzL2Inner (famV R0 n) (famV R0 m) = 0 := by
  rcases lt_or_gt_of_ne hnm with h | h
  · exact shiftSchwartz_orthogonal_of_far _ _ R0 hR0supp (famCentre_dist R0 hR0 h)
  · rw [schwartzL2Inner_comm]
    exact shiftSchwartz_orthogonal_of_far _ _ R0 hR0supp (famCentre_dist R0 hR0 h)

theorem famV_self_pos (R0 : ℝ) (n : ℕ) : 0 < schwartzL2Inner (famV R0 n) (famV R0 n) :=
  shiftSchwartz_self_pos (famCentre R0 n)

/-!
## Independence: a null finite combination has all-zero coefficients
-/

theorem famV_independent (R0 : ℝ) (hR0 : 0 ≤ R0)
    (hR0supp : tsupport (⇑phiSchwartz : Space → Space) ⊆ Metric.closedBall (0 : Space) R0) :
    ∀ (n : ℕ) (coef : ℕ → ℝ),
      schwartzL2Inner (∑ j ∈ Finset.range n, coef j • famV R0 j)
          (∑ j ∈ Finset.range n, coef j • famV R0 j) = 0 →
      ∀ j ∈ Finset.range n, coef j = 0 := by
  intro n
  induction n with
  | zero => intro coef _ j hj; simp at hj
  | succ n ih =>
    intro coef hsum j hj
    rw [Finset.sum_range_succ] at hsum
    set A := ∑ k ∈ Finset.range n, coef k • famV R0 k with hAdef
    set B := coef n • famV R0 n with hBdef
    have hABortho : schwartzL2Inner A B = 0 := by
      rw [hAdef, hBdef, schwartzL2Inner_sum_left]
      apply Finset.sum_eq_zero
      intro k hk
      rw [schwartzL2Inner_smul_left, schwartzL2Inner_smul_right]
      have hkn : k ≠ n := (Finset.mem_range.mp hk).ne
      rw [famV_orthogonal R0 hR0 hR0supp hkn]
      ring
    rw [schwartzL2Inner_self_add_of_orthogonal A B hABortho] at hsum
    have hAnn : 0 ≤ schwartzL2Inner A A := schwartzL2Inner_self_nonneg A
    have hBnn : 0 ≤ schwartzL2Inner B B := schwartzL2Inner_self_nonneg B
    have hA0 : schwartzL2Inner A A = 0 := by linarith
    have hB0 : schwartzL2Inner B B = 0 := by linarith
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rcases hjle.lt_or_eq with hjn | hjn
    · exact ih coef hA0 j (Finset.mem_range.mpr hjn)
    · subst hjn
      rw [hBdef, schwartzL2Inner_smul_left, schwartzL2Inner_smul_right] at hB0
      have hpos : 0 < schwartzL2Inner (famV R0 j) (famV R0 j) := famV_self_pos R0 j
      have hsq : coef j * coef j = 0 := by
        rcases mul_eq_zero.mp (by linarith : coef j * coef j * schwartzL2Inner (famV R0 j) (famV R0 j) = 0) with h | h
        · exact h
        · exact absurd h (ne_of_gt hpos)
      exact mul_self_eq_zero.mp hsq

/-!
## Bundled result: the strictly-lower sub-lemma feeding `exists_rawDivFreeFamily`
-/

/-- **A countable `L²`-independent divergence-free family exists.**  This
closes the `divergence_free` and `independent` fields of `RawDivFreeFamily`
for an explicit family (disjoint-support translates of the certified
`phiSchwartz`).  The sole remaining obstruction to
`exists_rawDivFreeFamily` is `dense_span`, which this specific family does
NOT satisfy (see the file docstring) — density needs a family that is
richer than disjoint translates of one fixed shape. -/
theorem exists_countable_independent_divFree_family :
    ∃ v : ℕ → SchwartzVelocity,
      (∀ j : ℕ, DivergenceFreeInitial (v j)) ∧
      (∀ (n : ℕ) (coef : ℕ → ℝ),
        schwartzL2Inner (∑ j ∈ Finset.range n, coef j • v j)
            (∑ j ∈ Finset.range n, coef j • v j) = 0 →
        ∀ j ∈ Finset.range n, coef j = 0) := by
  obtain ⟨R0, hR0, hR0supp⟩ := exists_phiSchwartz_support_radius
  exact ⟨famV R0, famV_divFree R0, famV_independent R0 hR0 hR0supp⟩

end Navier.Analysis.GalerkinBasis
