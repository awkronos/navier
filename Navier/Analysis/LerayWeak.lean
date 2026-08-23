import Navier.Analysis.Enstrophy
import Navier.Analysis.DissipativeODEGlobal
import Navier.Analysis.RieszKolmogorov
import Navier.Analysis.EnergyNormBridge

/-!
# Leray–Hopf weak solutions (rung 4 skeleton tower)

Leray (1934) proved global existence of weak solutions: divergence-free
`L²` velocity fields satisfying the Navier–Stokes equations against
divergence-free test functions, with non-increasing kinetic energy.  This file
lays the weak layer over the repository's own objects (`SchwartzVelocity`
slices, the `officialInner` pairing, the repo's Fréchet operators), so the
Galerkin/compactness tower has a home with no floating restatement.

## Encoding decisions (Step-0e checked)

* Test functions are **Schwartz-sliced, divergence-free, compact-in-time**
  (`DivergenceFreeTestFunction`).  Quantifying over this subclass of the
  classical test class makes the existence statement weaker-or-equal to
  Leray's — hence still TRUE — while staying expressible with the repo's
  Fréchet operators.  Pressure is eliminated by divergence-free tests, as
  usual.
* The weak form keeps explicit `x`-integrability fields; for a Leray solution
  (`u ∈ L^∞_t L²_x`) each pairing is integrable, so the fields are honest
  rather than restrictive.
* **Anti-vacuity**: `zeroTestFunction` inhabits the test class (so
  `weak_form` quantifies over a nonempty type), and `zero_isLerayHopfWeak`
  shows the zero solution realizes the structure for zero data.  That the
  test class contains a NONZERO member — without which `weak_form` would be
  trivially satisfiable and existence vacuous — is the point of the
  `exists_nonzero_testFunction` skeleton (curl-of-bump construction).

## Certified here (no sorry)

* `DivergenceFreeTestFunction` + `zeroTestFunction` (inhabitant).
* `exists_nonzero_testFunction` — the test class has a NONZERO member
  (curl-of-bump: smooth compactly-supported scalar, divergence-free by
  Clairaut, nonzero by a line-constancy contradiction, smooth-transition
  time envelope) — `weak_form` is not trivially satisfiable.
* `officialInner_zero_left` and the zero-solution smoke
  `zero_isLerayHopfWeak` — the structure is realizable, hence non-degenerate.
* **Coordinate-norm bridge** — `norm_sq_le_officialInner_self`,
  `officialInner_self_le_three_norm_sq`, `integrable_norm_sq_schwartz`,
  `integrable_officialInner_self`, and
  `tendsto_integral_norm_sq_of_tendsto_officialInner_self`: the product norm on
  `Space = Fin 3 → ℝ` versus Fefferman's Euclidean pairing.  This converts the
  Galerkin layer's Bessel convergence (Euclidean seminorm) into the
  product-norm `initial_converges` field.
* `galerkinApproximation_of_modeData` — transport of `GalerkinModeData` (the
  shape the finite-mode layer produces) to a `GalerkinApproximation`, plus the
  anti-vacuity inhabitant `zeroGalerkinModeData`.
* `StrongL2LocLimit.comp_strictMono`, `strongL2LocLimit_const`,
  `aubinLions_zero_instance` — subsequence bookkeeping for the Aubin–Lions
  diagonal extraction and the hypothesis/conclusion non-vacuity smoke.
* **Aubin–Lions assembly** — `aubin_lions_l2loc_compactness` is now a
  composition with no `sorry` of its own, on the Pattern-A repaired hypothesis
  list.  Three certified pieces carry it: `exists_diagonal_subseq` /
  `exists_subseq_forall_windowCauchy` (nested Cantor diagonal over the countable
  exhaustion, via `WindowCauchy.comp_strictMono` and `WindowCauchy.of_tail`);
  `strongL2LocLimit_of_natWindows` (integer windows ⇒ real windows, the step
  `JointlyMeasurable` unlocks) with its leaf `integrable_norm_sub_sq`; and the
  two named textbook residuals below.
* **Initial-slice patch** — `patchInitial`, `setIntegral_Ici_congr_off_zero`
  (the time integral over `Set.Ici 0` ignores the null set `{0}`), and
  `isLerayHopfWeakSolution_patchInitial`: `LerayLimitData` (Leray–Hopf clauses
  for `t > 0` only, which is all a compactness limit can give) transports to a
  full `IsLerayHopfWeakSolution` with pointwise `initial_attained`.  Anti-vacuity
  inhabitant: `zeroLerayLimitData`.
* `leray_of_galerkinApproximation` is a **composition**, with no `sorry` of
  its own.  `exists_galerkinModeData`, `galerkin_approximation_exists`, and
  `leray_weak_existence` (same namespace, same names, same types) live
  downstream in `Navier.Analysis.LerayWeakExistence` since 2026-08-18, wired
  to `GalerkinBasis.exists_galerkinModeData` instead of a duplicate upstream
  `sorry` — see the residual ledger.
* `exists_subseq_windowCauchy` — Riesz–Fréchet–Kolmogorov total boundedness on
  the single bounded window `(0,n] × B̄(0,n)` [Brezis 2011 Thm 4.26 + Cor 4.27;
  Simon 1987 Thm 1] — now CERTIFIED: the dyadic-average projection route,
  assembled from the cell family `winCellFinset`, the enclosure `encW`, the
  uniform translation modulus `fwd_modulus_encW` (kinetic collar +
  `nested_window_modulus`), `sum_cellError_le_modulus_of_memL2`, the
  cell-average step function `cellStep` with the ε/3 assembly
  `windowError_le_three_legs`, Bolzano–Weierstrass on the cell-average vector,
  and the `exists_diagonal_subseq` diagonal over the scale ladder `1/(l+1)`.
  With it, `aubin_lions_l2loc_compactness` is a complete composition.  This and
  the Fischer–Riesz leaf replace the former monolithic
  `aubin_lions_l2loc_compactness` residual, whose hypothesis list was FALSE as
  stated; the checked curl-free witness is in that theorem's docstring and in
  `experiments/aubin_lions_curlfree_witness.py`.

## Named residuals (honest `sorry`, strictly-lower leaves)

* (`exists_galerkinModeData` — the finite-mode Galerkin construction — was
  RELOCATED 2026-08-18 to `Navier.Analysis.LerayWeakExistence`, where it is a
  one-line composition of `GalerkinBasis.exists_galerkinModeData`; that
  downstream construction is assembled modulo exactly the named residuals
  `hspace`/`htime`/`hweak` [Temam III.3; Constantin–Foias II; Leray 1934
  §§18–20].  The duplicate upstream `sorry` is deleted.)
(`exists_limit_of_forall_windowCauchy` — Fischer–Riesz limit extraction from
window-Cauchy, with the pointwise-limit-or-zero representative that makes the
slicewise clauses true at **every** `t ≥ 0` [Brezis 2011 Thm 4.8] — is CERTIFIED
below.)
* `exists_lerayLimitData` — limit passage in the weak form, stated for `t > 0`
  [Leray 1934 §§21–23; Temam III.3.3; est ~700 LOC].
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace Navier.Analysis.LerayWeak

open scoped ContDiff

open Navier
open Navier.Analysis.Enstrophy
open Navier.Analysis.RieszKolmogorov
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.EnergyNormBridge

/-!
## Test functions
-/

/-- A divergence-free, compact-spacetime test function on nonnegative
spacetime, presented through Schwartz spatial slices.  The common compact
spatial carriers rule out slice supports escaping to infinity as time
approaches the terminal horizon. -/
structure DivergenceFreeTestFunction where
  /-- The Schwartz slice at each time. -/
  field : ℝ → SchwartzVelocity
  /-- The genuine Schwartz slice of the time derivative. -/
  timeDerivSchwartz : ℝ → SchwartzVelocity
  /-- Pointwise identification with the half-line time derivative used by the
  weak formulation. -/
  timeDeriv_eq : ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
    timeDerivative (fun s => (field s : Space → Space)) t x =
      timeDerivSchwartz t x
  /-- Joint spacetime smoothness on the nonnegative-time half-space, in the
  repo's within-derivative convention. -/
  smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × Space => (field z.1) z.2)
    ((Set.Ici (0:ℝ)) ×ˢ (Set.univ : Set Space))
  /-- The test function vanishes beyond a finite horizon. -/
  compact_time : ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → field t = 0
  /-- The time derivative has the same classical compact-time behavior. -/
  compact_time_deriv : ∃ T : ℝ, 0 < T ∧
    ∀ t : ℝ, T ≤ t → timeDerivSchwartz t = 0
  /-- All test slices vanish off one compact spatial carrier. -/
  compact_space : ∃ K : Set Space, IsCompact K ∧
    ∀ t : ℝ, ∀ x : Space, x ∉ K → field t x = 0
  /-- All time-derivative slices vanish off one compact spatial carrier. -/
  compact_space_deriv : ∃ K : Set Space, IsCompact K ∧
    ∀ t : ℝ, ∀ x : Space, x ∉ K → timeDerivSchwartz t x = 0
  /-- Every slice is divergence-free. -/
  divergence_free : ∀ t : ℝ, DivergenceFreeInitial (field t)

/-- The zero test function (inhabitant of the test class). -/
def zeroTestFunction : DivergenceFreeTestFunction where
  field := fun _ => 0
  timeDerivSchwartz := fun _ => 0
  timeDeriv_eq := by
    intro t ht x
    simp [timeDerivative]
  smooth := by
    have : (fun z : ℝ × Space => ((0 : SchwartzVelocity)) z.2) =
        fun _ : ℝ × Space => (0 : Space) := by
      funext z; simp
    simpa [this] using contDiffOn_const
  compact_time := ⟨1, one_pos, fun _ _ => rfl⟩
  compact_time_deriv := ⟨1, one_pos, fun _ _ => rfl⟩
  compact_space := ⟨∅, isCompact_empty, by simp⟩
  compact_space_deriv := ⟨∅, isCompact_empty, by simp⟩
  divergence_free := by
    intro t x
    simp [staticDivergence]

instance : Inhabited DivergenceFreeTestFunction := ⟨zeroTestFunction⟩

/-!
## A nonzero divergence-free test function (anti-vacuity, realized)

The curl-of-bump construction: for a smooth compactly-supported scalar bump
`g`, the field `x ↦ (∂₁g)(x)·e₀ − (∂₀g)(x)·e₁` is smooth, compactly supported
(hence Schwartz), divergence-free by Clairaut symmetry, and nonzero — were it
zero, `∂₀g ≡ 0` would make `g` constant along the `e₀`-line through the
origin, contradicting `g(0) = 1` with compact support.  A smooth-transition
time envelope makes it a compact-in-time test function.
-/

/-- A concrete smooth bump on `Space`. -/
noncomputable def bump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def gfun : Space → ℝ := ⇑bump

theorem gfun_smooth : ContDiff ℝ ∞ gfun := bump.contDiff
theorem gfun_supp : HasCompactSupport gfun := bump.hasCompactSupport
theorem gfun_zero : gfun 0 = 1 :=
  bump.one_of_mem_closedBall (Metric.mem_closedBall_self one_pos.le)

/-- The curl-of-bump velocity field `(∂₁g)·e₀ − (∂₀g)·e₁`. -/
noncomputable def phifun : Space → Space := fun x =>
  (fderiv ℝ gfun x (basisVector 1)) • basisVector 0 -
    (fderiv ℝ gfun x (basisVector 0)) • basisVector 1

theorem fderiv_gfun_smooth : ContDiff ℝ ∞ (fderiv ℝ gfun) :=
  gfun_smooth.fderiv_right (m := ∞) (by decide)

theorem comp_smooth (w : Space) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ gfun x w) :=
  fderiv_gfun_smooth.clm_apply contDiff_const

theorem phifun_smooth : ContDiff ℝ ∞ phifun := by
  unfold phifun
  have h1 := comp_smooth (basisVector 1)
  have h0 := comp_smooth (basisVector 0)
  fun_prop

theorem comp_supp (w : Space) :
    HasCompactSupport (fun x => fderiv ℝ gfun x w) :=
  (gfun_supp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L w) rfl

theorem phifun_supp : HasCompactSupport phifun := by
  apply HasCompactSupport.sub
  · exact (comp_supp (basisVector 1)).comp_left
      (g := fun r : ℝ => r • basisVector 0) (zero_smul _ _)
  · exact (comp_supp (basisVector 0)).comp_left
      (g := fun r : ℝ => r • basisVector 1) (zero_smul _ _)

/-- The bundled Schwartz field. -/
noncomputable def phiSchwartz : SchwartzVelocity :=
  phifun_supp.toSchwartzMap phifun_smooth

theorem phiSchwartz_apply (x : Space) : phiSchwartz x = phifun x := rfl

-- mixed-partial commutation for the bump
theorem mixed_partial (x u v : Space) :
    fderiv ℝ (fun y => fderiv ℝ gfun y u) x v =
      fderiv ℝ (fderiv ℝ gfun) x v u := by
  rw [fderiv_clm_apply
    (fderiv_gfun_smooth.differentiable (by decide) |>.differentiableAt)
    (differentiableAt_const u)]
  simp

theorem second_symm (x u v : Space) :
    fderiv ℝ (fderiv ℝ gfun) x u v = fderiv ℝ (fderiv ℝ gfun) x v u := by
  have hs : IsSymmSndFDerivAt ℝ gfun x :=
    (gfun_smooth.contDiffAt).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
  exact hs u v

/-- Divergence-free: the Clairaut cancellation. -/
theorem phiSchwartz_divfree : DivergenceFreeInitial phiSchwartz := by
  intro x
  show staticDivergence (fun y => phiSchwartz y) x = 0
  have hcoe : (fun y => phiSchwartz y) = phifun := rfl
  rw [hcoe]
  -- differentiability of the two summands
  have hd1 : DifferentiableAt ℝ (fun y => fderiv ℝ gfun y (basisVector 1)) x :=
    ((comp_smooth (basisVector 1)).differentiable (by decide)).differentiableAt
  have hd0 : DifferentiableAt ℝ (fun y => fderiv ℝ gfun y (basisVector 0)) x :=
    ((comp_smooth (basisVector 0)).differentiable (by decide)).differentiableAt
  have hA : DifferentiableAt ℝ
      (fun y => (fderiv ℝ gfun y (basisVector 1)) • basisVector 0) x :=
    hd1.smul_const _
  have hB : DifferentiableAt ℝ
      (fun y => (fderiv ℝ gfun y (basisVector 0)) • basisVector 1) x :=
    hd0.smul_const _
  have hsplit : ∀ i : Fin 3,
      fderiv ℝ phifun x (basisVector i) =
        (fderiv ℝ (fun y => fderiv ℝ gfun y (basisVector 1)) x (basisVector i))
          • basisVector 0 -
        (fderiv ℝ (fun y => fderiv ℝ gfun y (basisVector 0)) x (basisVector i))
          • basisVector 1 := by
    intro i
    unfold phifun
    have hAB := (hd1.hasFDerivAt.smul_const (basisVector 0)).sub
      (hd0.hasFDerivAt.smul_const (basisVector 1))
    rw [show (fun y : Space =>
        (fderiv ℝ gfun y) (basisVector 1) • basisVector 0 -
          (fderiv ℝ gfun y) (basisVector 0) • basisVector 1) =
      ((fun y : Space => (fderiv ℝ gfun y) (basisVector 1) • basisVector 0) -
        fun y : Space => (fderiv ℝ gfun y) (basisVector 0) • basisVector 1)
      from rfl]
    rw [hAB.fderiv]
    simp
  unfold staticDivergence
  rw [Fin.sum_univ_three]
  rw [hsplit 0, hsplit 1, hsplit 2]
  -- basisVector components
  have hb00 : basisVector 0 (0 : Fin 3) = 1 := rfl
  have hb01 : basisVector 0 (1 : Fin 3) = 0 := rfl
  have hb02 : basisVector 0 (2 : Fin 3) = 0 := rfl
  have hb10 : basisVector 1 (0 : Fin 3) = 0 := rfl
  have hb11 : basisVector 1 (1 : Fin 3) = 1 := rfl
  have hb12 : basisVector 1 (2 : Fin 3) = 0 := rfl
  simp only [Pi.sub_apply, Pi.smul_apply, hb00, hb01, hb02, hb10, hb11, hb12,
    smul_eq_mul, mul_one, mul_zero, sub_zero, zero_sub]
  -- remaining: D(∂₁g)(e₀) − (−D(∂₀g)(e₁)) pattern
  rw [mixed_partial x (basisVector 1) (basisVector 0),
    mixed_partial x (basisVector 0) (basisVector 1)]
  rw [second_symm x (basisVector 0) (basisVector 1)]
  ring

/-- The curl field is not the zero Schwartz map: otherwise `∂₀ g ≡ 0`, so `g`
is constant along the `e₀` line through the origin, contradicting `g 0 = 1`
with compact support. -/
theorem phiSchwartz_ne_zero : phiSchwartz ≠ 0 := by
  intro h0
  -- extract ∂₀ g ≡ 0 from the vanishing of component 1
  have hcomp : ∀ x : Space, fderiv ℝ gfun x (basisVector 0) = 0 := by
    intro x
    have hx : phifun x = 0 := by
      have := congrArg (fun (f : SchwartzVelocity) => f x) h0
      simpa [phiSchwartz_apply] using this
    have h1 := congrFun hx 1
    have hb01 : basisVector 0 (1 : Fin 3) = 0 := rfl
    have hb11 : basisVector 1 (1 : Fin 3) = 1 := rfl
    simp only [phifun, Pi.sub_apply, Pi.smul_apply, hb01, hb11,
      smul_eq_mul, mul_zero, mul_one, zero_sub, Pi.zero_apply] at h1
    linarith [h1]
  -- the line function
  set h : ℝ → ℝ := fun t => gfun (t • basisVector 0) with hh
  have hline : ∀ t : ℝ, HasDerivAt h (fderiv ℝ gfun (t • basisVector 0) (basisVector 0)) t := by
    intro t
    have hg : HasFDerivAt gfun (fderiv ℝ gfun (t • basisVector 0)) (t • basisVector 0) :=
      (gfun_smooth.differentiable (by decide)).differentiableAt.hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => s • basisVector 0) (basisVector 0) t := by
      simpa using (hasDerivAt_id t).smul_const (basisVector 0)
    exact hg.comp_hasDerivAt t hl
  have hconst : ∀ a b : ℝ, h a = h b := by
    apply is_const_of_deriv_eq_zero
    · intro t
      exact (hline t).differentiableAt
    · intro t
      rw [(hline t).deriv]
      exact hcomp _
  -- compact support gives a far-out zero
  obtain ⟨R, hR⟩ := gfun_supp.isBounded.subset_closedBall 0
  have hfar : h (R + 1) = 0 := by
    show gfun ((R + 1) • basisVector 0) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hR hmem
    rw [Metric.mem_closedBall] at this
    have hnorm : ‖(R + 1) • basisVector 0‖ = |R + 1| := by
      rw [norm_smul]
      have : ‖basisVector 0‖ = 1 := by
        simp [basisVector, Pi.norm_single]
      simp [this, Real.norm_eq_abs]
    have hR0 : 0 ≤ R := by
      have h0mem : (0 : Space) ∈ Metric.closedBall 0 R := by
        apply hR
        have : gfun 0 ≠ 0 := by rw [gfun_zero]; norm_num
        exact subset_tsupport _ (by simpa [Function.mem_support] using this)
      simpa using h0mem
    rw [dist_zero_right, hnorm] at this
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  have hzero : h 0 = 1 := by simp [hh, gfun_zero]
  have := hconst 0 (R + 1)
  rw [hzero, hfar] at this
  norm_num at this

/-!
## Envelope + witness test function
-/

noncomputable def envelope : ℝ → ℝ := fun t => Real.smoothTransition (2 - t)

theorem envelope_smooth : ContDiff ℝ ∞ envelope :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem envelope_zero : envelope 0 = 1 :=
  Real.smoothTransition.one_of_one_le (by norm_num)

theorem envelope_vanish {t : ℝ} (ht : 2 ≤ t) : envelope t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem staticDivergence_const_smul (c : ℝ) (f : Space → Space) (x : Space)
    (hf : DifferentiableAt ℝ f x) :
    staticDivergence (fun y => c • f y) x = c * staticDivergence f x := by
  unfold staticDivergence
  rw [Finset.mul_sum]
  congr 1; funext i
  rw [show (fun y => c • f y) = c • f from rfl, fderiv_const_smul hf c]
  simp

noncomputable def witnessTest : DivergenceFreeTestFunction where
  field := fun t => envelope t • phiSchwartz
  timeDerivSchwartz := fun t => deriv envelope t • phiSchwartz
  timeDeriv_eq := by
    intro t ht x
    unfold timeDerivative
    have he : HasDerivAt envelope (deriv envelope t) t :=
      (envelope_smooth.differentiable (by decide) t).hasDerivAt
    have hx := he.smul_const (phiSchwartz x)
    have hfun : (fun s : ℝ => ((envelope s • phiSchwartz : SchwartzVelocity)) x) =
        fun s : ℝ => envelope s • phiSchwartz x := by
      funext s
      simp
    rw [hfun, hx.hasFDerivAt.hasFDerivWithinAt.fderivWithin
      ((uniqueDiffOn_Ici 0) t (Set.mem_Ici.mpr ht))]
    simp
  smooth := by
    have hcoe : (fun z : ℝ × Space =>
        ((envelope z.1 • phiSchwartz : SchwartzVelocity)) z.2) =
        fun z : ℝ × Space => envelope z.1 • phifun z.2 := by
      funext z; simp [phiSchwartz_apply]
    rw [hcoe]
    have h1 := envelope_smooth
    have h2 := phifun_smooth
    have hjoint : ContDiff ℝ ∞ (fun z : ℝ × Space => envelope z.1 • phifun z.2) := by
      fun_prop
    exact hjoint.contDiffOn
  compact_time := ⟨2, two_pos, fun t ht => by
    rw [envelope_vanish ht, zero_smul]⟩
  compact_time_deriv := ⟨3, by norm_num, fun t ht => by
    have ht' : 2 < t := by linarith
    have hevent : envelope =ᶠ[nhds t] fun _ : ℝ => 0 := by
      filter_upwards [Ioi_mem_nhds ht'] with s hs
      exact envelope_vanish hs.le
    have hderiv : deriv envelope t = 0 := by
      rw [hevent.deriv_eq, deriv_const]
    rw [hderiv, zero_smul]⟩
  compact_space := ⟨tsupport phifun, phifun_supp, by
    intro t x hx
    have hphi : phiSchwartz x = 0 := by
      rw [phiSchwartz_apply]
      exact image_eq_zero_of_notMem_tsupport hx
    simp [hphi]⟩
  compact_space_deriv := ⟨tsupport phifun, phifun_supp, by
    intro t x hx
    have hphi : phiSchwartz x = 0 := by
      rw [phiSchwartz_apply]
      exact image_eq_zero_of_notMem_tsupport hx
    simp [hphi]⟩
  divergence_free := by
    intro t x
    show staticDivergence (fun y => (envelope t • phiSchwartz) y) x = 0
    have hcoe : (fun y => (envelope t • phiSchwartz) y) =
        fun y => envelope t • phifun y := by
      funext y; simp [phiSchwartz_apply]
    rw [hcoe, staticDivergence_const_smul _ _ _
      ((phifun_smooth.differentiable (by decide)).differentiableAt)]
    have hdiv : staticDivergence phifun x = 0 := phiSchwartz_divfree x
    rw [hdiv, mul_zero]

/-- **The test class contains a nonzero member.**  This is the anti-vacuity
guarantee for `weak_form`: with only the zero test the weak formulation would
be trivially satisfiable and `leray_weak_existence` vacuous.  Realized by the
curl-of-bump construction above. -/
theorem exists_nonzero_testFunction :
    ∃ φ : DivergenceFreeTestFunction, ∃ t : ℝ, 0 ≤ t ∧ φ.field t ≠ 0 := by
  refine ⟨witnessTest, 0, le_rfl, ?_⟩
  show envelope 0 • phiSchwartz ≠ 0
  rw [envelope_zero, one_smul]
  exact phiSchwartz_ne_zero

/-!
## The Leray–Hopf weak solution concept
-/

/-- A Leray–Hopf weak solution with datum `u₀`: square-integrable slices,
exact initial attainment (representative choice), non-increasing kinetic
energy, and the weak-form identity against every divergence-free
Schwartz-sliced test function

  `∫_{t≥0} ∫ₓ ⟨u, ∂ₜφ + (u·∇)φ + νΔφ⟩ = −∫ₓ ⟨u₀, φ(0)⟩`

(pressure eliminated by divergence-free tests; the sign convention is the
standard integration by parts from `∂ₜu + (u·∇)u = νΔu − ∇p`).  The full
Leray energy *inequality* with the dissipation term and the `L²`-continuity
at `t = 0` are strictly stronger clauses that belong to the weak-derivative
layer; they are named residuals of the existence skeleton, not hidden. -/
structure IsLerayHopfWeakSolution
    (ν : ℝ) (u₀ : SchwartzVelocity) (u : VelocityEvolution) : Prop where
  square_integrable :
    ∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)
  initial_attained : ∀ x : Space, u 0 x = u₀ x
  energy_nonincreasing :
    ∀ t : ℝ, 0 ≤ t → kineticEnergy u t ≤ kineticEnergy u 0
  pairing_integrable :
    ∀ φ : DivergenceFreeTestFunction, ∀ t : ℝ, 0 ≤ t →
      Integrable (fun x : Space =>
        officialInner (u t x)
          (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
            spatialDerivative (fun s => (φ.field s : Space → Space)) t x
              (u t x) +
            ν • laplacian (fun s => (φ.field s : Space → Space)) t x))
  weak_form :
    ∀ φ : DivergenceFreeTestFunction,
      (∫ t in Set.Ici (0:ℝ), ∫ x : Space,
        officialInner (u t x)
          (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
            spatialDerivative (fun s => (φ.field s : Space → Space)) t x
              (u t x) +
            ν • laplacian (fun s => (φ.field s : Space → Space)) t x)) =
      -(∫ x : Space, officialInner (u₀ x) ((φ.field 0) x))

/-!
## Non-degeneracy smoke: the zero solution realizes the structure
-/

theorem officialInner_zero_left (y : Space) : officialInner 0 y = 0 := by
  simp [officialInner, officialEuclideanPoint]

/-- The zero velocity is a Leray–Hopf weak solution for the zero datum: the
structure is realizable (Step-0e non-vacuity anchor for the layer). -/
theorem zero_isLerayHopfWeak (ν : ℝ) :
    IsLerayHopfWeakSolution ν (0 : SchwartzVelocity) (fun _ _ => 0) where
  square_integrable := by
    intro t _
    refine (integrable_zero Space ℝ volume).congr ?_
    exact Filter.Eventually.of_forall fun x => by simp
  initial_attained := by intro x; simp
  energy_nonincreasing := by intro t _; simp [kineticEnergy]
  pairing_integrable := by
    intro φ t _
    refine (integrable_zero Space ℝ volume).congr ?_
    exact Filter.Eventually.of_forall fun x =>
      (officialInner_zero_left _).symm
  weak_form := by
    intro φ
    simp [officialInner_zero_left]

/-!
## Energy and inner-product algebra (kernel-clean, reusable by the assembly)
-/

/-- Kinetic energy is nonnegative (Bochner integral of a nonnegative density).
Used for the uniform-bound bookkeeping of the Galerkin assembly below. -/
theorem kineticEnergy_nonneg (u : VelocityEvolution) (t : ℝ) :
    0 ≤ kineticEnergy u t := by
  unfold kineticEnergy
  exact integral_nonneg (fun x => by positivity)

/-- Coordinate formula for Fefferman's official inner product on `Space`. -/
theorem officialInner_eq_sum (x y : Space) :
    officialInner x y = ∑ i : Fin 3, x i * y i := by
  simp only [officialInner]
  rw [PiLp.inner_apply]
  simp only [officialEuclideanPoint_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The official inner product is additive in its right argument (bilinearity,
used when splitting the weak-form pairing into its time/convection/viscous
summands). -/
theorem officialInner_add_right (x y z : Space) :
    officialInner x (y + z) = officialInner x y + officialInner x z := by
  simp only [officialInner_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The official inner product is `ℝ`-homogeneous in its right argument
(pulls the viscosity scalar `ν` out of the viscous pairing term). -/
theorem officialInner_smul_right (c : ℝ) (x y : Space) :
    officialInner x (c • y) = c * officialInner x y := by
  simp only [officialInner_eq_sum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-!
### Coordinate-norm bridge: the Euclidean pairing vs. the product norm

`Space = Fin 3 → ℝ` carries the **product** (sup) norm `‖·‖`, while
`officialInner` is Fefferman's **Euclidean** pairing.  The Galerkin layer states
every `L²` fact with the Euclidean pairing (that is what `schwartzL2Inner` is),
whereas `kineticEnergy` and `GalerkinApproximation.initial_converges` are stated
with the product norm.  The two are comparable in both directions
(`norm_le_officialEuclideanNorm`, `officialEuclideanNorm_le`), and that
comparison — the "coordinate-norm equivalence bookkeeping" named in
`Navier.Analysis.GalerkinBasis.proj_tendsto_self` — is exactly what turns the
banked Bessel convergence `‖u₀ − P_m u₀‖²_{L²} → 0` into the
`initial_converges` field of a `GalerkinApproximation`.  It is certified here.
-/

/-- The product norm is dominated by the official Euclidean pairing:
`‖x‖² ≤ ⟨x, x⟩`. -/
theorem norm_sq_le_officialInner_self (x : Space) : ‖x‖ ^ 2 ≤ officialInner x x := by
  rw [officialInner_self]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_officialEuclideanNorm x) 2

/-- In dimension three the official Euclidean pairing is dominated by three
times the squared product norm: `⟨x, x⟩ ≤ 3‖x‖²`. -/
theorem officialInner_self_le_three_norm_sq (x : Space) :
    officialInner x x ≤ 3 * ‖x‖ ^ 2 := by
  rw [officialInner_self]
  have h := officialEuclideanNorm_le x
  nlinarith [officialEuclideanNorm_nonneg x, norm_nonneg x,
    Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0), Real.sqrt_nonneg 3]

/-- **The squared product-norm density of a Schwartz field is integrable.**
The uniform Schwartz bound `‖f x‖ ≤ C` (`k = n = 0` decay) dominates
`‖f x‖² ≤ C·‖f x‖`, and `x ↦ ‖f x‖` is integrable (`SchwartzMap.integrable`).
This is the integrability side of `kineticEnergy` for Schwartz slices. -/
theorem integrable_norm_sq_schwartz (f : SchwartzVelocity) :
    Integrable (fun x : Space => ‖f x‖ ^ 2) := by
  obtain ⟨C, hC0, hCraw⟩ :=
    (schwartzmap_satisfies_fefferman_euclidean_weight_rapid_decay f) 0 0
  have hC : ∀ x : Space, ‖f x‖ ≤ C := by
    intro x
    have h := hCraw x
    rw [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h
    exact h
  have hfint : Integrable (fun x : Space => ‖f x‖) volume := (SchwartzMap.integrable f).norm
  refine Integrable.mono' (hfint.const_mul C) ?_ ?_
  · exact ((f.continuous.norm).pow 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖f x‖ ^ 2 = ‖f x‖ * ‖f x‖ := sq _
      _ ≤ C * ‖f x‖ := mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- The Euclidean self-pairing density of a Schwartz field is integrable
(dominated by `3‖f x‖²`). -/
theorem integrable_officialInner_self (f : SchwartzVelocity) :
    Integrable (fun x : Space => officialInner (f x) (f x)) := by
  refine Integrable.mono' ((integrable_norm_sq_schwartz f).const_mul 3) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    simp only [officialInner_eq_sum]
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp f.continuous).mul ((continuous_apply i).comp f.continuous))
  · refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [officialInner_self]; positivity)]
    exact officialInner_self_le_three_norm_sq (f x)

/-- Integrated form of the pointwise comparison: the product-norm `L²` energy is
below the Euclidean `L²` energy. -/
theorem integral_norm_sq_le_integral_officialInner_self (f : SchwartzVelocity) :
    ∫ x : Space, ‖f x‖ ^ 2 ≤ ∫ x : Space, officialInner (f x) (f x) :=
  integral_mono (integrable_norm_sq_schwartz f) (integrable_officialInner_self f)
    (fun x => norm_sq_le_officialInner_self (f x))

/-- **The `L²` convergence bridge.**  A sequence of Schwartz fields whose
Euclidean `L²` energies vanish also has vanishing product-norm `L²` energies
(squeeze between `0` and the Euclidean energy).  With
`Navier.Analysis.GalerkinBasis.proj_tendsto_self` — which delivers exactly the
Euclidean hypothesis for `f m = P_m u₀ − u₀` — this produces the
`initial_converges` field of a `GalerkinApproximation`. -/
theorem tendsto_integral_norm_sq_of_tendsto_officialInner_self (f : ℕ → SchwartzVelocity)
    (h : Filter.Tendsto (fun m => ∫ x : Space, officialInner (f m x) (f m x))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => ∫ x : Space, ‖f m x‖ ^ 2) Filter.atTop (nhds 0) :=
  squeeze_zero (fun m => integral_nonneg fun x => by positivity)
    (fun m => integral_norm_sq_le_integral_officialInner_self (f m)) h

/-- **Energy-decay engine.**  In a real inner-product space, if a curve `u` has
derivative `u'` with `⟨u'(t), u(t)⟩ ≤ 0` for every `t`, then `‖u(t)‖²` is
antitone.  This is the a-priori-bound core of the Galerkin construction: for a
finite-mode solution `u'ₘ = −ν A uₘ + Pₘ B(uₘ)` with `A` dissipative and the
projected nonlinearity skew (`⟨Pₘ B(uₘ), uₘ⟩ = 0`), one has
`⟨u'ₘ, uₘ⟩ = −ν⟨A uₘ, uₘ⟩ ≤ 0`, so this lemma delivers `‖uₘ(t)‖² ≤ ‖uₘ(0)‖²`. -/
theorem norm_sq_antitone_of_inner_deriv_nonpos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u u' : ℝ → E)
    (hu : ∀ t : ℝ, HasDerivAt u (u' t) t)
    (hip : ∀ t : ℝ, inner ℝ (u' t) (u t) ≤ 0) :
    Antitone (fun t => ‖u t‖ ^ 2) := by
  apply antitone_of_hasDerivAt_nonpos (f' := fun t => 2 * inner ℝ (u' t) (u t))
  · intro t
    have h := (hu t).inner ℝ (hu t)
    have hrw : (fun t => ‖u t‖ ^ 2) = (fun t => (inner ℝ (u t) (u t) : ℝ)) := by
      funext s; rw [real_inner_self_eq_norm_sq]
    rw [hrw]
    have hcomm : (inner ℝ (u t) (u' t) : ℝ) + inner ℝ (u' t) (u t)
        = 2 * inner ℝ (u' t) (u t) := by
      rw [real_inner_comm (u t) (u' t)]; ring
    rw [← hcomm]; exact h
  · intro t; simp only [Pi.zero_apply]; linarith [hip t]

/-- **A-priori energy bound.**  A nonpositive inner-derivative keeps the squared
norm below its initial value for all nonnegative times (`UniformKineticBound`
shape at the abstract level). -/
theorem norm_sq_le_initial_of_inner_deriv_nonpos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u u' : ℝ → E)
    (hu : ∀ t : ℝ, HasDerivAt u (u' t) t)
    (hip : ∀ t : ℝ, inner ℝ (u' t) (u t) ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖u t‖ ^ 2 ≤ ‖u 0‖ ^ 2 :=
  norm_sq_antitone_of_inner_deriv_nonpos u u' hu hip ht

/-- **Galerkin a-priori bound (complete).**  If `u` solves the abstract
projected system `u' = −(ν • A u) + B u` with `A` dissipative
(`0 ≤ ⟨A x, x⟩`), the nonlinearity `B` skew (`⟨B x, x⟩ = 0`), and `ν ≥ 0`, then
the energy never exceeds its initial value: `‖u(t)‖² ≤ ‖u(0)‖²` for `t ≥ 0`.
This is exactly the mechanism producing the `UniformKineticBound` field of a
`GalerkinApproximation` — the skew nonlinearity contributes nothing to the
energy balance and the dissipative term only removes energy.  Kernel-clean;
the only Galerkin-specific inputs (skew-symmetry of `Pₘ B`, dissipativity of
the Stokes operator) enter as the two hypotheses. -/
theorem galerkin_apriori_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν : ℝ) (hν : 0 ≤ ν) (A B : E → E) (u u' : ℝ → E)
    (hu : ∀ t : ℝ, HasDerivAt u (u' t) t)
    (hode : ∀ t : ℝ, u' t = -(ν • A (u t)) + B (u t))
    (hA : ∀ t : ℝ, 0 ≤ inner ℝ (A (u t)) (u t))
    (hB : ∀ t : ℝ, inner ℝ (B (u t)) (u t) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖u t‖ ^ 2 ≤ ‖u 0‖ ^ 2 := by
  apply norm_sq_le_initial_of_inner_deriv_nonpos u u' hu _ ht
  intro s
  rw [hode s, inner_add_left, inner_neg_left, inner_smul_left, hB s]
  have hpos : (0:ℝ) ≤ (ν : ℝ) * inner ℝ (A (u s)) (u s) := mul_nonneg hν (hA s)
  simp only [conj_trivial, add_zero]
  nlinarith [hpos]

/-- **Forward a-priori confinement (squared).**  If a curve `u` on `[0,∞)` has
right-within-derivative `u'` with `⟨u'(t), u(t)⟩ ≤ 0`, then `‖u(t)‖² ≤ ‖u(0)‖²`
for all `t ≥ 0`.  This is the forward-time (`Set.Ici 0`) confinement engine —
the "no forward blow-up" heart of `finiteDim_dissipative_ode_global`: it keeps
a dissipative flow inside the initial ball, so the finite-mode Galerkin ODE has
no finite-time escape and extends to all of `[0,∞)`.  (Backward in time the
bound is false — see the `finiteDim_dissipative_ode_global` docstring.) -/
theorem norm_sq_le_initial_forward
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u u' : ℝ → E)
    (hu : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (u' t) (Set.Ici 0) t)
    (hip : ∀ t : ℝ, 0 ≤ t → inner ℝ (u' t) (u t) ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) : ‖u t‖ ^ 2 ≤ ‖u 0‖ ^ 2 := by
  have hcont : ContinuousOn (fun s => ‖u s‖ ^ 2) (Set.Ici 0) := fun s hs =>
    (((hu s hs).continuousWithinAt).norm).pow 2
  have hanti : AntitoneOn (fun s => ‖u s‖ ^ 2) (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun x => 2 * inner ℝ (u' x) (u x)) (convex_Ici 0) hcont
    · intro x hx
      rw [interior_Ici] at hx
      have hd : HasDerivWithinAt u (u' x) (Set.Ioi 0) x :=
        (hu x (le_of_lt hx)).mono Set.Ioi_subset_Ici_self
      have hi := hd.inner ℝ hd
      have hrw : (fun s => ‖u s‖ ^ 2) = (fun s => (inner ℝ (u s) (u s) : ℝ)) := by
        funext r; rw [real_inner_self_eq_norm_sq]
      have hcomm : (inner ℝ (u x) (u' x) : ℝ) + inner ℝ (u' x) (u x)
          = 2 * inner ℝ (u' x) (u x) := by rw [real_inner_comm (u x) (u' x)]; ring
      rw [hrw, interior_Ici, ← hcomm]; exact hi
    · intro x hx
      rw [interior_Ici] at hx
      show 2 * inner ℝ (u' x) (u x) ≤ 0
      linarith [hip x (le_of_lt hx)]
  exact hanti Set.self_mem_Ici (Set.mem_Ici.mpr ht) ht

/-- **Forward a-priori confinement (dissipative field form).**  A forward
solution `u' = F ∘ u` of a dissipative field (`⟨F x, x⟩ ≤ 0`) stays inside the
initial ball: `‖u(t)‖ ≤ ‖u(0)‖` for `t ≥ 0`.  This is exactly the confinement
`finiteDim_dissipative_ode_global` uses to rule out finite-time escape of the
Galerkin ODE and extend the local Picard–Lindelöf solution to all of `[0,∞)`. -/
theorem norm_le_initial_of_forward_dissipative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → E) (u : ℝ → E)
    (hu : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (F (u t)) (Set.Ici 0) t)
    (hdiss : ∀ x : E, inner ℝ (F x) x ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) : ‖u t‖ ≤ ‖u 0‖ := by
  have h2 : ‖u t‖ ^ 2 ≤ ‖u 0‖ ^ 2 :=
    norm_sq_le_initial_forward u (fun s => F (u s)) hu (fun s _ => hdiss (u s)) ht
  have hs := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg (u t)), Real.sqrt_sq (norm_nonneg (u 0))] at hs

/-!
## Galerkin / energy assembly (decomposition of the existence skeleton)

The Leray (1934) construction factors into three genuinely-lower obligations,
matching Temam III.3 and Constantin–Foias II: (1) build finite-mode Galerkin
approximants with uniform energy/dissipation bounds; (2) extract a strongly
`L²_loc`-convergent subsequence (Aubin–Lions–Simon compactness — the one
Mathlib-absent analytic core); (3) pass to the limit in the weak form.  The
top theorem `leray_weak_existence` below is now a real composition of these
named leaves, not a bare `sorry`.
-/

/-- The weak-form residual of a velocity field `u` against a test `φ`:
`LHS − RHS` of the Leray–Hopf identity.  A genuine (approximate) solution
drives this to `0`; this is the field that ties a Galerkin sequence to the
Navier–Stokes dynamics (a heat-flow or junk sequence fails it). -/
def weakFormResidual (ν : ℝ) (u₀ : SchwartzVelocity) (u : VelocityEvolution)
    (φ : DivergenceFreeTestFunction) : ℝ :=
  (∫ t in Set.Ici (0:ℝ), ∫ x : Space,
      officialInner (u t x)
        (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
          spatialDerivative (fun s => (φ.field s : Space → Space)) t x (u t x) +
          ν • laplacian (fun s => (φ.field s : Space → Space)) t x))
    + (∫ x : Space, officialInner (u₀ x) ((φ.field 0) x))

/-- Strong `L²(0,T; L²_loc)` convergence: on every finite time window `(0,T]`
and every spatial ball, the squared `L²` error of the sequence tends to `0`.
This is exactly the convergence Aubin–Lions delivers and that the quadratic
term needs for limit passage (weak × strong ⇒ convergent product). -/
def StrongL2LocLimit (uSeq : ℕ → VelocityEvolution) (u : VelocityEvolution) : Prop :=
  ∀ T R : ℝ, Filter.Tendsto
    (fun m => ∫ t in Set.Ioc (0:ℝ) T, ∫ x in Metric.closedBall (0:Space) R,
      ‖uSeq m t x - u t x‖ ^ 2)
    Filter.atTop (nhds 0)

/-- Uniform `L^∞_t L²_x` kinetic-energy bound across the sequence (from the
projected energy identity `‖u_m(t)‖² ≤ ‖u₀‖²`).  This is the file's internal
(inherited sup-norm) slice bound, not the official Euclidean `kineticEnergy` of
`Navier.Problem` — the two differ by at most the dimension-`3` factor bridged
in `Navier.Analysis.EnergyNormBridge`. -/
def UniformKineticBound (uSeq : ℕ → VelocityEvolution) (C : ℝ) : Prop :=
  ∀ (m : ℕ) (t : ℝ), 0 ≤ t → (∫ x : Space, ‖uSeq m t x‖ ^ 2) ≤ C

/-- Uniform slice bound in the **official Euclidean** energy `kineticEnergy`
(`∫ ∑ᵢ uᵢ²`) rather than the inherited sup-norm energy of `UniformKineticBound`.

**Why both predicates are needed, and why one does not reduce to the other.**
`Space = Fin 3 → ℝ` carries the product *sup* norm, so `UniformKineticBound` and
this predicate differ by the dimension factor `3`
(`EnergyNormBridge.norm_sq_le_sum_sq` and
`EnergyNormBridge.officialEuclideanNorm_sq_le_three_mul_norm_sq`).  Every
Leray-side consumer that has to reproduce Fefferman's energy clause with its
*exact* datum constant — `LerayLimitData.energy_le`, whose right-hand side is
literally `∫ ∑ᵢ (u₀)ᵢ²` — therefore cannot be served by the sup-norm bound:
routing `∫ ∑ᵢ uᵢ² ≤ 3∫‖u‖² ≤ 3C ≤ 3∫‖u₀‖² ≤ 3∫ ∑ᵢ (u₀)ᵢ²` loses a factor `3`
and lands on a strictly weaker inequality.  The gap is closed by carrying the
Euclidean bound as data from the finite-mode construction (where it is the
genuine projected energy identity `‖u_m(t)‖²_{L²} ≤ ‖P_m u₀‖²_{L²} ≤
‖u₀‖²_{L²}`, all three in the Euclidean `L²` norm) and transporting it through
Fischer–Riesz by the same Fatou step that transports the sup-norm bound
(`exists_limit_of_forall_windowCauchy`). -/
def UniformOfficialKineticBound (uSeq : ℕ → VelocityEvolution) (B : ℝ) : Prop :=
  ∀ (m : ℕ) (t : ℝ), 0 ≤ t → kineticEnergy (uSeq m) t ≤ B

/-- **The Euclidean bound implies the sup-norm bound at the *same* constant.**
Half of the machine-checked record that `UniformOfficialKineticBound` is
strictly the stronger hypothesis (`‖·‖² ≤ ∑ᵢ ·ᵢ²` pointwise). -/
theorem uniformKineticBound_of_official {uSeq : ℕ → VelocityEvolution} {B : ℝ}
    (hmeas : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → AEStronglyMeasurable (uSeq m t))
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (h : UniformOfficialKineticBound uSeq B) :
    UniformKineticBound uSeq B := by
  intro m t ht
  refine le_trans ?_ (h m t ht)
  have hoff : Integrable fun x : Space => officialEuclideanNorm (uSeq m t x) ^ 2 :=
    (Navier.Analysis.EnergyNormBridge.integrable_norm_sq_iff_officialEuclideanNorm_sq
      (uSeq m t) (hmeas m t ht)).1 (hint m t ht)
  have hsum : Integrable fun x : Space => ∑ i : Fin 3, (uSeq m t x i) ^ 2 :=
    hoff.congr (Filter.Eventually.of_forall fun x =>
      Navier.Analysis.EnergyNormBridge.officialEuclideanNorm_sq_eq_sum_sq (uSeq m t x))
  exact integral_mono (hint m t ht) hsum
    fun x => Navier.Analysis.EnergyNormBridge.norm_sq_le_sum_sq (uSeq m t x)

/-- **The converse costs the dimension factor `3`, and that loss is real.**  This
is the machine-checked form of the obstruction recorded in
`UniformOfficialKineticBound`: a sup-norm bundle bounds the Euclidean energy only
by `3C`, so it cannot serve `LerayLimitData.energy_le`, whose right-hand side is
the datum energy with constant exactly `1`.  Together with
`uniformKineticBound_of_official` this pins the exact strength gap between the
two predicates. -/
theorem officialKineticBound_of_uniformKineticBound {uSeq : ℕ → VelocityEvolution} {C : ℝ}
    (hmeas : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → AEStronglyMeasurable (uSeq m t))
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (h : UniformKineticBound uSeq C) :
    UniformOfficialKineticBound uSeq (3 * C) := by
  intro m t ht
  have hoff : Integrable fun x : Space => officialEuclideanNorm (uSeq m t x) ^ 2 :=
    (Navier.Analysis.EnergyNormBridge.integrable_norm_sq_iff_officialEuclideanNorm_sq
      (uSeq m t) (hmeas m t ht)).1 (hint m t ht)
  have hsum : Integrable fun x : Space => ∑ i : Fin 3, (uSeq m t x i) ^ 2 :=
    hoff.congr (Filter.Eventually.of_forall fun x =>
      Navier.Analysis.EnergyNormBridge.officialEuclideanNorm_sq_eq_sum_sq (uSeq m t x))
  have hstep : kineticEnergy (uSeq m) t ≤ ∫ x : Space, 3 * ‖uSeq m t x‖ ^ 2 := by
    refine integral_mono hsum ((hint m t ht).const_mul 3) fun x => ?_
    have := Navier.Analysis.EnergyNormBridge.officialEuclideanNorm_sq_le_three_mul_norm_sq
      (uSeq m t x)
    rwa [Navier.Analysis.EnergyNormBridge.officialEuclideanNorm_sq_eq_sum_sq
      (uSeq m t x)] at this
  calc kineticEnergy (uSeq m) t ≤ ∫ x : Space, 3 * ‖uSeq m t x‖ ^ 2 := hstep
    _ = 3 * ∫ x : Space, ‖uSeq m t x‖ ^ 2 := integral_const_mul 3 _
    _ ≤ 3 * C := by
        exact mul_le_mul_of_nonneg_left (h m t ht) (by norm_num)

/-- Uniform `L²(0,T; H¹)` dissipation bound (time-integrated enstrophy;
for divergence-free fields `‖ω‖_{L²} = ‖∇u‖_{L²}`), from `∫ ν‖∇u_m‖² ≤ ½‖u₀‖²`. -/
def UniformEnstrophyBound (uSeq : ℕ → VelocityEvolution) (C : ℝ) : Prop :=
  ∀ (m : ℕ) (T : ℝ), 0 ≤ T → (∫ t in Set.Ioc (0:ℝ) T, enstrophy (uSeq m) t) ≤ C

/-- Uniform `L²`-in-time translation equicontinuity (the Simon (1987)
time-regularity condition; in the smooth Galerkin setting it is the
`∂ₜu_m ∈ L²(0,T; H⁻¹)` bound in Kolmogorov–Riesz–Fréchet form).  Without a
time-regularity hypothesis the compactness statement below is FALSE
(`u_m(t,x) = sin(m t)·w(x)` is `L^∞L² ∩ L²H¹`-bounded but has no strong
`L²_loc` limit), so this field is load-bearing for `aubin_lions_l2loc_compactness`. -/
def TimeEquicontinuous (uSeq : ℕ → VelocityEvolution) : Prop :=
  ∀ (T ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (m : ℕ) (h : ℝ), |h| < δ →
      (∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖uSeq m (t + h) x - uSeq m t x‖ ^ 2) ≤ ε

/-- **(H-space) Uniform spatial-translation equicontinuity** — the
Riesz–Fréchet–Kolmogorov condition, and the exact spatial mirror of
`TimeEquicontinuous`: a space shift `y` in place of a time shift `h`.  This is
Simon (1987) Thm 1 condition (ii) / Brezis (2011) Thm 4.26 hypothesis, i.e. the
hypothesis that actually delivers *spatial* compactness.

**The falsification and the repair are one fact seen from two sides.**  Do not
"simplify" this hypothesis away.  `enstrophy` measures `‖ω‖_{L²}`, and the whole
question is whether that controls `‖∇u‖_{L²}`.  For a **divergence-free** field the
two are equal, which is why the Galerkin approximants satisfy this predicate
(`spaceEquicontinuous_of_dissipation_bound`, certified below, feeds Brezis Prop. 9.3
the gradient bound the enstrophy bound then *is*).  For a general field the identity
fails, and the curl-free witness below is exactly a family realizing that failure:
`‖ω‖ ≡ 0` while `‖∇u_m‖` blows up.  So the counterexample exhibits the gap between
enstrophy and gradient norm, and this hypothesis closes it by demanding what
divergence-freeness would have supplied.  Deleting it re-falsifies
`aubin_lions_l2loc_compactness`.

**Why this is a hypothesis and not a consequence of `UniformEnstrophyBound`.**
`enstrophy` integrates `‖curl u‖²` only, and nothing in the Galerkin bundle
forces divergence-freeness, so `‖ω‖_{L²} = ‖∇u‖_{L²}` is unavailable and the
enstrophy bound gives no spatial control whatsoever.  The curl-free family
`u_m = ∇(m⁻¹ cos(m x₀) χ)`, `χ = e^{−|x|²}`, has `curl u_m ≡ 0` by Clairaut
(so `UniformEnstrophyBound u_m 0`), is `L²`-bounded, is time-independent (so
`TimeEquicontinuous` holds with a `0` integrand), and yet has **no**
`L²_loc`-Cauchy subsequence.  Checked numerically (`experiments/aubin_lions_curlfree_witness.py`):
`‖u_m‖² → 0.6267 = ½∫χ²` while `‖u_m − u_{2m}‖² → 1.2533` for `m ≥ 8`.  That
family is excluded by exactly this predicate: at the shift `y = (π/m, 0, 0)`,
whose norm tends to `0`, the translation error stays at `≈ 2∫χ² = 2.507`,
so no `δ` works.  (Same script, part (3); part (4) checks a non-oscillating
family has translation error `→ 0`, so the predicate is not vacuous.) -/
def SpaceEquicontinuous (uSeq : ℕ → VelocityEvolution) : Prop :=
  ∀ (T ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (m : ℕ) (y : Space), ‖y‖ < δ →
      (∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖uSeq m t (x + y) - uSeq m t x‖ ^ 2) ≤ ε

/-- **(H-meas) Joint `(t,x)`-measurability.**  `VelocityEvolution` is the bare
function type `ℝ → Space → Space`, which carries no measurability at all, so
every `t`-integral of an `x`-integral in this file is a Bochner integral that
silently returns the junk value `0` off the integrable locus.  Without this
field even the elementary bookkeeping of the compactness argument fails: the
countable exhaustion `T = R = n` needs `∫_{Ioc 0 T} ≤ ∫_{Ioc 0 n}` for `T ≤ n`,
i.e. `IntegrableOn` in `t`, which slicewise `x`-integrability alone cannot give.
`strongL2LocLimit_of_natWindows` below is the theorem this field unlocks. -/
def JointlyMeasurable (uSeq : ℕ → VelocityEvolution) : Prop :=
  ∀ m : ℕ, Measurable (fun z : ℝ × Space => uSeq m z.1 z.2)

/-- A **Galerkin approximation** of Navier–Stokes with viscosity `ν` and datum
`u₀`: a sequence of velocity fields carrying the uniform energy/dissipation
bounds and time-regularity from the projected energy identity, plus the `L²`
initial-data consistency and approximate weak-form consistency.  The
`initial_converges` and `weak_consistent` fields tie the sequence to `u₀` and
to the NSE dynamics — the zero sequence does NOT inhabit this for `u₀ ≠ 0`
(it fails both), so the limit obligation `leray_of_galerkinApproximation`
below is non-vacuous and TRUE-as-stated (not satisfiable by junk). -/
structure GalerkinApproximation (ν : ℝ) (u₀ : SchwartzVelocity) where
  /-- The finite-mode approximants. -/
  approx : ℕ → VelocityEvolution
  /-- Uniform energy bound constant (`= ‖u₀‖²_{L²}` in the construction). -/
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  /-- The bound is at most the datum energy (equality in the construction). -/
  bound_le : bound ≤ ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2
  /-- Uniform `L^∞_t L²_x` bound. -/
  kinetic_bounded : UniformKineticBound approx bound
  /-- **Uniform slice bound in the official Euclidean energy, at the exact datum
  constant.**  In the finite-mode construction this is the projected energy
  identity read in the Euclidean `L²` norm: `‖u_m(t)‖²_{L²} ≤ ‖P_m u₀‖²_{L²} ≤
  ‖u₀‖²_{L²}`.  It is *not* implied by `kinetic_bounded` + `bound_le`, which only
  give the same inequality with an extra factor `3` — see
  `UniformOfficialKineticBound`.  This is the field that makes
  `LerayLimitData.energy_le` derivable rather than residual
  (`galerkinLimit_energy_le`). -/
  official_kinetic_bounded :
    UniformOfficialKineticBound approx (∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2)
  /-- `L²(0,T; H¹)` dissipation bound constant (envelope bound, may exceed `bound`). -/
  enstrophyBound : ℝ
  enstrophyBound_nonneg : 0 ≤ enstrophyBound
  /-- Uniform `L²(0,T; H¹)` dissipation bound. -/
  enstrophy_bounded : UniformEnstrophyBound approx enstrophyBound
  /-- Uniform time-translation equicontinuity (Simon time-regularity). -/
  time_equicontinuous : TimeEquicontinuous approx
  /-- (H-space) Uniform spatial-translation equicontinuity (Riesz–Kolmogorov).
  For genuine Galerkin approximants this comes from the divergence-free
  `H¹` bound `∫₀^T ‖∇u_m‖²_{L²} ≤ ‖u₀‖²/(2ν)` through
  `‖τ_y f − f‖_{L²} ≤ ‖y‖ ‖∇f‖_{L²}`; it does **not** follow from
  `enstrophy_bounded`, see `SpaceEquicontinuous`. -/
  space_equicontinuous : SpaceEquicontinuous approx
  /-- (H-meas) Joint `(t,x)`-measurability; automatic for the Galerkin
  approximants, which are finite sums `∑ᵢ cᵢ(t) wᵢ(x)` with continuous `cᵢ`. -/
  jointly_measurable : JointlyMeasurable approx
  /-- Each slice is square-integrable. -/
  sq_integrable :
    ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖approx m t x‖ ^ 2)
  /-- The initial data converges to `u₀` in `L²` (Galerkin projection consistency). -/
  initial_converges :
    Filter.Tendsto (fun m => ∫ x : Space, ‖approx m 0 x - u₀ x‖ ^ 2)
      Filter.atTop (nhds 0)
  /-- The approximants satisfy the weak form asymptotically (Galerkin
  consistency with the NSE dynamics). -/
  weak_consistent :
    ∀ φ : DivergenceFreeTestFunction,
      Filter.Tendsto (fun m => weakFormResidual ν u₀ (approx m) φ)
        Filter.atTop (nhds 0)

/-- **Cutoff construction (compactly-supported dissipative extension).**  Given
a `C¹` dissipative field `F` (`⟨F x, x⟩ ≤ 0`) and a radius `R ≥ 0`, produces a
`C¹`, **compactly-supported**, still-dissipative field `G` that agrees with `F`
on the closed ball `B̄(0, R)`.  Concretely `G = χ(‖·‖²) • F` with the smooth
cutoff `χ = Real.smoothTransition ((R+1)² − ·)` (`= 1` on `[0, R²]`, `= 0`
beyond `(R+1)²`, `∈ [0,1]`), so `‖·‖²` smoothness (`contDiff_norm_sq`) gives
`C¹`, the cutoff's outer vanishing gives compact support in `B̄(0, R+1)`, and
`χ ≥ 0` preserves dissipativity.  This is the globally-Lipschitz replacement of
`F` used by `finiteDim_dissipative_ode_global`: a compactly-supported `C¹` field
has uniform local existence time, so an all-`ℝ` integral curve exists, and the
forward confinement keeps it inside `B̄(0, ‖x₀‖) ⊆ B̄(0,R)` where `G = F`. -/
theorem exists_compactSupport_dissipative_extension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (hdiss : ∀ x : E, inner ℝ (F x) x ≤ 0)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ G : E → E, ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ x : E, inner ℝ (G x) x ≤ 0) ∧ (∀ x : E, ‖x‖ ≤ R → G x = F x) := by
  refine ⟨fun x => Real.smoothTransition ((R+1)^2 - ‖x‖^2) • F x, ?_, ?_, ?_, ?_⟩
  · have hns : ContDiff ℝ 1 (fun x : E => (R+1)^2 - ‖x‖^2) :=
      contDiff_const.sub (contDiff_norm_sq ℝ)
    exact ((Real.smoothTransition.contDiff.of_le (by exact_mod_cast le_top)).comp hns).smul hF
  · apply HasCompactSupport.intro (isCompact_closedBall (0:E) (R+1))
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have hle : (R+1)^2 - ‖x‖^2 ≤ 0 := by nlinarith [norm_nonneg x, hx, hR]
    simp only [Real.smoothTransition.zero_of_nonpos hle, zero_smul]
  · intro x
    rw [inner_smul_left]
    simp only [conj_trivial]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.smoothTransition.nonneg _) (hdiss x)
  · intro x hx
    have hge : (1:ℝ) ≤ (R+1)^2 - ‖x‖^2 := by nlinarith [norm_nonneg x, hx, hR]
    simp only [Real.smoothTransition.one_of_one_le hge, one_smul]

/-- **Finite-dim dissipative ODE forward-global existence** [ESTABLISHED 2026-07-17;
Hartman *ODE* Ch. II–III; Temam III §3; via Picard–Lindelöf
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` on `Icc 0 (n+1)`
glued by `ODE_solution_unique`].  On a finite-dimensional real
inner-product space, a `C¹` vector field `F` with `⟨F x, x⟩ ≤ 0` (so `‖·‖` is
non-increasing along **forward** solutions, ruling out forward blow-up) admits a
solution `u : [0,∞) → E`, `u(0) = x₀`, `u' = F ∘ u` on all of `[0,∞)`.

**Forward-time only (Step-0e).**  The dissipative bound confines the flow only
for `t ≥ 0`; backward in time `‖u‖` may grow and blow up in finite time — e.g.
`E = ℝ`, `F x = -x³` (so `⟨F x, x⟩ = -x⁴ ≤ 0`), `x₀ = 1` gives
`u(t) = (2t+1)^{-1/2}`, which blows up as `t → -1/2⁺`.  So the honest statement
is existence on `Set.Ici 0` (`HasDerivWithinAt … (Set.Ici 0)`), NOT on all of
`ℝ`; this is exactly what the Galerkin fields (all imposed on `t ≥ 0`) need.

This is the finite-mode Galerkin ODE existence (`F = −ν A + P_m B`); basis-free.
**Confinement half — CLOSED**: `norm_le_initial_of_forward_dissipative` (above)
proves any forward solution stays in the initial ball `‖u(t)‖ ≤ ‖u(0)‖`, ruling
out finite-time escape.  **Existence half — ESTABLISHED** (2026-07-17,
`DissipativeODEGlobal.exists_forward_global_of_contDiff_compactSupport`): the
smooth cutoff `exists_compactSupport_dissipative_extension F … ‖x₀‖` produces a
compactly-supported `C¹` dissipative `G` agreeing with `F` on `B̄(0,‖x₀‖)`;
`G` is then globally Lipschitz + bounded, so it has a global forward solution `u`
(Picard–Lindelöf on each `Icc 0 (n+1)` glued by `ODE_solution_unique`); and the
confinement `norm_le_initial_of_forward_dissipative` keeps `u` inside
`B̄(0,‖x₀‖)` where `G = F`, so `u` solves the original ODE forward. -/
theorem finiteDim_dissipative_ode_global
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (hdiss : ∀ x : E, inner ℝ (F x) x ≤ 0)
    (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (F (u t)) (Set.Ici (0:ℝ)) t := by
  -- cutoff `F` to a compactly-supported dissipative field `G` agreeing with `F`
  -- on `B̄(0, ‖x₀‖)`
  obtain ⟨G, hG_C1, hG_supp, hG_diss, hG_eq⟩ :=
    exists_compactSupport_dissipative_extension F hF hdiss ‖x₀‖ (norm_nonneg x₀)
  -- global forward solution for the (globally-Lipschitz, bounded) cutoff `G`
  obtain ⟨u, hu0, hu_deriv⟩ :=
    Navier.Analysis.DissipativeODEGlobal.exists_forward_global_of_contDiff_compactSupport
      G hG_C1 hG_supp x₀
  refine ⟨u, hu0, fun t ht => ?_⟩
  -- confinement: the dissipative flow stays in `B̄(0, ‖x₀‖)`, where `G = F`
  have hconf : ‖u t‖ ≤ ‖x₀‖ := by
    have h := norm_le_initial_of_forward_dissipative G u hu_deriv hG_diss ht
    rwa [hu0] at h
  rw [← hG_eq (u t) hconf]
  exact hu_deriv t ht

/-- **Projected finite-mode coefficient flow.**  Let `A` be the finite-mode
Stokes operator and `B` the projected convection field.  Positivity of `A`,
energy-skewness of `B`, and nonnegative viscosity make the concrete Galerkin
field `x ↦ -(ν • A x) + B x` dissipative.  Since a continuous linear `A` and a
`C¹` field `B` make this field `C¹`, the cutoff/global ODE theorem supplies a
forward trajectory; its squared coefficient norm is bounded by the initial
coefficient norm.

This is the ODE package consumed by the construction of
`GalerkinModeData`: the remaining finite-mode work is to instantiate `A`, `B`,
and the coefficient-to-Schwartz-field map from the divergence-free basis, not
to prove global continuation again. -/
theorem exists_forward_galerkinCoefficientFlow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (ν : ℝ) (hν : 0 ≤ ν) (A : E →L[ℝ] E)
    (hA : ∀ x : E, 0 ≤ inner ℝ (A x) x)
    (B : E → E) (hB_C1 : ContDiff ℝ 1 B)
    (hB_skew : ∀ x : E, inner ℝ (B x) x = 0) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt u (-(ν • A (u t)) + B (u t)) (Set.Ici (0 : ℝ)) t) ∧
      ∀ t : ℝ, 0 ≤ t → ‖u t‖ ^ 2 ≤ ‖x₀‖ ^ 2 := by
  let F : E → E := fun x => -(ν • A x) + B x
  have hF_C1 : ContDiff ℝ 1 F := by
    dsimp only [F]
    exact (A.contDiff.const_smul ν).neg.add hB_C1
  have hF_diss : ∀ x : E, inner ℝ (F x) x ≤ 0 := by
    intro x
    dsimp only [F]
    rw [inner_add_left, inner_neg_left, inner_smul_left, hB_skew]
    simp only [conj_trivial, add_zero]
    exact neg_nonpos.mpr (mul_nonneg hν (hA x))
  obtain ⟨u, hu0, hu⟩ := finiteDim_dissipative_ode_global F hF_C1 hF_diss x₀
  refine ⟨u, hu0, fun t ht => by simpa only [F] using hu t ht, fun t ht => ?_⟩
  simpa only [hu0] using
    norm_sq_le_initial_forward u (fun s => F (u s)) hu
      (fun s _ => hF_diss (u s)) ht

/-!
### Finite-mode Galerkin data and its transport to a `GalerkinApproximation`

`GalerkinApproximation.initial_converges` is phrased with the product norm on
`Space`, but the convergence the finite-mode layer actually produces is Bessel's
`‖u₀ − P_m u₀‖²_{L²} → 0` in the **Euclidean** pairing
(`Navier.Analysis.GalerkinBasis.proj_tendsto_self`, banked).  `GalerkinModeData`
records the construction in the form the finite-mode layer produces it — with an
explicit Schwartz initial mode `P_m u₀` and the Euclidean-`L²` convergence — and
`galerkinApproximation_of_modeData` transports it through the coordinate-norm
bridge above.  Every other field is carried through verbatim, so the residual
below is strictly the finite-mode ODE/basis construction.
-/

/-- **Finite-mode Galerkin construction data.**  Same content as
`GalerkinApproximation` except that the `t = 0` slice is exhibited as a Schwartz
field `initialMode m` (in the construction, `P_m u₀`) and the initial-data
convergence is stated in the Euclidean `L²` seminorm, which is the shape the
Galerkin projection layer delivers.  Non-vacuous: `zeroGalerkinModeData`
inhabits it at the zero datum. -/
structure GalerkinModeData (ν : ℝ) (u₀ : SchwartzVelocity) where
  /-- The finite-mode approximants. -/
  approx : ℕ → VelocityEvolution
  /-- The Schwartz field realizing the `t = 0` slice (`P_m u₀`). -/
  initialMode : ℕ → SchwartzVelocity
  /-- The `t = 0` slice is that Schwartz field. -/
  initial_eq : ∀ m : ℕ, approx m 0 = fun x => initialMode m x
  /-- Uniform energy bound constant. -/
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  /-- The bound is at most the datum energy. -/
  bound_le : bound ≤ ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2
  /-- Uniform `L^∞_t L²_x` bound. -/
  kinetic_bounded : UniformKineticBound approx bound
  /-- Uniform slice bound in the official Euclidean energy at the exact datum
  constant — the projected energy identity read in the Euclidean `L²` norm.  Not
  implied by `kinetic_bounded` + `bound_le`; see `UniformOfficialKineticBound`. -/
  official_kinetic_bounded :
    UniformOfficialKineticBound approx (∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2)
  /-- Separate enstrophy bound constant (may exceed `bound` when ν < 1/2). -/
  enstrophyBound : ℝ
  enstrophyBound_nonneg : 0 ≤ enstrophyBound
  /-- Uniform `L²(0,T; H¹)` dissipation bound. -/
  enstrophy_bounded : UniformEnstrophyBound approx enstrophyBound
  /-- Uniform time-translation equicontinuity. -/
  time_equicontinuous : TimeEquicontinuous approx
  /-- (H-space) Uniform spatial-translation equicontinuity (Riesz–Kolmogorov). -/
  space_equicontinuous : SpaceEquicontinuous approx
  /-- (H-meas) Joint `(t,x)`-measurability. -/
  jointly_measurable : JointlyMeasurable approx
  /-- Each slice is square-integrable. -/
  sq_integrable :
    ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖approx m t x‖ ^ 2)
  /-- Bessel convergence of the initial modes in the Euclidean `L²` seminorm. -/
  initial_converges_L2 :
    Filter.Tendsto (fun m => ∫ x : Space,
        officialInner ((initialMode m - u₀) x) ((initialMode m - u₀) x))
      Filter.atTop (nhds 0)
  /-- Asymptotic weak-form consistency with the NSE dynamics. -/
  weak_consistent :
    ∀ φ : DivergenceFreeTestFunction,
      Filter.Tendsto (fun m => weakFormResidual ν u₀ (approx m) φ)
        Filter.atTop (nhds 0)

/-- **Transport: finite-mode data yields a `GalerkinApproximation`.**  All
fields but one are carried verbatim; `initial_converges` is obtained from the
Euclidean-`L²` convergence through
`tendsto_integral_norm_sq_of_tendsto_officialInner_self`, using `initial_eq` to
identify the `t = 0` slice with the Schwartz error `initialMode m − u₀`. -/
theorem galerkinApproximation_of_modeData (ν : ℝ) (u₀ : SchwartzVelocity)
    (D : GalerkinModeData ν u₀) : Nonempty (GalerkinApproximation ν u₀) := by
  refine ⟨{ approx := D.approx, bound := D.bound, bound_nonneg := D.bound_nonneg,
            bound_le := D.bound_le,
            kinetic_bounded := D.kinetic_bounded,
            official_kinetic_bounded := D.official_kinetic_bounded,
            enstrophyBound := D.enstrophyBound,
            enstrophyBound_nonneg := D.enstrophyBound_nonneg,
            enstrophy_bounded := D.enstrophy_bounded,
            time_equicontinuous := D.time_equicontinuous,
            space_equicontinuous := D.space_equicontinuous,
            jointly_measurable := D.jointly_measurable,
            sq_integrable := D.sq_integrable,
            weak_consistent := D.weak_consistent, initial_converges := ?_ }⟩
  have hbridge := tendsto_integral_norm_sq_of_tendsto_officialInner_self
    (fun m => D.initialMode m - u₀) D.initial_converges_L2
  have hEq : (fun m => ∫ x : Space, ‖(D.initialMode m - u₀) x‖ ^ 2)
      = fun m => ∫ x : Space, ‖D.approx m 0 x - u₀ x‖ ^ 2 := by
    funext m
    congr 1; funext x
    rw [D.initial_eq m]
    simp
  rw [hEq] at hbridge
  exact hbridge

/-- **Consumer-instantiability smoke (anti-vacuity).**  `GalerkinModeData` is
inhabited at the zero datum by the zero sequence, so the transport above and the
residual below are not vacuous obligations. -/
def zeroGalerkinModeData (ν : ℝ) : GalerkinModeData ν (0 : SchwartzVelocity) where
  approx := fun _ _ _ => 0
  initialMode := fun _ => 0
  initial_eq := by intro m; funext x; simp
  bound := 0
  bound_nonneg := le_rfl
  bound_le := by simp
  kinetic_bounded := by intro m t _; simp
  official_kinetic_bounded := by intro m t _; simp [kineticEnergy]
  enstrophyBound := 0
  enstrophyBound_nonneg := le_rfl
  enstrophy_bounded := by intro m T _; simp only [enstrophy_zero_velocity]; simp
  time_equicontinuous := by
    intro T ε hε
    exact ⟨1, one_pos, fun m h _ => by simp only [sub_self, norm_zero]; simp [hε.le]⟩
  space_equicontinuous := by
    intro T ε hε
    exact ⟨1, one_pos, fun m y _ => by simp only [sub_self, norm_zero]; simp [hε.le]⟩
  jointly_measurable := fun _ => measurable_const
  sq_integrable := by
    intro m t _
    exact (integrable_zero Space ℝ volume).congr (Filter.Eventually.of_forall fun x => by simp)
  initial_converges_L2 := by
    have hpt : (fun x : Space =>
        officialInner (((0 : SchwartzVelocity) - (0 : SchwartzVelocity)) x)
          (((0 : SchwartzVelocity) - (0 : SchwartzVelocity)) x)) = fun _ : Space => (0:ℝ) := by
      funext x
      simp only [sub_self, zero_apply, officialInner_zero_left]
    have hz : (fun _ : ℕ => ∫ x : Space,
        officialInner (((0 : SchwartzVelocity) - (0 : SchwartzVelocity)) x)
          (((0 : SchwartzVelocity) - (0 : SchwartzVelocity)) x)) = fun _ : ℕ => (0:ℝ) := by
      funext m; rw [hpt, MeasureTheory.integral_zero]
    rw [hz]; exact tendsto_const_nhds
  weak_consistent := by
    intro φ
    have hz : (fun _ : ℕ => weakFormResidual ν (0 : SchwartzVelocity)
        (fun (_ : ℝ) (_ : Space) => (0:Space)) φ) = fun _ : ℕ => (0:ℝ) := by
      funext m; simp [weakFormResidual, officialInner_zero_left]
    rw [hz]; exact tendsto_const_nhds

/-!
### `SpaceEquicontinuous` from a dissipation bound (certified)

The other Pattern-A hypothesis.  `SpaceEquicontinuous` was added to repair the
falsified `aubin_lions_l2loc_compactness`, so — like `jointly_measurable` — it has
to be dischargeable by the Galerkin construction or the repair merely relocated
the problem.  It is, and the route is Brezis Prop. 9.3 against the banked
dissipation bound:

`‖τ_y u_m(t) − u_m(t)‖²_{L²} ≤ ‖y‖²·‖∇u_m(t)‖²_{L²}`
(`RieszKolmogorov.integral_norm_sub_sq_le_mul_integral_fderiv_sq`), integrated in
`t` against `∫₀^T ‖∇u_m(t)‖²_{L²} dt ≤ ‖u₀‖²_{L²}/(2ν)`
(`EnergyDissipation.dissipation_integral_le_forward`), gives a modulus uniform in
`m`, and `δ = √(ε/(C+1))` converts it into the `ε`-`δ` form.

Note where the divergence-free basis actually earns its keep: it is what makes
`‖ω‖_{L²} = ‖∇u_m‖_{L²}` true, hence what connects the repo's `enstrophy` to the
gradient bound this theorem consumes.  For a general sequence that identity fails,
which is exactly the curl-free falsification.
-/

/-- **`SpaceEquicontinuous` from a uniform `L²(0,T;H¹)` bound.**  Given the
slicewise Brezis Prop. 9.3 estimate and a uniform bound `C` on the time-integrated
squared gradient, the family is spatially equicontinuous, with the explicit
modulus `δ = √(ε/(C+1))`.

`C + 1` rather than `C` so that the modulus is well defined at `C = 0` and the
final estimate `‖y‖²·C < ε·C/(C+1) ≤ ε` needs no case split. -/
theorem spaceEquicontinuous_of_dissipation_bound
    (uSeq : ℕ → VelocityEvolution) (C : ℝ) (hC : 0 ≤ C)
    (hbrezis : ∀ (m : ℕ) (t : ℝ), 0 < t → ∀ y : Space,
      (∫ x : Space, ‖uSeq m t (x + y) - uSeq m t x‖ ^ 2)
        ≤ ‖y‖ ^ 2 * ∫ x : Space, ‖fderiv ℝ (uSeq m t) x‖ ^ 2)
    (hintTr : ∀ (m : ℕ) (T : ℝ) (y : Space),
      IntegrableOn (fun t => ∫ x : Space, ‖uSeq m t (x + y) - uSeq m t x‖ ^ 2)
        (Set.Ioc (0:ℝ) T) volume)
    (hintGr : ∀ (m : ℕ) (T : ℝ),
      IntegrableOn (fun t => ∫ x : Space, ‖fderiv ℝ (uSeq m t) x‖ ^ 2)
        (Set.Ioc (0:ℝ) T) volume)
    (hdiss : ∀ (m : ℕ) (T : ℝ), 0 ≤ T →
      (∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖fderiv ℝ (uSeq m t) x‖ ^ 2) ≤ C) :
    SpaceEquicontinuous uSeq := by
  intro T ε hε
  rcases lt_or_ge T 0 with hT | hT
  · -- degenerate window: `Ioc 0 T` is empty, so every error integral is `0`
    refine ⟨1, one_pos, fun m y _ => ?_⟩
    rw [show Set.Ioc (0:ℝ) T = ∅ from Set.Ioc_eq_empty (by linarith)]
    simpa using hε.le
  refine ⟨Real.sqrt (ε / (C + 1)), Real.sqrt_pos.mpr (by positivity), fun m y hy => ?_⟩
  -- `‖y‖² < ε/(C+1)`
  have hCpos : (0:ℝ) < C + 1 := by linarith
  have hysq : ‖y‖ ^ 2 < ε / (C + 1) := by
    have hlt : ‖y‖ < Real.sqrt (ε / (C + 1)) := hy
    have := (Real.lt_sqrt (norm_nonneg y)).mp hlt
    linarith
  -- Brezis, integrated in `t`, then the dissipation bound
  calc (∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖uSeq m t (x + y) - uSeq m t x‖ ^ 2)
      ≤ ∫ t in Set.Ioc (0:ℝ) T,
          ‖y‖ ^ 2 * ∫ x : Space, ‖fderiv ℝ (uSeq m t) x‖ ^ 2 :=
        setIntegral_mono_on (hintTr m T y) ((hintGr m T).const_mul _) measurableSet_Ioc
          fun t ht => hbrezis m t ht.1 y
    _ = ‖y‖ ^ 2 * ∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖fderiv ℝ (uSeq m t) x‖ ^ 2 :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ ‖y‖ ^ 2 * C := by
        exact mul_le_mul_of_nonneg_left (hdiss m T hT) (by positivity)
    _ ≤ ε := by
        rcases eq_or_lt_of_le hC with hC0 | hC0
        · rw [← hC0]; simpa using hε.le
        · have h1 : ‖y‖ ^ 2 * C < (ε / (C + 1)) * C := by
            exact mul_lt_mul_of_pos_right hysq hC0
          have h2 : (ε / (C + 1)) * C ≤ ε := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hCpos]
            nlinarith [hε.le]
          linarith

/-!
### Joint measurability of finite modal sums (certified)

`jointly_measurable` is one of the two hypotheses added to repair the falsified
`aubin_lions_l2loc_compactness`, so it has to be dischargeable by the Galerkin
construction or the repair merely moved the problem.  It is: a Galerkin
approximant is `u_m(t,x) = ∑_{i<m} cᵢ(t)·wᵢ(x)`, a finite sum of products of a
`t`-continuous coefficient and an `x`-continuous mode, hence jointly *continuous*.

The one wrinkle is that `finiteDim_dissipative_ode_global` (BANKED above) is
honestly forward-only: it constrains `u` on `Set.Ici 0` and says nothing at all
for `t < 0`, so the raw solution carries no measurability there.
`forwardExtend` is the canonical continuation, constant backwards from `t = 0`;
it changes nothing on `t ≥ 0`, which is the half-space on which every other
field of `GalerkinModeData` is imposed.
-/

/-- Continuation of a forward-only trajectory to negative times by its value at
`0`.  Agrees with the original on `Set.Ici 0` (`forwardExtend_eq_of_nonneg`). -/
def forwardExtend {E : Type*} (u : ℝ → E) : ℝ → E := fun t => u (max t 0)

theorem forwardExtend_eq_of_nonneg {E : Type*} (u : ℝ → E) {t : ℝ} (ht : 0 ≤ t) :
    forwardExtend u t = u t := by
  simp [forwardExtend, max_eq_left ht]

/-- A forward ODE solution, continued backwards by its value at `0`, is
continuous on all of `ℝ`.  `HasDerivWithinAt … (Set.Ici 0)` at every `t ≥ 0`
gives `ContinuousOn` there, and `t ↦ max t 0` maps `ℝ` into `Set.Ici 0`. -/
theorem continuous_forwardExtend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ → E) (F : ℝ → E)
    (hu : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt u (F t) (Set.Ici (0:ℝ)) t) :
    Continuous (forwardExtend u) := by
  have hcont : ContinuousOn u (Set.Ici (0:ℝ)) := fun t ht => (hu t ht).continuousWithinAt
  exact hcont.comp_continuous (continuous_id.max continuous_const)
    fun t => Set.mem_Ici.mpr (le_max_right t 0)

/-- **A finite modal sum is jointly `(t,x)`-measurable.**  Finite sums of products
of a `t`-continuous coefficient and an `x`-continuous mode are jointly continuous,
hence measurable. -/
theorem jointlyMeasurable_modalSum {n : ℕ} (c : Fin n → ℝ → ℝ) (w : Fin n → Space → Space)
    (hc : ∀ i, Continuous (c i)) (hw : ∀ i, Continuous (w i)) :
    Measurable fun z : ℝ × Space => ∑ i, c i z.1 • w i z.2 :=
  (continuous_finsetSum _ fun i _ =>
    ((hc i).comp continuous_fst).smul ((hw i).comp continuous_snd)).measurable

/-- `JointlyMeasurable` for a sequence of finite modal sums — the
`jointly_measurable` field of `GalerkinModeData` and `GalerkinApproximation`. -/
theorem jointlyMeasurable_of_modalSum (deg : ℕ → ℕ)
    (c : ∀ m : ℕ, Fin (deg m) → ℝ → ℝ) (w : ∀ m : ℕ, Fin (deg m) → Space → Space)
    (hc : ∀ (m : ℕ) (i : Fin (deg m)), Continuous (c m i))
    (hw : ∀ (m : ℕ) (i : Fin (deg m)), Continuous (w m i)) :
    JointlyMeasurable fun m t x => ∑ i, c m i t • w m i x :=
  fun m => jointlyMeasurable_modalSum (c m) (w m) (hc m) (hw m)

/-- **The field, discharged end-to-end from what is already banked.**  Given, for
each mode, a coefficient solving a forward ODE on `Set.Ici 0` — precisely the
output shape of `finiteDim_dissipative_ode_global` — and Schwartz modes, the
resulting Galerkin-shaped sequence is `JointlyMeasurable`.  So the Pattern-A
hypothesis added in the Aubin–Lions repair costs the Galerkin construction
nothing beyond choosing the (irrelevant, `t < 0`) continuation. -/
theorem jointlyMeasurable_of_forwardODE (deg : ℕ → ℕ)
    (c : ∀ m : ℕ, Fin (deg m) → ℝ → ℝ) (F : ∀ m : ℕ, Fin (deg m) → ℝ → ℝ)
    (hc : ∀ (m : ℕ) (i : Fin (deg m)) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m i) (F m i t) (Set.Ici (0:ℝ)) t)
    (w : ∀ m : ℕ, Fin (deg m) → SchwartzVelocity) :
    JointlyMeasurable fun m t x =>
      ∑ i, forwardExtend (c m i) t • (w m i) x :=
  jointlyMeasurable_of_modalSum deg (fun m i => forwardExtend (c m i))
    (fun m i => fun x => (w m i) x)
    (fun m i => continuous_forwardExtend (c m i) (F m i) (hc m i))
    (fun m i => (w m i).continuous)

/-!
### Coefficient flows realized as Schwartz velocity fields

The global ODE theorem produces a curve in the Euclidean coefficient space
`EuclideanSpace ℝ (Fin (deg m))`.  The following definitions perform the actual
finite-mode realization against Schwartz modes.  They are upstream of
`GalerkinBasis`: that file supplies the certified dense orthonormal
divergence-free family and can instantiate these constructors without creating
the forbidden import cycle `LerayWeak → GalerkinBasis → LerayWeak`.
-/

/-- The initial Schwartz field represented by a finite coefficient vector. -/
noncomputable def galerkinModalInitialMode (deg : ℕ → ℕ)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin (deg m)))
    (w : ∀ m : ℕ, Fin (deg m) → SchwartzVelocity) (m : ℕ) : SchwartzVelocity :=
  ∑ i, c m 0 i • w m i

/-- The velocity evolution represented by a forward coefficient flow, extended
constantly to negative time before taking the finite modal sum. -/
noncomputable def galerkinModalApprox (deg : ℕ → ℕ)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin (deg m)))
    (w : ∀ m : ℕ, Fin (deg m) → SchwartzVelocity) : ℕ → VelocityEvolution :=
  fun m t x => ∑ i, forwardExtend (c m) t i • (w m i) x

/-- The realized evolution has exactly the represented Schwartz field as its
`t = 0` slice.  This is `GalerkinModeData.initial_eq` for the modal constructor. -/
theorem galerkinModalApprox_initial_eq (deg : ℕ → ℕ)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin (deg m)))
    (w : ∀ m : ℕ, Fin (deg m) → SchwartzVelocity) :
    ∀ m : ℕ, galerkinModalApprox deg c w m 0 =
      fun x => galerkinModalInitialMode deg c w m x := by
  intro m
  funext x
  simp [galerkinModalApprox, galerkinModalInitialMode, forwardExtend]

/-- A forward differentiable Euclidean coefficient flow realizes a jointly
measurable spacetime velocity field.  This supplies
`GalerkinModeData.jointly_measurable` for the modal constructor. -/
theorem galerkinModalApprox_jointlyMeasurable (deg : ℕ → ℕ)
    (c F : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin (deg m)))
    (hc : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (c m) (F m t) (Set.Ici (0 : ℝ)) t)
    (w : ∀ m : ℕ, Fin (deg m) → SchwartzVelocity) :
    JointlyMeasurable (galerkinModalApprox deg c w) := by
  intro m
  apply jointlyMeasurable_modalSum
    (fun i t => forwardExtend (c m) t i) (fun i x => (w m i) x)
  · intro i
    exact (EuclideanSpace.proj i).continuous.comp
      (continuous_forwardExtend (c m) (F m) (hc m))
  · exact fun i => (w m i).continuous

/-- Every spatial slice of a realized finite modal flow is square-integrable,
because a finite linear combination of Schwartz modes is again Schwartz.  This
supplies `GalerkinModeData.sq_integrable` without an analytic payload. -/
theorem galerkinModalApprox_sq_integrable (deg : ℕ → ℕ)
    (c : ∀ m : ℕ, ℝ → EuclideanSpace ℝ (Fin (deg m)))
    (w : ∀ m : ℕ, Fin (deg m) → SchwartzVelocity) :
    ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      Integrable (fun x : Space => ‖galerkinModalApprox deg c w m t x‖ ^ 2) := by
  intro m t _
  let f : SchwartzVelocity := ∑ i, forwardExtend (c m) t i • w m i
  simpa [f, galerkinModalApprox] using integrable_norm_sq_schwartz f

/-! **[FORMER NAMED RESIDUAL — RELOCATED 2026-08-18; finite-mode Galerkin
construction; Temam, *NSE* III.3; Constantin–Foias, *NSE* II; Leray, Acta
Math. 63 (1934) §§18–20; est ~350 LOC.]**
Projecting NSE onto the first `m` divergence-free modes gives a `C¹` ODE on a
finite subspace whose field `F_m = −ν A_m + P_m B` is dissipative-plus-skew, so
`⟨F_m x, x⟩ ≤ 0`; `finiteDim_dissipative_ode_global` (BANKED, above) then yields
a global finite-mode solution and `galerkin_apriori_bound` (BANKED) gives
`kinetic_bounded`, while
`Navier.Analysis.EnergyDissipation.dissipation_integral_le_forward` (BANKED)
gives `enstrophy_bounded` with `C = ‖u₀‖²_{L²}/(2ν)`.

**Dependencies, exactly — corrected.**  (i) An earlier revision of this docstring
named `Navier.Analysis.GalerkinBasis.GalerkinBasisFamily` and its density residual
`exists_denseIndependentDivFreeFamily` as the dependency of this leaf.  **That is
structurally impossible and the claim is withdrawn**: `GalerkinBasis.lean` line 1
is `import Navier.Analysis.LerayWeak`, so this file is strictly *upstream* of
`GalerkinBasis` and cannot consume anything from it.  Nothing in this file
references it in code, and `GalerkinModeData` has no basis field — its data is
`approx`, `initialMode`, and the bound/regularity clauses.  So the divergence-free
basis is not a blocker for this leaf; whoever closes it either supplies the modes
as *data* at the point of use, or the leaf relocates downstream of `GalerkinBasis`.
`initial_converges_L2` is stated in the Euclidean seminorm because that is the
shape a projection layer delivers, not because a projection is imported here.
**Basis status: CERTIFIED, but downstream.**  The divergence-free basis now exists —
`Navier.Analysis.GalerkinBasis.exists_denseIndependentDivFreeFamily` (countable,
independent, divergence-free Schwartz family, dense among divergence-free Schwartz
fields for `schwartzL2Inner`), proved from the `GalerkinRawFamily` reservoir via the
hoisted `SchwartzL2Pairing` layer — so the relocation route is unblocked and no
*basis* mathematics is missing.  What remains after relocation is the finite-mode
construction itself: the projected field `F_m = −ν A_m + P_m B` is dissipative by
skew-symmetry of `B`; `exists_forward_galerkinCoefficientFlow` (CERTIFIED, above)
now constructs the global coefficient curve together with its exact forward
squared-norm bound.  The actual coefficient-to-field realization is also
certified: `galerkinModalApprox_initial_eq`,
`galerkinModalApprox_jointlyMeasurable`, and
`galerkinModalApprox_sq_integrable` discharge `initial_eq`,
`jointly_measurable`, and `sq_integrable` for the finite Schwartz modal sum.
`galerkin_apriori_bound` and
`EnergyDissipation.dissipation_integral_le_forward` give the two uniform bounds,
basis density gives `initial_converges_L2`, and the Galerkin equation against test
functions gives `weak_consistent`.
(ii) `time_equicontinuous` and `weak_consistent` from the finite-mode energy
identity and the `∂ₜu_m ∈ L²(0,T;H⁻¹)` bound (est ~100 LOC).
(iii) The two Pattern-A fields added in the Aubin–Lions repair are **both
discharged**, so neither is an obligation of this leaf any more.
`jointly_measurable`: `jointlyMeasurable_of_forwardODE` (CERTIFIED below) settles
it outright for any modal sum built from forward ODE solutions and Schwartz modes,
which is exactly the shape this construction produces.  `space_equicontinuous`:
`spaceEquicontinuous_of_dissipation_bound` (CERTIFIED below) reduces it to the
slicewise Brezis Prop. 9.3 estimate — itself certified as
`RieszKolmogorov.integral_norm_sub_sq_le_mul_integral_fderiv_sq` — together with
`∫₀^T ‖∇u_m‖²_{L²} ≤ ‖u₀‖²_{L²}/(2ν)`
(`EnergyDissipation.dissipation_integral_le_forward`, BANKED), and supplies the
explicit modulus `δ = √(ε/(C+1))`.  This is where the finite-mode construction
pays for what the bare Aubin–Lions bundle could not: `u_m(t)` lies in the span of
the first `m` **divergence-free** modes, so there `‖ω‖_{L²} = ‖∇u_m‖_{L²}` genuinely
holds and the enstrophy bound *is* a gradient bound.  For a general sequence that
identity fails — which is precisely the curl-free falsification.

The product-norm/Euclidean conversion that used to sit inside this obligation is
now certified (`galerkinApproximation_of_modeData`).

**RELOCATED 2026-08-18 (lane NK2).**  The declarations
`exists_galerkinModeData` and `galerkin_approximation_exists` now live in
`Navier.Analysis.LerayWeakExistence` (same namespace, same names, same types),
downstream of `GalerkinBasis`: `exists_galerkinModeData` is there a one-line
composition of `GalerkinBasis.exists_galerkinModeData` — the construction
described above, assembled from the certified basis modulo exactly
`hspace`/`htime`/`hweak`.  The duplicate upstream `sorry` that sat here is
deleted; nothing in this file referenced it in code. -/

/-!
### `StrongL2LocLimit` plumbing (certified)
-/

/-- Passing to a further subsequence preserves the strong `L²_loc` limit — the
bookkeeping step of the diagonal extraction inside Aubin–Lions. -/
theorem StrongL2LocLimit.comp_strictMono {uSeq : ℕ → VelocityEvolution}
    {u : VelocityEvolution} (h : StrongL2LocLimit uSeq u) {τ : ℕ → ℕ} (hτ : StrictMono τ) :
    StrongL2LocLimit (fun k => uSeq (τ k)) u :=
  fun T R => (h T R).comp hτ.tendsto_atTop

/-- The constant sequence converges to its own value (non-degeneracy smoke:
`StrongL2LocLimit` is satisfiable with a genuine, measurable limit). -/
theorem strongL2LocLimit_const (u : VelocityEvolution) : StrongL2LocLimit (fun _ => u) u := by
  intro T R
  have hz : (fun _ : ℕ => ∫ t in Set.Ioc (0:ℝ) T,
      ∫ x in Metric.closedBall (0:Space) R, ‖u t x - u t x‖ ^ 2) = fun _ : ℕ => (0:ℝ) := by
    funext m; simp
  rw [hz]; exact tendsto_const_nhds

/-- **Consumer-instantiability smoke (anti-vacuity, B-Audit-3/8).**  The zero
sequence satisfies every hypothesis of `aubin_lions_l2loc_compactness` at
`C = 0`, and the strengthened conclusion holds for it with limit `0` and
`σ = id`.  So neither the hypothesis bundle nor the strengthened conclusion is
vacuous. -/
theorem aubinLions_zero_instance :
    UniformKineticBound (fun (_ : ℕ) (_ : ℝ) (_ : Space) => (0 : Space)) 0 ∧
    UniformEnstrophyBound (fun (_ : ℕ) (_ : ℝ) (_ : Space) => (0 : Space)) 0 ∧
    TimeEquicontinuous (fun (_ : ℕ) (_ : ℝ) (_ : Space) => (0 : Space)) ∧
    SpaceEquicontinuous (fun (_ : ℕ) (_ : ℝ) (_ : Space) => (0 : Space)) ∧
    JointlyMeasurable (fun (_ : ℕ) (_ : ℝ) (_ : Space) => (0 : Space)) ∧
    (∀ t : ℝ, 0 ≤ t →
      Integrable (fun x : Space => ‖(fun (_ : ℝ) (_ : Space) => (0:Space)) t x‖ ^ 2)) ∧
    StrongL2LocLimit (fun (_ : ℕ) (_ : ℝ) (_ : Space) => (0 : Space)) (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m t _; simp
  · intro m T _; simp only [enstrophy_zero_velocity]; simp
  · intro T ε hε
    exact ⟨1, one_pos, fun m h _ => by simp only [sub_self, norm_zero]; simp [hε.le]⟩
  · intro T ε hε
    exact ⟨1, one_pos, fun m y _ => by simp only [sub_self, norm_zero]; simp [hε.le]⟩
  · exact fun _ => measurable_const
  · intro t _
    exact (integrable_zero Space ℝ volume).congr (Filter.Eventually.of_forall fun x => by simp)
  · exact strongL2LocLimit_const (fun _ _ => 0)

/-!
### The enstrophy blind spot (certified)

The checked obstruction that reshapes the residual below.  The diagonal extraction
that used to sit here is pure subsequence combinatorics with no Navier–Stokes content,
so it now lives upstream in `Navier.Analysis.RieszKolmogorov`.
-/

/-- The curl vanishes wherever the spatial Fréchet derivative vanishes. -/
theorem staticCurl_eq_zero_of_fderiv_eq_zero (u : VelocityField) (x : Space)
    (h : fderiv ℝ u x = 0) :
    Navier.Analysis.Vorticity.staticCurl u x = 0 := by
  simp [Navier.Analysis.Vorticity.staticCurl, h]

/-- **Enstrophy is blind to non-differentiability.**  Mathlib's `fderiv` takes the
junk value `0` at a point where `u` is not differentiable, so `staticCurl` — hence
`vorticity` and `enstrophy` — reads `0` there rather than detecting the singularity. -/
theorem staticCurl_eq_zero_of_not_differentiableAt (u : VelocityField) (x : Space)
    (h : ¬ DifferentiableAt ℝ u x) :
    Navier.Analysis.Vorticity.staticCurl u x = 0 :=
  staticCurl_eq_zero_of_fderiv_eq_zero u x (fderiv_zero_of_not_differentiableAt h)

/-- If the spatial derivative vanishes almost everywhere, the enstrophy is `0`. -/
theorem enstrophy_eq_zero_of_ae_fderiv_eq_zero (u : VelocityEvolution) (t : ℝ)
    (h : ∀ᵐ x : Space, fderiv ℝ (u t) x = 0) : enstrophy u t = 0 := by
  have hz : (fun x : Space => officialEuclideanNorm
      (Navier.Analysis.Vorticity.vorticity u t x) ^ 2) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [h] with x hx
    rw [show Navier.Analysis.Vorticity.vorticity u t x = 0 from
      staticCurl_eq_zero_of_fderiv_eq_zero (u t) x hx,
      (Navier.Analysis.Vorticity.officialEuclideanNorm_eq_zero_iff 0).mpr rfl]
    norm_num
  rw [enstrophy, integral_congr_ae hz]
  simp

/-- The step field: the indicator of the open unit ball in a fixed direction.  It is
bounded, compactly supported and square-integrable, and it is discontinuous across
the unit sphere. -/
def stepField : VelocityField :=
  Set.indicator (Metric.ball (0:Space) 1) (fun _ => basisVector 0)

theorem fderiv_stepField_eq_zero_of_notMem_sphere (x : Space)
    (hx : x ∉ Metric.sphere (0:Space) 1) : fderiv ℝ stepField x = 0 := by
  rcases lt_or_gt_of_ne (show ‖x‖ ≠ 1 by simpa [Metric.mem_sphere, dist_zero_right] using hx)
    with hlt | hgt
  · have hmem : x ∈ Metric.ball (0:Space) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hlt
    have hEq : stepField =ᶠ[nhds x] (fun _ : Space => basisVector 0) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with y hy
      simp [stepField, Set.indicator_of_mem hy]
    rw [hEq.fderiv_eq]; simp
  · have hopen : IsOpen {y : Space | 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
    have hEq : stepField =ᶠ[nhds x] (fun _ : Space => (0 : Space)) := by
      filter_upwards [hopen.mem_nhds hgt] with y hy
      have hnm : y ∉ Metric.ball (0:Space) 1 := by
        simp only [Metric.mem_ball, dist_zero_right, not_lt]; exact le_of_lt hy
      simp [stepField, Set.indicator_of_notMem hnm]
    rw [hEq.fderiv_eq]; simp

/-- **Checked witness: `UniformEnstrophyBound` detects no spatial singularity.**  The
discontinuous `stepField` has repo-`enstrophy` exactly `0` at every time, because the
curl is computed from `fderiv`, which is `0` off the (null) unit sphere by local
constancy and `0` on it by Mathlib's junk convention. -/
theorem enstrophy_stepField_eq_zero (t : ℝ) :
    enstrophy (fun _ => stepField) t = 0 := by
  refine enstrophy_eq_zero_of_ae_fderiv_eq_zero _ t ?_
  have hnull : volume (Metric.sphere (0:Space) 1) = 0 :=
    MeasureTheory.Measure.addHaar_sphere volume (0:Space) 1
  have hae : ∀ᵐ x : Space, x ∉ Metric.sphere (0:Space) 1 :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with x hx
  exact fderiv_stepField_eq_zero_of_notMem_sphere x hx

/-!
### The countable-window reduction (unlocked by `JointlyMeasurable`)

`StrongL2LocLimit` quantifies over **real** parameters `T, R`, while every
extraction argument produces convergence only along the **countable** exhaustion
`T = R = n`.  Bridging the two needs
`∫_{Ioc 0 T} ∫_{B_R} ≤ ∫_{Ioc 0 n} ∫_{B_n}` for `T, R ≤ n`, hence integrability
of the inner integral *in `t`* — which slicewise `x`-integrability cannot supply
and which `JointlyMeasurable` does.  This is the second of the two gaps recorded
in the Aubin–Lions residual; it is closed here.
-/

/-- `‖v − w‖²` is integrable as soon as both `‖v‖²` and `‖w‖²` are and the
difference is measurable, by `‖v − w‖² ≤ 2‖v‖² + 2‖w‖²`. -/
theorem integrable_norm_sub_sq (v w : VelocityField)
    (hmeas : Measurable fun x : Space => v x - w x)
    (hv : Integrable fun x : Space => ‖v x‖ ^ 2)
    (hw : Integrable fun x : Space => ‖w x‖ ^ 2) :
    Integrable fun x : Space => ‖v x - w x‖ ^ 2 := by
  refine Integrable.mono' ((hv.const_mul 2).add (hw.const_mul 2))
    (hmeas.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have htri : ‖v x - w x‖ ≤ ‖v x‖ + ‖w x‖ := norm_sub_le _ _
  have hbd : ‖v x - w x‖ ^ 2 ≤ 2 * ‖v x‖ ^ 2 + 2 * ‖w x‖ ^ 2 := by
    nlinarith [norm_nonneg (v x), norm_nonneg (w x), norm_nonneg (v x - w x),
      sq_nonneg (‖v x‖ - ‖w x‖)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v x - w x‖ ^ 2)]
  exact hbd

/-- **Real windows reduce to integer windows.**  Given joint `(t,x)`-measurability
of the sequence and of the limit, slicewise square-integrability, and a uniform
kinetic bound on both, convergence of the error over every *integer* window
`(0,n] × B̄(0,n)` upgrades to `StrongL2LocLimit`, i.e. convergence over every
*real* window `(0,T] × B̄(0,R)`.

The two monotonicity steps are exactly what the bare function type
`VelocityEvolution` could not support before: the inner one
(`setIntegral_mono_set` on `B̄(0,R) ⊆ B̄(0,n)`) needs slicewise integrability on
the larger ball, and the outer one (`Ioc 0 T ⊆ Ioc 0 n`) needs the inner integral
to be integrable **in `t`**, which follows from `JointlyMeasurable` via
`StronglyMeasurable.integral_prod_right'` together with the uniform bound
`∫_{B̄(0,n)} ‖u_k(t) − u(t)‖² ≤ 2‖u_k(t)‖²_{L²} + 2‖u(t)‖²_{L²} ≤ 4C`. -/
theorem strongL2LocLimit_of_natWindows
    (uSeq : ℕ → VelocityEvolution) (u : VelocityEvolution) (C : ℝ)
    (hmeasSeq : JointlyMeasurable uSeq)
    (hmeasU : Measurable fun z : ℝ × Space => u z.1 z.2)
    (hintSeq : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable fun x : Space => ‖uSeq m t x‖ ^ 2)
    (hintU : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖u t x‖ ^ 2)
    (hkinSeq : UniformKineticBound uSeq C)
    (hkinU : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ C)
    (hwin : ∀ n : ℕ, Filter.Tendsto
      (fun k => ∫ t in Set.Ioc (0:ℝ) (n:ℝ), ∫ x in Metric.closedBall (0:Space) (n:ℝ),
        ‖uSeq k t x - u t x‖ ^ 2) Filter.atTop (nhds 0)) :
    StrongL2LocLimit uSeq u := by
  have hFmeas : ∀ k : ℕ, Measurable fun z : ℝ × Space => ‖uSeq k z.1 z.2 - u z.1 z.2‖ ^ 2 :=
    fun k => (((hmeasSeq k).sub hmeasU).norm).pow_const 2
  have hFnn : ∀ (k : ℕ) (t : ℝ) (x : Space), (0:ℝ) ≤ ‖uSeq k t x - u t x‖ ^ 2 :=
    fun _ _ _ => by positivity
  -- slicewise integrability of the error
  have hslice : ∀ (k : ℕ) (t : ℝ), 0 ≤ t →
      Integrable fun x : Space => ‖uSeq k t x - u t x‖ ^ 2 := by
    intro k t ht
    have hm1 : Measurable fun x : Space => uSeq k t x := (hmeasSeq k).comp measurable_prodMk_left
    have hm2 : Measurable fun x : Space => u t x := hmeasU.comp measurable_prodMk_left
    exact integrable_norm_sub_sq (uSeq k t) (u t) (hm1.sub hm2) (hintSeq k t ht) (hintU t ht)
  -- the uniform slicewise bound `∫ ‖u_k(t) − u(t)‖² ≤ 4C`
  have hCnn : 0 ≤ C :=
    le_trans (integral_nonneg fun x => by positivity) (hkinSeq 0 0 le_rfl)
  have hglob : ∀ (k : ℕ) (t : ℝ), 0 ≤ t →
      (∫ x : Space, ‖uSeq k t x - u t x‖ ^ 2) ≤ 4 * C := by
    intro k t ht
    have hb : (∫ x : Space, ‖uSeq k t x - u t x‖ ^ 2)
        ≤ ∫ x : Space, (2 * ‖uSeq k t x‖ ^ 2 + 2 * ‖u t x‖ ^ 2) := by
      refine integral_mono (hslice k t ht)
        (((hintSeq k t ht).const_mul 2).add ((hintU t ht).const_mul 2)) fun x => ?_
      have htri : ‖uSeq k t x - u t x‖ ≤ ‖uSeq k t x‖ + ‖u t x‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (uSeq k t x), norm_nonneg (u t x),
        norm_nonneg (uSeq k t x - u t x), sq_nonneg (‖uSeq k t x‖ - ‖u t x‖)]
    rw [integral_add ((hintSeq k t ht).const_mul 2) ((hintU t ht).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hb
    have h1 : (∫ x : Space, ‖uSeq k t x‖ ^ 2) ≤ C := hkinSeq k t ht
    have h2 : (∫ x : Space, ‖u t x‖ ^ 2) ≤ C := hkinU t ht
    linarith
  -- the ball integral, as a function of `t`, is integrable on every `Ioc 0 b`
  have hInner : ∀ (k : ℕ) (ρ b : ℝ),
      IntegrableOn (fun t => ∫ x in Metric.closedBall (0:Space) ρ, ‖uSeq k t x - u t x‖ ^ 2)
        (Set.Ioc (0:ℝ) b) volume := by
    intro k ρ b
    have hsm : StronglyMeasurable
        fun t : ℝ => ∫ x in Metric.closedBall (0:Space) ρ, ‖uSeq k t x - u t x‖ ^ 2 :=
      (hFmeas k).stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Metric.closedBall (0:Space) ρ))
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (measure_Ioc_lt_top).ne hsm.aestronglyMeasurable (M := 4 * C) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    have hnn : 0 ≤ ∫ x in Metric.closedBall (0:Space) ρ, ‖uSeq k t x - u t x‖ ^ 2 :=
      setIntegral_nonneg measurableSet_closedBall fun x _ => hFnn k t x
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc (∫ x in Metric.closedBall (0:Space) ρ, ‖uSeq k t x - u t x‖ ^ 2)
        ≤ ∫ x : Space, ‖uSeq k t x - u t x‖ ^ 2 :=
          setIntegral_le_integral (hslice k t ht.1.le)
            (Filter.Eventually.of_forall fun x => hFnn k t x)
      _ ≤ 4 * C := hglob k t ht.1.le
  -- the squeeze against the integer window `n ≥ max T R`
  intro T R
  obtain ⟨n, hn⟩ := exists_nat_ge (max T R)
  have hTn : T ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
  have hRn : R ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
  refine squeeze_zero (fun k => ?_) (fun k => ?_) (hwin n)
  · exact setIntegral_nonneg measurableSet_Ioc fun t _ =>
      setIntegral_nonneg measurableSet_closedBall fun x _ => hFnn k t x
  · calc (∫ t in Set.Ioc (0:ℝ) T, ∫ x in Metric.closedBall (0:Space) R,
              ‖uSeq k t x - u t x‖ ^ 2)
        ≤ ∫ t in Set.Ioc (0:ℝ) T, ∫ x in Metric.closedBall (0:Space) (n:ℝ),
              ‖uSeq k t x - u t x‖ ^ 2 := by
          refine setIntegral_mono_on (hInner k R T) (hInner k (n:ℝ) T)
            measurableSet_Ioc fun t ht => ?_
          exact setIntegral_mono_set ((hslice k t ht.1.le).integrableOn)
            (Filter.Eventually.of_forall fun x => hFnn k t x)
            (HasSubset.Subset.eventuallyLE (Metric.closedBall_subset_closedBall hRn))
      _ ≤ ∫ t in Set.Ioc (0:ℝ) (n:ℝ), ∫ x in Metric.closedBall (0:Space) (n:ℝ),
              ‖uSeq k t x - u t x‖ ^ 2 := by
          refine setIntegral_mono_set (hInner k (n:ℝ) (n:ℝ))
            (Filter.Eventually.of_forall fun t =>
              setIntegral_nonneg measurableSet_closedBall fun x _ => hFnn k t x)
            (HasSubset.Subset.eventuallyLE (Set.Ioc_subset_Ioc_right hTn))

/-!
### Window-Cauchy bookkeeping and the diagonal (certified)

The compactness core factors through the *Cauchy* condition on a single integer
window, which mentions no limit and is therefore the object the diagonal
extraction can iterate over.  `WindowCauchy` is stable under passing to a
further subsequence and under dropping a finite head — exactly the two closure
properties `exists_diagonal_subseq` consumes.
-/

/-- The squared `L²` error of two velocity evolutions over the integer window
`(0,n] × B̄(0,n)`. -/
def windowError (v w : VelocityEvolution) (n : ℕ) : ℝ :=
  ∫ t in Set.Ioc (0:ℝ) (n:ℝ), ∫ x in Metric.closedBall (0:Space) (n:ℝ), ‖v t x - w t x‖ ^ 2

/-- The subsequence `τ` is `L²`-Cauchy on the integer window `(0,n] × B̄(0,n)`. -/
def WindowCauchy (uSeq : ℕ → VelocityEvolution) (n : ℕ) (τ : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j k : ℕ, N ≤ j → N ≤ k →
    windowError (uSeq (τ j)) (uSeq (τ k)) n < ε

/-- Window-Cauchy passes to further subsequences (`hsub` for the diagonal). -/
theorem WindowCauchy.comp_strictMono {uSeq : ℕ → VelocityEvolution} {n : ℕ} {τ : ℕ → ℕ}
    (h : WindowCauchy uSeq n τ) {ρ : ℕ → ℕ} (hρ : StrictMono ρ) :
    WindowCauchy uSeq n (τ ∘ ρ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun j k hj hk =>
    hN (ρ j) (ρ k) (le_trans hj hρ.le_apply) (le_trans hk hρ.le_apply)⟩

/-- Window-Cauchy is a tail condition (`htail` for the diagonal). -/
theorem WindowCauchy.of_tail {uSeq : ℕ → VelocityEvolution} {n : ℕ} (N : ℕ) {τ : ℕ → ℕ}
    (h : WindowCauchy uSeq n fun k => τ (k + N)) : WindowCauchy uSeq n τ := by
  intro ε hε
  obtain ⟨M, hM⟩ := h ε hε
  refine ⟨M + N, fun j k hj hk => ?_⟩
  have hjN : N ≤ j := le_trans (Nat.le_add_left N M) hj
  have hkN : N ≤ k := le_trans (Nat.le_add_left N M) hk
  have hres := hM (j - N) (k - N) (by omega) (by omega)
  simp only [Nat.sub_add_cancel hjN, Nat.sub_add_cancel hkN] at hres
  exact hres

/-- **One subsequence Cauchy on every window**, by the nested Cantor diagonal
`exists_diagonal_subseq` applied to `WindowCauchy`. -/
theorem exists_subseq_forall_windowCauchy (uSeq : ℕ → VelocityEvolution)
    (hstep : ∀ (n : ℕ) (τ : ℕ → ℕ), StrictMono τ →
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ WindowCauchy uSeq n (τ ∘ ρ)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n : ℕ, WindowCauchy uSeq n σ :=
  exists_diagonal_subseq (WindowCauchy uSeq)
    (fun _ _ _ hQ hρ => hQ.comp_strictMono hρ)
    (fun _ N _ hQ => WindowCauchy.of_tail N hQ)
    hstep

/-- **The window error is a product integral.**  `windowError` is a *nested* integral,
while the compactness criterion works with a single integral over the spacetime window.
`setIntegral_prod` bridges them — but it needs product-integrability, so the swap is
**not** free in Bochner form even though the integrand is nonnegative.  That matters:
without integrability `windowError` is a Bochner junk value, so the hypothesis is
load-bearing rather than bookkeeping.

Hypotheses read off the Galerkin bundle rather than chosen for convenience: joint
measurability (`JointlyMeasurable`), slicewise square-integrability (`sq_integrable`),
and a uniform slicewise bound (`UniformKineticBound`).  Those are exactly what
`integrable_prod_iff` consumes — slicewise integrability for a.e. `t`, plus
integrability in `t` of the inner integral, the latter from the uniform bound `4C` on
the finite interval `Ioc 0 n`. -/
theorem windowError_eq_setIntegral_prod (v w : VelocityEvolution) (n : ℕ) (C : ℝ)
    (hv : Measurable fun z : ℝ × Space => v z.1 z.2)
    (hw : Measurable fun z : ℝ × Space => w z.1 z.2)
    (hvi : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖v t x‖ ^ 2)
    (hwi : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖w t x‖ ^ 2)
    (hvb : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v t x‖ ^ 2) ≤ C)
    (hwb : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖w t x‖ ^ 2) ≤ C) :
    windowError v w n
      = ∫ z in Set.Ioc (0:ℝ) (n:ℝ) ×ˢ Metric.closedBall (0:Space) (n:ℝ),
          ‖v z.1 z.2 - w z.1 z.2‖ ^ 2 ∂(volume.prod volume) := by
  classical
  set T := Set.Ioc (0:ℝ) (n:ℝ) with hTdef
  set Bn := Metric.closedBall (0:Space) (n:ℝ) with hBdef
  have hFmeas : Measurable fun z : ℝ × Space => ‖v z.1 z.2 - w z.1 z.2‖ ^ 2 :=
    ((hv.sub hw).norm).pow_const 2
  have hnn : ∀ z : ℝ × Space, (0:ℝ) ≤ ‖v z.1 z.2 - w z.1 z.2‖ ^ 2 := fun _ => by positivity
  -- slicewise integrability of the difference
  have hslice : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖v t x - w t x‖ ^ 2 := by
    intro t ht
    exact integrable_norm_sub_sq (v t) (w t)
      ((hv.comp measurable_prodMk_left).sub (hw.comp measurable_prodMk_left))
      (hvi t ht) (hwi t ht)
  -- the uniform slicewise bound `4C`
  have hglob : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v t x - w t x‖ ^ 2) ≤ 4 * C := by
    intro t ht
    have hb : (∫ x : Space, ‖v t x - w t x‖ ^ 2)
        ≤ ∫ x : Space, (2 * ‖v t x‖ ^ 2 + 2 * ‖w t x‖ ^ 2) := by
      refine integral_mono (hslice t ht)
        (((hvi t ht).const_mul 2).add ((hwi t ht).const_mul 2)) fun x => ?_
      nlinarith [norm_nonneg (v t x), norm_nonneg (w t x), norm_nonneg (v t x - w t x),
        norm_sub_le (v t x) (w t x), sq_nonneg (‖v t x‖ - ‖w t x‖)]
    rw [integral_add ((hvi t ht).const_mul 2) ((hwi t ht).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hb
    linarith [hvb t ht, hwb t ht]
  -- the inner integral is integrable in `t` on the finite window
  have hsm : StronglyMeasurable fun t : ℝ => ∫ x in Bn, ‖v t x - w t x‖ ^ 2 :=
    hFmeas.stronglyMeasurable.integral_prod_right' (ν := volume.restrict Bn)
  have hInner : IntegrableOn (fun t => ∫ x in Bn, ‖v t x - w t x‖ ^ 2) T volume := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (measure_Ioc_lt_top).ne
      hsm.aestronglyMeasurable (M := 4 * C) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    have hnn' : 0 ≤ ∫ x in Bn, ‖v t x - w t x‖ ^ 2 :=
      setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn']
    calc (∫ x in Bn, ‖v t x - w t x‖ ^ 2)
        ≤ ∫ x : Space, ‖v t x - w t x‖ ^ 2 :=
          setIntegral_le_integral (hslice t ht.1.le)
            (Filter.Eventually.of_forall fun x => by positivity)
      _ ≤ 4 * C := hglob t ht.1.le
  -- product integrability, then the swap
  have hrestrict : (volume.restrict T).prod (volume.restrict Bn)
      = (volume.prod volume).restrict (T ×ˢ Bn) := Measure.prod_restrict _ _
  have hprod : IntegrableOn (fun z : ℝ × Space => ‖v z.1 z.2 - w z.1 z.2‖ ^ 2)
      (T ×ˢ Bn) (volume.prod volume) := by
    rw [IntegrableOn, ← hrestrict]
    refine (integrable_prod_iff hFmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun t ht => ?_)
      exact (hslice t ht.1.le).restrict
    · refine hInner.congr_fun (fun t _ => ?_) measurableSet_Ioc
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ‖v t x - w t x‖ ^ 2 = ‖‖v t x - w t x‖ ^ 2‖
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (MeasureTheory.setIntegral_prod _ hprod).symm

section FischerRiesz

open Filter
open scoped ENNReal NNReal Topology

/-- The integer spacetime window. -/
private def winQ (n : ℕ) : Set (ℝ × Space) :=
  Set.Ioc (0:ℝ) (n:ℝ) ×ˢ Metric.closedBall (0:Space) (n:ℝ)

private theorem winQ_mono {m n : ℕ} (h : m ≤ n) : winQ m ⊆ winQ n := by
  have hr : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast h
  exact Set.prod_mono (Set.Ioc_subset_Ioc_right hr) (Metric.closedBall_subset_closedBall hr)

private theorem eLpNorm_two_lt_of_lintegral_lt {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (F : α → Space) (c : ℝ≥0∞)
    (h : ∫⁻ z, ‖F z‖ₑ ^ 2 ∂ν < c ^ 2) : eLpNorm F 2 ν < c := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hz : ∀ z, ‖F z‖ₑ ^ (2:ℝ) = ‖F z‖ₑ ^ (2:ℕ) := by
    intro z; rw [← ENNReal.rpow_natCast]; norm_num
  simp_rw [hz]
  calc (∫⁻ z, ‖F z‖ₑ ^ (2:ℕ) ∂ν) ^ (1 / (2:ℝ))
      < (c ^ (2:ℕ)) ^ (1 / (2:ℝ)) := ENNReal.rpow_lt_rpow h (by norm_num)
    _ = c := by rw [← ENNReal.rpow_natCast c 2, ← ENNReal.rpow_mul]; norm_num

private theorem windowError_nonneg (v w : VelocityEvolution) (n : ℕ) :
    0 ≤ windowError v w n := by
  refine integral_nonneg fun t => ?_
  exact setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity

private theorem integrableOn_winQ (v w : VelocityEvolution) (n : ℕ) (C : ℝ)
    (hv : Measurable fun z : ℝ × Space => v z.1 z.2)
    (hw : Measurable fun z : ℝ × Space => w z.1 z.2)
    (hvi : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖v t x‖ ^ 2)
    (hwi : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖w t x‖ ^ 2)
    (hvb : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v t x‖ ^ 2) ≤ C)
    (hwb : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖w t x‖ ^ 2) ≤ C) :
    IntegrableOn (fun z : ℝ × Space => ‖v z.1 z.2 - w z.1 z.2‖ ^ 2) (winQ n)
      (volume.prod volume) := by
  classical
  set T := Set.Ioc (0:ℝ) (n:ℝ) with hTdef
  set Bn := Metric.closedBall (0:Space) (n:ℝ) with hBdef
  have hFmeas : Measurable fun z : ℝ × Space => ‖v z.1 z.2 - w z.1 z.2‖ ^ 2 :=
    ((hv.sub hw).norm).pow_const 2
  have hslice : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖v t x - w t x‖ ^ 2 := by
    intro t ht
    exact integrable_norm_sub_sq (v t) (w t)
      ((hv.comp measurable_prodMk_left).sub (hw.comp measurable_prodMk_left))
      (hvi t ht) (hwi t ht)
  have hglob : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v t x - w t x‖ ^ 2) ≤ 4 * C := by
    intro t ht
    have hb : (∫ x : Space, ‖v t x - w t x‖ ^ 2)
        ≤ ∫ x : Space, (2 * ‖v t x‖ ^ 2 + 2 * ‖w t x‖ ^ 2) := by
      refine integral_mono (hslice t ht)
        (((hvi t ht).const_mul 2).add ((hwi t ht).const_mul 2)) fun x => ?_
      nlinarith [norm_nonneg (v t x), norm_nonneg (w t x), norm_nonneg (v t x - w t x),
        norm_sub_le (v t x) (w t x), sq_nonneg (‖v t x‖ - ‖w t x‖)]
    rw [integral_add ((hvi t ht).const_mul 2) ((hwi t ht).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hb
    linarith [hvb t ht, hwb t ht]
  have hsm : StronglyMeasurable fun t : ℝ => ∫ x in Bn, ‖v t x - w t x‖ ^ 2 :=
    hFmeas.stronglyMeasurable.integral_prod_right' (ν := volume.restrict Bn)
  have hInner : IntegrableOn (fun t => ∫ x in Bn, ‖v t x - w t x‖ ^ 2) T volume := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (measure_Ioc_lt_top).ne
      hsm.aestronglyMeasurable (M := 4 * C) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    have hnn' : 0 ≤ ∫ x in Bn, ‖v t x - w t x‖ ^ 2 :=
      setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn']
    calc (∫ x in Bn, ‖v t x - w t x‖ ^ 2)
        ≤ ∫ x : Space, ‖v t x - w t x‖ ^ 2 :=
          setIntegral_le_integral (hslice t ht.1.le)
            (Filter.Eventually.of_forall fun x => by positivity)
      _ ≤ 4 * C := hglob t ht.1.le
  have hrestrict : (volume.restrict T).prod (volume.restrict Bn)
      = (volume.prod volume).restrict (T ×ˢ Bn) := Measure.prod_restrict _ _
  rw [winQ, IntegrableOn, ← hTdef, ← hBdef, ← hrestrict]
  refine (integrable_prod_iff hFmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    exact (hslice t ht.1.le).restrict
  · refine hInner.congr_fun (fun t _ => ?_) measurableSet_Ioc
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖v t x - w t x‖ ^ 2 = ‖‖v t x - w t x‖ ^ 2‖
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]


private theorem lintegral_winQ_eq (v w : VelocityEvolution) (n : ℕ) (C : ℝ)
    (hv : Measurable fun z : ℝ × Space => v z.1 z.2)
    (hw : Measurable fun z : ℝ × Space => w z.1 z.2)
    (hvi : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖v t x‖ ^ 2)
    (hwi : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖w t x‖ ^ 2)
    (hvb : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖v t x‖ ^ 2) ≤ C)
    (hwb : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖w t x‖ ^ 2) ≤ C) :
    ∫⁻ z in winQ n, ‖v z.1 z.2 - w z.1 z.2‖ₑ ^ 2 ∂(volume.prod volume)
      = ENNReal.ofReal (windowError v w n) := by
  have hI := integrableOn_winQ v w n C hv hw hvi hwi hvb hwb
  rw [windowError_eq_setIntegral_prod v w n C hv hw hvi hwi hvb hwb,
    show (Set.Ioc (0:ℝ) (n:ℝ) ×ˢ Metric.closedBall (0:Space) (n:ℝ)) = winQ n from rfl,
    ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun z => by positivity)]
  refine lintegral_congr fun z => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

private theorem continuous_enorm_sq :
    Continuous fun y : Space => ‖y‖ₑ ^ 2 := by
  have he : (fun y : Space => ‖y‖ₑ ^ 2) = fun y : Space => ENNReal.ofReal (‖y‖ ^ 2) := by
    funext y; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [he]
  exact ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)

/-- The official Euclidean squared norm, read into `ℝ≥0∞`, is continuous.  This is
the Euclidean counterpart of `continuous_enorm_sq`, and it is what lets the Fatou
step of Fischer–Riesz transport a `kineticEnergy` bound (not merely the sup-norm
bound) to the limit. -/
private theorem continuous_official_ofReal_sq :
    Continuous fun y : Space => ENNReal.ofReal (officialEuclideanNorm y ^ 2) :=
  ENNReal.continuous_ofReal.comp
    ((Navier.Analysis.EnergyNormBridge.continuous_officialEuclideanNorm).pow 2)

/-- `kineticEnergy` written through the official Euclidean norm, so that the
pointwise Fatou comparison can be run against a continuous function of the
velocity vector. -/
private theorem kineticEnergy_eq_integral_official (v : VelocityEvolution) (t : ℝ) :
    kineticEnergy v t = ∫ x : Space, officialEuclideanNorm (v t x) ^ 2 := by
  unfold kineticEnergy
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (Navier.Analysis.EnergyNormBridge.officialEuclideanNorm_sq_eq_sum_sq (v t x)).symm)

private theorem ofReal_quarter_pow (N : ℕ) :
    ENNReal.ofReal (((4:ℝ)⁻¹) ^ N) = (((2:ℝ≥0∞)⁻¹) ^ N) ^ 2 := by
  rw [ENNReal.ofReal_pow (by norm_num), ← pow_mul, mul_comm, pow_mul]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.inv_pow]
  norm_num

private theorem lintegral_enorm_sq_eq (v : VelocityField)
    (h : Integrable fun x : Space => ‖v x‖ ^ 2) :
    ∫⁻ x : Space, ‖v x‖ₑ ^ 2 = ENNReal.ofReal (∫ x : Space, ‖v x‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall fun x => by positivity)]
  exact lintegral_congr fun x => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-!
### The nested-to-product bridge

`TimeEquicontinuous` and `SpaceEquicontinuous` are stated as *nested* integrals
`∫_t ∫_x`, while `sum_cellError_le_modulus_of_memL2` consumes a single integral against
`volume.prod volume`.  The two are equal on a slab `S ×ˢ univ` once the integrand is
product-integrable, which `integrable_prod_iff` supplies from slicewise integrability
plus integrability of the inner integral in `t` — the same bookkeeping as
`windowError_eq_setIntegral_prod` and `integrableOn_winQ` above, with the spatial ball
replaced by all of `Space` (the equicontinuity hypotheses integrate over all of `x`).
-/

private theorem integrableOn_prod_univ (F : ℝ × Space → ℝ) (hFmeas : Measurable F)
    (S : Set ℝ) (hS : MeasurableSet S) (hnn : ∀ z, 0 ≤ F z)
    (hslice : ∀ t : ℝ, Integrable fun x : Space => F (t, x))
    (hOuter : IntegrableOn (fun t : ℝ => ∫ x : Space, F (t, x)) S) :
    IntegrableOn F (S ×ˢ (univ : Set Space)) (volume.prod volume) := by
  have hrestrict : (volume.restrict S).prod (volume.restrict (univ : Set Space))
      = (volume.prod volume).restrict (S ×ˢ (univ : Set Space)) := Measure.prod_restrict _ _
  rw [IntegrableOn, ← hrestrict, Measure.restrict_univ]
  refine (integrable_prod_iff hFmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact (MeasureTheory.ae_restrict_iff' hS).mpr
      (Filter.Eventually.of_forall fun t _ => hslice t)
  · refine hOuter.congr_fun (fun t _ => ?_) hS
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show F (t, x) = ‖F (t, x)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]

private theorem setIntegral_prod_univ_eq_nested (F : ℝ × Space → ℝ) (hFmeas : Measurable F)
    (S : Set ℝ) (hS : MeasurableSet S) (hnn : ∀ z, 0 ≤ F z)
    (hslice : ∀ t : ℝ, Integrable fun x : Space => F (t, x))
    (hOuter : IntegrableOn (fun t : ℝ => ∫ x : Space, F (t, x)) S) :
    (∫ z in S ×ˢ (univ : Set Space), F z ∂(volume.prod volume))
      = ∫ t in S, ∫ x : Space, F (t, x) := by
  rw [MeasureTheory.setIntegral_prod F
    (integrableOn_prod_univ F hFmeas S hS hnn hslice hOuter)]
  exact setIntegral_congr_fun hS fun t _ => by rw [Measure.restrict_univ]

/-- **(i) The window modulus: the two-leg split, with the negative-time overhang
resolved.**  A spacetime shift `k = (a, y)` with `‖k‖ ≤ h` is split
`τ_{(a,y)}f − f = (τ_{(a,y)}f − τ_{(a,0)}f) + (τ_{(a,0)}f − f)`, so the squared error
is at most twice the space leg plus twice the time leg.

**The design content is the working window.**  The space leg is a *space* shift taken
at the shifted time `t + a`, so after the change of variables `s = t + a`
(`intervalIntegral.integral_comp_add_right`) it lives on `Ioc (c+a) (T+a)`.  With
`|a| ≤ h` that set reaches back to `c − h`, and `SpaceEquicontinuous` says nothing for
`s ≤ 0` — `VelocityEvolution` is a bare function type with no obligation at negative
time, so the naive window `(0,T]` makes this step FALSE-as-stated, not merely
unprovable.  The repair is the hypothesis `h ≤ c`: the working window starts at `c`,
the shifted window `Ioc (c+a) (T+a)` then sits inside `Ioc 0 (T+h)`, and the space
modulus at horizon `T + h` covers it.  The discarded initial slab `(0,c]` is not lost
— `UniformKineticBound` bounds its contribution by `4Cc`, which the consumer drives to
zero along with `h` by taking `c = h → 0`.

The time leg needs no change of variables: `Ioc c T ⊆ Ioc 0 T` and
`TimeEquicontinuous` applies directly.

Integrability of the displacement integrals is taken as hypotheses, following the
convention of `Navier.Analysis.RieszKolmogorov`; each is discharged from
`JointlyMeasurable` plus slicewise square-integrability at the call site. -/
private theorem nested_window_modulus
    (v : VelocityEvolution) (a : ℝ) (y : Space) (c T h ε₁ ε₂ : ℝ)
    (hcT : c ≤ T) (hh : 0 < h) (hhc : h ≤ c) (ha : |a| ≤ h)
    (hInnerA : ∀ t : ℝ, Integrable fun x : Space => ‖v (t + a) (x + y) - v t x‖ ^ 2)
    (hInnerB1 : ∀ t : ℝ, Integrable fun x : Space => ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2)
    (hInnerB2 : ∀ t : ℝ, Integrable fun x : Space => ‖v (t + a) x - v t x‖ ^ 2)
    (hOutA : IntegrableOn
      (fun t : ℝ => ∫ x : Space, ‖v (t + a) (x + y) - v t x‖ ^ 2) (Set.Ioc c T))
    (hOutB1 : IntegrableOn
      (fun t : ℝ => ∫ x : Space, ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2) (Set.Ioc c T))
    (hOutB2 : IntegrableOn
      (fun t : ℝ => ∫ x : Space, ‖v (t + a) x - v t x‖ ^ 2) (Set.Ioc c T))
    (hOutS : IntegrableOn
      (fun s : ℝ => ∫ x : Space, ‖v s (x + y) - v s x‖ ^ 2) (Set.Ioc (0:ℝ) (T + h)))
    (hOutT : IntegrableOn
      (fun t : ℝ => ∫ x : Space, ‖v (t + a) x - v t x‖ ^ 2) (Set.Ioc (0:ℝ) T))
    (hS : (∫ s in Set.Ioc (0:ℝ) (T + h), ∫ x : Space, ‖v s (x + y) - v s x‖ ^ 2) ≤ ε₁)
    (hT : (∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖v (t + a) x - v t x‖ ^ 2) ≤ ε₂) :
    (∫ t in Set.Ioc c T, ∫ x : Space, ‖v (t + a) (x + y) - v t x‖ ^ 2) ≤ 2 * ε₁ + 2 * ε₂ := by
  have hc0 : 0 ≤ c := le_trans hh.le hhc
  have habs : -h ≤ a ∧ a ≤ h := abs_le.mp ha
  -- (1) pointwise + inner monotonicity
  have hinner : ∀ t : ℝ, (∫ x : Space, ‖v (t + a) (x + y) - v t x‖ ^ 2)
      ≤ 2 * (∫ x : Space, ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2)
        + 2 * ∫ x : Space, ‖v (t + a) x - v t x‖ ^ 2 := by
    intro t
    have hpt : ∀ x : Space, ‖v (t + a) (x + y) - v t x‖ ^ 2
        ≤ 2 * ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2 + 2 * ‖v (t + a) x - v t x‖ ^ 2 := by
      intro x
      have hsplit : v (t + a) (x + y) - v t x
          = (v (t + a) (x + y) - v (t + a) x) + (v (t + a) x - v t x) := by abel
      have hn := norm_add_le (v (t + a) (x + y) - v (t + a) x) (v (t + a) x - v t x)
      rw [← hsplit] at hn
      nlinarith [norm_nonneg (v (t + a) (x + y) - v (t + a) x),
        norm_nonneg (v (t + a) x - v t x), norm_nonneg (v (t + a) (x + y) - v t x),
        sq_nonneg (‖v (t + a) (x + y) - v (t + a) x‖ - ‖v (t + a) x - v t x‖)]
    have hsum : Integrable (fun x : Space =>
        2 * ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2 + 2 * ‖v (t + a) x - v t x‖ ^ 2) :=
      ((hInnerB1 t).const_mul 2).add ((hInnerB2 t).const_mul 2)
    have hmono := integral_mono (hInnerA t) hsum hpt
    rwa [integral_add ((hInnerB1 t).const_mul 2) ((hInnerB2 t).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  -- (2) outer monotonicity on the working window
  have houter : (∫ t in Set.Ioc c T, ∫ x : Space, ‖v (t + a) (x + y) - v t x‖ ^ 2)
      ≤ 2 * (∫ t in Set.Ioc c T, ∫ x : Space, ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2)
        + 2 * ∫ t in Set.Ioc c T, ∫ x : Space, ‖v (t + a) x - v t x‖ ^ 2 := by
    have hsum2 : IntegrableOn (fun t : ℝ =>
        2 * (∫ x : Space, ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2)
          + 2 * ∫ x : Space, ‖v (t + a) x - v t x‖ ^ 2) (Set.Ioc c T) :=
      (hOutB1.const_mul 2).add (hOutB2.const_mul 2)
    have hmono := integral_mono hOutA hsum2 (fun t => hinner t)
    rwa [integral_add (hOutB1.const_mul 2) (hOutB2.const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  -- (3) the space leg: translate the time variable, then enlarge the time window
  have hleg1 : (∫ t in Set.Ioc c T, ∫ x : Space, ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2) ≤ ε₁ := by
    have htrans : (∫ t in Set.Ioc c T, ∫ x : Space, ‖v (t + a) (x + y) - v (t + a) x‖ ^ 2)
        = ∫ s in Set.Ioc (c + a) (T + a), ∫ x : Space, ‖v s (x + y) - v s x‖ ^ 2 := by
      rw [← intervalIntegral.integral_of_le hcT, ← intervalIntegral.integral_of_le (by linarith)]
      exact intervalIntegral.integral_comp_add_right
        (fun s => ∫ x : Space, ‖v s (x + y) - v s x‖ ^ 2) a
    rw [htrans]
    refine le_trans (setIntegral_mono_set hOutS
      (Filter.Eventually.of_forall fun s => integral_nonneg fun x => by positivity)
      (HasSubset.Subset.eventuallyLE ?_)) hS
    exact Set.Ioc_subset_Ioc (by linarith) (by linarith)
  -- (4) the time leg: just enlarge the time window
  have hleg2 : (∫ t in Set.Ioc c T, ∫ x : Space, ‖v (t + a) x - v t x‖ ^ 2) ≤ ε₂ := by
    refine le_trans (setIntegral_mono_set hOutT
      (Filter.Eventually.of_forall fun s => integral_nonneg fun x => by positivity)
      (HasSubset.Subset.eventuallyLE ?_)) hT
    exact Set.Ioc_subset_Ioc hc0 le_rfl
  linarith

/-- **(i) in product form** — the exact `hmod` hypothesis of
`sum_cellError_le_modulus_of_memL2`, obtained from `nested_window_modulus` through the
bridge.  The shift `k : ℝ × Space` has product (sup) norm, so `‖k‖ ≤ h` gives both
`|k.1| ≤ h` and `‖k.2‖ ≤ h`, which is precisely what the two legs need. -/
private theorem prod_window_modulus
    (v : VelocityEvolution) (k : ℝ × Space) (c T h ε₁ ε₂ : ℝ)
    (hcT : c ≤ T) (hh : 0 < h) (hhc : h ≤ c) (hk : ‖k‖ ≤ h)
    (hvmeas : Measurable fun z : ℝ × Space => v z.1 z.2)
    (hInnerA : ∀ t : ℝ, Integrable fun x : Space => ‖v (t + k.1) (x + k.2) - v t x‖ ^ 2)
    (hInnerB1 : ∀ t : ℝ,
      Integrable fun x : Space => ‖v (t + k.1) (x + k.2) - v (t + k.1) x‖ ^ 2)
    (hInnerB2 : ∀ t : ℝ, Integrable fun x : Space => ‖v (t + k.1) x - v t x‖ ^ 2)
    (hOutA : IntegrableOn
      (fun t : ℝ => ∫ x : Space, ‖v (t + k.1) (x + k.2) - v t x‖ ^ 2) (Set.Ioc c T))
    (hOutB1 : IntegrableOn
      (fun t : ℝ => ∫ x : Space, ‖v (t + k.1) (x + k.2) - v (t + k.1) x‖ ^ 2) (Set.Ioc c T))
    (hOutB2 : IntegrableOn
      (fun t : ℝ => ∫ x : Space, ‖v (t + k.1) x - v t x‖ ^ 2) (Set.Ioc c T))
    (hOutS : IntegrableOn
      (fun s : ℝ => ∫ x : Space, ‖v s (x + k.2) - v s x‖ ^ 2) (Set.Ioc (0:ℝ) (T + h)))
    (hOutT : IntegrableOn
      (fun t : ℝ => ∫ x : Space, ‖v (t + k.1) x - v t x‖ ^ 2) (Set.Ioc (0:ℝ) T))
    (hS : (∫ s in Set.Ioc (0:ℝ) (T + h), ∫ x : Space, ‖v s (x + k.2) - v s x‖ ^ 2) ≤ ε₁)
    (hT : (∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖v (t + k.1) x - v t x‖ ^ 2) ≤ ε₂) :
    (∫ z in Set.Ioc c T ×ˢ (univ : Set Space),
        ‖v (z + k).1 (z + k).2 - v z.1 z.2‖ ^ 2 ∂(volume.prod volume))
      ≤ 2 * ε₁ + 2 * ε₂ := by
  have hka : |k.1| ≤ h := by
    refine le_trans ?_ hk
    simp [Prod.norm_def, Real.norm_eq_abs]
  have hky : ‖k.2‖ ≤ h := by
    refine le_trans ?_ hk
    simp [Prod.norm_def, Real.norm_eq_abs]
  have hFmeas : Measurable fun z : ℝ × Space => ‖v (z + k).1 (z + k).2 - v z.1 z.2‖ ^ 2 :=
    (((hvmeas.comp (measurable_id.add_const k)).sub hvmeas).norm).pow_const 2
  have hbridge := setIntegral_prod_univ_eq_nested
    (fun z : ℝ × Space => ‖v (z + k).1 (z + k).2 - v z.1 z.2‖ ^ 2) hFmeas
    (Set.Ioc c T) measurableSet_Ioc (fun z => by positivity)
    (fun t => hInnerA t) hOutA
  rw [hbridge]
  exact nested_window_modulus v k.1 k.2 c T h ε₁ ε₂ hcT hh hhc hka
    hInnerA hInnerB1 hInnerB2 hOutA hOutB1 hOutB2 hOutS hOutT hS hT

/-- **The middle step, in the form the Leray bundle can actually feed.**  Summing the
per-cell oscillation bound over a finite family of spacetime cells of side `h`, with
the `L^∞` hypothesis of `RieszKolmogorov.sum_cellError_le_modulus` replaced by
square-integrability on an enlarged window `W`, and with the disjointness step
localized to `W` rather than to all of `ℝ × ℝ³`.

Both replacements are forced, not cosmetic.  A Leray field is **not** uniformly
bounded, so the `∀ z, ‖f z‖ ≤ M` hypothesis is not dischargeable from
`UniformKineticBound`; and `VelocityEvolution` is uncontrolled for `t < 0`, so
`∀ k, Integrable fun x => ‖f (x + k) − f x‖²` over the whole spacetime is not
dischargeable either.  The two upstream lemmas that make the swap possible are
`RieszKolmogorov.setIntegral_cellError_le_displacement_of_memL2` (per cell) and
`RieszKolmogorov.sum_finset_setIntegral_le_setIntegral_of_disjoint` (disjointness on
a window); both are certified there.

The constant is the same `ν(B_h)/h^{d}` as in the bounded case — for the sup-norm ball
in `ℝ × ℝ³` this is `(2h)⁴/h⁴ = 2⁴`, independent of `h`, which is what lets `h → 0`
drive the cell error to zero uniformly over an equicontinuous family.

Truth-checked before formalization at `experiments/riesz_kolmogorov_cell_sum_toy.py`:
in `d = 1` on an off-grid step function (so the cell error is nonzero), at four dyadic
scales and two grid resolutions, both `∑_cells ≤ h^{-d}∫_{|k|≤h}` and
`h^{-d}∫_{|k|≤h} ≤ 2^d·sup_{|k|≤h}` hold with slack, and the left side tends to `0`
as `h → 0`. -/
private theorem sum_cellError_le_modulus_of_memL2
    {h : ℝ} (hh : 0 < h) (S : Finset (ℤ × (Fin 3 → ℤ)))
    (f : ℝ × Space → Space) (hmeas : Measurable f)
    (W : Set (ℝ × Space)) (_hWm : MeasurableSet W)
    (hcellW : ∀ p ∈ S, prodGridCell h p.1 p.2 ⊆ W)
    (hcellWB : ∀ p ∈ S, ∀ x ∈ prodGridCell h p.1 p.2,
      ∀ k ∈ Metric.closedBall (0 : ℝ × Space) h, x + k ∈ W)
    (hL2 : IntegrableOn (fun z => ‖f z‖ ^ 2) W)
    (Mmod : ℝ)
    (hmod : ∀ k ∈ Metric.closedBall (0 : ℝ × Space) h,
      (∫ x in W, ‖f (x + k) - f x‖ ^ 2) ≤ Mmod)
    (hglobW : ∀ k, IntegrableOn (fun x => ‖f (x + k) - f x‖ ^ 2) W)
    (hFp : ∀ p ∈ S, IntegrableOn
      (fun k => ∫ x in prodGridCell h p.1 p.2, ‖f (x + k) - f x‖ ^ 2)
      (Metric.closedBall (0 : ℝ × Space) h))
    (hG : IntegrableOn (fun k => ∫ x in W, ‖f (x + k) - f x‖ ^ 2)
      (Metric.closedBall (0 : ℝ × Space) h)) :
    ∑ p ∈ S, (∫ x in prodGridCell h p.1 p.2,
        ‖f x - ⨍ y in prodGridCell h p.1 p.2, f y‖ ^ 2)
      ≤ (h ^ 4)⁻¹ * (volume.real (Metric.closedBall (0 : ℝ × Space) h) * Mmod) := by
  classical
  haveI : (volume : Measure (ℝ × Space)).IsAddLeftInvariant := by
    rw [MeasureTheory.Measure.volume_eq_prod]; infer_instance
  set B := Metric.closedBall (0 : ℝ × Space) h with hBdef
  have hdpos : (0:ℝ) < h ^ 4 := by positivity
  have hvolcell : ∀ p : ℤ × (Fin 3 → ℤ), volume (prodGridCell h p.1 p.2)
      = ENNReal.ofReal (h ^ 4) := by
    intro p
    have := volume_prodGridCell (ι := Fin 3) hh.le p.1 p.2
    simpa using this
  have hne : ∀ p : ℤ × (Fin 3 → ℤ), volume (prodGridCell h p.1 p.2) ≠ 0 := by
    intro p; rw [hvolcell p, Ne, ENNReal.ofReal_eq_zero]; exact not_le.mpr hdpos
  have hfin : ∀ p : ℤ × (Fin 3 → ℤ), volume (prodGridCell h p.1 p.2) ≠ ⊤ := by
    intro p; rw [hvolcell p]; exact ENNReal.ofReal_ne_top
  have hreal : ∀ p : ℤ × (Fin 3 → ℤ), volume.real (prodGridCell h p.1 p.2) = h ^ 4 := by
    intro p; rw [Measure.real, hvolcell p, ENNReal.toReal_ofReal hdpos.le]
  have hBfin : volume B ≠ ⊤ := measure_closedBall_lt_top.ne
  have hcell : ∀ p ∈ S, (∫ x in prodGridCell h p.1 p.2,
      ‖f x - ⨍ y in prodGridCell h p.1 p.2, f y‖ ^ 2)
      ≤ (h ^ 4)⁻¹ * ∫ k in B, (∫ x in prodGridCell h p.1 p.2,
          ‖f (x + k) - f x‖ ^ 2) := by
    intro p hp
    have hres := setIntegral_cellError_le_displacement_of_memL2
      (prodGridCell h p.1 p.2) W (measurableSet_prodGridCell h p.1 p.2) _hWm h f hmeas
      (hne p) (hfin p) hBfin (hcellW p hp) (hcellWB p hp) hL2
      (fun x hx y hy => norm_sub_le_of_mem_prodGridCell hh.le hy hx)
    rwa [hreal p] at hres
  calc ∑ p ∈ S, (∫ x in prodGridCell h p.1 p.2,
          ‖f x - ⨍ y in prodGridCell h p.1 p.2, f y‖ ^ 2)
      ≤ ∑ p ∈ S, (h ^ 4)⁻¹ * ∫ k in B, (∫ x in prodGridCell h p.1 p.2,
          ‖f (x + k) - f x‖ ^ 2) := Finset.sum_le_sum hcell
    _ = (h ^ 4)⁻¹ * ∑ p ∈ S, ∫ k in B, (∫ x in prodGridCell h p.1 p.2,
          ‖f (x + k) - f x‖ ^ 2) := by rw [← Finset.mul_sum]
    _ = (h ^ 4)⁻¹ * ∫ k in B, (∑ p ∈ S, ∫ x in prodGridCell h p.1 p.2,
          ‖f (x + k) - f x‖ ^ 2) := by
        rw [MeasureTheory.integral_finsetSum S hFp]
    _ ≤ (h ^ 4)⁻¹ * ∫ k in B, (∫ x in W, ‖f (x + k) - f x‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine setIntegral_mono_on (integrable_finsetSum S hFp) hG
          measurableSet_closedBall fun k _ => ?_
        exact sum_finset_setIntegral_le_setIntegral_of_disjoint S
          (fun p => prodGridCell h p.1 p.2) W hcellW
          (fun p => measurableSet_prodGridCell h p.1 p.2)
          (fun p q hpq => prodGridCell_disjoint hh (by simpa [Prod.ext_iff] using hpq))
          _ (fun x => by positivity) (hglobW k)
    _ ≤ (h ^ 4)⁻¹ * (volume.real B * Mmod) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact setIntegral_le_measureReal_mul_const measurableSet_closedBall hBfin
          _ Mmod (fun k hk => hmod k hk) hG

/-!
### The forward extension layer for the window criterion (certified)

`exists_subseq_windowCauchy` is run on the *forward extension*
`fwd uSeq m t x := uSeq m (max t 0) x` of the sequence, per repair (b) of the
residual plan below: `hint`/`hkin` hold only for `t ≥ 0`, while
`nested_window_modulus` quantifies its integrability hypotheses over all `t : ℝ`.
This section certifies that the forward extension preserves every hypothesis of
the criterion — slicewise square-integrability and the kinetic bound `C` now at
*every* `t` (`fwd_int`, `fwd_kin`), joint measurability (`fwd_meas`),
space-equicontinuity verbatim (`fwd_space`), and time-equicontinuity with an
extra `4C|h|` slab on `(0, |h|)` absorbed by shrinking `δ` (`fwd_time`) — and
that `windowError` is unchanged by the extension (`windowError_fwd`), so the
criterion's conclusion transfers back verbatim.  The displacement
integrability/bound lemmas (`fwd_disp2_*`, `fwd_tdisp_*`) are the slicewise
side conditions the modulus lemmas consume.
-/

noncomputable def fwd (uSeq : ℕ → VelocityEvolution) (m : ℕ) : VelocityEvolution :=
  fun t x => uSeq m (max t 0) x

theorem fwd_kin (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C) (m : ℕ) (t : ℝ) :
    (∫ x : Space, ‖fwd uSeq m t x‖ ^ 2) ≤ C := by
  unfold fwd
  exact hkin m (max t 0) (le_max_right t 0)

theorem fwd_int (uSeq : ℕ → VelocityEvolution)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (m : ℕ) (t : ℝ) : Integrable (fun x : Space => ‖fwd uSeq m t x‖ ^ 2) := by
  unfold fwd
  exact hint m (max t 0) (le_max_right t 0)

theorem fwd_meas (uSeq : ℕ → VelocityEvolution) (hmeas : JointlyMeasurable uSeq) (m : ℕ) :
    Measurable (fun z : ℝ × Space => fwd uSeq m z.1 z.2) := by
  show Measurable ((fun z : ℝ × Space => uSeq m z.1 z.2) ∘ (fun z : ℝ × Space => (max z.1 0, z.2)))
  exact (hmeas m).comp
    ((continuous_fst.max continuous_const).measurable.prodMk measurable_snd)

theorem sq_norm_sub_le_two {E : Type*} [NormedAddCommGroup E] (a b : E) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b,
    mul_self_le_mul_self (norm_nonneg (a - b)) h]

/-- generic: a measurable nonnegative function bounded by `M` is integrable on any
finite-interval window. -/
theorem integrableOn_Ioc_of_le {F : ℝ → ℝ} (hFm : Measurable F) (a b M : ℝ)
    (hnn : ∀ t, 0 ≤ F t) (hM : ∀ t, F t ≤ M) :
    IntegrableOn F (Set.Ioc a b) := by
  have hb : IntegrableOn (fun _ : ℝ => M) (Set.Ioc a b) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  refine hb.mono' hFm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t)]; exact hM t

/-- inner-integral measurability via Tonelli -/
theorem inner_sq_measurable {G : ℝ × Space → ℝ} (hG : Measurable G)
    (hnn : ∀ z, 0 ≤ G z) (hGi : ∀ t : ℝ, Integrable (fun x : Space => G (t, x))) :
    Measurable (fun t : ℝ => ∫ x : Space, G (t, x)) := by
  have hG' : Measurable (fun z : ℝ × Space => ENNReal.ofReal (G z)) := hG.ennreal_ofReal
  have hlint : Measurable (fun t : ℝ => ∫⁻ x : Space, ENNReal.ofReal (G (t, x))) := by
    exact Measurable.lintegral_prod_right
      (ν := volume) (f := fun (t : ℝ) (x : Space) => ENNReal.ofReal (G (t, x))) hG'
  have heq : (fun t : ℝ => ∫ x : Space, G (t, x))
      = fun t : ℝ => (∫⁻ x : Space, ENNReal.ofReal (G (t, x))).toReal := by
    funext t
    rw [← ofReal_integral_eq_lintegral_ofReal (hGi t)
        (Filter.Eventually.of_forall fun x => hnn (t, x)),
      ENNReal.toReal_ofReal (integral_nonneg fun x => hnn (t, x))]
  rw [heq]
  exact hlint.ennreal_toReal

/-- joint measurability of a two-term displacement of `fwd`. -/
theorem fwd_disp2_meas (uSeq : ℕ → VelocityEvolution) (hmeas : JointlyMeasurable uSeq)
    (m : ℕ) (a₁ a₂ : ℝ) (w₁ w₂ : Space) :
    Measurable (fun z : ℝ × Space =>
      ‖fwd uSeq m (z.1 + a₁) (z.2 + w₁) - fwd uSeq m (z.1 + a₂) (z.2 + w₂)‖ ^ 2) := by
  have h1 : Measurable (fun z : ℝ × Space => fwd uSeq m (z.1 + a₁) (z.2 + w₁)) :=
    (fwd_meas uSeq hmeas m).comp
      ((measurable_fst.add_const a₁).prodMk (measurable_snd.add_const w₁))
  have h2 : Measurable (fun z : ℝ × Space => fwd uSeq m (z.1 + a₂) (z.2 + w₂)) :=
    (fwd_meas uSeq hmeas m).comp
      ((measurable_fst.add_const a₂).prodMk (measurable_snd.add_const w₂))
  exact (h1.sub h2).norm.pow_const 2

/-- slicewise integrability of a two-term displacement of `fwd`. -/
theorem fwd_disp2_int (uSeq : ℕ → VelocityEvolution)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq)
    (m : ℕ) (t₁ t₂ : ℝ) (w₁ w₂ : Space) :
    Integrable (fun x : Space =>
      ‖fwd uSeq m t₁ (x + w₁) - fwd uSeq m t₂ (x + w₂)‖ ^ 2) := by
  haveI : (volume : Measure Space).IsAddRightInvariant := by infer_instance
  have h1 : Integrable (fun x : Space => ‖fwd uSeq m t₁ (x + w₁)‖ ^ 2) :=
    (fwd_int uSeq hint m t₁).comp_add_right w₁
  have h2 : Integrable (fun x : Space => ‖fwd uSeq m t₂ (x + w₂)‖ ^ 2) :=
    (fwd_int uSeq hint m t₂).comp_add_right w₂
  refine ((h1.const_mul 2).add (h2.const_mul 2)).mono' ?_ ?_
  · have hm1 : Measurable (fun x : Space => fwd uSeq m t₁ (x + w₁)) :=
      (fwd_meas uSeq hmeas m).comp (measurable_const.prodMk (measurable_id.add_const w₁))
    have hm2 : Measurable (fun x : Space => fwd uSeq m t₂ (x + w₂)) :=
      (fwd_meas uSeq hmeas m).comp (measurable_const.prodMk (measurable_id.add_const w₂))
    exact ((hm1.sub hm2).norm.pow_const 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact sq_norm_sub_le_two _ _



theorem fwd_disp2_inner_le (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq)
    (m : ℕ) (t₁ t₂ : ℝ) (w₁ w₂ : Space) :
    (∫ x : Space, ‖fwd uSeq m t₁ (x + w₁) - fwd uSeq m t₂ (x + w₂)‖ ^ 2) ≤ 4 * C := by
  haveI : (volume : Measure Space).IsAddRightInvariant := inferInstance
  have h1 : (∫ x : Space, ‖fwd uSeq m t₁ (x + w₁)‖ ^ 2) ≤ C := by
    show (∫ x : Space, (fun x : Space => ‖fwd uSeq m t₁ x‖ ^ 2) (x + w₁)) ≤ C
    rw [integral_add_right_eq_self (μ := volume) (fun x : Space => ‖fwd uSeq m t₁ x‖ ^ 2) w₁]
    exact fwd_kin uSeq C hkin m t₁
  have h2 : (∫ x : Space, ‖fwd uSeq m t₂ (x + w₂)‖ ^ 2) ≤ C := by
    show (∫ x : Space, (fun x : Space => ‖fwd uSeq m t₂ x‖ ^ 2) (x + w₂)) ≤ C
    rw [integral_add_right_eq_self (μ := volume) (fun x : Space => ‖fwd uSeq m t₂ x‖ ^ 2) w₂]
    exact fwd_kin uSeq C hkin m t₂
  have hi1 : Integrable (fun x : Space => ‖fwd uSeq m t₁ (x + w₁)‖ ^ 2) :=
    (fwd_int uSeq hint m t₁).comp_add_right w₁
  have hi2 : Integrable (fun x : Space => ‖fwd uSeq m t₂ (x + w₂)‖ ^ 2) :=
    (fwd_int uSeq hint m t₂).comp_add_right w₂
  have hmono := integral_mono (fwd_disp2_int uSeq hint hmeas m t₁ t₂ w₁ w₂)
    ((hi1.const_mul 2).add (hi2.const_mul 2)) (fun x => sq_norm_sub_le_two _ _)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
  nlinarith [hmono, h1, h2]

theorem fwd_disp2_outer (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq)
    (m : ℕ) (a₁ a₂ : ℝ) (w₁ w₂ : Space) (p q : ℝ) :
    IntegrableOn (fun t : ℝ => ∫ x : Space,
      ‖fwd uSeq m (t + a₁) (x + w₁) - fwd uSeq m (t + a₂) (x + w₂)‖ ^ 2) (Set.Ioc p q) := by
  refine integrableOn_Ioc_of_le ?_ p q (4 * C)
    (fun t => integral_nonneg fun x => by positivity)
    (fun t => fwd_disp2_inner_le uSeq C hkin hint hmeas m (t + a₁) (t + a₂) w₁ w₂)
  have hG : Measurable (fun z : ℝ × Space =>
      ‖fwd uSeq m (z.1 + a₁) (z.2 + w₁) - fwd uSeq m (z.1 + a₂) (z.2 + w₂)‖ ^ 2) :=
    fwd_disp2_meas uSeq hmeas m a₁ a₂ w₁ w₂
  exact inner_sq_measurable hG (fun z => by positivity)
    (fun t => fwd_disp2_int uSeq hint hmeas m (t + a₁) (t + a₂) w₁ w₂)

/-- plain inner integral is measurable and bounded by `C` -/
theorem fwd_inner_measurable (uSeq : ℕ → VelocityEvolution)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) :
    Measurable (fun t : ℝ => ∫ x : Space, ‖fwd uSeq m t x‖ ^ 2) := by
  have hG : Measurable (fun z : ℝ × Space => ‖fwd uSeq m z.1 z.2‖ ^ 2) :=
    (fwd_meas uSeq hmeas m).norm.pow_const 2
  exact inner_sq_measurable hG (fun z => by positivity) (fun t => fwd_int uSeq hint m t)

theorem fwd_inner_integrableOn (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (p q : ℝ) :
    IntegrableOn (fun t : ℝ => ∫ x : Space, ‖fwd uSeq m t x‖ ^ 2) (Set.Ioc p q) := by
  refine integrableOn_Ioc_of_le (fwd_inner_measurable uSeq hint hmeas m) p q C
    (fun t => integral_nonneg fun x => by positivity) (fun t => ?_)
  exact fwd_kin uSeq C hkin m t



/-- time-only displacement: slicewise integrability -/
theorem fwd_tdisp_int (uSeq : ℕ → VelocityEvolution)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (h t : ℝ) :
    Integrable (fun x : Space => ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2) := by
  have h2 := fwd_disp2_int uSeq hint hmeas m (t + h) t 0 0
  simpa [add_zero] using h2

/-- time-only displacement: `4C` bound on the inner integral -/
theorem fwd_tdisp_le (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (h t : ℝ) :
    (∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2) ≤ 4 * C := by
  have h2 := fwd_disp2_inner_le uSeq C hkin hint hmeas m (t + h) t 0 0
  rwa [show (∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2)
      = ∫ x : Space, ‖fwd uSeq m (t + h) (x + 0) - fwd uSeq m t (x + 0)‖ ^ 2 from
    by simp [add_zero]]

/-- time-only displacement: outer integrability on any finite window -/
theorem fwd_tdisp_outer (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (h p q : ℝ) :
    IntegrableOn (fun t : ℝ => ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2)
      (Set.Ioc p q) := by
  refine (fwd_disp2_outer uSeq C hkin hint hmeas m h 0 0 0 p q).congr_fun
    (fun t _ => ?_) measurableSet_Ioc
  simp [add_zero]

/-- windowError transfer: on `(0,n]`, `max t 0 = t`. -/
theorem windowError_fwd (uSeq : ℕ → VelocityEvolution) (a b : ℕ) (n : ℕ) :
    windowError (fwd uSeq a) (fwd uSeq b) n = windowError (uSeq a) (uSeq b) n := by
  unfold windowError
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht0 : 0 ≤ t := le_of_lt ht.1
  simp only [fwd, max_eq_left ht0]

/-- SpaceEquicontinuous transfers verbatim. -/
theorem fwd_space (uSeq : ℕ → VelocityEvolution) (hspace : SpaceEquicontinuous uSeq) :
    SpaceEquicontinuous (fwd uSeq) := by
  intro T ε hε
  obtain ⟨δ, hδ, hh⟩ := hspace T ε hε
  refine ⟨δ, hδ, fun m y hy => ?_⟩
  have h2 := hh m y hy
  rwa [show (∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖fwd uSeq m t (x + y) - fwd uSeq m t x‖ ^ 2)
      = ∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖uSeq m t (x + y) - uSeq m t x‖ ^ 2 from ?_]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp only [fwd, max_eq_left (le_of_lt ht.1)]

/-- **TimeEquicontinuous survives forward extension**, with an extra `4C|h|`
slab on `(0, |h|)` absorbed by shrinking `δ`. -/
theorem fwd_time (uSeq : ℕ → VelocityEvolution) (C : ℝ) (hC : 0 ≤ C)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq)
    (htime : TimeEquicontinuous uSeq) :
    TimeEquicontinuous (fwd uSeq) := by
  intro T ε hε
  by_cases hT0 : T ≤ 0
  · exact ⟨1, one_pos, fun m h _ => by
      rw [Set.Ioc_eq_empty (by simpa using hT0), setIntegral_empty]; exact hε.le⟩
  have hT : 0 < T := lt_of_not_ge hT0
  obtain ⟨δ₀, hδ₀, hδ₀b⟩ := htime T (ε / 2) (half_pos hε)
  have hC8 : (0:ℝ) < 8 * C + 1 := by nlinarith [hC]
  refine ⟨min δ₀ (ε / (8 * C + 1)), lt_min hδ₀ (by positivity), fun m h hh => ?_⟩
  have hhδ₀ : |h| < δ₀ := lt_of_lt_of_le hh (min_le_left _ _)
  have hhε : |h| < ε / (8 * C + 1) := lt_of_lt_of_le hh (min_le_right _ _)
  by_cases hh0 : 0 ≤ h
  · -- case A: `0 ≤ h`, everything reduces to `uSeq` directly
    have heq : (∫ t in Set.Ioc (0:ℝ) T,
        ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2)
        = ∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, ‖uSeq m (t + h) x - uSeq m t x‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have hth : 0 ≤ t + h := le_trans ht0 (by linarith)
      simp only [fwd, max_eq_left ht0, max_eq_left hth]
    rw [heq]
    exact le_trans (hδ₀b m h hhδ₀) (half_le_self hε.le)
  · -- case B: `h < 0`; split at `c = min T (-h)`
    have hh0' : h < 0 := lt_of_not_ge hh0
    have hneg : 0 < -h := neg_pos.mpr hh0' 
    set c := min T (-h) with hcdef
    have h0c : 0 ≤ c := le_min hT.le hneg.le
    have hcT : c ≤ T := min_le_left _ _
    have hch : c ≤ -h := min_le_right _ _
    have hunion : Set.Ioc (0:ℝ) c ∪ Set.Ioc c T = Set.Ioc (0:ℝ) T :=
      Set.Ioc_union_Ioc_eq_Ioc h0c hcT
    have hdisj : Disjoint (Set.Ioc (0:ℝ) c) (Set.Ioc c T) := by
      rw [Set.Ioc_disjoint_Ioc]
      exact le_trans (min_le_left _ _) (le_max_right _ _)
    have hsplit : (∫ t in Set.Ioc (0:ℝ) T,
        ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2)
        = (∫ t in Set.Ioc (0:ℝ) c,
            ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2)
          + ∫ t in Set.Ioc c T,
            ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2 := by
      rw [← hunion, setIntegral_union hdisj measurableSet_Ioc
        (fwd_tdisp_outer uSeq C hkin hint hmeas m h 0 c)
        (fwd_tdisp_outer uSeq C hkin hint hmeas m h c T)]
    rw [hsplit]
    -- slab leg
    have hleg1 : (∫ t in Set.Ioc (0:ℝ) c,
        ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2) ≤ 4 * C * (-h) := by
      calc _ ≤ ∫ _ in Set.Ioc (0:ℝ) c, (4 * C) :=
            setIntegral_mono_on (fwd_tdisp_outer uSeq C hkin hint hmeas m h 0 c)
              (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc
              (fun t _ => fwd_tdisp_le uSeq C hkin hint hmeas m h t)
        _ = (volume.real (Set.Ioc (0:ℝ) c)) * (4 * C) := by
            rw [setIntegral_const]; simp [smul_eq_mul]
        _ = c * (4 * C) := by
            rw [show volume.real (Set.Ioc (0:ℝ) c) = c from by
              rw [Measure.real, Real.volume_Ioc,
                ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ c - 0), sub_zero]]
        _ ≤ (-h) * (4 * C) := by
            apply mul_le_mul_of_nonneg_right hch (by nlinarith [hC])
        _ = 4 * C * (-h) := by ring
    -- main leg
    have hleg2 : (∫ t in Set.Ioc c T,
        ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2) ≤ ε / 2 := by
      by_cases hTh : T ≤ -h
      · rw [hcdef, min_eq_left hTh, Set.Ioc_self, setIntegral_empty]
        exact (half_pos hε).le
      · push_neg at hTh
        rw [hcdef, min_eq_right hTh.le]
        -- substitute `s = t + h`
        have hsub : (∫ t in Set.Ioc (-h) T,
            ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2)
            = ∫ s in Set.Ioc (0:ℝ) (T + h),
              ∫ x : Space, ‖fwd uSeq m s x - fwd uSeq m (s + -h) x‖ ^ 2 := by
          rw [← intervalIntegral.integral_of_le hTh.le,
            ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ T + h)]
          have key := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := T + h)
            (fun t => ∫ x : Space, ‖fwd uSeq m (t + h) x - fwd uSeq m t x‖ ^ 2) (-h)
          rw [show (0:ℝ) + -h = -h from by ring, show T + h + -h = T from by ring] at key
          rw [← key]
          apply intervalIntegral.integral_congr
          intro t _
          have hrw : t + -h + h = t := by ring
          simp only [hrw]
        rw [hsub]
        -- identify with the `uSeq` modulus on `(0, T+h]`
        have hident : (∫ s in Set.Ioc (0:ℝ) (T + h),
            ∫ x : Space, ‖fwd uSeq m s x - fwd uSeq m (s + -h) x‖ ^ 2)
            = ∫ s in Set.Ioc (0:ℝ) (T + h),
              ∫ x : Space, ‖uSeq m (s + -h) x - uSeq m s x‖ ^ 2 := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          have hs0 : 0 ≤ s := le_of_lt hs.1
          have hsh : 0 ≤ s + -h := by linarith [hs.1, hneg]
          simp only [fwd, max_eq_left hs0, max_eq_left hsh, norm_sub_rev]
        rw [hident]
        -- enlarge the window to `(0, T]` and apply `htime`
        have hmono : (∫ s in Set.Ioc (0:ℝ) (T + h),
            ∫ x : Space, ‖uSeq m (s + -h) x - uSeq m s x‖ ^ 2)
            ≤ ∫ s in Set.Ioc (0:ℝ) T,
              ∫ x : Space, ‖uSeq m (s + -h) x - uSeq m s x‖ ^ 2 := by
          apply setIntegral_mono_set
          · -- integrability on the big window, via the fwd version
            have hfi := fwd_tdisp_outer uSeq C hkin hint hmeas m (-h) 0 T
            refine hfi.congr_fun (fun s hs => ?_) measurableSet_Ioc
            have hs0 : 0 ≤ s := le_of_lt hs.1
            have hsh : 0 ≤ s + -h := by linarith [hs.1, hneg]
            simp only [fwd, max_eq_left hs0, max_eq_left hsh]
          · exact Filter.Eventually.of_forall fun s =>
              integral_nonneg fun x => by positivity
          · exact HasSubset.Subset.eventuallyLE
              (Set.Ioc_subset_Ioc le_rfl (by linarith))
        exact le_trans hmono (hδ₀b m (-h) (by rwa [abs_neg]))
    -- close: `4C|h| + ε/2 ≤ ε`
    have hbound : 4 * C * (-h) ≤ ε / 2 := by
      have habs : -h = |h| := (abs_of_neg hh0').symm
      rw [habs]
      have h1 : 4 * C * |h| ≤ 4 * C * (ε / (8 * C + 1)) :=
        mul_le_mul_of_nonneg_left hhε.le (by nlinarith [hC])
      have h2 : 4 * C * (ε / (8 * C + 1)) ≤ ε / 2 := by
        rw [← mul_div_assoc, div_le_iff₀ hC8]
        nlinarith [hC, hε.le]
      linarith
    linarith [hleg1, hleg2, hbound]

/-!
### Window compactness: the cell family, the enclosure, and the modulus

Infrastructure for `exists_subseq_windowCauchy`.  `fwdFn` packages the forward
extension as a single spacetime function; `winCellFinset` is the finite family
of side-`h` spacetime cells meeting the window `Q_n`; `encW` is the enlarged
enclosure `(−2h, n+2h] × B̄(0, n+2h)` containing each such cell together with
all its `‖k‖ ≤ h` translates; `fwd_modulus_encW` is the uniform translation
modulus on `encW` (kinetic collar on `(−2h, h]` plus `nested_window_modulus` at
`c = h`); `fwd_cellError_sum_le` instantiates
`sum_cellError_le_modulus_of_memL2`; `cellStep` is the cell-average step
function of the ε/3 assembly; `windowError_le_three_legs` is the assembled
comparison; and `exists_subseq_cauchy_of_bounded_finiteDim` is
Bolzano–Weierstrass for the cell-average vector.
-/

/-- The forward extension, as a single spacetime function. -/
private def fwdFn (uSeq : ℕ → VelocityEvolution) (m : ℕ) : ℝ × Space → Space :=
  fun z => fwd uSeq m z.1 z.2

private theorem fwdFn_meas (uSeq : ℕ → VelocityEvolution)
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) : Measurable (fwdFn uSeq m) :=
  fwd_meas uSeq hmeas m

/-- The enlarged enclosure `(−2h, n+2h] × B̄(0, n+2h)`. -/
private def encW (n : ℕ) (h : ℝ) : Set (ℝ × Space) :=
  Set.Ioc (-(2*h)) ((n:ℝ) + 2*h) ×ˢ Metric.closedBall (0 : Space) ((n:ℝ) + 2*h)

private theorem measurableSet_encW (n : ℕ) (h : ℝ) : MeasurableSet (encW n h) := by
  rw [encW]; exact measurableSet_Ioc.prod measurableSet_closedBall

private theorem measurableSet_winQ (n : ℕ) : MeasurableSet (winQ n) := by
  rw [winQ]; exact measurableSet_Ioc.prod measurableSet_closedBall

private theorem volume_winQ_ne_top (n : ℕ) : volume (winQ n) ≠ ⊤ := by
  rw [winQ, Measure.volume_eq_prod, Measure.prod_prod]
  exact (ENNReal.mul_lt_top measure_Ioc_lt_top measure_closedBall_lt_top).ne

/-- Spacetime cell volume in the `3+1`-dimensional instantiation. -/
private theorem volume_cell {h : ℝ} (hh : 0 ≤ h) (p : ℤ × (Fin 3 → ℤ)) :
    volume (prodGridCell h p.1 p.2) = ENNReal.ofReal (h ^ 4) := by
  simpa using volume_prodGridCell (ι := Fin 3) hh p.1 p.2

private theorem volume_cell_ne_zero {h : ℝ} (hh : 0 < h) (p : ℤ × (Fin 3 → ℤ)) :
    volume (prodGridCell h p.1 p.2) ≠ 0 := by
  rw [volume_cell hh.le p, Ne, ENNReal.ofReal_eq_zero]
  exact not_le.mpr (by positivity)

private theorem volume_cell_ne_top {h : ℝ} (hh : 0 < h) (p : ℤ × (Fin 3 → ℤ)) :
    volume (prodGridCell h p.1 p.2) ≠ ⊤ := by
  rw [volume_cell hh.le p]; exact ENNReal.ofReal_ne_top

private theorem volume_real_cell {h : ℝ} (hh : 0 < h) (p : ℤ × (Fin 3 → ℤ)) :
    volume.real (prodGridCell h p.1 p.2) = h ^ 4 := by
  rw [Measure.real, volume_cell hh.le p, ENNReal.toReal_ofReal (by positivity)]

/-- The indices of the side-`h` spacetime cells meeting the window `Q_n`. -/
private def winCells (n : ℕ) (h : ℝ) : Set (ℤ × (Fin 3 → ℤ)) :=
  {p | (prodGridCell h p.1 p.2 ∩ winQ n).Nonempty}

private theorem winCells_finite {h : ℝ} (hh : 0 < h) (n : ℕ) : (winCells n h).Finite := by
  refine (finite_prodGridIndices hh (n:ℝ)).subset ?_
  rintro ⟨m, j⟩ ⟨z, hzc, hzQ⟩
  refine ⟨z, hzc, ?_⟩
  have hsub := window_subset_closedBall (ι := Fin 3) (T := (n:ℝ)) (R := (n:ℝ))
  have hz := hsub hzQ
  simpa [max_self] using hz

/-- The finite family of side-`h` cells meeting `Q_n`. -/
private noncomputable def winCellFinset (n : ℕ) {h : ℝ} (hh : 0 < h) :
    Finset (ℤ × (Fin 3 → ℤ)) :=
  (winCells_finite hh n).toFinset

private theorem mem_winCellFinset {n : ℕ} {h : ℝ} {hh : 0 < h} {p : ℤ × (Fin 3 → ℤ)} :
    p ∈ winCellFinset n hh ↔ (prodGridCell h p.1 p.2 ∩ winQ n).Nonempty := by
  rw [winCellFinset, Set.Finite.mem_toFinset]
  rfl

set_option maxHeartbeats 800000 in
/-- The cells meeting the window cover it. -/
private theorem winQ_subset_biUnion {n : ℕ} {h : ℝ} (hh : 0 < h) :
    winQ n ⊆ ⋃ p ∈ winCellFinset n hh, prodGridCell h p.1 p.2 := by
  intro z hz
  have hzc := mem_prodGridCell_floor hh z
  have hpmem : (⌊z.1 / h⌋, fun i => ⌊z.2 i / h⌋) ∈ winCellFinset n hh :=
    mem_winCellFinset.mpr ⟨z, hzc, hz⟩
  exact Set.mem_biUnion (x := (⌊z.1 / h⌋, fun i => ⌊z.2 i / h⌋)) hpmem hzc

/-- **The enclosure geometry**: a cell meeting `Q_n` stays inside `encW n h`
under every shift of norm at most `h`. -/
private theorem winCell_shift_mem_encW {n : ℕ} {h : ℝ} (hh : 0 < h)
    {p : ℤ × (Fin 3 → ℤ)} (hp : p ∈ winCellFinset n hh)
    {z : ℝ × Space} (hz : z ∈ prodGridCell h p.1 p.2)
    {k : ℝ × Space} (hk : k ∈ Metric.closedBall (0 : ℝ × Space) h) :
    z + k ∈ encW n h := by
  obtain ⟨z₀, hz₀c, hz₀Q⟩ := mem_winCellFinset.mp hp
  have hknorm : ‖k‖ ≤ h := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hk
  have hdiam : ‖z - z₀‖ ≤ h := norm_sub_le_of_mem_prodGridCell hh.le hz hz₀c
  have hd1 : |z.1 - z₀.1| ≤ h := by
    refine le_trans ?_ hdiam
    simp [Prod.norm_def, Real.norm_eq_abs]
  have hd2 : ‖z.2 - z₀.2‖ ≤ h := by
    refine le_trans ?_ hdiam
    simp [Prod.norm_def]
  have hk1 : |k.1| ≤ h := by
    refine le_trans ?_ hknorm
    simp [Prod.norm_def, Real.norm_eq_abs]
  have hk2 : ‖k.2‖ ≤ h := by
    refine le_trans ?_ hknorm
    simp [Prod.norm_def]
  have hz₀Q' : z₀.1 ∈ Set.Ioc (0:ℝ) (n:ℝ) ∧
      z₀.2 ∈ Metric.closedBall (0 : Space) (n:ℝ) := hz₀Q
  have hz₀2 : ‖z₀.2‖ ≤ (n:ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz₀Q'.2
  obtain ⟨hd1a, hd1b⟩ := abs_le.mp hd1
  obtain ⟨hk1a, hk1b⟩ := abs_le.mp hk1
  have h01 : 0 < z₀.1 := hz₀Q'.1.1
  have h02 : z₀.1 ≤ (n:ℝ) := hz₀Q'.1.2
  rw [encW]
  refine ⟨?_, ?_⟩
  · simp only [Prod.fst_add, Set.mem_Ioc]
    constructor
    · linarith
    · linarith
  · simp only [Prod.snd_add, Metric.mem_closedBall, dist_zero_right]
    have hrw : z.2 + k.2 = z₀.2 + ((z.2 - z₀.2) + k.2) := by abel
    rw [hrw]
    have hn1 := norm_add_le z₀.2 ((z.2 - z₀.2) + k.2)
    have hn2 := norm_add_le (z.2 - z₀.2) k.2
    linarith

private theorem winCell_subset_encW {n : ℕ} {h : ℝ} (hh : 0 < h)
    {p : ℤ × (Fin 3 → ℤ)} (hp : p ∈ winCellFinset n hh) :
    prodGridCell h p.1 p.2 ⊆ encW n h := by
  intro z hz
  have h0 : (0 : ℝ × Space) ∈ Metric.closedBall (0 : ℝ × Space) h :=
    Metric.mem_closedBall_self hh.le
  have hmem := winCell_shift_mem_encW hh hp hz h0
  simpa using hmem

private theorem winQ_subset_encW {n : ℕ} {h : ℝ} (hh : 0 < h) : winQ n ⊆ encW n h := by
  intro z hz
  have hz' : z.1 ∈ Set.Ioc (0:ℝ) (n:ℝ) ∧
      z.2 ∈ Metric.closedBall (0 : Space) (n:ℝ) := hz
  have h1 : 0 < z.1 := hz'.1.1
  have h2 : z.1 ≤ (n:ℝ) := hz'.1.2
  have h3 : ‖z.2‖ ≤ (n:ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz'.2
  rw [encW]
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_Ioc]
    constructor <;> linarith
  · simp only [Metric.mem_closedBall, dist_zero_right]
    linarith

/-- Bridge: a set integral against the ambient product-space volume equals the
same integral against `volume.prod volume`. -/
private theorem setIntegral_eq_prod_volume (F : ℝ × Space → ℝ) (s : Set (ℝ × Space)) :
    (∫ z in s, F z) = ∫ z in s, F z ∂(volume.prod volume) := by
  rw [Measure.volume_eq_prod]

/-- Displacement integrand of the forward extension: product-integrable on any
time-slab. -/
private theorem fwd_disp_integrableOn_slab (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (k : ℝ × Space) (p q : ℝ) :
    IntegrableOn (fun z : ℝ × Space => ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      (Set.Ioc p q ×ˢ (univ : Set Space)) := by
  have h1 := integrableOn_prod_univ
    (fun z : ℝ × Space => ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
    (by simpa [fwdFn] using fwd_disp2_meas uSeq hmeas m k.1 0 k.2 0)
    (Set.Ioc p q) measurableSet_Ioc (fun z => by positivity)
    (fun t => by simpa [fwdFn] using fwd_disp2_int uSeq hint hmeas m (t + k.1) t k.2 0)
    (by simpa [fwdFn] using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 k.2 0 p q)
  rwa [IntegrableOn, ← Measure.volume_eq_prod] at h1

private theorem fwd_disp_integrableOn_encW (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (k : ℝ × Space) (n : ℕ) (h : ℝ) :
    IntegrableOn (fun z : ℝ × Space => ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      (encW n h) := by
  refine (fwd_disp_integrableOn_slab uSeq C hkin hint hmeas m k
    (-(2*h)) ((n:ℝ)+2*h)).mono_set ?_
  rw [encW]
  exact Set.prod_mono subset_rfl (Set.subset_univ _)

private theorem fwd_L2_integrableOn_slab (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (p q : ℝ) :
    IntegrableOn (fun z : ℝ × Space => ‖fwdFn uSeq m z‖ ^ 2)
      (Set.Ioc p q ×ˢ (univ : Set Space)) := by
  have h1 := integrableOn_prod_univ (fun z : ℝ × Space => ‖fwdFn uSeq m z‖ ^ 2)
    ((fwdFn_meas uSeq hmeas m).norm.pow_const 2) (Set.Ioc p q) measurableSet_Ioc
    (fun z => by positivity) (fun t => by simpa [fwdFn] using fwd_int uSeq hint m t)
    (by simpa [fwdFn] using fwd_inner_integrableOn uSeq C hkin hint hmeas m p q)
  rwa [IntegrableOn, ← Measure.volume_eq_prod] at h1

private theorem fwd_L2_integrableOn_encW (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (n : ℕ) (h : ℝ) :
    IntegrableOn (fun z : ℝ × Space => ‖fwdFn uSeq m z‖ ^ 2) (encW n h) := by
  refine (fwd_L2_integrableOn_slab uSeq C hkin hint hmeas m (-(2*h)) ((n:ℝ)+2*h)).mono_set ?_
  rw [encW]
  exact Set.prod_mono subset_rfl (Set.subset_univ _)

/-- The nested displacement integral over any finite time interval is at most
`4C` times the interval length. -/
private theorem fwd_disp_nested_le (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (k : ℝ × Space) {p q : ℝ} (hpq : p ≤ q) :
    (∫ t in Set.Ioc p q, ∫ x : Space,
        ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2) ≤ 4 * C * (q - p) := by
  have houter : IntegrableOn (fun t : ℝ => ∫ x : Space,
      ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2) (Set.Ioc p q) := by
    simpa using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 k.2 0 p q
  calc (∫ t in Set.Ioc p q, ∫ x : Space,
        ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2)
      ≤ ∫ _ in Set.Ioc p q, (4 * C) := by
        refine setIntegral_mono_on houter (integrableOn_const (hs := measure_Ioc_lt_top.ne))
          measurableSet_Ioc (fun t _ => ?_)
        simpa using fwd_disp2_inner_le uSeq C hkin hint hmeas m (t + k.1) t k.2 0
    _ = (volume.real (Set.Ioc p q)) * (4 * C) := by
        rw [setIntegral_const]; simp [smul_eq_mul]
    _ = (q - p) * (4 * C) := by
        rw [show volume.real (Set.Ioc p q) = q - p from by
          rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]]
    _ = 4 * C * (q - p) := by ring

/-- The nested kinetic integral over any finite time interval is at most `C`
times the interval length. -/
private theorem fwd_L2_nested_le (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) {p q : ℝ} (hpq : p ≤ q) :
    (∫ t in Set.Ioc p q, ∫ x : Space, ‖fwd uSeq m t x‖ ^ 2) ≤ C * (q - p) := by
  calc (∫ t in Set.Ioc p q, ∫ x : Space, ‖fwd uSeq m t x‖ ^ 2)
      ≤ ∫ _ in Set.Ioc p q, C := by
        refine setIntegral_mono_on (fwd_inner_integrableOn uSeq C hkin hint hmeas m p q)
          (integrableOn_const (hs := measure_Ioc_lt_top.ne)) measurableSet_Ioc
          (fun t _ => fwd_kin uSeq C hkin m t)
    _ = (volume.real (Set.Ioc p q)) * C := by
        rw [setIntegral_const]; simp [smul_eq_mul]
    _ = (q - p) * C := by
        rw [show volume.real (Set.Ioc p q) = q - p from by
          rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]]
    _ = C * (q - p) := by ring

/-- The displacement over the enclosure is at most `4C(n + 4h)` (kinetic bound
alone, no equicontinuity). -/
private theorem fwd_disp_encW_le (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (k : ℝ × Space) (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ z in encW n h, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      ≤ 4 * C * ((n:ℝ) + 4 * h) := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hpq : -(2*h) ≤ (n:ℝ) + 2*h := by linarith
  have hslab := fwd_disp_integrableOn_slab uSeq C hkin hint hmeas m k (-(2*h)) ((n:ℝ)+2*h)
  have hmono : (∫ z in encW n h, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      ≤ ∫ z in Set.Ioc (-(2*h)) ((n:ℝ)+2*h) ×ˢ (univ : Set Space),
          ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2 := by
    refine setIntegral_mono_set hslab
      (Filter.Eventually.of_forall fun z => by positivity)
      (HasSubset.Subset.eventuallyLE ?_)
    rw [encW]
    exact Set.prod_mono subset_rfl (Set.subset_univ _)
  have hnested : (∫ z in Set.Ioc (-(2*h)) ((n:ℝ)+2*h) ×ˢ (univ : Set Space),
      ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      = ∫ t in Set.Ioc (-(2*h)) ((n:ℝ)+2*h), ∫ x : Space,
          ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2 := by
    rw [setIntegral_eq_prod_volume]
    have hbr := setIntegral_prod_univ_eq_nested
      (fun z : ℝ × Space => ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      (by simpa [fwdFn] using fwd_disp2_meas uSeq hmeas m k.1 0 k.2 0)
      (Set.Ioc (-(2*h)) ((n:ℝ)+2*h)) measurableSet_Ioc (fun z => by positivity)
      (fun t => by simpa [fwdFn] using fwd_disp2_int uSeq hint hmeas m (t + k.1) t k.2 0)
      (by simpa [fwdFn] using
        fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 k.2 0 (-(2*h)) ((n:ℝ)+2*h))
    exact hbr
  rw [hnested] at hmono
  calc (∫ z in encW n h, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      ≤ ∫ t in Set.Ioc (-(2*h)) ((n:ℝ)+2*h), ∫ x : Space,
          ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2 := hmono
    _ ≤ 4 * C * (((n:ℝ) + 2*h) - (-(2*h))) :=
        fwd_disp_nested_le uSeq C hkin hint hmeas m k hpq
    _ = 4 * C * ((n:ℝ) + 4 * h) := by ring

/-- The kinetic energy over the enclosure is at most `C(n + 4h)`. -/
private theorem fwd_L2_encW_le (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∫ z in encW n h, ‖fwdFn uSeq m z‖ ^ 2) ≤ C * ((n:ℝ) + 4 * h) := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hpq : -(2*h) ≤ (n:ℝ) + 2*h := by linarith
  have hslab := fwd_L2_integrableOn_slab uSeq C hkin hint hmeas m (-(2*h)) ((n:ℝ)+2*h)
  have hmono : (∫ z in encW n h, ‖fwdFn uSeq m z‖ ^ 2)
      ≤ ∫ z in Set.Ioc (-(2*h)) ((n:ℝ)+2*h) ×ˢ (univ : Set Space), ‖fwdFn uSeq m z‖ ^ 2 := by
    refine setIntegral_mono_set hslab
      (Filter.Eventually.of_forall fun z => by positivity)
      (HasSubset.Subset.eventuallyLE ?_)
    rw [encW]
    exact Set.prod_mono subset_rfl (Set.subset_univ _)
  have hnested : (∫ z in Set.Ioc (-(2*h)) ((n:ℝ)+2*h) ×ˢ (univ : Set Space),
      ‖fwdFn uSeq m z‖ ^ 2)
      = ∫ t in Set.Ioc (-(2*h)) ((n:ℝ)+2*h), ∫ x : Space, ‖fwd uSeq m t x‖ ^ 2 := by
    rw [setIntegral_eq_prod_volume]
    have hbr := setIntegral_prod_univ_eq_nested
      (fun z : ℝ × Space => ‖fwdFn uSeq m z‖ ^ 2)
      ((fwdFn_meas uSeq hmeas m).norm.pow_const 2)
      (Set.Ioc (-(2*h)) ((n:ℝ)+2*h)) measurableSet_Ioc (fun z => by positivity)
      (fun t => by simpa [fwdFn] using fwd_int uSeq hint m t)
      (by simpa [fwdFn] using
        fwd_inner_integrableOn uSeq C hkin hint hmeas m (-(2*h)) ((n:ℝ)+2*h))
    exact hbr
  rw [hnested] at hmono
  calc (∫ z in encW n h, ‖fwdFn uSeq m z‖ ^ 2)
      ≤ ∫ t in Set.Ioc (-(2*h)) ((n:ℝ)+2*h), ∫ x : Space, ‖fwd uSeq m t x‖ ^ 2 := hmono
    _ ≤ C * (((n:ℝ) + 2*h) - (-(2*h))) := fwd_L2_nested_le uSeq C hkin hint hmeas m hpq
    _ = C * ((n:ℝ) + 4 * h) := by ring

/-- **The uniform translation modulus on the enclosure.**  For `‖k‖ ≤ h ≤ 1`
the squared `L²(encW)` displacement of the forward extension is at most
`12Ch` (the collar `(−2h, h]`, kinetic bound alone) plus `4εm` (the main window
`(h, n+2h]` via `nested_window_modulus` at `c = h`), where `εm` bounds both
equicontinuity moduli at the fixed horizon `n + 3`. -/
private theorem fwd_modulus_encW (uSeq : ℕ → VelocityEvolution) (C : ℝ) (_hC : 0 ≤ C)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (n : ℕ) (m : ℕ) {h εm : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (k : ℝ × Space) (hk : ‖k‖ ≤ h)
    (hSb : (∫ s in Set.Ioc (0:ℝ) ((n:ℝ) + 3), ∫ x : Space,
        ‖fwd uSeq m s (x + k.2) - fwd uSeq m s x‖ ^ 2) ≤ εm)
    (hTb : (∫ t in Set.Ioc (0:ℝ) ((n:ℝ) + 3), ∫ x : Space,
        ‖fwd uSeq m (t + k.1) x - fwd uSeq m t x‖ ^ 2) ≤ εm) :
    (∫ z in encW n h, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      ≤ 12 * C * h + 4 * εm := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hk1 : |k.1| ≤ h := by
    refine le_trans ?_ hk
    simp [Prod.norm_def, Real.norm_eq_abs]
  have hslab := fwd_disp_integrableOn_slab uSeq C hkin hint hmeas m k (-(2*h)) ((n:ℝ)+2*h)
  -- (1) enlarge to the slab
  have hstep1 : (∫ z in encW n h, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      ≤ ∫ z in Set.Ioc (-(2*h)) ((n:ℝ)+2*h) ×ˢ (univ : Set Space),
          ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2 := by
    refine setIntegral_mono_set hslab
      (Filter.Eventually.of_forall fun z => by positivity)
      (HasSubset.Subset.eventuallyLE ?_)
    rw [encW]
    exact Set.prod_mono subset_rfl (Set.subset_univ _)
  -- (2) nested form
  have hstep2 : (∫ z in Set.Ioc (-(2*h)) ((n:ℝ)+2*h) ×ˢ (univ : Set Space),
      ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      = ∫ t in Set.Ioc (-(2*h)) ((n:ℝ)+2*h), ∫ x : Space,
          ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2 := by
    rw [setIntegral_eq_prod_volume]
    have hbr := setIntegral_prod_univ_eq_nested
      (fun z : ℝ × Space => ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      (by simpa [fwdFn] using fwd_disp2_meas uSeq hmeas m k.1 0 k.2 0)
      (Set.Ioc (-(2*h)) ((n:ℝ)+2*h)) measurableSet_Ioc (fun z => by positivity)
      (fun t => by simpa [fwdFn] using fwd_disp2_int uSeq hint hmeas m (t + k.1) t k.2 0)
      (by simpa [fwdFn] using
        fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 k.2 0 (-(2*h)) ((n:ℝ)+2*h))
    exact hbr
  -- (3) split the time interval at `h`
  have hu : Set.Ioc (-(2*h)) h ∪ Set.Ioc h ((n:ℝ)+2*h) = Set.Ioc (-(2*h)) ((n:ℝ)+2*h) :=
    Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hdisj : Disjoint (Set.Ioc (-(2*h)) h) (Set.Ioc h ((n:ℝ)+2*h)) := by
    rw [Set.Ioc_disjoint_Ioc]
    exact le_trans (min_le_left _ _) (le_max_right _ _)
  have hOut1 : IntegrableOn (fun t : ℝ => ∫ x : Space,
      ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2) (Set.Ioc (-(2*h)) h) := by
    simpa using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 k.2 0 (-(2*h)) h
  have hOut2 : IntegrableOn (fun t : ℝ => ∫ x : Space,
      ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2) (Set.Ioc h ((n:ℝ)+2*h)) := by
    simpa using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 k.2 0 h ((n:ℝ)+2*h)
  have hstep3 : (∫ t in Set.Ioc (-(2*h)) ((n:ℝ)+2*h), ∫ x : Space,
      ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2)
      = (∫ t in Set.Ioc (-(2*h)) h, ∫ x : Space,
          ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2)
        + ∫ t in Set.Ioc h ((n:ℝ)+2*h), ∫ x : Space,
            ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2 := by
    rw [← hu, setIntegral_union hdisj measurableSet_Ioc hOut1 hOut2]
  -- (4) the collar
  have hcollar : (∫ t in Set.Ioc (-(2*h)) h, ∫ x : Space,
      ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2) ≤ 12 * C * h := by
    calc (∫ t in Set.Ioc (-(2*h)) h, ∫ x : Space,
        ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2)
        ≤ 4 * C * (h - (-(2*h))) :=
          fwd_disp_nested_le uSeq C hkin hint hmeas m k (by linarith)
      _ = 12 * C * h := by ring
  -- (5) the main window, via the certified modulus
  have hmain : (∫ t in Set.Ioc h ((n:ℝ)+2*h), ∫ x : Space,
      ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2) ≤ 2 * εm + 2 * εm := by
    refine nested_window_modulus (fwd uSeq m) k.1 k.2 h ((n:ℝ)+2*h) h εm εm
      (by linarith) hh le_rfl hk1
      (fun t => by simpa using fwd_disp2_int uSeq hint hmeas m (t + k.1) t k.2 0)
      (fun t => by simpa using fwd_disp2_int uSeq hint hmeas m (t + k.1) (t + k.1) k.2 0)
      (fun t => by simpa using fwd_disp2_int uSeq hint hmeas m (t + k.1) t 0 0)
      (by simpa using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 k.2 0 h ((n:ℝ)+2*h))
      (by simpa using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 k.1 k.2 0 h ((n:ℝ)+2*h))
      (by simpa using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 0 0 h ((n:ℝ)+2*h))
      (by simpa using fwd_disp2_outer uSeq C hkin hint hmeas m 0 0 k.2 0 0 (((n:ℝ)+2*h)+h))
      (by simpa using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 0 0 0 ((n:ℝ)+2*h))
      ?_ ?_
    · refine le_trans (setIntegral_mono_set
        (by simpa using fwd_disp2_outer uSeq C hkin hint hmeas m 0 0 k.2 0 0 ((n:ℝ)+3))
        (Filter.Eventually.of_forall fun s => integral_nonneg fun x => by positivity)
        (HasSubset.Subset.eventuallyLE (Set.Ioc_subset_Ioc le_rfl (by linarith)))) hSb
    · refine le_trans (setIntegral_mono_set
        (by simpa using fwd_disp2_outer uSeq C hkin hint hmeas m k.1 0 0 0 0 ((n:ℝ)+3))
        (Filter.Eventually.of_forall fun s => integral_nonneg fun x => by positivity)
        (HasSubset.Subset.eventuallyLE (Set.Ioc_subset_Ioc le_rfl (by linarith)))) hTb
  calc (∫ z in encW n h, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      ≤ ∫ z in Set.Ioc (-(2*h)) ((n:ℝ)+2*h) ×ˢ (univ : Set Space),
          ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2 := hstep1
    _ = _ := hstep2
    _ = _ := hstep3
    _ ≤ 12 * C * h + (2 * εm + 2 * εm) := by
        have hnn : (0:ℝ) ≤ ∫ t in Set.Ioc h ((n:ℝ)+2*h), ∫ x : Space,
            ‖fwd uSeq m (t + k.1) (x + k.2) - fwd uSeq m t x‖ ^ 2 :=
          setIntegral_nonneg measurableSet_Ioc fun t _ =>
            integral_nonneg fun x => by positivity
        linarith [hcollar, hmain]
    _ = 12 * C * h + 4 * εm := by ring

/-- Integrability, in the shift variable, of the displacement integral over any
subset of the enclosure. -/
private theorem fwd_shiftIntegral_integrableOn_ball (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (m : ℕ) (n : ℕ) {h : ℝ} (hh : 0 < h)
    {A : Set (ℝ × Space)} (hAW : A ⊆ encW n h) :
    IntegrableOn (fun k : ℝ × Space => ∫ z in A,
        ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      (Metric.closedBall (0 : ℝ × Space) h) := by
  have hj : Measurable fun w : (ℝ × Space) × (ℝ × Space) =>
      ‖fwdFn uSeq m (w.2 + w.1) - fwdFn uSeq m w.2‖ ^ 2 := by
    have h1 : Measurable fun w : (ℝ × Space) × (ℝ × Space) => fwdFn uSeq m (w.2 + w.1) :=
      (fwdFn_meas uSeq hmeas m).comp (measurable_snd.add measurable_fst)
    have h2 : Measurable fun w : (ℝ × Space) × (ℝ × Space) => fwdFn uSeq m w.2 :=
      (fwdFn_meas uSeq hmeas m).comp measurable_snd
    exact ((h1.sub h2).norm).pow_const 2
  have hsm : StronglyMeasurable fun k : ℝ × Space => ∫ z in A,
      ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2 :=
    hj.stronglyMeasurable.integral_prod_right' (ν := volume.restrict A)
  refine Measure.integrableOn_of_bounded measure_closedBall_lt_top.ne
    hsm.aestronglyMeasurable (M := 4 * C * ((n:ℝ) + 4 * h)) ?_
  refine Filter.Eventually.of_forall fun k => ?_
  have hIenc := fwd_disp_integrableOn_encW uSeq C hkin hint hmeas m k n h
  have hnnI : (0:ℝ) ≤ ∫ z in A, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2 :=
    integral_nonneg fun z => by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnnI]
  calc (∫ z in A, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2)
      ≤ ∫ z in encW n h, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2 :=
        setIntegral_mono_set hIenc
          (Filter.Eventually.of_forall fun z => by positivity)
          (HasSubset.Subset.eventuallyLE hAW)
    _ ≤ 4 * C * ((n:ℝ) + 4 * h) :=
        fwd_disp_encW_le uSeq C hkin hint hmeas m k n hh.le

/-- **The cell-error sum at one scale**, from
`sum_cellError_le_modulus_of_memL2` with `W := encW n h`. -/
private theorem fwd_cellError_sum_le (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (n : ℕ) (m : ℕ) {h Mmod : ℝ} (hh : 0 < h)
    (hmod : ∀ k ∈ Metric.closedBall (0 : ℝ × Space) h,
      (∫ z in encW n h, ‖fwdFn uSeq m (z + k) - fwdFn uSeq m z‖ ^ 2) ≤ Mmod) :
    ∑ p ∈ winCellFinset n hh, (∫ z in prodGridCell h p.1 p.2,
        ‖fwdFn uSeq m z - ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq m y‖ ^ 2)
      ≤ (h ^ 4)⁻¹ * (volume.real (Metric.closedBall (0 : ℝ × Space) h) * Mmod) :=
  sum_cellError_le_modulus_of_memL2 hh (winCellFinset n hh)
    (fwdFn uSeq m) (fwdFn_meas uSeq hmeas m)
    (encW n h) (measurableSet_encW n h)
    (fun _ hp => winCell_subset_encW hh hp)
    (fun _ hp _ hz _ hk => winCell_shift_mem_encW hh hp hz hk)
    (fwd_L2_integrableOn_encW uSeq C hkin hint hmeas m n h)
    Mmod hmod
    (fun k => fwd_disp_integrableOn_encW uSeq C hkin hint hmeas m k n h)
    (fun _ hp => fwd_shiftIntegral_integrableOn_ball uSeq C hkin hint hmeas m n hh
      (winCell_subset_encW hh hp))
    (fwd_shiftIntegral_integrableOn_ball uSeq C hkin hint hmeas m n hh
      (subset_refl (encW n h)))

/-- **The cell-average norm bound**: Jensen against the kinetic energy over the
enclosure. -/
private theorem fwd_avg_sq_le (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq) (n : ℕ) (m : ℕ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {p : ℤ × (Fin 3 → ℤ)} (hp : p ∈ winCellFinset n hh) :
    ‖⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq m y‖ ^ 2
      ≤ (h ^ 4)⁻¹ * (C * ((n:ℝ) + 4)) := by
  have hC' : 0 ≤ C := le_trans (integral_nonneg fun x => by positivity) (hkin m 0 le_rfl)
  have h0 := volume_cell_ne_zero hh p
  have hfin := volume_cell_ne_top hh p
  have hL2cell : IntegrableOn (fun z : ℝ × Space => ‖fwdFn uSeq m z‖ ^ 2)
      (prodGridCell h p.1 p.2) :=
    (fwd_L2_integrableOn_encW uSeq C hkin hint hmeas m n h).mono_set
      (winCell_subset_encW hh hp)
  have hfmeas := fwdFn_meas uSeq hmeas m
  have hfi : IntegrableOn (fwdFn uSeq m) (prodGridCell h p.1 p.2) :=
    (integrable_norm_iff hfmeas.aestronglyMeasurable.restrict).mp
      (integrableOn_norm_of_sq hfin hfmeas.norm.aestronglyMeasurable hL2cell)
  have hj := norm_setAverage_sub_sq_le h0 hfin (fwdFn uSeq m) 0 hfi
    (by simpa using hL2cell)
  simp only [sub_zero] at hj
  have havg : (⨍ y in prodGridCell h p.1 p.2, ‖fwdFn uSeq m y‖ ^ 2)
      = (h ^ 4)⁻¹ * ∫ y in prodGridCell h p.1 p.2, ‖fwdFn uSeq m y‖ ^ 2 := by
    rw [setAverage_eq, volume_real_cell hh p, smul_eq_mul]
  have hIb : (∫ y in prodGridCell h p.1 p.2, ‖fwdFn uSeq m y‖ ^ 2) ≤ C * ((n:ℝ) + 4) := by
    calc (∫ y in prodGridCell h p.1 p.2, ‖fwdFn uSeq m y‖ ^ 2)
        ≤ ∫ z in encW n h, ‖fwdFn uSeq m z‖ ^ 2 :=
          setIntegral_mono_set (fwd_L2_integrableOn_encW uSeq C hkin hint hmeas m n h)
            (Filter.Eventually.of_forall fun z => by positivity)
            (HasSubset.Subset.eventuallyLE (winCell_subset_encW hh hp))
      _ ≤ C * ((n:ℝ) + 4 * h) := fwd_L2_encW_le uSeq C hkin hint hmeas m n hh.le
      _ ≤ C * ((n:ℝ) + 4) := by nlinarith
  calc ‖⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq m y‖ ^ 2
      ≤ ⨍ y in prodGridCell h p.1 p.2, ‖fwdFn uSeq m y‖ ^ 2 := hj
    _ = (h ^ 4)⁻¹ * ∫ y in prodGridCell h p.1 p.2, ‖fwdFn uSeq m y‖ ^ 2 := havg
    _ ≤ (h ^ 4)⁻¹ * (C * ((n:ℝ) + 4)) :=
        mul_le_mul_of_nonneg_left hIb (by positivity)

/-!
### The cell-average step function and the ε/3 assembly
-/

/-- The cell-average step function over the finite cell family. -/
private noncomputable def cellStep (h : ℝ) (S : Finset (ℤ × (Fin 3 → ℤ)))
    (f : ℝ × Space → Space) : ℝ × Space → Space := fun z =>
  ∑ p ∈ S, (prodGridCell h p.1 p.2).indicator
    (fun _ => ⨍ y in prodGridCell h p.1 p.2, f y) z

private theorem cellStep_measurable (h : ℝ) (S : Finset (ℤ × (Fin 3 → ℤ)))
    (f : ℝ × Space → Space) : Measurable (cellStep h S f) := by
  unfold cellStep
  exact Finset.measurable_sum S fun p _ =>
    Measurable.indicator measurable_const (measurableSet_prodGridCell h p.1 p.2)

private theorem cellStep_eq_avg {h : ℝ} (hh : 0 < h) {S : Finset (ℤ × (Fin 3 → ℤ))}
    {p : ℤ × (Fin 3 → ℤ)} (hp : p ∈ S) (f : ℝ × Space → Space)
    {z : ℝ × Space} (hz : z ∈ prodGridCell h p.1 p.2) :
    cellStep h S f z = ⨍ y in prodGridCell h p.1 p.2, f y := by
  unfold cellStep
  rw [Finset.sum_eq_single p ?_ (fun hpS => absurd hp hpS)]
  · rw [Set.indicator_of_mem hz]
  · intro q _ hqp
    refine Set.indicator_of_notMem (fun hzq => ?_) _
    have hne : (q.1, q.2) ≠ (p.1, p.2) := by
      simpa using hqp
    exact Set.disjoint_left.mp (prodGridCell_disjoint hh hne) hzq hz

private theorem cellStep_norm_le (h : ℝ) (S : Finset (ℤ × (Fin 3 → ℤ)))
    (f : ℝ × Space → Space) (z : ℝ × Space) :
    ‖cellStep h S f z‖ ≤ ∑ p ∈ S, ‖⨍ y in prodGridCell h p.1 p.2, f y‖ := by
  unfold cellStep
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
  exact norm_indicator_le_norm_self
    (f := fun _ : ℝ × Space => ⨍ y in prodGridCell h p.1 p.2, f y) (a := z)

/-- Bounded measurable difference is square-integrable on a finite-measure set. -/
private theorem integrableOn_sq_norm_sub_of_bound {g₁ g₂ : ℝ × Space → Space}
    (h₁ : Measurable g₁) (h₂ : Measurable g₂)
    {s : Set (ℝ × Space)} (hsfin : volume s ≠ ⊤)
    {M : ℝ} (hM : ∀ z, ‖g₁ z - g₂ z‖ ^ 2 ≤ M) :
    IntegrableOn (fun z => ‖g₁ z - g₂ z‖ ^ 2) s := by
  refine Measure.integrableOn_of_bounded hsfin
    (((h₁.sub h₂).norm.pow_const 2).aestronglyMeasurable) (M := M) ?_
  refine Filter.Eventually.of_forall fun z => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hM z

/-- `L²` against bounded: the difference is square-integrable on a
finite-measure set. -/
private theorem integrableOn_sq_norm_sub_of_L2 {f g : ℝ × Space → Space}
    (hf : Measurable f) (hg : Measurable g)
    {s : Set (ℝ × Space)} (hsfin : volume s ≠ ⊤)
    (hL2 : IntegrableOn (fun z => ‖f z‖ ^ 2) s)
    {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M) :
    IntegrableOn (fun z => ‖f z - g z‖ ^ 2) s := by
  refine Integrable.mono' ((hL2.const_mul 2).add
      (integrableOn_const hsfin (C := 2 * M ^ 2)))
    (((hf.sub hg).norm.pow_const 2).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 := sq_norm_sub_le_two (f z) (g z)
  have h2 : ‖g z‖ ^ 2 ≤ M ^ 2 := by
    have h3 := hM z
    nlinarith [norm_nonneg (g z)]
  linarith

/-- The window integral of a nonnegative integrand is at most its sum over the
covering cell family. -/
private theorem setIntegral_winQ_le_sum_winCells {g : ℝ × Space → ℝ}
    (hgnn : ∀ z, 0 ≤ g z) {h : ℝ} (hh : 0 < h) (n : ℕ)
    (hcell : ∀ p ∈ winCellFinset n hh, IntegrableOn g (prodGridCell h p.1 p.2))
    (_hwinQ : IntegrableOn g (winQ n)) :
    (∫ z in winQ n, g z)
      ≤ ∑ p ∈ winCellFinset n hh, ∫ z in prodGridCell h p.1 p.2, g z := by
  have hUnion : IntegrableOn g (⋃ p ∈ winCellFinset n hh, prodGridCell h p.1 p.2) :=
    integrableOn_finset_iUnion.mpr hcell
  have hle : (∫ z in winQ n, g z)
      ≤ ∫ z in ⋃ p ∈ winCellFinset n hh, prodGridCell h p.1 p.2, g z :=
    setIntegral_mono_set hUnion (Filter.Eventually.of_forall hgnn)
      (HasSubset.Subset.eventuallyLE (winQ_subset_biUnion hh))
  rwa [MeasureTheory.integral_biUnion_finset _
    (fun p _ => measurableSet_prodGridCell h p.1 p.2)
    (fun p _ q _ hpq => prodGridCell_disjoint hh (by simpa using hpq)) hcell] at hle

/-- **Bolzano–Weierstrass** in any finite-dimensional real normed space, in the
Cauchy-subsequence form the diagonal consumes. -/
private theorem exists_subseq_cauchy_of_bounded_finiteDim {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (v : ℕ → F) (M : ℝ) (hb : ∀ k : ℕ, ‖v k‖ ≤ M) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ j k : ℕ, K ≤ j → K ≤ k →
        ‖v (ρ j) - v (ρ k)‖ < ε := by
  haveI : ProperSpace F := FiniteDimensional.proper_real F
  obtain ⟨b, -, ρ, hρ, hconv⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall (x := (0 : F)) (r := M))
      (fun k => by simpa [Metric.mem_closedBall, dist_zero_right] using hb k)
  refine ⟨ρ, hρ, fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq ε hε
  exact ⟨K, fun j k hj hk => by simpa [dist_eq_norm] using hK j hj k hk⟩

/-- Haar scaling of the spacetime ball: `vol(B̄(0,h)) = h⁴ · vol(B̄(0,1))`. -/
private theorem volume_real_closedBall_prodSpace {h : ℝ} (hh : 0 ≤ h) :
    volume.real (Metric.closedBall (0 : ℝ × Space) h)
      = h ^ 4 * volume.real (Metric.closedBall (0 : ℝ × Space) 1) := by
  haveI : (volume : Measure (ℝ × Space)).IsAddHaarMeasure := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    infer_instance
  have h4 : Module.finrank ℝ (ℝ × Space) = 4 := by
    rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
  have hHaar := MeasureTheory.Measure.addHaar_real_closedBall'
    (volume : Measure (ℝ × Space)) (0 : ℝ × Space) hh
  rwa [h4] at hHaar

/-- The scalar budget arithmetic of the final assembly, isolated so that the
huge integral expressions enter only as opaque atoms. -/
private theorem window_budget {W S1 S2 Sm κC C h εm ε' cardS ε : ℝ}
    (hchain : W ≤ 3 * S1 + 3 * Sm + 3 * S2)
    (hS1 : S1 ≤ κC * (12 * C * h + 4 * εm))
    (hS2 : S2 ≤ κC * (12 * C * h + 4 * εm))
    (hSm : Sm ≤ cardS * (h ^ 4 * ε' ^ 2))
    (hε'sq : ε' ^ 2 * (12 * (h ^ 4 * cardS + 1)) = ε)
    (hεmeq : εm * (400 * (κC + 1)) = ε)
    (hhlin : h * (400 * (C * κC + 1)) < ε)
    (hCκh0 : 0 ≤ C * κC * h)
    (hh0 : 0 ≤ h) (hεm0 : 0 ≤ εm) :
    W < ε := by nlinarith

set_option maxHeartbeats 1600000 in
/-- **The ε/3 assembly at one scale.**  The window error of two members of the
forward-extended family is controlled by their two cell-average errors plus the
finite-dimensional mid-leg on the cell-average vectors. -/
private theorem windowError_le_three_legs (uSeq : ℕ → VelocityEvolution) (C : ℝ)
    (hkin : UniformKineticBound uSeq C)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (hmeas : JointlyMeasurable uSeq)
    (n : ℕ) {h : ℝ} (hh : 0 < h) (a b : ℕ) :
    windowError (uSeq a) (uSeq b) n
      ≤ 3 * (∑ p ∈ winCellFinset n hh, ∫ z in prodGridCell h p.1 p.2,
            ‖fwdFn uSeq a z - ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y‖ ^ 2)
        + 3 * (∑ p ∈ winCellFinset n hh, h ^ 4 *
            ‖(⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y) -
              ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖ ^ 2)
        + 3 * (∑ p ∈ winCellFinset n hh, ∫ z in prodGridCell h p.1 p.2,
            ‖fwdFn uSeq b z - ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖ ^ 2) := by
  classical
  have hf₁m : Measurable (fwdFn uSeq a) := fwdFn_meas uSeq hmeas a
  have hf₂m : Measurable (fwdFn uSeq b) := fwdFn_meas uSeq hmeas b
  have hE₁m : Measurable (cellStep h (winCellFinset n hh) (fwdFn uSeq a)) :=
    cellStep_measurable _ _ _
  have hE₂m : Measurable (cellStep h (winCellFinset n hh) (fwdFn uSeq b)) :=
    cellStep_measurable _ _ _
  have hQfin : volume (winQ n) ≠ ⊤ := volume_winQ_ne_top n
  have hL2₁ : IntegrableOn (fun z : ℝ × Space => ‖fwdFn uSeq a z‖ ^ 2) (winQ n) :=
    (fwd_L2_integrableOn_encW uSeq C hkin hint hmeas a n h).mono_set (winQ_subset_encW hh)
  have hL2₂ : IntegrableOn (fun z : ℝ × Space => ‖fwdFn uSeq b z‖ ^ 2) (winQ n) :=
    (fwd_L2_integrableOn_encW uSeq C hkin hint hmeas b n h).mono_set (winQ_subset_encW hh)
  have hE₁b : ∀ z, ‖cellStep h (winCellFinset n hh) (fwdFn uSeq a) z‖
      ≤ ∑ p ∈ winCellFinset n hh, ‖⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y‖ :=
    fun z => cellStep_norm_le h _ _ z
  have hE₂b : ∀ z, ‖cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖
      ≤ ∑ p ∈ winCellFinset n hh, ‖⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖ :=
    fun z => cellStep_norm_le h _ _ z
  have hE₁₂sq : ∀ z, ‖cellStep h (winCellFinset n hh) (fwdFn uSeq a) z -
      cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2
      ≤ ((∑ p ∈ winCellFinset n hh, ‖⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y‖) +
          ∑ p ∈ winCellFinset n hh, ‖⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖) ^ 2 := by
    intro z
    have hn := norm_sub_le (cellStep h (winCellFinset n hh) (fwdFn uSeq a) z)
      (cellStep h (winCellFinset n hh) (fwdFn uSeq b) z)
    have h1 := hE₁b z
    have h2 := hE₂b z
    nlinarith [norm_nonneg (cellStep h (winCellFinset n hh) (fwdFn uSeq a) z -
      cellStep h (winCellFinset n hh) (fwdFn uSeq b) z),
      norm_nonneg (cellStep h (winCellFinset n hh) (fwdFn uSeq a) z),
      norm_nonneg (cellStep h (winCellFinset n hh) (fwdFn uSeq b) z)]
  -- three-legs integrabilities on the window
  have h1 : IntegrableOn (fun z : ℝ × Space =>
      ‖fwdFn uSeq a z - fwdFn uSeq b z‖ ^ 2) (winQ n) := by
    have h0 := integrableOn_winQ (fwd uSeq a) (fwd uSeq b) n C
      (fwd_meas uSeq hmeas a) (fwd_meas uSeq hmeas b)
      (fun t _ => fwd_int uSeq hint a t) (fun t _ => fwd_int uSeq hint b t)
      (fun t _ => fwd_kin uSeq C hkin a t) (fun t _ => fwd_kin uSeq C hkin b t)
    rwa [IntegrableOn, ← Measure.volume_eq_prod] at h0
  have h2 : IntegrableOn (fun z : ℝ × Space =>
      ‖fwdFn uSeq a z - cellStep h (winCellFinset n hh) (fwdFn uSeq a) z‖ ^ 2) (winQ n) :=
    integrableOn_sq_norm_sub_of_L2 hf₁m hE₁m hQfin hL2₁ hE₁b
  have h3 : IntegrableOn (fun z : ℝ × Space =>
      ‖cellStep h (winCellFinset n hh) (fwdFn uSeq a) z -
        cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2) (winQ n) :=
    integrableOn_sq_norm_sub_of_bound hE₁m hE₂m hQfin hE₁₂sq
  have h4' : IntegrableOn (fun z : ℝ × Space =>
      ‖fwdFn uSeq b z - cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2) (winQ n) :=
    integrableOn_sq_norm_sub_of_L2 hf₂m hE₂m hQfin hL2₂ hE₂b
  have h4 : IntegrableOn (fun z : ℝ × Space =>
      ‖cellStep h (winCellFinset n hh) (fwdFn uSeq b) z - fwdFn uSeq b z‖ ^ 2) (winQ n) :=
    h4'.congr (Filter.Eventually.of_forall fun z => by
      show ‖fwdFn uSeq b z - cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2
          = ‖cellStep h (winCellFinset n hh) (fwdFn uSeq b) z - fwdFn uSeq b z‖ ^ 2
      rw [norm_sub_rev])
  -- the window error as a single product integral
  have hwe : windowError (uSeq a) (uSeq b) n
      = ∫ z in winQ n, ‖fwdFn uSeq a z - fwdFn uSeq b z‖ ^ 2 := by
    rw [← windowError_fwd uSeq a b n,
      windowError_eq_setIntegral_prod (fwd uSeq a) (fwd uSeq b) n C
        (fwd_meas uSeq hmeas a) (fwd_meas uSeq hmeas b)
        (fun t _ => fwd_int uSeq hint a t) (fun t _ => fwd_int uSeq hint b t)
        (fun t _ => fwd_kin uSeq C hkin a t) (fun t _ => fwd_kin uSeq C hkin b t),
      show (Set.Ioc (0:ℝ) (n:ℝ) ×ˢ Metric.closedBall (0:Space) (n:ℝ)) = winQ n from rfl,
      ← Measure.volume_eq_prod]
    rfl
  -- three legs
  have hthree := setIntegral_norm_sub_sq_le_three_legs (measurableSet_winQ n)
    (fwdFn uSeq a) (cellStep h (winCellFinset n hh) (fwdFn uSeq a))
    (cellStep h (winCellFinset n hh) (fwdFn uSeq b)) (fwdFn uSeq b) h1 h2 h3 h4
  -- leg 1
  have hcellint₁ : ∀ p ∈ winCellFinset n hh, IntegrableOn (fun z : ℝ × Space =>
      ‖fwdFn uSeq a z - cellStep h (winCellFinset n hh) (fwdFn uSeq a) z‖ ^ 2)
      (prodGridCell h p.1 p.2) := fun p hp =>
    integrableOn_sq_norm_sub_of_L2 hf₁m hE₁m (volume_cell_ne_top hh p)
      ((fwd_L2_integrableOn_encW uSeq C hkin hint hmeas a n h).mono_set
        (winCell_subset_encW hh hp)) hE₁b
  have hleg1 : (∫ z in winQ n,
      ‖fwdFn uSeq a z - cellStep h (winCellFinset n hh) (fwdFn uSeq a) z‖ ^ 2)
      ≤ ∑ p ∈ winCellFinset n hh, ∫ z in prodGridCell h p.1 p.2,
          ‖fwdFn uSeq a z - ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y‖ ^ 2 := by
    refine le_trans (setIntegral_winQ_le_sum_winCells (fun z => by positivity) hh n
      hcellint₁ h2) (le_of_eq (Finset.sum_congr rfl fun p hp => ?_))
    refine setIntegral_congr_fun (measurableSet_prodGridCell h p.1 p.2) fun z hz => ?_
    show ‖fwdFn uSeq a z - cellStep h (winCellFinset n hh) (fwdFn uSeq a) z‖ ^ 2
        = ‖fwdFn uSeq a z - ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y‖ ^ 2
    rw [cellStep_eq_avg hh hp _ hz]
  -- leg 3
  have hcellint₂ : ∀ p ∈ winCellFinset n hh, IntegrableOn (fun z : ℝ × Space =>
      ‖fwdFn uSeq b z - cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2)
      (prodGridCell h p.1 p.2) := fun p hp =>
    integrableOn_sq_norm_sub_of_L2 hf₂m hE₂m (volume_cell_ne_top hh p)
      ((fwd_L2_integrableOn_encW uSeq C hkin hint hmeas b n h).mono_set
        (winCell_subset_encW hh hp)) hE₂b
  have hleg3 : (∫ z in winQ n,
      ‖cellStep h (winCellFinset n hh) (fwdFn uSeq b) z - fwdFn uSeq b z‖ ^ 2)
      ≤ ∑ p ∈ winCellFinset n hh, ∫ z in prodGridCell h p.1 p.2,
          ‖fwdFn uSeq b z - ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖ ^ 2 := by
    have hswap : (∫ z in winQ n,
        ‖cellStep h (winCellFinset n hh) (fwdFn uSeq b) z - fwdFn uSeq b z‖ ^ 2)
        = ∫ z in winQ n,
            ‖fwdFn uSeq b z - cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2 :=
      setIntegral_congr_fun (measurableSet_winQ n) fun z _ => by
        show ‖cellStep h (winCellFinset n hh) (fwdFn uSeq b) z - fwdFn uSeq b z‖ ^ 2
            = ‖fwdFn uSeq b z - cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2
        rw [norm_sub_rev]
    rw [hswap]
    refine le_trans (setIntegral_winQ_le_sum_winCells (fun z => by positivity) hh n
      hcellint₂ h4') (le_of_eq (Finset.sum_congr rfl fun p hp => ?_))
    refine setIntegral_congr_fun (measurableSet_prodGridCell h p.1 p.2) fun z hz => ?_
    show ‖fwdFn uSeq b z - cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2
        = ‖fwdFn uSeq b z - ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖ ^ 2
    rw [cellStep_eq_avg hh hp _ hz]
  -- mid leg
  have hcellint₃ : ∀ p ∈ winCellFinset n hh, IntegrableOn (fun z : ℝ × Space =>
      ‖cellStep h (winCellFinset n hh) (fwdFn uSeq a) z -
        cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2)
      (prodGridCell h p.1 p.2) := fun p _ =>
    integrableOn_sq_norm_sub_of_bound hE₁m hE₂m (volume_cell_ne_top hh p) hE₁₂sq
  have hmid : (∫ z in winQ n,
      ‖cellStep h (winCellFinset n hh) (fwdFn uSeq a) z -
        cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2)
      ≤ ∑ p ∈ winCellFinset n hh, h ^ 4 *
          ‖(⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y) -
            ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖ ^ 2 := by
    refine le_trans (setIntegral_winQ_le_sum_winCells (fun z => by positivity) hh n
      hcellint₃ h3) (le_of_eq (Finset.sum_congr rfl fun p hp => ?_))
    have hcongr : (∫ z in prodGridCell h p.1 p.2,
        ‖cellStep h (winCellFinset n hh) (fwdFn uSeq a) z -
          cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2)
        = ∫ _ in prodGridCell h p.1 p.2,
            ‖(⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y) -
              ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖ ^ 2 :=
      setIntegral_congr_fun (measurableSet_prodGridCell h p.1 p.2) fun z hz => by
        show ‖cellStep h (winCellFinset n hh) (fwdFn uSeq a) z -
            cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2
            = ‖(⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq a y) -
                ⨍ y in prodGridCell h p.1 p.2, fwdFn uSeq b y‖ ^ 2
        rw [cellStep_eq_avg hh hp _ hz, cellStep_eq_avg hh hp _ hz]
    rw [hcongr, setIntegral_const, smul_eq_mul, volume_real_cell hh p]
  rw [hwe]
  calc (∫ z in winQ n, ‖fwdFn uSeq a z - fwdFn uSeq b z‖ ^ 2)
      ≤ 3 * (∫ z in winQ n,
            ‖fwdFn uSeq a z - cellStep h (winCellFinset n hh) (fwdFn uSeq a) z‖ ^ 2)
          + 3 * (∫ z in winQ n,
            ‖cellStep h (winCellFinset n hh) (fwdFn uSeq a) z -
              cellStep h (winCellFinset n hh) (fwdFn uSeq b) z‖ ^ 2)
          + 3 * ∫ z in winQ n,
              ‖cellStep h (winCellFinset n hh) (fwdFn uSeq b) z - fwdFn uSeq b z‖ ^ 2 :=
        hthree
    _ ≤ _ := by
        have hg1 := hleg1
        have hg2 := hmid
        have hg3 := hleg3
        linarith

set_option maxHeartbeats 1600000 in
/-- **[CERTIFIED — Riesz–Fréchet–Kolmogorov compactness on one window;
Brezis, *Functional Analysis, Sobolev Spaces and PDE*, Springer 2011, Thm 4.26
+ Cor 4.27; Simon, *Ann. Mat. Pura Appl.* **146** (1987) 65–96, Thm 1.]**
On the single bounded window `Q = (0,n] × B̄(0,n) ⊂ ℝ × ℝ³`, a family
that is `L²(Q)`-bounded and uniformly equicontinuous under translations in *both*
variables is totally bounded in `L²(Q)`, so any subsequence has an `L²(Q)`-Cauchy
refinement.

The `(t,x)`-translation modulus is the composite of the two supplied ones:
`‖τ_{(h,y)}f − f‖ ≤ ‖τ_{(h,0)}f − f‖ + ‖τ_{(0,y)}f − f‖`, controlled by
`TimeEquicontinuous` and `SpaceEquicontinuous` respectively; `Q` is bounded so
the tightness clause of Cor 4.27 is automatic; `JointlyMeasurable` is what makes
the members elements of `L²(Q)` at all.  Mathlib has no Riesz–Kolmogorov
criterion (only Arzelà–Ascoli for `C(K)`), so the mollify-and-Arzelà–Ascoli
argument — or the equivalent finite-dimensional dyadic-average projection
`‖E_h f − f‖_{L²} ≤ sup_{|k| ≤ diam} ‖τ_k f − f‖_{L²}` — has to be built.

**Route taken, and what is already built.**  The dyadic-average projection, not
mollify-and-Arzelà–Ascoli: `Navier.Analysis.RieszKolmogorov` carries its two
engines, both certified.  Engine 1 is `norm_setAverage_sub_sq_le` with its
oscillation form `norm_setAverage_sub_apply_sq_le`, the Jensen/Cauchy–Schwarz
bound `‖(⨍_Q f) − f x‖² ≤ ⨍_Q ‖f y − f x‖²` that makes the cell-average close to
`f` uniformly over the family.  Engine 2 is `exists_subseq_cauchy_of_bounded_pi`,
Bolzano–Weierstrass on the cell-average vector — legitimate because `E_h f` lives
in the finite-dimensional span of the finitely many cell indicators, so no
infinite-dimensional compactness is invoked anywhere.

**The middle step is now certified too.**  `sum_cellError_le_modulus_of_memL2`
(immediately above) sums the cell-oscillation bound over a finite family of spacetime
cells of side `h` and converts it into `2⁴ · sup_{|k|_∞ ≤ h} ‖τ_k f − f‖²_{L²(W)}`.
Its `L²`-on-a-window hypotheses are the ones this bundle can discharge: the earlier
`RieszKolmogorov.sum_cellError_le_modulus` asks for a global sup bound `∀ z, ‖f z‖ ≤ M`
and for `‖τ_k f − f‖²` integrable over **all** of `ℝ × ℝ³`, and a Leray field supplies
neither — it is not uniformly bounded, and `VelocityEvolution` is uncontrolled for
`t < 0`.  The `2^d` constant is checked numerically in
`experiments/riesz_kolmogorov_dyadic_core.py`, and the summation inequality itself in
`experiments/riesz_kolmogorov_cell_sum_toy.py`.

**Step (i) is now certified too.**  `nested_window_modulus` (above) turns
`TimeEquicontinuous` + `SpaceEquicontinuous` into the single spacetime bound
`∫_{Ioc c T} ∫_x ‖v(t+a)(x+y) − v(t)(x)‖² ≤ 2ε₁ + 2ε₂` for `|a| ≤ h`, `‖y‖ ≤ h`.  The
negative-time overhang — the only genuine design choice in the whole criterion — is
resolved there by the hypothesis `h ≤ c`: the working window starts at `c`, so the
time-shifted space leg lands inside `Ioc 0 (T+h)` where `SpaceEquicontinuous` speaks.
The discarded slab `(0,c]` costs `4Cc`, driven to zero by taking `c = h → 0`.

**The last two steps, now certified below as well.**  Two mechanical steps plus
one bridge:
(ii) *cell-average vector* — feed the finitely many cells meeting the window
(`finite_prodGridIndices`, `closedBall_subset_biUnion_prodGridCell`,
`window_subset_closedBall`) to `exists_subseq_cauchy_of_bounded_pi_finiteDim`.
(iii) *three-leg assembly* — `setIntegral_norm_sub_sq_le_three_legs` on
`f_j − E_h f_j`, `E_h f_j − E_h f_k`, `E_h f_k − f_k`, then a diagonal over `h = 1/m`.
The *bridge* is certified: `setIntegral_prod_univ_eq_nested` and
`prod_window_modulus` deliver `∫_W ‖f(·+k) − f‖² ≤ 2ε₁ + 2ε₂` against
`volume.prod volume` on the slab `W = Ioc c T ×ˢ univ`, which is verbatim the `hmod`
hypothesis of `sum_cellError_le_modulus_of_memL2`.

**Audit of that plan found two gaps; both repairs are recorded here.**  (a) *Cell
family.*  `closedBall_subset_biUnion_prodGridCell` yields the cells meeting the
*spacetime* ball `closedBall 0 n`, which reaches down to time `−n − h`; on those
negative-time cells the modulus bridge says nothing, and bounding the displacement
there by the kinetic bound costs `≈ 4Cn` — not `→ 0` in `h`.  The cell family must
instead be the cells meeting the window `Q_n = (0,n] ×ˢ B̄(0,n)` itself — finite as a
subset of the ball family, and covering `Q_n` by `mem_prodGridCell_floor` — with
enclosure `W := Ioc (−2h) (n+2h) ×ˢ B̄(0,n+2h)`: a cell meeting `Q_n` has times in
`(−h, n+h)`, and a further `h`-shift stays in `W`.  The `hmod` integral over `W` then
splits at `c = h`: the collar `(−2h, h]` costs `≤ 12 C h` from the kinetic bound
(slab length `3h`, integrand `≤ 4C` by `‖a−b‖² ≤ 2‖a‖² + 2‖b‖²` and translation
invariance of `volume`), and the main window `(h, n+2h]` is `prod_window_modulus` at
`c = h`, `T = n+2h` — so `Mmod(h) = 12Ch + 2ε₁(h) + 2ε₂(h) → 0` as `h → 0`, with
`ε₁`, `ε₂` taken at the fixed horizon `n + 3` for all `h ≤ 1`.
(b) *The `∀ t` integrability legs.*  `nested_window_modulus` quantifies its
inner/outer integrability hypotheses over **all** `t : ℝ`, but `hint`/`hkin` hold
only for `t ≥ 0`.  Repair: run the whole argument on the forward extension
`v m t x := uSeq m (max t 0) x`.  **This repair is now CERTIFIED** as the
forward-extension layer immediately above this docstring: `fwd` is the
extension; `windowError_fwd` shows `windowError` on `(0,n]` is unchanged
(`max t 0 = t` there), so `WindowCauchy` transfers back verbatim; `fwd_int` and
`fwd_kin` give slicewise square-integrability and the kinetic bound `C` at
*every* `t`; `fwd_space` preserves `SpaceEquicontinuous` verbatim; and
`fwd_time` shows `TimeEquicontinuous` survives with an extra `4C|h|` slab on
`(0,|h|)`, absorbed by shrinking `δ` — with `fwd_disp2_*`/`fwd_tdisp_*`
discharging the slicewise and outer integrability side conditions that
`nested_window_modulus`/`prod_window_modulus` quantify over all `t : ℝ`.
With `Mmod(h) → 0` the cell error is
`≤ h⁻⁴ · volume.real (closedBall 0 h) · Mmod(h) = volume.real (closedBall 0 1) · Mmod(h)`
(finite-dimensional `addHaar` scaling of the sup-norm ball), the middle leg is
Engine 2 on the cell-average vector in `Fin (#S) → Space` — norm-bounded by
`2(n+2h)C/h⁴` from `sq_setAverage_le` and cell disjointness, Cauchy in the pi norm,
feeding leg two through `∑_p h⁴‖d_p‖² ≤ h⁴·#S·ε'²` — and the diagonal over `h ↓ 0`
is `exists_diagonal_subseq` with `Q l σ` = cell-average Cauchyness at scale `l`
(`hsub` = restriction to a subsequence, `htail` = index shift), exactly the shape
`exists_subseq_forall_windowCauchy` already consumes.  The degenerate case `n = 0`
has `Ioc 0 0 = ∅`, hence `windowError = 0`.
[Brezis Thm 4.26 + Cor 4.27; Simon Thm 1.] -/
theorem exists_subseq_windowCauchy
    (uSeq : ℕ → VelocityEvolution) (C : ℝ) (hC : 0 ≤ C)
    (hkin : UniformKineticBound uSeq C)
    (htime : TimeEquicontinuous uSeq) (hspace : SpaceEquicontinuous uSeq)
    (hmeas : JointlyMeasurable uSeq)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (n : ℕ) (τ : ℕ → ℕ) (_hτ : StrictMono τ) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ WindowCauchy uSeq n (τ ∘ ρ) := by
  classical
  -- transfer the hypotheses along `τ`
  set vSeq : ℕ → VelocityEvolution := fun j => uSeq (τ j) with hvdef
  have vkin : UniformKineticBound vSeq C := fun m t ht => hkin (τ m) t ht
  have vint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      Integrable (fun x : Space => ‖vSeq m t x‖ ^ 2) := fun m t ht => hint (τ m) t ht
  have vmeas : JointlyMeasurable vSeq := fun m => hmeas (τ m)
  have vtime : TimeEquicontinuous vSeq := by
    intro T ε hε
    obtain ⟨δ, hδ, hb⟩ := htime T ε hε
    exact ⟨δ, hδ, fun m e he => hb (τ m) e he⟩
  have vspace : SpaceEquicontinuous vSeq := by
    intro T ε hε
    obtain ⟨δ, hδ, hb⟩ := hspace T ε hε
    exact ⟨δ, hδ, fun m y hy => hb (τ m) y hy⟩
  have wtime : TimeEquicontinuous (fwd vSeq) := fwd_time vSeq C hC vkin vint vmeas vtime
  have wspace : SpaceEquicontinuous (fwd vSeq) := fwd_space vSeq vspace
  -- the scale ladder
  have hscale_pos : ∀ l : ℕ, 0 < 1 / ((l:ℝ) + 1) := fun l => by positivity
  have hscale_le1 : ∀ l : ℕ, 1 / ((l:ℝ) + 1) ≤ 1 := fun l => by
    rw [div_le_one (by positivity)]
    have h0 : (0:ℝ) ≤ (l:ℝ) := Nat.cast_nonneg l
    linarith
  -- the per-scale cell-average Cauchy predicate
  set Q : ℕ → (ℕ → ℕ) → Prop := fun l σ' =>
    ∀ ε' : ℝ, 0 < ε' → ∃ K : ℕ, ∀ j k : ℕ, K ≤ j → K ≤ k →
      ∀ p ∈ winCellFinset n (hscale_pos l),
        ‖(⨍ y in prodGridCell (1 / ((l:ℝ) + 1)) p.1 p.2, fwdFn vSeq (σ' j) y) -
          ⨍ y in prodGridCell (1 / ((l:ℝ) + 1)) p.1 p.2, fwdFn vSeq (σ' k) y‖ < ε'
    with hQdef
  have hQsub : ∀ (l : ℕ) (σ' ρ : ℕ → ℕ), Q l σ' → StrictMono ρ → Q l (σ' ∘ ρ) := by
    intro l σ' ρ hQl hρ ε' hε'
    obtain ⟨K, hK⟩ := hQl ε' hε'
    exact ⟨K, fun j k hj hk => hK (ρ j) (ρ k)
      (le_trans hj hρ.le_apply) (le_trans hk hρ.le_apply)⟩
  have hQtail : ∀ (l N : ℕ) (σ' : ℕ → ℕ), Q l (fun k => σ' (k + N)) → Q l σ' := by
    intro l N σ' hQl ε' hε'
    obtain ⟨M, hM⟩ := hQl ε' hε'
    refine ⟨M + N, fun j k hj hk => ?_⟩
    have hjN : N ≤ j := le_trans (Nat.le_add_left N M) hj
    have hkN : N ≤ k := le_trans (Nat.le_add_left N M) hk
    have hres := hM (j - N) (k - N) (by omega) (by omega)
    simpa [Nat.sub_add_cancel hjN, Nat.sub_add_cancel hkN] using hres
  have hQstep : ∀ (l : ℕ) (σ' : ℕ → ℕ), StrictMono σ' →
      ∃ ρ, StrictMono ρ ∧ Q l (σ' ∘ ρ) := by
    intro l σ' _
    have hbound : ∀ j : ℕ,
        ‖(fun q : ↥(winCellFinset n (hscale_pos l)) =>
          ⨍ y in prodGridCell (1 / ((l:ℝ) + 1)) q.1.1 q.1.2, fwdFn vSeq (σ' j) y)‖
        ≤ Real.sqrt (((1 / ((l:ℝ) + 1)) ^ 4)⁻¹ * (C * ((n:ℝ) + 4))) := by
      intro j
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun q => ?_
      have hsq := fwd_avg_sq_le vSeq C vkin vint vmeas n (σ' j)
        (hscale_pos l) (hscale_le1 l) q.2
      calc ‖⨍ y in prodGridCell (1 / ((l:ℝ) + 1)) q.1.1 q.1.2, fwdFn vSeq (σ' j) y‖
          = Real.sqrt (‖⨍ y in prodGridCell (1 / ((l:ℝ) + 1)) q.1.1 q.1.2,
              fwdFn vSeq (σ' j) y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (((1 / ((l:ℝ) + 1)) ^ 4)⁻¹ * (C * ((n:ℝ) + 4))) :=
            Real.sqrt_le_sqrt hsq
    obtain ⟨ρ, hρ, hcau⟩ := exists_subseq_cauchy_of_bounded_finiteDim
      (fun j (q : ↥(winCellFinset n (hscale_pos l))) =>
        ⨍ y in prodGridCell (1 / ((l:ℝ) + 1)) q.1.1 q.1.2, fwdFn vSeq (σ' j) y)
      (Real.sqrt (((1 / ((l:ℝ) + 1)) ^ 4)⁻¹ * (C * ((n:ℝ) + 4)))) hbound
    refine ⟨ρ, hρ, fun ε' hε' => ?_⟩
    obtain ⟨K, hK⟩ := hcau ε' hε'
    refine ⟨K, fun j k hj hk p hp => ?_⟩
    have hnp := norm_le_pi_norm
      ((fun q : ↥(winCellFinset n (hscale_pos l)) =>
          ⨍ y in prodGridCell (1 / ((l:ℝ) + 1)) q.1.1 q.1.2, fwdFn vSeq (σ' (ρ j)) y) -
        fun q : ↥(winCellFinset n (hscale_pos l)) =>
          ⨍ y in prodGridCell (1 / ((l:ℝ) + 1)) q.1.1 q.1.2, fwdFn vSeq (σ' (ρ k)) y)
      (⟨p, hp⟩ : ↥(winCellFinset n (hscale_pos l)))
    exact lt_of_le_of_lt hnp (hK j k hj hk)
  -- the diagonal
  obtain ⟨σ, hσmono, hσQ⟩ := exists_diagonal_subseq Q hQsub hQtail hQstep
  refine ⟨σ, hσmono, ?_⟩
  intro ε hε
  -- constants
  have hκ0 : (0:ℝ) ≤ volume.real (Metric.closedBall (0 : ℝ × Space) 1) :=
    ENNReal.toReal_nonneg
  set κC := volume.real (Metric.closedBall (0 : ℝ × Space) 1) with hκdef
  have h400κ : (0:ℝ) < 400 * (κC + 1) := by linarith
  have h400Cκ : (0:ℝ) < 400 * (C * κC + 1) := by nlinarith [mul_nonneg hC hκ0]
  set εm := ε / (400 * (κC + 1)) with hεmdef
  have hεmpos : 0 < εm := div_pos hε h400κ
  -- equicontinuity moduli at the fixed horizon `n + 3`
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := wspace ((n:ℝ) + 3) εm hεmpos
  obtain ⟨δ₂, hδ₂, hδ₂b⟩ := wtime ((n:ℝ) + 3) εm hεmpos
  -- the scale choice
  have hdpos : 0 < min δ₁ (min δ₂ (min 1 (ε / (400 * (C * κC + 1))))) :=
    lt_min hδ₁ (lt_min hδ₂ (lt_min one_pos (div_pos hε h400Cκ)))
  obtain ⟨l, hl⟩ := exists_nat_one_div_lt hdpos
  have hQl := hσQ l
  set h := 1 / ((l:ℝ) + 1) with hhdef
  have hh : 0 < h := hscale_pos l
  have hhδ₁ : h < δ₁ := lt_of_lt_of_le hl (min_le_left _ _)
  have hhδ₂ : h < δ₂ :=
    lt_of_lt_of_le hl (le_trans (min_le_right _ _) (min_le_left _ _))
  have hh1 : h ≤ 1 := le_of_lt (lt_of_lt_of_le hl (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hhε : h < ε / (400 * (C * κC + 1)) :=
    lt_of_lt_of_le hl (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- the uniform translation modulus at this scale
  have hmod : ∀ m : ℕ, ∀ k ∈ Metric.closedBall (0 : ℝ × Space) h,
      (∫ z in encW n h, ‖fwdFn vSeq m (z + k) - fwdFn vSeq m z‖ ^ 2)
        ≤ 12 * C * h + 4 * εm := by
    intro m k hk
    have hknorm : ‖k‖ ≤ h := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hk
    have hk1 : |k.1| ≤ h := by
      refine le_trans ?_ hknorm
      simp [Prod.norm_def, Real.norm_eq_abs]
    have hk2 : ‖k.2‖ ≤ h := by
      refine le_trans ?_ hknorm
      simp [Prod.norm_def]
    exact fwd_modulus_encW vSeq C hC vkin vint vmeas n m hh hh1 k hknorm
      (hδ₁b m k.2 (lt_of_le_of_lt hk2 hhδ₁))
      (hδ₂b m k.1 (lt_of_le_of_lt hk1 hhδ₂))
  -- the two outer legs, uniformly over members
  have hcellerr : ∀ m : ℕ,
      (∑ p ∈ winCellFinset n hh, ∫ z in prodGridCell h p.1 p.2,
        ‖fwdFn vSeq m z - ⨍ y in prodGridCell h p.1 p.2, fwdFn vSeq m y‖ ^ 2)
      ≤ κC * (12 * C * h + 4 * εm) := by
    intro m
    have hs := fwd_cellError_sum_le vSeq C vkin vint vmeas n m hh (hmod m)
    rw [volume_real_closedBall_prodSpace hh.le, ← hκdef] at hs
    calc (∑ p ∈ winCellFinset n hh, ∫ z in prodGridCell h p.1 p.2,
        ‖fwdFn vSeq m z - ⨍ y in prodGridCell h p.1 p.2, fwdFn vSeq m y‖ ^ 2)
        ≤ (h ^ 4)⁻¹ * (h ^ 4 * κC * (12 * C * h + 4 * εm)) := hs
      _ = κC * (12 * C * h + 4 * εm) := by
          rw [show (h ^ 4)⁻¹ * (h ^ 4 * κC * (12 * C * h + 4 * εm))
              = ((h ^ 4)⁻¹ * h ^ 4) * (κC * (12 * C * h + 4 * εm)) from by ring,
            inv_mul_cancel₀ (ne_of_gt (by positivity : (0:ℝ) < h ^ 4)), one_mul]
  -- the mid-leg tolerance
  set ε' := Real.sqrt (ε / (12 * (h ^ 4 * ((winCellFinset n hh).card : ℝ) + 1)))
    with hε'def
  have hBpos : (0:ℝ) < 12 * (h ^ 4 * ((winCellFinset n hh).card : ℝ) + 1) := by
    positivity
  have hε'pos : 0 < ε' := Real.sqrt_pos.mpr (div_pos hε hBpos)
  obtain ⟨K, hK⟩ := hQl ε' hε'pos
  refine ⟨K, fun a b ha hb => ?_⟩
  -- the three-leg estimate at this scale
  have hchain := windowError_le_three_legs vSeq C vkin vint vmeas n hh (σ a) (σ b)
  have hS1 := hcellerr (σ a)
  have hS2 := hcellerr (σ b)
  have hSmid : (∑ p ∈ winCellFinset n hh, h ^ 4 *
      ‖(⨍ y in prodGridCell h p.1 p.2, fwdFn vSeq (σ a) y) -
        ⨍ y in prodGridCell h p.1 p.2, fwdFn vSeq (σ b) y‖ ^ 2)
      ≤ ((winCellFinset n hh).card : ℝ) * (h ^ 4 * ε' ^ 2) := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ (h ^ 4 * ε' ^ 2) fun p hp => ?_) ?_
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hK a b ha hb p hp).le 2) (by positivity)
    · rw [nsmul_eq_mul]
  -- the numeric assembly
  have hε'sq : ε' ^ 2 * (12 * (h ^ 4 * ((winCellFinset n hh).card : ℝ) + 1)) = ε := by
    rw [hε'def, Real.sq_sqrt (le_of_lt (div_pos hε hBpos))]
    exact div_mul_cancel₀ ε (ne_of_gt hBpos)
  have hεmeq : εm * (400 * (κC + 1)) = ε := by
    rw [hεmdef]
    exact div_mul_cancel₀ ε (ne_of_gt h400κ)
  have hhlin : h * (400 * (C * κC + 1)) < ε := (lt_div_iff₀ h400Cκ).mp hhε
  have hCκh0 : (0:ℝ) ≤ C * κC * h := mul_nonneg (mul_nonneg hC hκ0) hh.le
  have hfinal : windowError (vSeq (σ a)) (vSeq (σ b)) n < ε :=
    window_budget hchain hS1 hS2 hSmid hε'sq hεmeq hhlin hCκh0 hh.le hεmpos.le
  exact hfinal

/-- **[CERTIFIED — Fischer–Riesz limit extraction; Brezis, *Functional
Analysis*, Springer 2011, Thm 4.8.]**  A sequence of jointly
measurable velocity evolutions that is `L²`-Cauchy on every integer window has
an `L²`-limit on every window, realized by a genuine `VelocityEvolution`.

**Step-0e: the `∀ t` clauses are TRUE for the constructed representative, not
merely a.e.**  An `L²` limit is pinned only off `(t,x)`-null sets, so a bare
"some limit" would leave the slicewise clauses false on a null set of times.
They are recovered by *choosing* the representative
`u t x = lim_k v_{k_j} t x` on the measurable set where a fast subsequence
converges pointwise and `u t x = 0` off it (`MeasureTheory.measurableSet_exists_tendsto`
for the convergence set, `MeasureTheory.StronglyMeasurable.limUnder` for the
representative, which is why `JointlyMeasurable` is needed here too).
With that choice every slice is a pointwise-limit-or-zero, so Fatou gives
`∫ ‖u t‖² ≤ liminf ∫ ‖v_k t‖² ≤ C` and hence integrability **at every `t ≥ 0`**,
the bad times contributing the zero field.

**Proof, as certified.**  The fast subsequence is `φ j = j + ∑_{i ≤ j} N_i`,
where `N_n` is the Cauchy index for window `n` at tolerance `4⁻ⁿ`; `φ` is
strictly monotone and dominates every `N_n` from index `n` on.  Almost-everywhere
convergence on the window `Q_n = (0,n] × B̄(0,n)` comes from Mathlib's Riesz–Fischer
core `MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm` applied to the *shifted*
sequence `j ↦ v_{φ(j+n)}` on `μ.restrict Q_n`, with `B N = 2⁻ᴺ`: the shift is what
makes the controlled-Cauchy hypothesis available at **every** `N`, since indices
`≥ N + n` are controlled on the larger window `Q_{N+n} ⊇ Q_n`.  The full sequence
— not just the fast subsequence — converges to that `u` on each window by Fatou:
`∫_{Q_n} ‖v_k − u‖² ≤ liminf_j ∫_{Q_n} ‖v_k − v_{φ j}‖² ≤ ε/2` for `k` past the
window-`n` Cauchy index, so no second completeness argument is needed. -/
theorem exists_limit_of_forall_windowCauchy
    (vSeq : ℕ → VelocityEvolution) (C : ℝ) (hC : 0 ≤ C)
    (hkin : UniformKineticBound vSeq C)
    (hmeas : JointlyMeasurable vSeq)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖vSeq m t x‖ ^ 2))
    (hcauchy : ∀ n : ℕ, WindowCauchy vSeq n id)
    (B : ℝ) (hB : 0 ≤ B) (hofficial : UniformOfficialKineticBound vSeq B) :
    ∃ u : VelocityEvolution,
      Measurable (fun z : ℝ × Space => u z.1 z.2) ∧
      (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
      (∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ C) ∧
      (∀ t : ℝ, 0 ≤ t → kineticEnergy u t ≤ B) ∧
      (∀ n : ℕ, Filter.Tendsto (fun k => windowError (vSeq k) u n) Filter.atTop (nhds 0)) := by
  classical
  have hbnd : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → (∫ x : Space, ‖vSeq m t x‖ ^ 2) ≤ C :=
    fun m t ht => hkin m t ht
  have hstep : ∀ n : ℕ, ∃ N : ℕ, ∀ j k : ℕ, N ≤ j → N ≤ k →
      windowError (vSeq j) (vSeq k) n < ((4:ℝ)⁻¹) ^ n := by
    intro n
    obtain ⟨N, hN⟩ := hcauchy n (((4:ℝ)⁻¹) ^ n) (by positivity)
    exact ⟨N, fun j k hj hk => hN j k hj hk⟩
  choose Nf hNf using hstep
  set φ : ℕ → ℕ := fun j => j + ∑ i ∈ Finset.range (j+1), Nf i with hφdef
  have hφstrict : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    simp only [hφdef]
    have hs : ∑ i ∈ Finset.range (j+1+1), Nf i = (∑ i ∈ Finset.range (j+1), Nf i) + Nf (j+1) :=
      Finset.sum_range_succ _ _
    omega
  have hφge : ∀ j, Nf j ≤ φ j := by
    intro j
    have hs : Nf j ≤ ∑ i ∈ Finset.range (j+1), Nf i :=
      Finset.single_le_sum (f := Nf) (fun i _ => Nat.zero_le _) (Finset.self_mem_range_succ j)
    simp only [hφdef]; omega
  have hφid : ∀ j, j ≤ φ j := fun j => hφstrict.le_apply
  set g : ℕ → ℝ × Space → Space := fun j z => vSeq (φ j) z.1 z.2 with hgdef
  have hgmeas : ∀ j, Measurable (g j) := fun j => hmeas (φ j)
  set S : Set (ℝ × Space) := {z | ∃ c, Tendsto (fun j => g j z) atTop (𝓝 c)} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_exists_tendsto hgmeas
  set L : ℝ × Space → Space := fun z => limUnder atTop (fun j => g j z) with hLdef
  have hLmeas : Measurable L :=
    (MeasureTheory.StronglyMeasurable.limUnder
      (fun j => (hgmeas j).stronglyMeasurable)).measurable
  set u : VelocityEvolution := fun t x => S.indicator L (t, x) with hudef
  have humeas : Measurable fun z : ℝ × Space => u z.1 z.2 := by
    have he : (fun z : ℝ × Space => u z.1 z.2) = S.indicator L := by
      funext z; simp [hudef]
    rw [he]; exact hLmeas.indicator hSmeas
  have hutend : ∀ z : ℝ × Space, z ∈ S → Tendsto (fun j => g j z) atTop (𝓝 (u z.1 z.2)) := by
    intro z hz
    obtain ⟨c, hc⟩ := hz
    have hv : u z.1 z.2 = c := by
      have hmem : z ∈ S := ⟨c, hc⟩
      simp only [hudef, Prod.mk.eta]
      rw [Set.indicator_of_mem hmem, hLdef]
      exact hc.limUnder_eq
    rw [hv]; exact hc
  have huzero : ∀ z : ℝ × Space, z ∉ S → u z.1 z.2 = 0 := by
    intro z hz
    simp only [hudef, Prod.mk.eta]
    exact Set.indicator_of_notMem hz _
  have hslicemeas : ∀ t : ℝ, Measurable fun x : Space => u t x := fun t =>
    humeas.comp measurable_prodMk_left
  have hFatou : ∀ t : ℝ, 0 ≤ t → ∫⁻ x : Space, ‖u t x‖ₑ ^ 2 ≤ ENNReal.ofReal C := by
    intro t ht
    have hpt : ∀ x : Space, ‖u t x‖ₑ ^ 2
        ≤ atTop.liminf (fun j => ‖vSeq (φ j) t x‖ₑ ^ 2) := by
      intro x
      by_cases hx : (t, x) ∈ S
      · have h1 : Tendsto (fun j => g j (t, x)) atTop (𝓝 (u t x)) := hutend (t, x) hx
        have h2 : Tendsto (fun j => ‖vSeq (φ j) t x‖ₑ ^ 2) atTop (𝓝 (‖u t x‖ₑ ^ 2)) :=
          (continuous_enorm_sq.tendsto _).comp h1
        rw [h2.liminf_eq]
      · rw [huzero (t, x) hx]; simp
    calc ∫⁻ x : Space, ‖u t x‖ₑ ^ 2
        ≤ ∫⁻ x : Space, atTop.liminf (fun j => ‖vSeq (φ j) t x‖ₑ ^ 2) := lintegral_mono hpt
      _ ≤ atTop.liminf (fun j => ∫⁻ x : Space, ‖vSeq (φ j) t x‖ₑ ^ 2) :=
          lintegral_liminf_le (fun j =>
            ((((hmeas (φ j)).comp measurable_prodMk_left)).enorm).pow_const 2)
      _ ≤ ENNReal.ofReal C := by
          refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun j => ?_)
          rw [lintegral_enorm_sq_eq _ (hint (φ j) t ht)]
          exact ENNReal.ofReal_le_ofReal (hbnd (φ j) t ht)
  have huint : ∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2) := by
    intro t ht
    refine ⟨((hslicemeas t).norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have he : ∀ x : Space, ‖(‖u t x‖ ^ 2)‖ₑ = ‖u t x‖ₑ ^ 2 := by
      intro x
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [he]
    exact lt_of_le_of_lt (hFatou t ht) ENNReal.ofReal_lt_top
  have hukin : ∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ C := by
    intro t ht
    have h1 : (∫ x : Space, ‖u t x‖ ^ 2) = (∫⁻ x : Space, ‖u t x‖ₑ ^ 2).toReal := by
      rw [lintegral_enorm_sq_eq (u t) (huint t ht),
        ENNReal.toReal_ofReal (integral_nonneg fun x => by positivity)]
    rw [h1]
    calc (∫⁻ x : Space, ‖u t x‖ₑ ^ 2).toReal ≤ (ENNReal.ofReal C).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hFatou t ht)
      _ = C := ENNReal.toReal_ofReal hC
  -- (B') the *same* Fatou step run against the official Euclidean density, which
  -- transports the exact-constant `kineticEnergy` bound to the limit.  Off the
  -- convergence set `S` the limit is `0`, so the pointwise comparison is trivial
  -- there; on `S` it is continuity of `y ↦ ofReal (officialEuclideanNorm y ^ 2)`.
  have hofficialLimit : ∀ t : ℝ, 0 ≤ t → kineticEnergy u t ≤ B := by
    intro t ht
    have hmeasOff : ∀ j : ℕ,
        Measurable fun x : Space => ENNReal.ofReal (officialEuclideanNorm (vSeq (φ j) t x) ^ 2) :=
      fun j => continuous_official_ofReal_sq.measurable.comp
        ((hmeas (φ j)).comp measurable_prodMk_left)
    have hintOff : ∀ j : ℕ,
        Integrable fun x : Space => officialEuclideanNorm (vSeq (φ j) t x) ^ 2 := by
      intro j
      exact (Navier.Analysis.EnergyNormBridge.integrable_norm_sq_iff_officialEuclideanNorm_sq
        (vSeq (φ j) t)
        (((hmeas (φ j)).comp measurable_prodMk_left).aestronglyMeasurable)).1 (hint (φ j) t ht)
    have huintOff : Integrable fun x : Space => officialEuclideanNorm (u t x) ^ 2 :=
      (Navier.Analysis.EnergyNormBridge.integrable_norm_sq_iff_officialEuclideanNorm_sq
        (u t) (hslicemeas t).aestronglyMeasurable).1 (huint t ht)
    have hpt : ∀ x : Space, ENNReal.ofReal (officialEuclideanNorm (u t x) ^ 2)
        ≤ atTop.liminf
            (fun j => ENNReal.ofReal (officialEuclideanNorm (vSeq (φ j) t x) ^ 2)) := by
      intro x
      by_cases hx : (t, x) ∈ S
      · have h1 : Tendsto (fun j => g j (t, x)) atTop (𝓝 (u t x)) := hutend (t, x) hx
        have h2 : Tendsto
            (fun j => ENNReal.ofReal (officialEuclideanNorm (vSeq (φ j) t x) ^ 2)) atTop
            (𝓝 (ENNReal.ofReal (officialEuclideanNorm (u t x) ^ 2))) :=
          (continuous_official_ofReal_sq.tendsto _).comp h1
        rw [h2.liminf_eq]
      · rw [huzero (t, x) hx]
        simp [officialEuclideanNorm, officialEuclideanPoint]
    have hFatouOff : ENNReal.ofReal (∫ x : Space, officialEuclideanNorm (u t x) ^ 2)
        ≤ ENNReal.ofReal B := by
      rw [ofReal_integral_eq_lintegral_ofReal huintOff
        (Filter.Eventually.of_forall fun x => by positivity)]
      calc ∫⁻ x : Space, ENNReal.ofReal (officialEuclideanNorm (u t x) ^ 2)
          ≤ ∫⁻ x : Space, atTop.liminf
              (fun j => ENNReal.ofReal (officialEuclideanNorm (vSeq (φ j) t x) ^ 2)) :=
            lintegral_mono hpt
        _ ≤ atTop.liminf (fun j => ∫⁻ x : Space,
              ENNReal.ofReal (officialEuclideanNorm (vSeq (φ j) t x) ^ 2)) :=
            lintegral_liminf_le hmeasOff
        _ ≤ ENNReal.ofReal B := by
            refine Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun j => ?_)
            rw [← ofReal_integral_eq_lintegral_ofReal (hintOff j)
              (Filter.Eventually.of_forall fun x => by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [← kineticEnergy_eq_integral_official (vSeq (φ j)) t]
            exact hofficial (φ j) t ht
    rw [kineticEnergy_eq_integral_official u t]
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp hFatouOff
  refine ⟨u, humeas, huint, hukin, hofficialLimit, ?_⟩

  -- (C) almost-everywhere convergence of the fast subsequence on each window
  have hae : ∀ n : ℕ, ∀ᵐ z ∂((volume.prod volume).restrict (winQ n)), z ∈ S := by
    intro n
    have hBsum : ∑' (N : ℕ), ((2:ℝ≥0∞)⁻¹) ^ N ≠ ⊤ := by
      rw [ENNReal.tsum_geometric]; simp
    have hcau : ∀ N j k : ℕ, N ≤ j → N ≤ k →
        eLpNorm ((fun z => g (j + n) z) - (fun z => g (k + n) z)) 2
          ((volume.prod volume).restrict (winQ n)) < ((2:ℝ≥0∞)⁻¹) ^ N := by
      intro N j k hj hk
      refine eLpNorm_two_lt_of_lintegral_lt _ _ ?_
      have hstep1 : ∫⁻ z, ‖((fun z => g (j + n) z) - (fun z => g (k + n) z)) z‖ₑ ^ 2
            ∂((volume.prod volume).restrict (winQ n))
          ≤ ∫⁻ z in winQ (N + n),
              ‖vSeq (φ (j + n)) z.1 z.2 - vSeq (φ (k + n)) z.1 z.2‖ₑ ^ 2
              ∂(volume.prod volume) := by
        refine lintegral_mono' (Measure.restrict_mono (winQ_mono (Nat.le_add_left _ _)) le_rfl) ?_
        intro z
        simp [hgdef]
      have hstep2 : ∫⁻ z in winQ (N + n),
            ‖vSeq (φ (j + n)) z.1 z.2 - vSeq (φ (k + n)) z.1 z.2‖ₑ ^ 2 ∂(volume.prod volume)
          = ENNReal.ofReal (windowError (vSeq (φ (j + n))) (vSeq (φ (k + n))) (N + n)) :=
        lintegral_winQ_eq _ _ _ C (hmeas _) (hmeas _) (hint _) (hint _) (hbnd _) (hbnd _)
      have hidx : ∀ i : ℕ, N ≤ i → Nf (N + n) ≤ φ (i + n) := by
        intro i hi
        exact le_trans (hφge (N + n)) (hφstrict.monotone (by omega))
      have hlt : windowError (vSeq (φ (j + n))) (vSeq (φ (k + n))) (N + n)
          < ((4:ℝ)⁻¹) ^ N := by
        refine lt_of_lt_of_le (hNf (N + n) _ _ (hidx j hj) (hidx k hk)) ?_
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
      calc ∫⁻ z, ‖((fun z => g (j + n) z) - (fun z => g (k + n) z)) z‖ₑ ^ 2
            ∂((volume.prod volume).restrict (winQ n))
          ≤ ENNReal.ofReal (windowError (vSeq (φ (j + n))) (vSeq (φ (k + n))) (N + n)) := by
            rw [← hstep2]; exact hstep1
        _ < ENNReal.ofReal (((4:ℝ)⁻¹) ^ N) := by
            exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hlt
        _ = (((2:ℝ≥0∞)⁻¹) ^ N) ^ 2 := ofReal_quarter_pow N
    have hres := MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm
      (μ := (volume.prod volume).restrict (winQ n)) (p := 2)
      (f := fun j => g (j + n)) (fun j => (hgmeas (j + n)).aestronglyMeasurable)
      (by norm_num) hBsum hcau
    filter_upwards [hres] with z hz
    obtain ⟨l, hl⟩ := hz
    exact ⟨l, (Filter.tendsto_add_atTop_iff_nat n).mp hl⟩
  -- (D) the full sequence converges to `u` on every window
  intro n
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy n (ε / 2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hnn := windowError_nonneg (vSeq k) u n
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have key : ENNReal.ofReal (windowError (vSeq k) u n) ≤ ENNReal.ofReal (ε / 2) := by
    rw [← lintegral_winQ_eq (vSeq k) u n C (hmeas k) humeas (hint k) huint (hbnd k) hukin]
    have hcongr : ∫⁻ z in winQ n, ‖vSeq k z.1 z.2 - u z.1 z.2‖ₑ ^ 2 ∂(volume.prod volume)
        = ∫⁻ z in winQ n,
            atTop.liminf (fun j => ‖vSeq k z.1 z.2 - g j z‖ₑ ^ 2) ∂(volume.prod volume) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae n] with z hz
      have h1 : Tendsto (fun j => g j z) atTop (𝓝 (u z.1 z.2)) := hutend z hz
      have h2 : Tendsto (fun j => ‖vSeq k z.1 z.2 - g j z‖ₑ ^ 2) atTop
          (𝓝 (‖vSeq k z.1 z.2 - u z.1 z.2‖ₑ ^ 2)) :=
        (continuous_enorm_sq.tendsto _).comp (tendsto_const_nhds.sub h1)
      exact (h2.liminf_eq).symm
    rw [hcongr]
    refine le_trans (lintegral_liminf_le
      (fun j => ((((hmeas k).sub (hgmeas j))).enorm).pow_const 2)) ?_
    refine Filter.liminf_le_of_frequently_le'
      ((eventually_ge_atTop N).frequently.mono fun j hj => ?_)
    have hcalc : ∫⁻ z in winQ n, ‖vSeq k z.1 z.2 - g j z‖ₑ ^ 2 ∂(volume.prod volume)
        = ENNReal.ofReal (windowError (vSeq k) (vSeq (φ j)) n) := by
      have := lintegral_winQ_eq (vSeq k) (vSeq (φ j)) n C (hmeas k) (hmeas _) (hint k)
        (hint _) (hbnd k) (hbnd _)
      rw [← this]
    rw [hcalc]
    exact ENNReal.ofReal_le_ofReal
      (le_of_lt (hN k (φ j) hk (le_trans hj (hφid j))))
  have hle : windowError (vSeq k) u n ≤ ε / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp key
  linarith

end FischerRiesz

/-- **[CERTIFIED — Aubin–Lions–Simon compactness, Pattern-A repaired
statement; Aubin (*C. R. Acad. Sci.* **256**, 1963); Lions (*Quelques méthodes de
résolution des problèmes aux limites non linéaires*, Dunod 1969, Ch. 1 §5);
Simon ("Compact sets in `L^p(0,T;B)`", *Ann. Mat. Pura Appl.* **146** (1987)
65–96, Thm 1); Temam, *Navier–Stokes Equations*, AMS Chelsea 2001, III.2.3;
Brezis, *Functional Analysis*, Springer 2011, Thm 4.26 + Cor 4.27.]**  A sequence
bounded in `L^∞_t L²_x`, uniformly equicontinuous under **both** time and space
translations, jointly `(t,x)`-measurable and slicewise square-integrable, has a
subsequence converging strongly in `L²(0,T; L²_loc)` to a jointly measurable,
slicewise square-integrable limit.  This is the Mathlib-absent compact-embedding
core: Mathlib has Banach–Alaoglu (weak-* compactness) but neither the Aubin–Lions
embedding `{u ∈ L²(H¹) : ∂ₜu ∈ L²(H⁻¹)} ↪↪ L²(L²)` nor the
Riesz–Fréchet–Kolmogorov criterion it rests on.

## Pattern-A repair (this wave): the previous hypothesis list was FALSE as stated

The earlier version asked for **spatial** compactness out of
`UniformEnstrophyBound` alone.  Two independent checked defects; both are removed
here by *adding* a hypothesis, never by weakening the conclusion.

* **(H-space) was missing.**  `enstrophy` integrates `‖curl u‖²`, and nothing in
  the bundle forces `uSeq` to be divergence-free, so the identity
  `‖ω‖_{L²} = ‖∇u‖_{L²}` — the only route from enstrophy to an `H¹` bound — is
  unavailable.  Falsifying family: `u_m = ∇(m⁻¹ cos(m x₀) χ)`, `χ = e^{−|x|²}`.
  Its curl vanishes identically by Clairaut, so `UniformEnstrophyBound u_m 0`
  holds; it is `L²`-bounded; it is time-independent, so `TimeEquicontinuous`
  holds with a `0` integrand; and it has **no** `L²_loc`-Cauchy subsequence.
  Checked numerically (`experiments/aubin_lions_curlfree_witness.py`, part (1)):
  `‖u_m‖² → 0.6267 = ½∫χ²` while `‖u_m − u_{2m}‖² → 1.2533` for `m ≥ 8`; part (2)
  checks `curl ∇ψ = 0` to `2.8e-13` in 3-D.  `SpaceEquicontinuous` excludes
  exactly this family: part (3) exhibits shifts `y = (π/m,0,0)` with `‖y‖ → 0`
  along which the translation error stays at `≈ 2∫χ² = 2.507`, so no `δ` works.
  Part (4) checks a non-oscillating family *does* satisfy it, so the added
  hypothesis is not vacuous; `aubinLions_zero_instance` certifies the same in
  Lean.
* **(H-meas) was missing.**  `VelocityEvolution` is the bare function type
  `ℝ → Space → Space`, so no `t`-integral in the conclusion had any integrability
  behind it and every one of them could silently be the Bochner junk value `0`.
  `strongL2LocLimit_of_natWindows` (CERTIFIED above) is precisely the bookkeeping
  step that was unreachable without it, and is now proved.

Adding these two hypotheses is the *correct* repair rather than a weakening: the
old statement was false, so any proof of it would have been a proof of a
falsehood.  Note the binder `_hens`: the enstrophy bound is kept for signature
continuity with the classical statement and with
`GalerkinApproximation.enstrophy_bounded`, but the repaired assembly never
consumes it, and neither does Riesz–Fréchet–Kolmogorov on a bounded window.
That unused binder *is* the falsification, made visible in the signature: on
this hypothesis bundle `enstrophy` does no compactness work at all.  The conclusion is simultaneously **strengthened** with joint
measurability of the limit, which the Riesz–Fischer construction supplies for
free and which every downstream consumer needs in order to integrate against the
limit at all.  A second, earlier strengthening is retained: the limit is
slicewise square-integrable (`IsLerayHopfWeakSolution` has a `square_integrable`
field, and without the clause `StrongL2LocLimit uSeq u` alone is satisfiable by a
limit for which every error integral is a Bochner integral of a non-integrable
function).

## Certified support, and what remains

`enstrophy` is additionally blind to non-differentiability —
`enstrophy_stepField_eq_zero` (CERTIFIED above) is a discontinuous field with
enstrophy exactly `0` — so no repair routed through `enstrophy` could work; the
hypothesis had to be added at the translation level, which is what Simon (1987)
actually assumes.  `TimeEquicontinuous` is likewise load-bearing and does its job
(the family `u_m(t,x) = sin(m t)·w(x)` meets the kinetic and enstrophy bounds, has
no strong `L²_loc` limit, and is excluded exactly by it).

The route, all four steps now certified: **(i)+(ii)** Riesz–Fréchet–Kolmogorov
total boundedness on the single window `(0,n] × B̄(0,n)` from (H-space) +
(H-time) + the `L²` bound, giving an `L²`-Cauchy refinement of any subsequence
(`exists_subseq_windowCauchy`, CERTIFIED above)
[Brezis Thm 4.26 + Cor 4.27; Simon Thm 1]; **(iii)** the nested
Cantor diagonal over the countable exhaustion — `exists_diagonal_subseq` /
`exists_subseq_forall_window_tendsto` (CERTIFIED in
`Navier.Analysis.RieszKolmogorov`), with
`StrongL2LocLimit.comp_strictMono` for the bookkeeping; **(iv)** Riesz–Fischer
(`exists_limit_of_forall_windowCauchy`, CERTIFIED above): an `L²`-Cauchy sequence
of jointly measurable fields has a jointly measurable pointwise-a.e. limit with
vanishing window errors, slicewise square-integrable by Fatou [Brezis Thm 4.8];
then `strongL2LocLimit_of_natWindows`
(CERTIFIED above) turns the integer windows into the real ones. -/
theorem aubin_lions_l2loc_compactness
    (uSeq : ℕ → VelocityEvolution) (C : ℝ) (hC : 0 ≤ C)
    (hkin : UniformKineticBound uSeq C) (_hens : UniformEnstrophyBound uSeq C)
    (htime : TimeEquicontinuous uSeq) (hspace : SpaceEquicontinuous uSeq)
    (hmeas : JointlyMeasurable uSeq)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (B : ℝ) (hB : 0 ≤ B) (hofficial : UniformOfficialKineticBound uSeq B) :
    ∃ (u : VelocityEvolution) (σ : ℕ → ℕ), StrictMono σ ∧
      Measurable (fun z : ℝ × Space => u z.1 z.2) ∧
      (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
      (∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ C) ∧
      (∀ t : ℝ, 0 ≤ t → kineticEnergy u t ≤ B) ∧
      StrongL2LocLimit (fun k => uSeq (σ k)) u := by
  obtain ⟨σ, hσ, hσC⟩ := exists_subseq_forall_windowCauchy uSeq
    fun n τ hτ => exists_subseq_windowCauchy uSeq C hC hkin htime hspace hmeas hint n τ hτ
  have hmeas' : JointlyMeasurable (fun k => uSeq (σ k)) := fun k => hmeas (σ k)
  have hint' : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      Integrable (fun x : Space => ‖uSeq (σ m) t x‖ ^ 2) := fun m t ht => hint (σ m) t ht
  have hkin' : UniformKineticBound (fun k => uSeq (σ k)) C := fun m t ht => hkin (σ m) t ht
  have hoff' : UniformOfficialKineticBound (fun k => uSeq (σ k)) B :=
    fun m t ht => hofficial (σ m) t ht
  obtain ⟨u, humeas, huint, hukin, huoff, huwin⟩ :=
    exists_limit_of_forall_windowCauchy (fun k => uSeq (σ k)) C hC hkin' hmeas' hint'
      (fun n => hσC n) B hB hoff'
  refine ⟨u, σ, hσ, humeas, huint, hukin, huoff,
    strongL2LocLimit_of_natWindows (fun k => uSeq (σ k)) u C hmeas' humeas hint' huint
      hkin' hukin huwin⟩

/-!
### Initial-slice patching (certified)

The compactness step produces a limit that is controlled only for `t > 0` (the
time integrals in `StrongL2LocLimit` and in the weak form never see the single
instant `t = 0`), whereas `IsLerayHopfWeakSolution.initial_attained` asks for
*pointwise* attainment at `t = 0`.  The gap is closed by redefining the limit on
the null set `{0}`: `patchInitial` does that, and
`isLerayHopfWeakSolution_patchInitial` certifies that the patch changes neither
the weak form (`setIntegral_Ici_congr_off_zero`: the time integral over
`Set.Ici 0` does not see `{0}`) nor the energy bound, while supplying
`initial_attained` by construction.
-/

/-- The weak-form test density `⟨u, ∂ₜφ + (u·∇)φ + νΔφ⟩` (the integrand of the
Leray–Hopf weak form). -/
def weakPairingDensity (ν : ℝ) (u : VelocityEvolution) (φ : DivergenceFreeTestFunction)
    (t : ℝ) (x : Space) : ℝ :=
  officialInner (u t x)
    (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
      spatialDerivative (fun s => (φ.field s : Space → Space)) t x (u t x) +
      ν • laplacian (fun s => (φ.field s : Space → Space)) t x)

/-- Redefinition of a velocity evolution at the single instant `t = 0`. -/
def patchInitial (u : VelocityEvolution) (u₀ : SchwartzVelocity) : VelocityEvolution :=
  fun t x => if t = 0 then u₀ x else u t x

theorem patchInitial_apply_zero (u : VelocityEvolution) (u₀ : SchwartzVelocity) :
    patchInitial u u₀ 0 = fun x => u₀ x := by
  funext x; simp [patchInitial]

theorem patchInitial_apply_of_ne (u : VelocityEvolution) (u₀ : SchwartzVelocity) {t : ℝ}
    (ht : t ≠ 0) : patchInitial u u₀ t = u t := by
  funext x; simp [patchInitial, ht]

/-- **The time integral over `Set.Ici 0` does not see the instant `0`.**  Two
integrands agreeing off `{0}` have the same integral (`{0}` is Lebesgue-null).
This is what makes the initial-slice patch invisible to the weak form. -/
theorem setIntegral_Ici_congr_off_zero {F G : ℝ → ℝ} (h : ∀ t : ℝ, t ≠ 0 → F t = G t) :
    ∫ t in Set.Ici (0:ℝ), F t = ∫ t in Set.Ici (0:ℝ), G t := by
  refine setIntegral_congr_ae measurableSet_Ici ?_
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {a : ℝ | ¬ a ≠ 0} = {(0:ℝ)} := by ext t; simp
    rw [hset]; simp
  filter_upwards [h0] with t ht _ using h t ht

/-- **Leray limit data**: what the compactness + limit-passage step produces —
a velocity evolution satisfying the Leray–Hopf clauses for **positive** times
only (the limit of an `L²`-convergent subsequence is pinned only off null sets),
together with the datum-side integrability at `t = 0`.  Non-vacuous:
`zeroLerayLimitData` inhabits it at the zero datum. -/
structure LerayLimitData (ν : ℝ) (u₀ : SchwartzVelocity) where
  /-- The limit velocity evolution. -/
  limit : VelocityEvolution
  /-- Slicewise square-integrability for positive times. -/
  sq_integrable : ∀ t : ℝ, 0 < t → Integrable (fun x : Space => ‖limit t x‖ ^ 2)
  /-- The datum is square-integrable (automatic for Schwartz data). -/
  datum_sq_integrable : Integrable (fun x : Space => ‖u₀ x‖ ^ 2)
  /-- The Leray energy bound for positive times.  Both sides are the Euclidean
  (Fefferman) energy: `kineticEnergy` integrates `∑ᵢ uᵢ²`, so the datum side is
  `∫ ∑ᵢ (u₀)ᵢ²` and not the inherited sup-norm mass `∫ ‖u₀‖²`.  Mixing the two
  would compare different quantities, since `Space` carries the product
  (supremum) norm. -/
  energy_le : ∀ t : ℝ, 0 < t →
    kineticEnergy limit t ≤ ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2
  /-- Integrability of the weak-form density for positive times. -/
  pairing_integrable : ∀ (φ : DivergenceFreeTestFunction) (t : ℝ), 0 < t →
    Integrable (fun x : Space => weakPairingDensity ν limit φ t x)
  /-- Integrability of the weak-form density of the datum slice. -/
  datum_pairing_integrable : ∀ φ : DivergenceFreeTestFunction,
    Integrable (fun x : Space => weakPairingDensity ν (fun _ y => u₀ y) φ 0 x)
  /-- The Leray–Hopf weak form. -/
  weak_form : ∀ φ : DivergenceFreeTestFunction,
    (∫ t in Set.Ici (0:ℝ), ∫ x : Space, weakPairingDensity ν limit φ t x) =
      -(∫ x : Space, officialInner (u₀ x) ((φ.field 0) x))

/-- **Transport: patched limit data is a Leray–Hopf weak solution.**  The patch
supplies `initial_attained` by construction; `square_integrable`,
`energy_nonincreasing` and `pairing_integrable` split on `t = 0` (datum side)
versus `t > 0` (limit side); and `weak_form` is unchanged because the time
integral over `Set.Ici 0` ignores the null set `{0}`
(`setIntegral_Ici_congr_off_zero`).  Note `kineticEnergy (patch) 0 = ‖u₀‖²_{L²}`,
so the record's `energy_le` field is exactly Leray's energy inequality. -/
theorem isLerayHopfWeakSolution_patchInitial (ν : ℝ) (u₀ : SchwartzVelocity)
    (D : LerayLimitData ν u₀) :
    IsLerayHopfWeakSolution ν u₀ (patchInitial D.limit u₀) where
  square_integrable := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, patchInitial_apply_zero]; exact D.datum_sq_integrable
    · rw [patchInitial_apply_of_ne _ _ (ne_of_gt h)]; exact D.sq_integrable t h
  initial_attained := by intro x; simp [patchInitial]
  energy_nonincreasing := by
    intro t ht
    have h0 : kineticEnergy (patchInitial D.limit u₀) 0 =
        ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 := by
      unfold kineticEnergy; rw [patchInitial_apply_zero]
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]
    · rw [h0]
      have hslice : kineticEnergy (patchInitial D.limit u₀) t = kineticEnergy D.limit t := by
        unfold kineticEnergy; rw [patchInitial_apply_of_ne _ _ (ne_of_gt h)]
      rw [hslice]; exact D.energy_le t h
  pairing_integrable := by
    intro φ t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]
      have hcong : (fun x : Space => weakPairingDensity ν (patchInitial D.limit u₀) φ 0 x)
          = fun x : Space => weakPairingDensity ν (fun _ y => u₀ y) φ 0 x := by
        funext x; unfold weakPairingDensity; rw [patchInitial_apply_zero]
      have hres := D.datum_pairing_integrable φ
      rw [← hcong] at hres
      exact hres
    · have hcong : (fun x : Space => weakPairingDensity ν (patchInitial D.limit u₀) φ t x)
          = fun x : Space => weakPairingDensity ν D.limit φ t x := by
        funext x; unfold weakPairingDensity; rw [patchInitial_apply_of_ne _ _ (ne_of_gt h)]
      have hres := D.pairing_integrable φ t h
      rw [← hcong] at hres
      exact hres
  weak_form := by
    intro φ
    have hcong : ∀ t : ℝ, t ≠ 0 →
        (∫ x : Space, weakPairingDensity ν (patchInitial D.limit u₀) φ t x)
          = ∫ x : Space, weakPairingDensity ν D.limit φ t x := by
      intro t ht
      congr 1; funext x; unfold weakPairingDensity; rw [patchInitial_apply_of_ne _ _ ht]
    have hint := setIntegral_Ici_congr_off_zero hcong
    show (∫ t in Set.Ici (0:ℝ), ∫ x : Space,
      weakPairingDensity ν (patchInitial D.limit u₀) φ t x) = _
    rw [hint]
    exact D.weak_form φ

/-- **Consumer-instantiability smoke (anti-vacuity, B-Audit-8).**  `LerayLimitData`
is inhabited at the zero datum by the zero evolution, so the transport above and
the residual below are not vacuous obligations. -/
def zeroLerayLimitData (ν : ℝ) : LerayLimitData ν (0 : SchwartzVelocity) where
  limit := fun _ _ => 0
  sq_integrable := by
    intro t _
    exact (integrable_zero Space ℝ volume).congr (Filter.Eventually.of_forall fun x => by simp)
  datum_sq_integrable :=
    (integrable_zero Space ℝ volume).congr (Filter.Eventually.of_forall fun x => by simp)
  energy_le := by intro t _; simp [kineticEnergy]
  pairing_integrable := by
    intro φ t _
    refine (integrable_zero Space ℝ volume).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [weakPairingDensity, officialInner_zero_left]
  datum_pairing_integrable := by
    intro φ
    refine (integrable_zero Space ℝ volume).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [weakPairingDensity, officialInner_zero_left]
  weak_form := by
    intro φ
    simp [weakPairingDensity, officialInner_zero_left]

/-- **The datum energy in Fefferman's Euclidean form is nonnegative.**  The
right-hand side of `LerayLimitData.energy_le`, needed as the constant fed to the
compactness step. -/
theorem datumOfficialEnergy_nonneg (u₀ : SchwartzVelocity) :
    0 ≤ ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2 :=
  integral_nonneg fun x => by positivity

/-- **[CERTIFIED — audit item (0) of `exists_lerayLimitData`, discharged.]**  From
a Galerkin approximation, the compactness step produces a strong `L²_loc` limit
that is jointly measurable, slicewise square-integrable, and satisfies the Leray
energy inequality **at the exact datum constant**
`kineticEnergy u t ≤ ∫ ∑ᵢ (u₀)ᵢ²` — Fefferman's Euclidean energy clause, not a
constant-degraded surrogate.

**What was actually missing, and what fixed it.**  An earlier revision of the
`exists_lerayLimitData` docstring recorded item (0) as "add `bound_le : bound ≤
∫ ‖u₀‖²` to the two Galerkin structures, then `energy_le` is immediate".  Both
halves of that were wrong.  `bound_le` was already present, and
`aubin_lions_l2loc_compactness` already re-exported the kinetic conjunct — yet
`energy_le` still did not follow, because `UniformKineticBound` and `bound_le`
both live in the inherited **sup** norm on `Space = Fin 3 → ℝ` while
`kineticEnergy` is the **Euclidean** `∫ ∑ᵢ uᵢ²`.  Routing the sup bound through
`EnergyNormBridge` gives `kineticEnergy u t ≤ 3 ∫ ∑ᵢ (u₀)ᵢ²`: the dimension
factor `3` is irreducible on that hypothesis bundle, and no amount of extra
sup-norm bookkeeping removes it.  The repair is therefore to carry the Euclidean
bound as data — `GalerkinApproximation.official_kinetic_bounded`, true with the
exact constant in the finite-mode construction — and to transport it through
Fischer–Riesz by the same Fatou step that transports the sup-norm bound
(the `hofficialLimit` block of `exists_limit_of_forall_windowCauchy`).

With this theorem, `LerayLimitData.sq_integrable`, `datum_sq_integrable` and
`energy_le` are all discharged for the compactness limit, and the residue of
`exists_lerayLimitData` is exactly the three weak-form clauses — which is what
`exists_lerayLimitData_of_weakClauses` below makes formal. -/
theorem exists_galerkinLimit_energy_le (ν : ℝ) (u₀ : SchwartzVelocity)
    (G : GalerkinApproximation ν u₀) :
    ∃ (u : VelocityEvolution) (σ : ℕ → ℕ), StrictMono σ ∧
      Measurable (fun z : ℝ × Space => u z.1 z.2) ∧
      (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
      (∀ t : ℝ, 0 ≤ t → kineticEnergy u t ≤ ∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2) ∧
      StrongL2LocLimit (fun k => G.approx (σ k)) u := by
  let Cmax := max G.bound G.enstrophyBound
  have hCmax_nonneg : 0 ≤ Cmax :=
    le_max_of_le_left G.bound_nonneg
  have hkin_max : UniformKineticBound G.approx Cmax := by
    intro m t ht
    exact le_trans (G.kinetic_bounded m t ht) (le_max_left _ _)
  have hens_max : UniformEnstrophyBound G.approx Cmax := by
    intro m T hT
    exact le_trans (G.enstrophy_bounded m T hT) (le_max_right _ _)
  obtain ⟨u, σ, hσ, humeas, huint, _hukin, huoff, hlim⟩ :=
    aubin_lions_l2loc_compactness G.approx Cmax hCmax_nonneg hkin_max
      hens_max G.time_equicontinuous G.space_equicontinuous
      G.jointly_measurable G.sq_integrable
      (∫ x : Space, ∑ i : Fin 3, (u₀ x i) ^ 2) (datumOfficialEnergy_nonneg u₀)
      G.official_kinetic_bounded
  exact ⟨u, σ, hσ, humeas, huint, huoff, hlim⟩

/-!
### Pairing-side integrability from the certified Schwartz time derivative

The weak-pairing density splits as `⟨u, ∂ₜφ⟩ + ⟨u, (∇φ)(u)⟩ + ν⟨u, Δφ⟩`.  The
two *spatial* factors are derivatives of the Schwartz slice `φ.field t`, hence
Schwartz themselves (`SchwartzMap.fderivCLM` composed with `evalCLM`).  The
repaired test interface also carries the genuine time derivative as a Schwartz
slice.  Thus all three pairings are integrable against any measurable
square-integrable velocity slice by Cauchy–Schwarz.
-/

/-- Coordinatewise Cauchy–Schwarz for the official pairing against the ambient
sup norm: `|⟨x, y⟩| ≤ 3‖x‖‖y‖`.  The factor `3` is the dimension, and it is
attained (constant vectors), so this is the sharp sup-norm form. -/
theorem abs_officialInner_le_three (x y : Space) :
    |officialInner x y| ≤ 3 * (‖x‖ * ‖y‖) := by
  rw [officialInner_eq_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hb : ∀ i : Fin 3, |x i * y i| ≤ ‖x‖ * ‖y‖ := by
    intro i
    rw [abs_mul]
    have hx : |x i| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    have hy : |y i| ≤ ‖y‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
    exact mul_le_mul hx hy (abs_nonneg _) (norm_nonneg _)
  calc (∑ i : Fin 3, |x i * y i|) ≤ ∑ _i : Fin 3, ‖x‖ * ‖y‖ :=
      Finset.sum_le_sum fun i _ => hb i
    _ = 3 * (‖x‖ * ‖y‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

private theorem measurable_officialInner_comp
    {α : Type*} [MeasurableSpace α] {u w : α → Space}
    (hu : Measurable u) (hw : Measurable w) :
    Measurable fun x : α => officialInner (u x) (w x) := by
  have heq : (fun x : α => officialInner (u x) (w x))
      = fun x : α => ∑ i : Fin 3, u x i * w x i := by
    funext x
    rw [officialInner_eq_sum]
  rw [heq]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hu).mul ((measurable_pi_apply i).comp hw)

/-- **Cauchy–Schwarz for the official pairing**: the pairing of two measurable
square-integrable fields is integrable. -/
theorem integrable_officialInner_pairing {u w : Space → Space}
    (hu : Measurable u) (hw : Measurable w)
    (hu2 : Integrable fun x : Space => ‖u x‖ ^ 2)
    (hw2 : Integrable fun x : Space => ‖w x‖ ^ 2) :
    Integrable fun x : Space => officialInner (u x) (w x) := by
  refine ((hu2.const_mul (3/2)).add (hw2.const_mul (3/2))).mono'
    (measurable_officialInner_comp hu hw).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  have h1 := abs_officialInner_le_three (u x) (w x)
  nlinarith [sq_nonneg (‖u x‖ - ‖w x‖), norm_nonneg (u x), norm_nonneg (w x)]

/-- **Quantitative Cauchy–Young bound for the official pairing.**  This is the
majorant form of `integrable_officialInner_pairing`: it bounds the spatial
integral by the two squared `L²` masses with the sharp ambient-coordinate
factor inherited from `abs_officialInner_le_three`. -/
theorem abs_integral_officialInner_le_three_halves {u w : Space → Space}
    (hu : Measurable u) (hw : Measurable w)
    (hu2 : Integrable fun x : Space => ‖u x‖ ^ 2)
    (hw2 : Integrable fun x : Space => ‖w x‖ ^ 2) :
    |∫ x : Space, officialInner (u x) (w x)| ≤
      (3 / 2 : ℝ) * ((∫ x : Space, ‖u x‖ ^ 2) + ∫ x : Space, ‖w x‖ ^ 2) := by
  have hp := integrable_officialInner_pairing hu hw hu2 hw2
  have hm : Integrable fun x : Space =>
      (3 / 2 : ℝ) * ‖u x‖ ^ 2 + (3 / 2 : ℝ) * ‖w x‖ ^ 2 :=
    (hu2.const_mul (3 / 2)).add (hw2.const_mul (3 / 2))
  calc
    |∫ x : Space, officialInner (u x) (w x)|
        ≤ ∫ x : Space, |officialInner (u x) (w x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x : Space,
        ((3 / 2 : ℝ) * ‖u x‖ ^ 2 + (3 / 2 : ℝ) * ‖w x‖ ^ 2) := by
      apply integral_mono hp.abs hm
      intro x
      have h := abs_officialInner_le_three (u x) (w x)
      nlinarith [sq_nonneg (‖u x‖ - ‖w x‖), norm_nonneg (u x), norm_nonneg (w x)]
    _ = (3 / 2 : ℝ) * ((∫ x : Space, ‖u x‖ ^ 2) +
        ∫ x : Space, ‖w x‖ ^ 2) := by
      rw [integral_add (hu2.const_mul (3 / 2)) (hw2.const_mul (3 / 2)),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      ring

/-- The directional spatial derivative of a Schwartz slice, as a Schwartz map
(Mathlib's `fderivCLM` composed with `evalCLM`). -/
private noncomputable def schwartzDirDeriv (f : SchwartzVelocity) (v : Space) :
    SchwartzVelocity :=
  SchwartzMap.evalCLM ℝ Space Space v (SchwartzMap.fderivCLM ℝ Space Space f)

private theorem schwartzDirDeriv_apply (f : SchwartzVelocity) (v x : Space) :
    schwartzDirDeriv f v x = fderiv ℝ (⇑f) x v := by
  simp [schwartzDirDeriv]

/-- **The convection pairing is integrable**: `⟨u, (∇φ)(u)⟩ ≤ 3M‖u‖²` with `M`
the global operator-norm bound of the Schwartz slice's derivative. -/
theorem integrable_convection_pairing (f : SchwartzVelocity) {u : Space → Space}
    (hu : Measurable u) (hu2 : Integrable fun x : Space => ‖u x‖ ^ 2) :
    Integrable fun x : Space => officialInner (u x) (fderiv ℝ (⇑f) x (u x)) := by
  have hM : ∀ x : Space, ‖fderiv ℝ (⇑f) x‖ ≤ (SchwartzMap.seminorm ℝ 0 1) f := by
    intro x
    have h1 := f.norm_iteratedFDeriv_le_seminorm ℝ 1 x
    rwa [norm_iteratedFDeriv_one] at h1
  have happly : Continuous fun p : (Space →L[ℝ] Space) × Space => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  have hfc : Continuous fun x : Space => fderiv ℝ (⇑f) x :=
    (f.smooth ⊤).continuous_fderiv (by simp)
  have hcont2 : Continuous fun q : Space × Space => fderiv ℝ (⇑f) q.1 q.2 :=
    happly.comp (hfc.prodMap continuous_id)
  have hwmeas : Measurable fun x : Space => fderiv ℝ (⇑f) x (u x) :=
    hcont2.measurable.comp (measurable_id.prodMk hu)
  refine (hu2.const_mul (3 * (SchwartzMap.seminorm ℝ 0 1) f)).mono'
    (measurable_officialInner_comp hu hwmeas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_officialInner_le_three (u x) (fderiv ℝ (⇑f) x (u x))
  have h2 : ‖fderiv ℝ (⇑f) x (u x)‖ ≤ (SchwartzMap.seminorm ℝ 0 1) f * ‖u x‖ :=
    le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  have h3 : ‖u x‖ * ‖fderiv ℝ (⇑f) x (u x)‖
      ≤ ‖u x‖ * ((SchwartzMap.seminorm ℝ 0 1) f * ‖u x‖) :=
    mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  nlinarith [h1, h3]

/-- **Quantitative convection majorant at one time slice.**  The quadratic
weak-form leg is controlled by the velocity's squared `L²` mass times the
first Schwartz derivative seminorm of the test slice.  Unlike mere
integrability, this inequality exposes the exact scalar that the remaining
compact-time argument must bound uniformly before dominated convergence.

-- Citation: Leray (1934), §§21–23; Temam, Navier–Stokes Equations, III.3.3. -/
theorem abs_integral_convection_pairing_le (f : SchwartzVelocity)
    {u : Space → Space} (hu : Measurable u)
    (hu2 : Integrable fun x : Space => ‖u x‖ ^ 2) :
    |∫ x : Space, officialInner (u x) (fderiv ℝ (⇑f) x (u x))| ≤
      3 * (SchwartzMap.seminorm ℝ 0 1) f * ∫ x : Space, ‖u x‖ ^ 2 := by
  let M : ℝ := (SchwartzMap.seminorm ℝ 0 1) f
  have hM : ∀ x : Space, ‖fderiv ℝ (⇑f) x‖ ≤ M := by
    intro x
    have h1 := f.norm_iteratedFDeriv_le_seminorm ℝ 1 x
    rwa [norm_iteratedFDeriv_one] at h1
  have hpair := integrable_convection_pairing f hu hu2
  have hmaj : Integrable fun x : Space => (3 * M) * ‖u x‖ ^ 2 :=
    hu2.const_mul (3 * M)
  calc
    |∫ x : Space, officialInner (u x) (fderiv ℝ (⇑f) x (u x))|
        ≤ ∫ x : Space, |officialInner (u x) (fderiv ℝ (⇑f) x (u x))| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : Space, (3 * M) * ‖u x‖ ^ 2 := by
      apply integral_mono hpair.abs hmaj
      intro x
      have h1 := abs_officialInner_le_three (u x) (fderiv ℝ (⇑f) x (u x))
      have h2 : ‖fderiv ℝ (⇑f) x (u x)‖ ≤ M * ‖u x‖ :=
        le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
      have h3 : ‖u x‖ * ‖fderiv ℝ (⇑f) x (u x)‖ ≤
          ‖u x‖ * (M * ‖u x‖) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      nlinarith
    _ = 3 * (SchwartzMap.seminorm ℝ 0 1) f *
        ∫ x : Space, ‖u x‖ ^ 2 := by
      rw [MeasureTheory.integral_const_mul]

/-- The quantitative convection estimate consumed at the Galerkin energy
level: any certified squared `L²` bound `E` gives the corresponding scalar
majorant for the full quadratic spatial pairing. -/
theorem abs_integral_convection_pairing_le_energy (f : SchwartzVelocity)
    {u : Space → Space} (E : ℝ) (hu : Measurable u)
    (hu2 : Integrable fun x : Space => ‖u x‖ ^ 2)
    (huE : (∫ x : Space, ‖u x‖ ^ 2) ≤ E) :
    |∫ x : Space, officialInner (u x) (fderiv ℝ (⇑f) x (u x))| ≤
      3 * (SchwartzMap.seminorm ℝ 0 1) f * E := by
  exact (abs_integral_convection_pairing_le f hu hu2).trans
    (mul_le_mul_of_nonneg_left huE (by positivity))

/-- Bilinearity of the official pairing over finite sums in the right slot. -/
private theorem officialInner_sum_right {κ : Type*} (x : Space) (s : Finset κ)
    (g : κ → Space) :
    officialInner x (∑ j ∈ s, g j) = ∑ j ∈ s, officialInner x (g j) := by
  simp only [officialInner_eq_sum, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- **The Laplacian pairing is integrable**: each second-derivative factor of a
Schwartz slice is itself Schwartz, so Cauchy–Schwarz applies leg by leg. -/
theorem integrable_laplacian_pairing (f : SchwartzVelocity) (t : ℝ) {u : Space → Space}
    (hu : Measurable u) (hu2 : Integrable fun x : Space => ‖u x‖ ^ 2) :
    Integrable fun x : Space =>
      officialInner (u x) (laplacian (fun _ => (⇑f : Space → Space)) t x) := by
  have hg : ∀ i : Fin 3, (fun y : Space => fderiv ℝ (⇑f) y (basisVector i))
      = ⇑(schwartzDirDeriv f (basisVector i)) := by
    intro i
    funext y
    rw [schwartzDirDeriv_apply]
  have hL : ∀ x : Space, laplacian (fun _ => (⇑f : Space → Space)) t x
      = ∑ i : Fin 3,
          schwartzDirDeriv (schwartzDirDeriv f (basisVector i)) (basisVector i) x := by
    intro x
    unfold laplacian
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg i, schwartzDirDeriv_apply]
  have hpart : ∀ i : Fin 3, Integrable fun x : Space =>
      officialInner (u x)
        (schwartzDirDeriv (schwartzDirDeriv f (basisVector i)) (basisVector i) x) := by
    intro i
    exact integrable_officialInner_pairing hu
      (schwartzDirDeriv (schwartzDirDeriv f (basisVector i))
        (basisVector i)).continuous.measurable hu2
      (integrable_norm_sq_schwartz _)
  have hsum : Integrable fun x : Space => ∑ i : Fin 3,
      officialInner (u x)
        (schwartzDirDeriv (schwartzDirDeriv f (basisVector i)) (basisVector i) x) :=
    integrable_finsetSum _ fun i _ => hpart i
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  show (∑ i : Fin 3, officialInner (u x)
      (schwartzDirDeriv (schwartzDirDeriv f (basisVector i)) (basisVector i) x))
      = officialInner (u x) (laplacian (fun _ => (⇑f : Space → Space)) t x)
  rw [← officialInner_sum_right, ← hL x]

/-- **The pairing-side residue, reduced to the time-derivative factor.**  Once
the time-derivative slice of the test is measurable and square-integrable, the
whole weak-pairing density is integrable against any measurable
square-integrable velocity slice.  The two spatial factors need no hypothesis:
the derivative and Laplacian of a Schwartz slice are Schwartz. -/
theorem integrable_weakPairingDensity_of_timeDeriv (ν : ℝ)
    (φ : DivergenceFreeTestFunction) (t : ℝ) {u : Space → Space}
    (hu : Measurable u) (hu2 : Integrable fun x : Space => ‖u x‖ ^ 2)
    (hT : Measurable fun x : Space =>
      timeDerivative (fun s => (φ.field s : Space → Space)) t x)
    (hT2 : Integrable fun x : Space =>
      ‖timeDerivative (fun s => (φ.field s : Space → Space)) t x‖ ^ 2) :
    Integrable fun x : Space =>
      officialInner (u x)
        (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
          spatialDerivative (fun s => (φ.field s : Space → Space)) t x (u x) +
          ν • laplacian (fun s => (φ.field s : Space → Space)) t x) := by
  have hTpart : Integrable fun x : Space => officialInner (u x)
      (timeDerivative (fun s => (φ.field s : Space → Space)) t x) :=
    integrable_officialInner_pairing hu hT hu2 hT2
  have hSpart : Integrable fun x : Space => officialInner (u x)
      (spatialDerivative (fun s => (φ.field s : Space → Space)) t x (u x)) :=
    integrable_convection_pairing (φ.field t) hu hu2
  have hLpart : Integrable fun x : Space => officialInner (u x)
      (ν • laplacian (fun s => (φ.field s : Space → Space)) t x) := by
    have hbase := integrable_laplacian_pairing (φ.field t) t hu hu2
    have hsc : (fun x : Space => officialInner (u x)
        (ν • laplacian (fun s => (φ.field s : Space → Space)) t x))
        = fun x : Space => ν * officialInner (u x)
            (laplacian (fun s => (φ.field s : Space → Space)) t x) := by
      funext x
      rw [officialInner_smul_right]
    rw [hsc]
    exact hbase.const_mul ν
  have hsplit : (fun x : Space =>
      officialInner (u x)
        (timeDerivative (fun s => (φ.field s : Space → Space)) t x +
          spatialDerivative (fun s => (φ.field s : Space → Space)) t x (u x) +
          ν • laplacian (fun s => (φ.field s : Space → Space)) t x))
      = fun x : Space =>
        officialInner (u x)
            (timeDerivative (fun s => (φ.field s : Space → Space)) t x) +
          officialInner (u x)
            (spatialDerivative (fun s => (φ.field s : Space → Space)) t x (u x)) +
          officialInner (u x)
            (ν • laplacian (fun s => (φ.field s : Space → Space)) t x) := by
    funext x
    rw [officialInner_add_right, officialInner_add_right]
  rw [hsplit]
  exact (hTpart.add hSpart).add hLpart

/-- The datum-side pairing clause of `LerayLimitData`, reduced to the same
time-derivative residue (the datum is Schwartz, hence measurable and `L²`). -/
theorem datum_pairing_integrable_of_timeDeriv (ν : ℝ) (u₀ : SchwartzVelocity)
    (φ : DivergenceFreeTestFunction)
    (hT : Measurable fun x : Space =>
      timeDerivative (fun s => (φ.field s : Space → Space)) 0 x)
    (hT2 : Integrable fun x : Space =>
      ‖timeDerivative (fun s => (φ.field s : Space → Space)) 0 x‖ ^ 2) :
    Integrable fun x : Space => weakPairingDensity ν (fun _ y => u₀ y) φ 0 x :=
  integrable_weakPairingDensity_of_timeDeriv ν φ 0 u₀.continuous.measurable
    (integrable_norm_sq_schwartz u₀) hT hT2

/-- The limit-side pairing clause of `LerayLimitData`, reduced to the same
time-derivative residue, for any jointly measurable slicewise-`L²` evolution. -/
theorem pairing_integrable_of_timeDeriv (ν : ℝ) (u : VelocityEvolution)
    (humeas : Measurable fun z : ℝ × Space => u z.1 z.2)
    (huint : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖u t x‖ ^ 2)
    (φ : DivergenceFreeTestFunction) (t : ℝ) (ht : 0 < t)
    (hT : Measurable fun x : Space =>
      timeDerivative (fun s => (φ.field s : Space → Space)) t x)
    (hT2 : Integrable fun x : Space =>
      ‖timeDerivative (fun s => (φ.field s : Space → Space)) t x‖ ^ 2) :
    Integrable fun x : Space => weakPairingDensity ν u φ t x :=
  integrable_weakPairingDensity_of_timeDeriv ν φ t
    (humeas.comp measurable_prodMk_left) (huint t ht.le) hT hT2

/-- The time derivative of a certified test is measurable in space on the
nonnegative time half-line. -/
theorem DivergenceFreeTestFunction.timeDerivative_measurable
    (φ : DivergenceFreeTestFunction) (t : ℝ) (ht : 0 ≤ t) :
    Measurable fun x : Space =>
      timeDerivative (fun s => (φ.field s : Space → Space)) t x := by
  have heq : (fun x : Space =>
      timeDerivative (fun s => (φ.field s : Space → Space)) t x) =
      φ.timeDerivSchwartz t := by
    funext x
    exact φ.timeDeriv_eq t ht x
  rw [heq]
  exact (φ.timeDerivSchwartz t).continuous.measurable

/-- The time derivative of a certified test is square-integrable in space on
the nonnegative time half-line. -/
theorem DivergenceFreeTestFunction.timeDerivative_sq_integrable
    (φ : DivergenceFreeTestFunction) (t : ℝ) (ht : 0 ≤ t) :
    Integrable fun x : Space =>
      ‖timeDerivative (fun s => (φ.field s : Space → Space)) t x‖ ^ 2 := by
  have heq : (fun x : Space =>
      ‖timeDerivative (fun s => (φ.field s : Space → Space)) t x‖ ^ 2) =
      fun x : Space => ‖φ.timeDerivSchwartz t x‖ ^ 2 := by
    funext x
    rw [φ.timeDeriv_eq t ht x]
  rw [heq]
  exact integrable_norm_sq_schwartz (φ.timeDerivSchwartz t)

/-- The datum-side weak pairing is integrable for every certified test; no
extra decay hypothesis on its time derivative is needed. -/
theorem datum_pairing_integrable (ν : ℝ) (u₀ : SchwartzVelocity)
    (φ : DivergenceFreeTestFunction) :
    Integrable fun x : Space => weakPairingDensity ν (fun _ y => u₀ y) φ 0 x :=
  datum_pairing_integrable_of_timeDeriv ν u₀ φ
    (φ.timeDerivative_measurable 0 le_rfl)
    (φ.timeDerivative_sq_integrable 0 le_rfl)

/-- The limit-side weak pairing is integrable for every certified test and
every positive time whenever the velocity has measurable `L²` slices. -/
theorem pairing_integrable (ν : ℝ) (u : VelocityEvolution)
    (humeas : Measurable fun z : ℝ × Space => u z.1 z.2)
    (huint : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖u t x‖ ^ 2)
    (φ : DivergenceFreeTestFunction) (t : ℝ) (ht : 0 < t) :
    Integrable fun x : Space => weakPairingDensity ν u φ t x :=
  pairing_integrable_of_timeDeriv ν u humeas huint φ t ht
    (φ.timeDerivative_measurable t ht.le)
    (φ.timeDerivative_sq_integrable t ht.le)

/-!
### Time truncation of the weak form (certified)

The weak-pairing density vanishes identically beyond the common horizon of the
test's field slice and its time-derivative slice, so the half-line time integral
of the weak form is a *finite-window* integral.  This is step (a) of the limit
passage in its bookkeeping form: it is what makes the window estimates below
about the whole weak form rather than about a truncation of it.
-/

theorem officialInner_zero_right (x : Space) : officialInner x 0 = 0 := by
  simp [officialInner_eq_sum]

/-- Beyond the common horizon of the test's field and time-derivative slices the
weak-pairing density vanishes identically. -/
theorem weakPairingDensity_eq_zero_of_vanishing (ν : ℝ) (u : VelocityEvolution)
    (φ : DivergenceFreeTestFunction) {t : ℝ} (ht : 0 ≤ t)
    (hf : φ.field t = 0) (hd : φ.timeDerivSchwartz t = 0) (x : Space) :
    weakPairingDensity ν u φ t x = 0 := by
  have hcoe : (⇑(φ.field t) : Space → Space) = fun _ : Space => (0 : Space) := by
    funext y; rw [hf]; rfl
  have h1 : timeDerivative (fun s => (φ.field s : Space → Space)) t x = 0 := by
    rw [φ.timeDeriv_eq t ht x, hd]; rfl
  have h2 : spatialDerivative (fun s => (φ.field s : Space → Space)) t x = 0 := by
    unfold spatialDerivative
    simp [hcoe]
  have h3 : laplacian (fun s => (φ.field s : Space → Space)) t x = 0 := by
    unfold laplacian
    simp [hcoe]
  unfold weakPairingDensity
  rw [h1, h3]
  have h2' : spatialDerivative (fun s => (φ.field s : Space → Space)) t x (u t x) = 0 := by
    rw [h2]; rfl
  rw [h2']
  simp only [add_zero, smul_zero]
  exact officialInner_zero_right _

/-- A single horizon beyond which both the test slices and their time
derivatives vanish. -/
theorem DivergenceFreeTestFunction.exists_horizon (φ : DivergenceFreeTestFunction) :
    ∃ T : ℝ, 0 < T ∧ (∀ s : ℝ, T ≤ s → φ.field s = 0) ∧
      (∀ s : ℝ, T ≤ s → φ.timeDerivSchwartz s = 0) := by
  obtain ⟨T1, hT1, h1⟩ := φ.compact_time
  obtain ⟨T2, hT2, h2⟩ := φ.compact_time_deriv
  exact ⟨max T1 T2, lt_max_of_lt_left hT1,
    fun s hs => h1 s (le_trans (le_max_left _ _) hs),
    fun s hs => h2 s (le_trans (le_max_right _ _) hs)⟩

/-- One time horizon and one compact spatial carrier work simultaneously for
the test field and its time derivative.  Restricted to nonnegative time, this
is the compact-spacetime support needed for uniform estimates on test
factors. -/
theorem DivergenceFreeTestFunction.exists_compact_spacetime_carrier
    (φ : DivergenceFreeTestFunction) :
    ∃ T : ℝ, ∃ K : Set Space, 0 < T ∧ IsCompact K ∧
      (∀ t : ℝ, ∀ x : Space, T ≤ t ∨ x ∉ K → φ.field t x = 0) ∧
      (∀ t : ℝ, ∀ x : Space,
        T ≤ t ∨ x ∉ K → φ.timeDerivSchwartz t x = 0) := by
  obtain ⟨T, hT, hfield, hderiv⟩ := φ.exists_horizon
  obtain ⟨K₁, hK₁, hspace⟩ := φ.compact_space
  obtain ⟨K₂, hK₂, hspaceDeriv⟩ := φ.compact_space_deriv
  refine ⟨T, K₁ ∪ K₂, hT, hK₁.union hK₂, ?_, ?_⟩
  · intro t x htx
    rcases htx with ht | hx
    · rw [hfield t ht]
      rfl
    · apply hspace t x
      intro hx₁
      exact hx (Set.mem_union_left K₂ hx₁)
  · intro t x htx
    rcases htx with ht | hx
    · rw [hderiv t ht]
      rfl
    · apply hspaceDeriv t x
      intro hx₂
      exact hx (Set.mem_union_right K₁ hx₂)

/-- The genuine time derivative is uniformly bounded on every compact
nonnegative spacetime window.  The proof derives joint continuity from the
test's existing half-space smoothness; it does not add a regularity payload. -/
theorem DivergenceFreeTestFunction.exists_uniform_timeDeriv_bound
    (φ : DivergenceFreeTestFunction) {T : ℝ} {K : Set Space} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      ∀ x : Space, x ∈ K → ‖φ.timeDerivSchwartz t x‖ ≤ C := by
  let S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let F : ℝ × Space → Space := fun z => φ.field z.1 z.2
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ContinuousOn
      (fun z : ℝ × Space => fderivWithin ℝ F S z (1, 0)) S :=
    ((φ.smooth.continuousOn_fderivWithin hUD (by norm_num)).clm_apply
      continuousOn_const)
  have hbridge : ∀ z ∈ S,
      fderivWithin ℝ F S z (1, 0) = φ.timeDerivSchwartz z.1 z.2 := by
    rintro ⟨t, x⟩ hz
    rw [← φ.timeDeriv_eq t hz.1 x]
    unfold timeDerivative
    have hG : HasFDerivWithinAt F (fderivWithin ℝ F S (t, x)) S (t, x) :=
      ((φ.smooth (t, x) hz).differentiableWithinAt
        (by decide : (∞ : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
    have hi : HasFDerivAt (fun s : ℝ => (s, x))
        (ContinuousLinearMap.inl ℝ ℝ Space) t := hasFDerivAt_prodMk_left t x
    have hmaps : Set.MapsTo (fun s : ℝ => (s, x)) (Set.Ici 0) S := fun s hs =>
      Set.mem_prod.mpr ⟨hs, Set.mem_univ x⟩
    have hcomp := HasFDerivWithinAt.comp t hG hi.hasFDerivWithinAt hmaps
    rw [show (F ∘ (fun s : ℝ => (s, x))) = (fun s => (φ.field s) x) from rfl]
      at hcomp
    rw [hcomp.fderivWithin ((uniqueDiffOn_Ici 0) t hz.1),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have htd : ContinuousOn
      (fun z : ℝ × Space => φ.timeDerivSchwartz z.1 z.2) S :=
    hD.congr (fun z hz => (hbridge z hz).symm)
  let W : Set (ℝ × Space) := Set.Icc (0 : ℝ) T ×ˢ K
  have hW : IsCompact W := isCompact_Icc.prod hK
  have hWS : W ⊆ S := by
    rintro ⟨t, x⟩ htx
    exact Set.mem_prod.mpr ⟨Set.mem_Ici.mpr htx.1.1, Set.mem_univ x⟩
  have hn : ContinuousOn
      (fun z : ℝ × Space => ‖φ.timeDerivSchwartz z.1 z.2‖) W :=
    htd.norm.mono hWS
  obtain ⟨C, hC⟩ := hW.bddAbove_image hn
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro t ht x hx
  exact le_trans (hC ⟨(t, x), Set.mem_prod.mpr ⟨ht, hx⟩, rfl⟩) (le_max_left C 0)

/-- The spatial Fréchet derivatives of the test slices are uniformly bounded
on every compact nonnegative spacetime window.  This is a restriction of the
joint spacetime derivative to the spatial inclusion, not an extra
Schwartz-topology continuity assumption. -/
theorem DivergenceFreeTestFunction.exists_uniform_spatialFDeriv_bound
    (φ : DivergenceFreeTestFunction) {T : ℝ} {K : Set Space} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      ∀ x : Space, x ∈ K → ‖fderiv ℝ (⇑(φ.field t)) x‖ ≤ C := by
  let S : Set (ℝ × Space) := Set.Ici (0 : ℝ) ×ˢ Set.univ
  let F : ℝ × Space → Space := fun z => φ.field z.1 z.2
  let J : Space →L[ℝ] ℝ × Space := ContinuousLinearMap.inr ℝ ℝ Space
  have hUD : UniqueDiffOn ℝ S := (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ
  have hD : ContinuousOn (fun z : ℝ × Space => fderivWithin ℝ F S z) S :=
    φ.smooth.continuousOn_fderivWithin hUD (by norm_num)
  have hbridge : ∀ z ∈ S,
      (fderivWithin ℝ F S z).comp J = fderiv ℝ (⇑(φ.field z.1)) z.2 := by
    rintro ⟨t, x⟩ hz
    have hG : HasFDerivWithinAt F (fderivWithin ℝ F S (t, x)) S (t, x) :=
      ((φ.smooth (t, x) hz).differentiableWithinAt
        (by decide : (∞ : ℕ∞ω) ≠ 0)).hasFDerivWithinAt
    have hi : HasFDerivAt (fun y : Space => (t, y)) J x :=
      hasFDerivAt_prodMk_right t x
    have hmaps : Set.MapsTo (fun y : Space => (t, y)) Set.univ S := fun y _ =>
      Set.mem_prod.mpr ⟨hz.1, Set.mem_univ y⟩
    have hcomp := HasFDerivWithinAt.comp x hG hi.hasFDerivWithinAt hmaps
    rw [show (F ∘ (fun y : Space => (t, y))) = (⇑(φ.field t) : Space → Space)
      from rfl] at hcomp
    have heq := hcomp.fderivWithin (uniqueDiffOn_univ x (Set.mem_univ x))
    simpa only [fderivWithin_univ] using heq.symm
  let W : Set (ℝ × Space) := Set.Icc (0 : ℝ) T ×ˢ K
  have hW : IsCompact W := isCompact_Icc.prod hK
  have hWS : W ⊆ S := by
    rintro ⟨t, x⟩ htx
    exact Set.mem_prod.mpr ⟨Set.mem_Ici.mpr htx.1.1, Set.mem_univ x⟩
  have hn : ContinuousOn (fun z : ℝ × Space => ‖fderivWithin ℝ F S z‖) W :=
    hD.norm.mono hWS
  obtain ⟨C, hC⟩ := hW.bddAbove_image hn
  let B : ℝ := max C 0 * ‖J‖
  have hB : 0 ≤ B := mul_nonneg (le_max_right C 0) (norm_nonneg J)
  refine ⟨B, hB, ?_⟩
  intro t ht x hx
  have hzS : (t, x) ∈ S :=
    Set.mem_prod.mpr ⟨Set.mem_Ici.mpr ht.1, Set.mem_univ x⟩
  rw [← hbridge (t, x) hzS]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (le_trans (hC ⟨(t, x), Set.mem_prod.mpr ⟨ht, hx⟩, rfl⟩)
        (le_max_left C 0)) (norm_nonneg J))

/-- Compact spacetime support upgrades the preceding pointwise derivative
estimate to one uniform bound for the first Schwartz seminorm of every test
slice in the active time window. -/
theorem DivergenceFreeTestFunction.exists_uniform_first_seminorm_bound
    (φ : DivergenceFreeTestFunction) :
    ∃ T C : ℝ, 0 < T ∧ 0 ≤ C ∧ ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      (SchwartzMap.seminorm ℝ 0 1) (φ.field t) ≤ C := by
  obtain ⟨T, K, hT, hK, hfield, _hderiv⟩ := φ.exists_compact_spacetime_carrier
  obtain ⟨C, hC, hbound⟩ := φ.exists_uniform_spatialFDeriv_bound hK
  refine ⟨T, C, hT, hC, ?_⟩
  intro t ht
  apply SchwartzMap.seminorm_le_bound ℝ 0 1 (φ.field t) hC
  intro x
  rw [pow_zero, one_mul, norm_iteratedFDeriv_one]
  by_cases hx : x ∈ K
  · exact hbound t ht x hx
  · have hevent : (⇑(φ.field t) : Space → Space) =ᶠ[nhds x]
        (fun _ : Space => (0 : Space)) := by
      filter_upwards [hK.isClosed.isOpen_compl.eventually_mem hx] with y hy
      exact hfield t y (Or.inr hy)
    have hz : fderiv ℝ (⇑(φ.field t)) x = 0 := by
      simpa using hevent.fderiv_eq
    simp [hz, hC]

/-- The compact-time first-seminorm bound supplies a constant integrable
majorant for the quadratic convection leg under a uniform kinetic-energy
bound.  This is the domination input only; no limit interchange is claimed. -/
theorem DivergenceFreeTestFunction.exists_integrable_convection_pairing_majorant
    (φ : DivergenceFreeTestFunction) (u : VelocityEvolution) (E : ℝ)
    (hE : 0 ≤ E)
    (humeas : Measurable fun z : ℝ × Space => u z.1 z.2)
    (huint : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖u t x‖ ^ 2)
    (huE : ∀ t : ℝ, 0 < t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ E) :
    ∃ T B : ℝ, 0 < T ∧ 0 ≤ B ∧
      IntegrableOn (fun _t : ℝ => B) (Set.Ioc (0 : ℝ) T) ∧
      ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) T →
        |∫ x : Space,
          officialInner (u t x) (fderiv ℝ (⇑(φ.field t)) x (u t x))| ≤ B := by
  obtain ⟨T, C, hT, hC, hseminorm⟩ := φ.exists_uniform_first_seminorm_bound
  let B : ℝ := 3 * C * E
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) hC) hE
  refine ⟨T, B, hT, hB, integrableOn_const (hs := measure_Ioc_lt_top.ne), ?_⟩
  intro t ht
  have hslice := abs_integral_convection_pairing_le_energy (φ.field t) E
    (humeas.comp measurable_prodMk_left) (huint t ht.1.le) (huE t ht.1)
  exact hslice.trans (by
    simpa [B] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hseminorm t ⟨ht.1.le, ht.2⟩) (by norm_num)) hE)

/-- A uniformly energy-bounded family has one common integrable majorant for
all of its quadratic convection pairings on the compact time window of the
test.  Unlike the single-velocity version above, this is the domination shape
consumed by the Galerkin limit passage. -/
theorem DivergenceFreeTestFunction.exists_integrable_convection_pairing_majorant_family
    (φ : DivergenceFreeTestFunction) (uSeq : ℕ → VelocityEvolution) (E : ℝ)
    (hE : 0 ≤ E)
    (humeas : JointlyMeasurable uSeq)
    (huint : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → Integrable fun x : Space => ‖uSeq k t x‖ ^ 2)
    (huE : ∀ (k : ℕ) (t : ℝ), 0 < t → (∫ x : Space, ‖uSeq k t x‖ ^ 2) ≤ E) :
    ∃ T B : ℝ, 0 < T ∧ 0 ≤ B ∧
      IntegrableOn (fun _t : ℝ => B) (Set.Ioc (0 : ℝ) T) ∧
      ∀ (k : ℕ) (t : ℝ), t ∈ Set.Ioc (0 : ℝ) T →
        |∫ x : Space,
          officialInner (uSeq k t x)
            (fderiv ℝ (⇑(φ.field t)) x (uSeq k t x))| ≤ B := by
  obtain ⟨T, C, hT, hC, hseminorm⟩ := φ.exists_uniform_first_seminorm_bound
  let B : ℝ := 3 * C * E
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) hC) hE
  refine ⟨T, B, hT, hB, integrableOn_const (hs := measure_Ioc_lt_top.ne), ?_⟩
  intro k t ht
  have hslice := abs_integral_convection_pairing_le_energy (φ.field t) E
    ((humeas k).comp measurable_prodMk_left) (huint k t ht.1.le) (huE k t ht.1)
  exact hslice.trans (by
    simpa [B] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hseminorm t ⟨ht.1.le, ht.2⟩) (by norm_num)) hE)

/-- **Restricted-time measurability of the signed convection pairing.**

Joint measurability of `u` and half-space smoothness of the test suffice; no
integrability hypothesis at negative times is needed.  The proof continuously
extends the test to all times by `t ↦ max t 0`, applies Mathlib's measurable
parameterized-Fréchet-derivative theorem, and then identifies the extension
with the original test on `(0,T]`. -/
theorem DivergenceFreeTestFunction.aestronglyMeasurable_convection_pairing_restrict_Ioc
    (φ : DivergenceFreeTestFunction) (u : VelocityEvolution)
    (humeas : Measurable fun z : ℝ × Space => u z.1 z.2)
    (T : ℝ) :
    AEStronglyMeasurable
      (fun t : ℝ => ∫ x : Space,
        officialInner (u t x) (fderiv ℝ (⇑(φ.field t)) x (u t x)))
      (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
  let Φ : ℝ → Space → Space := fun t x => φ.field (max t 0) x
  have hΦcont : Continuous Φ.uncurry := by
    have hmap : ∀ z : ℝ × Space,
        (max z.1 0, z.2) ∈ (Set.Ici (0 : ℝ)) ×ˢ (Set.univ : Set Space) := by
      intro z
      exact ⟨le_max_right z.1 0, Set.mem_univ z.2⟩
    exact φ.smooth.continuousOn.comp_continuous
      ((continuous_fst.max continuous_const).prodMk continuous_snd) hmap
  have hD : Measurable fun z : ℝ × Space =>
      fderiv ℝ (Φ z.1) z.2 := measurable_fderiv_with_param ℝ hΦcont
  have hDu : Measurable fun z : ℝ × Space =>
      fderiv ℝ (Φ z.1) z.2 (u z.1 z.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      (hD.prodMk humeas)
  have hjoint : Measurable fun z : ℝ × Space =>
      officialInner (u z.1 z.2) (fderiv ℝ (Φ z.1) z.2 (u z.1 z.2)) :=
    measurable_officialInner_comp humeas hDu
  have hclamp : StronglyMeasurable fun t : ℝ => ∫ x : Space,
      officialInner (u t x) (fderiv ℝ (Φ t) x (u t x)) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  refine hclamp.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr
    (Filter.Eventually.of_forall fun t ht => ?_)
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [Φ, max_eq_left ht.1.le]

/-- The explicit-window dominated-convergence engine for quadratic convection
pairings.  This is separated from window selection so a compactness-extracted
subsequence on that exact window can consume it directly. -/
theorem DivergenceFreeTestFunction.tendsto_integral_convection_pairing_on_timeWindow_of_ae
    (φ : DivergenceFreeTestFunction) (uSeq : ℕ → VelocityEvolution)
    (u : VelocityEvolution) (T B : ℝ)
    (hpairMeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun t : ℝ => ∫ x : Space,
        officialInner (uSeq k t x) (fderiv ℝ (⇑(φ.field t)) x (uSeq k t x)))
      (volume.restrict (Set.Ioc (0 : ℝ) T)))
    (hBint : IntegrableOn (fun _t : ℝ => B) (Set.Ioc (0 : ℝ) T))
    (hbound : ∀ (k : ℕ) (t : ℝ), t ∈ Set.Ioc (0 : ℝ) T →
      |∫ x : Space,
        officialInner (uSeq k t x)
          (fderiv ℝ (⇑(φ.field t)) x (uSeq k t x))| ≤ B)
    (hpairLim : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), Filter.Tendsto
      (fun k : ℕ => ∫ x : Space,
        officialInner (uSeq k t x) (fderiv ℝ (⇑(φ.field t)) x (uSeq k t x)))
      Filter.atTop
      (nhds (∫ x : Space,
        officialInner (u t x) (fderiv ℝ (⇑(φ.field t)) x (u t x))))) :
    Filter.Tendsto
      (fun k : ℕ => ∫ t in Set.Ioc (0 : ℝ) T, ∫ x : Space,
        officialInner (uSeq k t x) (fderiv ℝ (⇑(φ.field t)) x (uSeq k t x)))
      Filter.atTop
      (nhds (∫ t in Set.Ioc (0 : ℝ) T, ∫ x : Space,
        officialInner (u t x) (fderiv ℝ (⇑(φ.field t)) x (u t x)))) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _t : ℝ => B)
  · exact hpairMeas
  · exact hBint
  · intro k
    refine (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs]
    exact hbound k t ht
  · exact hpairLim

/-- **Dominated-convergence assembly for the quadratic time leg.**

If the spatial convection pairings of a uniformly energy-bounded family are
measurable in time and converge almost everywhere to the limit pairing, then
their time integrals converge on the certified compact window of the test.
The common dominating function is constructed above from the test's uniform
first Schwartz seminorm and the kinetic-energy bound; it is not an additional
hypothesis. -/
theorem DivergenceFreeTestFunction.exists_timeWindow_tendsto_integral_convection_pairing_of_ae
    (φ : DivergenceFreeTestFunction) (uSeq : ℕ → VelocityEvolution)
    (u : VelocityEvolution) (E : ℝ) (hE : 0 ≤ E)
    (humeas : JointlyMeasurable uSeq)
    (huint : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → Integrable fun x : Space => ‖uSeq k t x‖ ^ 2)
    (huE : ∀ (k : ℕ) (t : ℝ), 0 < t → (∫ x : Space, ‖uSeq k t x‖ ^ 2) ≤ E)
    (hpairMeas : ∀ T : ℝ, 0 < T → ∀ k : ℕ, AEStronglyMeasurable
      (fun t : ℝ => ∫ x : Space,
        officialInner (uSeq k t x) (fderiv ℝ (⇑(φ.field t)) x (uSeq k t x)))
      (volume.restrict (Set.Ioc (0 : ℝ) T)))
    (hpairLim : ∀ T : ℝ, 0 < T →
      ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), Filter.Tendsto
        (fun k : ℕ => ∫ x : Space,
          officialInner (uSeq k t x) (fderiv ℝ (⇑(φ.field t)) x (uSeq k t x)))
        Filter.atTop
        (nhds (∫ x : Space,
          officialInner (u t x) (fderiv ℝ (⇑(φ.field t)) x (u t x))))) :
    ∃ T : ℝ, 0 < T ∧
      Filter.Tendsto
        (fun k : ℕ => ∫ t in Set.Ioc (0 : ℝ) T, ∫ x : Space,
          officialInner (uSeq k t x) (fderiv ℝ (⇑(φ.field t)) x (uSeq k t x)))
        Filter.atTop
        (nhds (∫ t in Set.Ioc (0 : ℝ) T, ∫ x : Space,
          officialInner (u t x) (fderiv ℝ (⇑(φ.field t)) x (u t x)))) := by
  obtain ⟨T, B, hT, _hB, hBint, hbound⟩ :=
    φ.exists_integrable_convection_pairing_majorant_family uSeq E hE humeas huint huE
  refine ⟨T, hT, ?_⟩
  exact φ.tendsto_integral_convection_pairing_on_timeWindow_of_ae
    uSeq u T B (hpairMeas T hT) hBint hbound (hpairLim T hT)

/-- Compact spatial support turns the uniform pointwise time-derivative bound
into a uniform squared `L²_x` bound. -/
theorem DivergenceFreeTestFunction.timeDeriv_norm_sq_le_volume_mul_bound
    (φ : DivergenceFreeTestFunction) {T C : ℝ} {K : Set Space}
    (hK : IsCompact K)
    (hspace : ∀ t : ℝ, ∀ x : Space, x ∉ K → φ.timeDerivSchwartz t x = 0)
    (hbound : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      ∀ x : Space, x ∈ K → ‖φ.timeDerivSchwartz t x‖ ≤ C) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
      (∫ x : Space, ‖φ.timeDerivSchwartz t x‖ ^ 2) ≤ volume.real K * C ^ 2 := by
  intro t ht
  have heq : (∫ x : Space, ‖φ.timeDerivSchwartz t x‖ ^ 2) =
      ∫ x in K, ‖φ.timeDerivSchwartz t x‖ ^ 2 := by
    rw [← MeasureTheory.integral_indicator hK.measurableSet]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, hspace t x hx]
  rw [heq]
  have hf : IntegrableOn (fun x : Space => ‖φ.timeDerivSchwartz t x‖ ^ 2) K :=
    (integrable_norm_sq_schwartz (φ.timeDerivSchwartz t)).integrableOn
  have hg : IntegrableOn (fun _x : Space => C ^ 2) K :=
    integrableOn_const (hs := hK.measure_lt_top.ne)
  calc
    (∫ x in K, ‖φ.timeDerivSchwartz t x‖ ^ 2) ≤ ∫ _x in K, C ^ 2 := by
      exact setIntegral_mono_on hf hg hK.measurableSet fun x hx =>
        pow_le_pow_left₀ (norm_nonneg _) (hbound t ht x hx) 2
    _ = volume.real K * C ^ 2 := by simp [smul_eq_mul]

/-- **The first genuine time majorant for the Leray limit passage.**  The
time-derivative test factor has a single constant squared `L²_x` majorant on
the test horizon, and that constant is integrable in time. -/
theorem DivergenceFreeTestFunction.exists_integrable_timeDeriv_l2_majorant
    (φ : DivergenceFreeTestFunction) :
    ∃ T M : ℝ, 0 < T ∧ 0 ≤ M ∧
      IntegrableOn (fun _t : ℝ => M) (Set.Ioc (0 : ℝ) T) ∧
      ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) T →
        (∫ x : Space, ‖φ.timeDerivSchwartz t x‖ ^ 2) ≤ M := by
  obtain ⟨T, K, hT, hK, _hfield, hderiv⟩ := φ.exists_compact_spacetime_carrier
  obtain ⟨C, _hC, hbound⟩ := φ.exists_uniform_timeDeriv_bound hK
  let M : ℝ := volume.real K * C ^ 2
  have hM : 0 ≤ M := mul_nonneg measureReal_nonneg (sq_nonneg C)
  refine ⟨T, M, hT, hM, integrableOn_const (hs := measure_Ioc_lt_top.ne), ?_⟩
  intro t ht
  exact φ.timeDeriv_norm_sq_le_volume_mul_bound hK
    (fun s x hx => hderiv s x (Or.inr hx)) hbound t ⟨ht.1.le, ht.2⟩

/-- A uniform velocity `L²_x` bound and the compact-carrier test bound give an
integrable time majorant for the linear `⟨u, ∂ₜφ⟩` leg.  This is the
quantitative consumer needed before dominated convergence; it is independent
of the convection and Laplacian legs. -/
theorem DivergenceFreeTestFunction.exists_integrable_timeDeriv_pairing_majorant
    (φ : DivergenceFreeTestFunction) (u : VelocityEvolution) (E : ℝ)
    (hE : 0 ≤ E)
    (humeas : Measurable fun z : ℝ × Space => u z.1 z.2)
    (huint : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖u t x‖ ^ 2)
    (huE : ∀ t : ℝ, 0 < t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ E) :
    ∃ T B : ℝ, 0 < T ∧ 0 ≤ B ∧
      IntegrableOn (fun _t : ℝ => B) (Set.Ioc (0 : ℝ) T) ∧
      ∀ t : ℝ, t ∈ Set.Ioc (0 : ℝ) T →
        |∫ x : Space, officialInner (u t x) (φ.timeDerivSchwartz t x)| ≤ B := by
  obtain ⟨T, M, hT, hM, hMint, hMbound⟩ := φ.exists_integrable_timeDeriv_l2_majorant
  let B : ℝ := (3 / 2 : ℝ) * (E + M)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (add_nonneg hE hM)
  refine ⟨T, B, hT, hB, integrableOn_const (hs := measure_Ioc_lt_top.ne), ?_⟩
  intro t ht
  have hpair := abs_integral_officialInner_le_three_halves
    (humeas.comp measurable_prodMk_left)
    (φ.timeDerivSchwartz t).continuous.measurable (huint t ht.1.le)
    (integrable_norm_sq_schwartz (φ.timeDerivSchwartz t))
  exact hpair.trans (mul_le_mul_of_nonneg_left
    (add_le_add (huE t ht.1) (hMbound t ht)) (by norm_num))

/-- A function vanishing beyond `T ≥ 0` has the same integral over `Ici 0` and
over the finite window `Ioc 0 T`; no integrability hypothesis is needed since
the two indicators agree off the null set `{0}`. -/
theorem setIntegral_Ici_eq_Ioc_of_vanishing {F : ℝ → ℝ} {T : ℝ}
    (hT : ∀ t : ℝ, T ≤ t → F t = 0) :
    ∫ t in Set.Ici (0:ℝ), F t = ∫ t in Set.Ioc (0:ℝ) T, F t := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ici,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have hset : {a : ℝ | ¬ a ≠ 0} = {(0:ℝ)} := by ext t; simp
    rw [hset]; simp
  filter_upwards [h0] with t ht
  rcases lt_trichotomy t 0 with h | h | h
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ici (0:ℝ) by simp; linarith),
      Set.indicator_of_notMem (show t ∉ Set.Ioc (0:ℝ) T by simp; intro hc; linarith)]
  · exact absurd h ht
  · by_cases hTt : t ≤ T
    · rw [Set.indicator_of_mem (show t ∈ Set.Ici (0:ℝ) from h.le),
        Set.indicator_of_mem (show t ∈ Set.Ioc (0:ℝ) T from ⟨h, hTt⟩)]
    · have hTt' : T < t := lt_of_not_ge hTt
      rw [Set.indicator_of_mem (show t ∈ Set.Ici (0:ℝ) from h.le),
        Set.indicator_of_notMem (show t ∉ Set.Ioc (0:ℝ) T by simp; intro _; linarith)]
      exact hT t hTt'.le

/-- **Time truncation of the weak form.**  The weak-form time integral over the
half-line collapses to the finite window `Ioc 0 T` given by the test's
horizon. -/
theorem weakForm_time_integral_eq_Ioc (ν : ℝ) (u : VelocityEvolution)
    (φ : DivergenceFreeTestFunction) {T : ℝ} (hT0 : 0 ≤ T)
    (hf : ∀ s : ℝ, T ≤ s → φ.field s = 0)
    (hd : ∀ s : ℝ, T ≤ s → φ.timeDerivSchwartz s = 0) :
    (∫ t in Set.Ici (0:ℝ), ∫ x : Space, weakPairingDensity ν u φ t x)
      = ∫ t in Set.Ioc (0:ℝ) T, ∫ x : Space, weakPairingDensity ν u φ t x := by
  refine setIntegral_Ici_eq_Ioc_of_vanishing fun t htT => ?_
  have h0 : 0 ≤ t := le_trans hT0 htT
  have : (fun x : Space => weakPairingDensity ν u φ t x) = fun _ : Space => (0:ℝ) := by
    funext x
    exact weakPairingDensity_eq_zero_of_vanishing ν u φ h0 (hf t htT) (hd t htT) x
  rw [this, integral_zero]

/-!
### Spatial limit passage against a fixed `L²` field (certified)

Step (b) of the limit passage, in the form the compactness limit actually needs.
`StrongL2LocLimit` delivers convergence only on balls, while the test slices have
merely Schwartz — not compact — spatial support, so the far field has to be
controlled by the *test's own* `L²` tail rather than by any local convergence.
The Young form of Cauchy–Schwarz below is what lets the two legs be tuned
independently: a large parameter kills the near-field test factor and a small one
kills the far-field velocity factor.
-/

theorem officialInner_sub_left (a b c : Space) :
    officialInner (a - b) c = officialInner a c - officialInner b c := by
  simp only [officialInner_eq_sum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- **Young form of the official Cauchy–Schwarz bound.**  Splitting the product
with a free parameter `lam > 0` is what lets the near-field and far-field legs of
the limit passage be tuned independently. -/
theorem abs_officialInner_le_young (a b : Space) {lam : ℝ} (hlam : 0 < lam) :
    |officialInner a b| ≤ 3 * (lam / 2 * ‖a‖ ^ 2 + 1 / (2 * lam) * ‖b‖ ^ 2) := by
  have h := abs_officialInner_le_three a b
  have hy : ‖a‖ * ‖b‖ ≤ lam / 2 * ‖a‖ ^ 2 + 1 / (2 * lam) * ‖b‖ ^ 2 := by
    rw [← sub_nonneg]
    have hid : lam / 2 * ‖a‖ ^ 2 + 1 / (2 * lam) * ‖b‖ ^ 2 - ‖a‖ * ‖b‖
        = (lam * ‖a‖ - ‖b‖) ^ 2 / (2 * lam) := by
      field_simp
      ring
    rw [hid]
    positivity
  linarith

/-- **Young form of the pairing bound on an arbitrary measurable region.** -/
theorem abs_setIntegral_officialInner_le_young {a b : Space → Space} (s : Set Space)
    (ha : Measurable a) (hb : Measurable b)
    (ha2 : Integrable fun x : Space => ‖a x‖ ^ 2)
    (hb2 : Integrable fun x : Space => ‖b x‖ ^ 2)
    {lam : ℝ} (hlam : 0 < lam) :
    |∫ x in s, officialInner (a x) (b x)| ≤
      3 * (lam / 2 * (∫ x in s, ‖a x‖ ^ 2) + 1 / (2 * lam) * (∫ x in s, ‖b x‖ ^ 2)) := by
  have hpair : Integrable fun x : Space => officialInner (a x) (b x) :=
    integrable_officialInner_pairing ha hb ha2 hb2
  have hmaj : Integrable fun x : Space =>
      3 * (lam / 2 * ‖a x‖ ^ 2 + 1 / (2 * lam) * ‖b x‖ ^ 2) :=
    ((ha2.const_mul (lam / 2)).add (hb2.const_mul (1 / (2 * lam)))).const_mul 3
  calc |∫ x in s, officialInner (a x) (b x)|
      ≤ ∫ x in s, |officialInner (a x) (b x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x in s, 3 * (lam / 2 * ‖a x‖ ^ 2 + 1 / (2 * lam) * ‖b x‖ ^ 2) :=
        integral_mono hpair.abs.integrableOn hmaj.integrableOn
          (fun x => abs_officialInner_le_young (a x) (b x) hlam)
    _ = 3 * (lam / 2 * (∫ x in s, ‖a x‖ ^ 2) + 1 / (2 * lam) * (∫ x in s, ‖b x‖ ^ 2)) := by
        rw [MeasureTheory.integral_const_mul,
          integral_add ((ha2.const_mul (lam / 2)).integrableOn)
            ((hb2.const_mul (1 / (2 * lam))).integrableOn),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **Spatial tail of an `L²` field.**  The mass outside a ball of radius `n`
tends to `0`; this is the quantitative content of "Schwartz decay controls the
far field" used by the limit passage. -/
theorem tendsto_setIntegral_compl_closedBall_norm_sq {b : Space → Space}
    (hb2 : Integrable fun x : Space => ‖b x‖ ^ 2) :
    Filter.Tendsto (fun n : ℕ => ∫ x in (Metric.closedBall (0:Space) (n:ℝ))ᶜ, ‖b x‖ ^ 2)
      Filter.atTop (nhds 0) := by
  have hmono : Monotone fun n : ℕ => Metric.closedBall (0:Space) (n:ℝ) := by
    intro m n hmn
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  have hunion : (⋃ n : ℕ, Metric.closedBall (0:Space) (n:ℝ)) = (Set.univ : Set Space) := by
    ext x
    simp only [Set.mem_iUnion, Metric.mem_closedBall, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_ge (dist x (0:Space))
    exact ⟨n, hn⟩
  have hlim := tendsto_setIntegral_of_monotone (μ := (volume : Measure Space))
      (f := fun x : Space => ‖b x‖ ^ 2) (fun _ => measurableSet_closedBall) hmono
      (by rw [hunion]; exact hb2.integrableOn)
  rw [hunion, Measure.restrict_univ] at hlim
  have heq : ∀ n : ℕ, (∫ x in (Metric.closedBall (0:Space) (n:ℝ))ᶜ, ‖b x‖ ^ 2)
      = (∫ x : Space, ‖b x‖ ^ 2) - ∫ x in Metric.closedBall (0:Space) (n:ℝ), ‖b x‖ ^ 2 := by
    intro n
    have h := integral_add_compl
      (measurableSet_closedBall (x := (0:Space)) (ε := (n:ℝ))) hb2
    linarith
  simp only [heq]
  have h2 := hlim.const_sub (∫ x : Space, ‖b x‖ ^ 2)
  simpa using h2

set_option maxHeartbeats 1000000 in
/-- **(a)+(b) of the limit passage, in fixed-time form.**  A sequence of
velocity slices converging in `L²` on every ball, with a uniform global `L²`
error bound, pairs convergently against any fixed `L²` field — the far-field
leg being controlled by the field's own `L²` tail rather than by any local
convergence.  This is the estimate the weak-form limit passage needs at each
time, and it needs no compact support of the pairing field. -/
theorem tendsto_integral_officialInner_of_l2loc
    (v : ℕ → Space → Space) (w b : Space → Space) (C : ℝ)
    (hvm : ∀ k, Measurable (v k)) (hwm : Measurable w) (hbm : Measurable b)
    (hv2 : ∀ k, Integrable fun x : Space => ‖v k x‖ ^ 2)
    (hw2 : Integrable fun x : Space => ‖w x‖ ^ 2)
    (hb2 : Integrable fun x : Space => ‖b x‖ ^ 2)
    (hC : ∀ k, (∫ x : Space, ‖v k x - w x‖ ^ 2) ≤ C)
    (hloc : ∀ R : ℝ, Filter.Tendsto
      (fun k => ∫ x in Metric.closedBall (0:Space) R, ‖v k x - w x‖ ^ 2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∫ x : Space, officialInner (v k x) (b x)) Filter.atTop
      (nhds (∫ x : Space, officialInner (w x) (b x))) := by
  classical
  set d : ℕ → Space → Space := fun k x => v k x - w x with hd
  have hdm : ∀ k, Measurable (d k) := fun k => (hvm k).sub hwm
  have hd2 : ∀ k, Integrable fun x : Space => ‖d k x‖ ^ 2 := fun k =>
    integrable_norm_sub_sq (v k) w ((hvm k).sub hwm) (hv2 k) hw2
  have hCnn : 0 ≤ C := le_trans (integral_nonneg fun x => by positivity) (hC 0)
  have hPsi_nn : 0 ≤ ∫ x : Space, ‖b x‖ ^ 2 := integral_nonneg fun x => by positivity
  set Psi : ℝ := ∫ x : Space, ‖b x‖ ^ 2 with hPsi
  -- the difference of the two pairings is the pairing of the difference
  have hkey : ∀ k, (∫ x : Space, officialInner (v k x) (b x))
      - (∫ x : Space, officialInner (w x) (b x)) = ∫ x : Space, officialInner (d k x) (b x) := by
    intro k
    rw [← integral_sub (integrable_officialInner_pairing (hvm k) hbm (hv2 k) hb2)
      (integrable_officialInner_pairing hwm hbm hw2 hb2)]
    congr 1
    funext x
    rw [← officialInner_sub_left]
  have hzero : Filter.Tendsto (fun k => ∫ x : Space, officialInner (d k x) (b x))
      Filter.atTop (nhds 0) := by
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    -- far-field Young parameter
    set μ : ℝ := ε / (12 * (C + 1)) with hμdef
    have hμ : 0 < μ := by
      apply div_pos hε
      linarith
    have hCp : (0:ℝ) < C + 1 := by linarith
    have hfar1 : 3 * (μ / 2 * C) < ε / 4 := by
      have heq : ε / 4 - 3 * (μ / 2 * C) = ε * (C + 2) / (8 * (C + 1)) := by
        rw [hμdef]
        field_simp
        ring
      have hpos : 0 < ε * (C + 2) / (8 * (C + 1)) :=
        div_pos (mul_pos hε (by linarith)) (by linarith)
      linarith
    -- choose the radius so that the far-field mass of `b` is small
    have htail := tendsto_setIntegral_compl_closedBall_norm_sq hb2
    rw [NormedAddGroup.tendsto_nhds_zero] at htail
    obtain ⟨n₀, hn₀⟩ := (htail (ε * μ / 6) (by positivity)).exists_forall_of_atTop
    have hR : ∫ x in (Metric.closedBall (0:Space) (n₀:ℝ))ᶜ, ‖b x‖ ^ 2 < ε * μ / 6 := by
      have := hn₀ n₀ le_rfl
      rw [Real.norm_eq_abs] at this
      exact lt_of_abs_lt this
    -- near-field Young parameter
    set lam : ℝ := 6 * Psi / ε + 1 with hlamdef
    have hlam : 0 < lam := by
      have : 0 ≤ 6 * Psi / ε := by positivity
      linarith
    have hlne : lam ≠ 0 := ne_of_gt hlam
    have hnear2 : 3 * (1 / (2 * lam) * Psi) < ε / 4 := by
      have hcancel : (6 * Psi / ε) * ε = 6 * Psi := div_mul_cancel₀ _ (ne_of_gt hε)
      have h1 : 6 * Psi < lam * ε := by
        rw [hlamdef]
        nlinarith [hε, hcancel]
      have heq : ε / 4 - 3 * (1 / (2 * lam) * Psi) = (lam * ε - 6 * Psi) / (4 * lam) := by
        field_simp
        ring
      have hpos : 0 < (lam * ε - 6 * Psi) / (4 * lam) :=
        div_pos (by linarith) (by linarith)
      linarith
    -- near-field convergence
    have hnear := hloc (n₀:ℝ)
    rw [NormedAddGroup.tendsto_nhds_zero] at hnear
    filter_upwards [hnear (ε / (6 * lam)) (by positivity)] with k hk
    have hAk : (∫ x in Metric.closedBall (0:Space) (n₀:ℝ), ‖d k x‖ ^ 2) < ε / (6 * lam) := by
      rw [Real.norm_eq_abs] at hk
      exact lt_of_abs_lt hk
    have hAknn : 0 ≤ ∫ x in Metric.closedBall (0:Space) (n₀:ℝ), ‖d k x‖ ^ 2 :=
      setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
    -- split
    have hsplit : (∫ x : Space, officialInner (d k x) (b x))
        = (∫ x in Metric.closedBall (0:Space) (n₀:ℝ), officialInner (d k x) (b x))
          + ∫ x in (Metric.closedBall (0:Space) (n₀:ℝ))ᶜ, officialInner (d k x) (b x) :=
      (integral_add_compl measurableSet_closedBall
        (integrable_officialInner_pairing (hdm k) hbm (hd2 k) hb2)).symm
    -- near-field bound
    have hnearB : |∫ x in Metric.closedBall (0:Space) (n₀:ℝ), officialInner (d k x) (b x)|
        < ε / 2 := by
      refine lt_of_le_of_lt (abs_setIntegral_officialInner_le_young _ (hdm k) hbm
        (hd2 k) hb2 hlam) ?_
      have hb_ball : (∫ x in Metric.closedBall (0:Space) (n₀:ℝ), ‖b x‖ ^ 2) ≤ Psi :=
        setIntegral_le_integral hb2 (Filter.Eventually.of_forall fun x => by positivity)
      have h1 : lam / 2 * (∫ x in Metric.closedBall (0:Space) (n₀:ℝ), ‖d k x‖ ^ 2)
          < lam / 2 * (ε / (6 * lam)) :=
        mul_lt_mul_of_pos_left hAk (by linarith)
      have h2 : lam / 2 * (ε / (6 * lam)) = ε / 12 := by
        field_simp
        ring
      have h3 : 1 / (2 * lam) * (∫ x in Metric.closedBall (0:Space) (n₀:ℝ), ‖b x‖ ^ 2)
          ≤ 1 / (2 * lam) * Psi := by
        exact mul_le_mul_of_nonneg_left hb_ball (by positivity)
      have h4 : 3 * (1 / (2 * lam) * Psi) < ε / 4 := hnear2
      linarith
    -- far-field bound
    have hfarB : |∫ x in (Metric.closedBall (0:Space) (n₀:ℝ))ᶜ, officialInner (d k x) (b x)|
        < ε / 2 := by
      refine lt_of_le_of_lt (abs_setIntegral_officialInner_le_young _ (hdm k) hbm
        (hd2 k) hb2 hμ) ?_
      have hd_out : (∫ x in (Metric.closedBall (0:Space) (n₀:ℝ))ᶜ, ‖d k x‖ ^ 2) ≤ C :=
        le_trans (setIntegral_le_integral (hd2 k)
          (Filter.Eventually.of_forall fun x => by positivity)) (hC k)
      have h1 : μ / 2 * (∫ x in (Metric.closedBall (0:Space) (n₀:ℝ))ᶜ, ‖d k x‖ ^ 2)
          ≤ μ / 2 * C := mul_le_mul_of_nonneg_left hd_out (by positivity)
      have h2 : 1 / (2 * μ) * (∫ x in (Metric.closedBall (0:Space) (n₀:ℝ))ᶜ, ‖b x‖ ^ 2)
          < 1 / (2 * μ) * (ε * μ / 6) := mul_lt_mul_of_pos_left hR (by positivity)
      have hmne : μ ≠ 0 := ne_of_gt hμ
      have h3 : 1 / (2 * μ) * (ε * μ / 6) = ε / 12 := by
        field_simp
        ring
      linarith
    rw [Real.norm_eq_abs, hsplit]
    calc |(∫ x in Metric.closedBall (0:Space) (n₀:ℝ), officialInner (d k x) (b x))
            + ∫ x in (Metric.closedBall (0:Space) (n₀:ℝ))ᶜ, officialInner (d k x) (b x)|
        ≤ |∫ x in Metric.closedBall (0:Space) (n₀:ℝ), officialInner (d k x) (b x)|
          + |∫ x in (Metric.closedBall (0:Space) (n₀:ℝ))ᶜ, officialInner (d k x) (b x)| :=
          abs_add_le _ _
      _ < ε := by linarith
  have hfin := hzero.add_const (∫ x : Space, officialInner (w x) (b x))
  simp only [zero_add] at hfin
  refine hfin.congr fun k => ?_
  rw [← hkey k]
  ring

/-!
### The convection leg and the full fixed-time limit passage (certified)

Step (c): the quadratic term.  The far field can no longer be handled by the
test's `L²` tail, because the pairing field is the velocity itself; it is
handled instead by the Schwartz decay `‖x‖·‖∇φ(x)‖ ≤ K`, which makes
`‖∇φ‖` uniformly small outside a ball.  Assembling the two linear legs and this
one gives the whole weak-pairing density's spatial limit passage at each fixed
time.
-/

/-- Young's inequality in the form the two legs of the limit passage need. -/
theorem mul_le_young (a b : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    a * b ≤ lam / 2 * a ^ 2 + 1 / (2 * lam) * b ^ 2 := by
  rw [← sub_nonneg]
  have hid : lam / 2 * a ^ 2 + 1 / (2 * lam) * b ^ 2 - a * b
      = (lam * a - b) ^ 2 / (2 * lam) := by
    field_simp
    ring
  rw [hid]
  positivity

/-- Additivity of the official pairing in the right slot, subtractive form. -/
theorem officialInner_sub_right (x a b : Space) :
    officialInner x (a - b) = officialInner x a - officialInner x b := by
  simp only [officialInner_eq_sum, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

set_option maxHeartbeats 1000000 in
/-- **The bilinear (convection-type) leg of the limit passage.**  A real
integrand dominated by `3‖∇f(x)‖·‖g_k(x)‖·‖h_k(x)‖`, with `g_k → 0` in `L²` on
every ball and both factors uniformly `L²`-bounded, has vanishing integral in the
limit.  The far field is controlled by the Schwartz decay `‖x‖·‖∇f(x)‖ ≤ K`,
which is what replaces compact support of the test; the near field by Young's
inequality with a large parameter. -/
theorem tendsto_integral_of_dominated_l2loc (f : SchwartzVelocity)
    (F : ℕ → Space → ℝ) (g h : ℕ → Space → Space) (C : ℝ) (hCnn : 0 ≤ C)
    (hFint : ∀ k, Integrable (F k))
    (hg2 : ∀ k, Integrable fun x : Space => ‖g k x‖ ^ 2)
    (hh2 : ∀ k, Integrable fun x : Space => ‖h k x‖ ^ 2)
    (hgC : ∀ k, (∫ x : Space, ‖g k x‖ ^ 2) ≤ C)
    (hhC : ∀ k, (∫ x : Space, ‖h k x‖ ^ 2) ≤ C)
    (hdom : ∀ (k : ℕ) (x : Space),
      |F k x| ≤ 3 * ‖fderiv ℝ (⇑f) x‖ * (‖g k x‖ * ‖h k x‖))
    (hgloc : ∀ R : ℝ, Filter.Tendsto
      (fun k => ∫ x in Metric.closedBall (0:Space) R, ‖g k x‖ ^ 2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∫ x : Space, F k x) Filter.atTop (nhds 0) := by
  classical
  set M : ℝ := (SchwartzMap.seminorm ℝ 0 1) f with hMdef
  have hMbd : ∀ x : Space, ‖fderiv ℝ (⇑f) x‖ ≤ M := by
    intro x
    have h1 := f.norm_iteratedFDeriv_le_seminorm ℝ 1 x
    rwa [norm_iteratedFDeriv_one] at h1
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hMbd 0)
  set K : ℝ := (SchwartzMap.seminorm ℝ 1 1) f with hKdef
  have hKbd : ∀ x : Space, ‖x‖ * ‖fderiv ℝ (⇑f) x‖ ≤ K := by
    intro x
    have h1 := SchwartzMap.le_seminorm ℝ 1 1 f x
    rwa [norm_iteratedFDeriv_one, pow_one] at h1
  have hKnn : 0 ≤ K := by
    have := hKbd 0
    simpa using this
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  -- far-field radius
  set R : ℝ := 1 + 12 * K * C / ε with hRdef
  have hR1 : (1:ℝ) ≤ R := by
    have : 0 ≤ 12 * K * C / ε := by positivity
    linarith
  have hRpos : (0:ℝ) < R := by linarith
  have hRfar : 3 * (K / R) * C < ε / 2 := by
    have hεR : ε * R = ε + 12 * K * C := by
      rw [hRdef]
      field_simp
    have heq : ε / 2 - 3 * (K / R) * C = (ε * R - 6 * K * C) / (2 * R) := by
      field_simp
      ring
    have hnum : 0 < ε * R - 6 * K * C := by
      rw [hεR]
      nlinarith
    have hpos : 0 < (ε * R - 6 * K * C) / (2 * R) := div_pos hnum (by linarith)
    linarith
  -- near-field Young parameter
  set lam : ℝ := 1 + 12 * M * C / ε with hlamdef
  have hlam : (0:ℝ) < lam := by
    have : 0 ≤ 12 * M * C / ε := by positivity
    linarith
  have hnearC : 3 * M * (1 / (2 * lam) * C) < ε / 4 := by
    have hεl : ε * lam = ε + 12 * M * C := by
      rw [hlamdef]
      field_simp
    have heq : ε / 4 - 3 * M * (1 / (2 * lam) * C) = (ε * lam - 6 * M * C) / (4 * lam) := by
      field_simp
      ring
    have hnum : 0 < ε * lam - 6 * M * C := by
      rw [hεl]
      nlinarith
    have hpos : 0 < (ε * lam - 6 * M * C) / (4 * lam) := div_pos hnum (by linarith)
    linarith
  -- eventual near-field smallness
  have hnearlim := hgloc R
  rw [NormedAddGroup.tendsto_nhds_zero] at hnearlim
  filter_upwards [hnearlim (ε / (6 * M * lam + 1)) (by positivity)] with k hk
  have hAk : (∫ x in Metric.closedBall (0:Space) R, ‖g k x‖ ^ 2) < ε / (6 * M * lam + 1) := by
    rw [Real.norm_eq_abs] at hk
    exact lt_of_abs_lt hk
  have hAknn : 0 ≤ ∫ x in Metric.closedBall (0:Space) R, ‖g k x‖ ^ 2 :=
    setIntegral_nonneg measurableSet_closedBall fun x _ => by positivity
  -- majorants
  have hmajFar : Integrable fun x : Space =>
      3 * (K / R) * ((‖g k x‖ ^ 2 + ‖h k x‖ ^ 2) / 2) :=
    (((hg2 k).add (hh2 k)).div_const 2).const_mul _
  have hmajNear : Integrable fun x : Space =>
      3 * M * (lam / 2 * ‖g k x‖ ^ 2 + 1 / (2 * lam) * ‖h k x‖ ^ 2) :=
    (((hg2 k).const_mul (lam / 2)).add ((hh2 k).const_mul (1 / (2 * lam)))).const_mul _
  -- the far-field estimate
  have hfar : (∫ x in (Metric.closedBall (0:Space) R)ᶜ, |F k x|) < ε / 2 := by
    have hstep : (∫ x in (Metric.closedBall (0:Space) R)ᶜ, |F k x|)
        ≤ ∫ x in (Metric.closedBall (0:Space) R)ᶜ,
            3 * (K / R) * ((‖g k x‖ ^ 2 + ‖h k x‖ ^ 2) / 2) := by
      refine setIntegral_mono_on (hFint k).abs.integrableOn hmajFar.integrableOn
        measurableSet_closedBall.compl fun x hx => ?_
      have hxR : R ≤ ‖x‖ := by
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
        exact hx.le
      have hdecay : ‖fderiv ℝ (⇑f) x‖ ≤ K / R := by
        have hxpos : (0:ℝ) < ‖x‖ := lt_of_lt_of_le hRpos hxR
        have h1 : ‖x‖ * ‖fderiv ℝ (⇑f) x‖ ≤ K := hKbd x
        rw [le_div_iff₀ hRpos]
        nlinarith [norm_nonneg (fderiv ℝ (⇑f) x)]
      have h2 : |F k x| ≤ 3 * (K / R) * (‖g k x‖ * ‖h k x‖) := by
        refine le_trans (hdom k x) ?_
        have hnn : 0 ≤ ‖g k x‖ * ‖h k x‖ := by positivity
        nlinarith [hnn, hdecay]
      have h3 : ‖g k x‖ * ‖h k x‖ ≤ (‖g k x‖ ^ 2 + ‖h k x‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖g k x‖ - ‖h k x‖)]
      have hKR : 0 ≤ 3 * (K / R) := by positivity
      nlinarith [h2, h3, hKR]
    have hstep2 : (∫ x in (Metric.closedBall (0:Space) R)ᶜ,
        3 * (K / R) * ((‖g k x‖ ^ 2 + ‖h k x‖ ^ 2) / 2))
        ≤ ∫ x : Space, 3 * (K / R) * ((‖g k x‖ ^ 2 + ‖h k x‖ ^ 2) / 2) := by
      refine setIntegral_le_integral hmajFar (Filter.Eventually.of_forall fun x => ?_)
      have : 0 ≤ 3 * (K / R) := by positivity
      have h2 : 0 ≤ (‖g k x‖ ^ 2 + ‖h k x‖ ^ 2) / 2 := by positivity
      exact mul_nonneg this h2
    have hval : (∫ x : Space, 3 * (K / R) * ((‖g k x‖ ^ 2 + ‖h k x‖ ^ 2) / 2))
        = 3 * (K / R) * (((∫ x : Space, ‖g k x‖ ^ 2) + ∫ x : Space, ‖h k x‖ ^ 2) / 2) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
        integral_add (hg2 k) (hh2 k)]
    have hle : 3 * (K / R) * (((∫ x : Space, ‖g k x‖ ^ 2) + ∫ x : Space, ‖h k x‖ ^ 2) / 2)
        ≤ 3 * (K / R) * C := by
      have hKR : 0 ≤ 3 * (K / R) := by positivity
      have := hgC k
      have := hhC k
      nlinarith [hgC k, hhC k, hKR]
    linarith [hstep, hstep2, hval ▸ hle]
  -- the near-field estimate
  have hnear : (∫ x in Metric.closedBall (0:Space) R, |F k x|) < ε / 2 := by
    have hstep : (∫ x in Metric.closedBall (0:Space) R, |F k x|)
        ≤ ∫ x in Metric.closedBall (0:Space) R,
            3 * M * (lam / 2 * ‖g k x‖ ^ 2 + 1 / (2 * lam) * ‖h k x‖ ^ 2) := by
      refine setIntegral_mono_on (hFint k).abs.integrableOn hmajNear.integrableOn
        measurableSet_closedBall fun x _ => ?_
      have h2 : |F k x| ≤ 3 * M * (‖g k x‖ * ‖h k x‖) := by
        refine le_trans (hdom k x) ?_
        have hnn : 0 ≤ ‖g k x‖ * ‖h k x‖ := by positivity
        nlinarith [hnn, hMbd x]
      have h3 : ‖g k x‖ * ‖h k x‖
          ≤ lam / 2 * ‖g k x‖ ^ 2 + 1 / (2 * lam) * ‖h k x‖ ^ 2 :=
        mul_le_young _ _ hlam
      nlinarith [h2, h3, hMnn]
    have hval : (∫ x in Metric.closedBall (0:Space) R,
        3 * M * (lam / 2 * ‖g k x‖ ^ 2 + 1 / (2 * lam) * ‖h k x‖ ^ 2))
        = 3 * M * (lam / 2 * (∫ x in Metric.closedBall (0:Space) R, ‖g k x‖ ^ 2)
            + 1 / (2 * lam) * ∫ x in Metric.closedBall (0:Space) R, ‖h k x‖ ^ 2) := by
      rw [MeasureTheory.integral_const_mul,
        integral_add ((hg2 k).const_mul (lam / 2)).integrableOn
          ((hh2 k).const_mul (1 / (2 * lam))).integrableOn,
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hhball : (∫ x in Metric.closedBall (0:Space) R, ‖h k x‖ ^ 2) ≤ C :=
      le_trans (setIntegral_le_integral (hh2 k)
        (Filter.Eventually.of_forall fun x => by positivity)) (hhC k)
    have hb1 : 3 * M * (lam / 2 * (∫ x in Metric.closedBall (0:Space) R, ‖g k x‖ ^ 2))
        < ε / 4 := by
      have hMl : 0 ≤ 3 * M * (lam / 2) := by positivity
      have hstep2 : 3 * M * (lam / 2) * (∫ x in Metric.closedBall (0:Space) R, ‖g k x‖ ^ 2)
          ≤ 3 * M * (lam / 2) * (ε / (6 * M * lam + 1)) :=
        mul_le_mul_of_nonneg_left hAk.le hMl
      have hden : (0:ℝ) < 6 * M * lam + 1 := by positivity
      have hfinal : 3 * M * (lam / 2) * (ε / (6 * M * lam + 1)) < ε / 4 := by
        rw [mul_div_assoc'] at *
        have heq : ε / 4 - 3 * M * (lam / 2) * ε / (6 * M * lam + 1)
            = (ε * (6 * M * lam + 1) - 6 * M * lam * ε) / (4 * (6 * M * lam + 1)) := by
          field_simp
          ring
        have hnum : 0 < ε * (6 * M * lam + 1) - 6 * M * lam * ε := by nlinarith
        have hpos : 0 < (ε * (6 * M * lam + 1) - 6 * M * lam * ε) / (4 * (6 * M * lam + 1)) :=
          div_pos hnum (by linarith)
        linarith
      nlinarith [hstep2, hfinal]
    have hb2 : 3 * M * (1 / (2 * lam) * (∫ x in Metric.closedBall (0:Space) R, ‖h k x‖ ^ 2))
        ≤ 3 * M * (1 / (2 * lam) * C) := by
      have h1 : 1 / (2 * lam) * (∫ x in Metric.closedBall (0:Space) R, ‖h k x‖ ^ 2)
          ≤ 1 / (2 * lam) * C := mul_le_mul_of_nonneg_left hhball (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hdist : 3 * M * (lam / 2 * (∫ x in Metric.closedBall (0:Space) R, ‖g k x‖ ^ 2)
          + 1 / (2 * lam) * ∫ x in Metric.closedBall (0:Space) R, ‖h k x‖ ^ 2)
        = 3 * M * (lam / 2 * (∫ x in Metric.closedBall (0:Space) R, ‖g k x‖ ^ 2))
          + 3 * M * (1 / (2 * lam) * ∫ x in Metric.closedBall (0:Space) R, ‖h k x‖ ^ 2) := by
      ring
    linarith [hstep, hb1, hb2, hnearC, hval.le, hval.ge, hdist.le, hdist.ge]
  -- assemble
  have hsplit : (∫ x : Space, |F k x|)
      = (∫ x in Metric.closedBall (0:Space) R, |F k x|)
        + ∫ x in (Metric.closedBall (0:Space) R)ᶜ, |F k x| :=
    (integral_add_compl measurableSet_closedBall (hFint k).abs).symm
  rw [Real.norm_eq_abs]
  calc |∫ x : Space, F k x| ≤ ∫ x : Space, |F k x| := abs_integral_le_integral_abs
    _ = (∫ x in Metric.closedBall (0:Space) R, |F k x|)
        + ∫ x in (Metric.closedBall (0:Space) R)ᶜ, |F k x| := hsplit
    _ < ε := by linarith

set_option maxHeartbeats 1000000 in
/-- **The convection (quadratic) term passes to the limit.**  Step (c): split
`⟨u,(u·∇)φ⟩ − ⟨u_m,(u_m·∇)φ⟩ = ⟨u−u_m,(u·∇)φ⟩ + ⟨u_m,((u−u_m)·∇)φ⟩` and drive
each leg to zero by the dominated `L²_loc` estimate above. -/
theorem tendsto_integral_convection_of_l2loc (f : SchwartzVelocity)
    (v : ℕ → Space → Space) (w : Space → Space) (C : ℝ) (hCnn : 0 ≤ C)
    (hvm : ∀ k, Measurable (v k)) (hwm : Measurable w)
    (hv2 : ∀ k, Integrable fun x : Space => ‖v k x‖ ^ 2)
    (hw2 : Integrable fun x : Space => ‖w x‖ ^ 2)
    (hvC : ∀ k, (∫ x : Space, ‖v k x‖ ^ 2) ≤ C)
    (hwC : (∫ x : Space, ‖w x‖ ^ 2) ≤ C)
    (hdC : ∀ k, (∫ x : Space, ‖v k x - w x‖ ^ 2) ≤ C)
    (hloc : ∀ R : ℝ, Filter.Tendsto
      (fun k => ∫ x in Metric.closedBall (0:Space) R, ‖v k x - w x‖ ^ 2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∫ x : Space, officialInner (v k x) (fderiv ℝ (⇑f) x (v k x)))
      Filter.atTop (nhds (∫ x : Space, officialInner (w x) (fderiv ℝ (⇑f) x (w x)))) := by
  classical
  set M : ℝ := (SchwartzMap.seminorm ℝ 0 1) f with hMdef
  have hMbd : ∀ x : Space, ‖fderiv ℝ (⇑f) x‖ ≤ M := by
    intro x
    have h1 := f.norm_iteratedFDeriv_le_seminorm ℝ 1 x
    rwa [norm_iteratedFDeriv_one] at h1
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hMbd 0)
  have hfc : Continuous fun x : Space => fderiv ℝ (⇑f) x :=
    (f.smooth ⊤).continuous_fderiv (by simp)
  have happly : Continuous fun p : (Space →L[ℝ] Space) × Space => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  have hcont2 : Continuous fun q : Space × Space => fderiv ℝ (⇑f) q.1 q.2 :=
    happly.comp (hfc.prodMap continuous_id)
  have hAmeas : ∀ u : Space → Space, Measurable u →
      Measurable fun x : Space => fderiv ℝ (⇑f) x (u x) :=
    fun u hu => hcont2.measurable.comp (measurable_id.prodMk hu)
  have hAnorm : ∀ (u : Space → Space) (x : Space),
      ‖fderiv ℝ (⇑f) x (u x)‖ ≤ M * ‖u x‖ := by
    intro u x
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_mul_of_nonneg_right (hMbd x) (norm_nonneg _))
  have hAsq : ∀ u : Space → Space, Measurable u → (Integrable fun x : Space => ‖u x‖ ^ 2) →
      Integrable fun x : Space => ‖fderiv ℝ (⇑f) x (u x)‖ ^ 2 := by
    intro u hu hu2
    refine (hu2.const_mul (M ^ 2)).mono'
      ((hAmeas u hu).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hAnorm u x, norm_nonneg (fderiv ℝ (⇑f) x (u x)), norm_nonneg (u x), hMnn]
  set d : ℕ → Space → Space := fun k x => v k x - w x with hddef
  have hdm : ∀ k, Measurable (d k) := fun k => (hvm k).sub hwm
  have hd2 : ∀ k, Integrable fun x : Space => ‖d k x‖ ^ 2 := fun k =>
    integrable_norm_sub_sq (v k) w ((hvm k).sub hwm) (hv2 k) hw2
  have hF1int : ∀ k, Integrable fun x : Space =>
      officialInner (d k x) (fderiv ℝ (⇑f) x (v k x)) := fun k =>
    integrable_officialInner_pairing (hdm k) (hAmeas _ (hvm k)) (hd2 k)
      (hAsq _ (hvm k) (hv2 k))
  have hF2int : ∀ k, Integrable fun x : Space =>
      officialInner (w x) (fderiv ℝ (⇑f) x (d k x)) := fun k =>
    integrable_officialInner_pairing hwm (hAmeas _ (hdm k)) hw2
      (hAsq _ (hdm k) (hd2 k))
  have hFvint : ∀ k, Integrable fun x : Space =>
      officialInner (v k x) (fderiv ℝ (⇑f) x (v k x)) := fun k =>
    integrable_convection_pairing f (hvm k) (hv2 k)
  have hFwint : Integrable fun x : Space =>
      officialInner (w x) (fderiv ℝ (⇑f) x (w x)) :=
    integrable_convection_pairing f hwm hw2
  have hsplit : ∀ k, (∫ x : Space, officialInner (v k x) (fderiv ℝ (⇑f) x (v k x)))
      - (∫ x : Space, officialInner (w x) (fderiv ℝ (⇑f) x (w x)))
      = (∫ x : Space, officialInner (d k x) (fderiv ℝ (⇑f) x (v k x)))
        + ∫ x : Space, officialInner (w x) (fderiv ℝ (⇑f) x (d k x)) := by
    intro k
    rw [← integral_sub (hFvint k) hFwint, ← integral_add (hF1int k) (hF2int k)]
    congr 1
    funext x
    have hlin : fderiv ℝ (⇑f) x (d k x)
        = fderiv ℝ (⇑f) x (v k x) - fderiv ℝ (⇑f) x (w x) := by
      simp only [hddef]
      exact map_sub _ _ _
    rw [hlin, officialInner_sub_right, show d k x = v k x - w x from rfl,
      officialInner_sub_left]
    ring
  have hT1 : Filter.Tendsto
      (fun k => ∫ x : Space, officialInner (d k x) (fderiv ℝ (⇑f) x (v k x)))
      Filter.atTop (nhds 0) := by
    refine tendsto_integral_of_dominated_l2loc f
      (fun k x => officialInner (d k x) (fderiv ℝ (⇑f) x (v k x))) d v C hCnn
      hF1int hd2 hv2 hdC hvC (fun k x => ?_) hloc
    have h1 := abs_officialInner_le_three (d k x) (fderiv ℝ (⇑f) x (v k x))
    have h2 := (fderiv ℝ (⇑f) x).le_opNorm (v k x)
    nlinarith [h1, h2, norm_nonneg (d k x), norm_nonneg (v k x),
      norm_nonneg (fderiv ℝ (⇑f) x)]
  have hT2 : Filter.Tendsto
      (fun k => ∫ x : Space, officialInner (w x) (fderiv ℝ (⇑f) x (d k x)))
      Filter.atTop (nhds 0) := by
    refine tendsto_integral_of_dominated_l2loc f
      (fun k x => officialInner (w x) (fderiv ℝ (⇑f) x (d k x))) d (fun _ => w) C hCnn
      hF2int hd2 (fun _ => hw2) hdC (fun _ => hwC) (fun k x => ?_) hloc
    have h1 := abs_officialInner_le_three (w x) (fderiv ℝ (⇑f) x (d k x))
    have h2 := (fderiv ℝ (⇑f) x).le_opNorm (d k x)
    nlinarith [h1, h2, norm_nonneg (d k x), norm_nonneg (w x),
      norm_nonneg (fderiv ℝ (⇑f) x)]
  have hzero : Filter.Tendsto
      (fun k => (∫ x : Space, officialInner (v k x) (fderiv ℝ (⇑f) x (v k x)))
        - ∫ x : Space, officialInner (w x) (fderiv ℝ (⇑f) x (w x)))
      Filter.atTop (nhds 0) := by
    have hsum := hT1.add hT2
    rw [add_zero] at hsum
    exact hsum.congr fun k => (hsplit k).symm
  have hfin := hzero.add_const (∫ x : Space, officialInner (w x) (fderiv ℝ (⇑f) x (w x)))
  rw [zero_add] at hfin
  exact hfin.congr fun k => by ring

/-- One directional spatial derivative of a Schwartz slice, packaged as a
Schwartz map. -/
noncomputable def schwartzDeriv (f : SchwartzVelocity) (e : Space) : SchwartzVelocity :=
  SchwartzMap.evalCLM ℝ Space Space e (SchwartzMap.fderivCLM ℝ Space Space f)

theorem schwartzDeriv_apply (f : SchwartzVelocity) (e x : Space) :
    schwartzDeriv f e x = fderiv ℝ (⇑f) x e := by
  simp [schwartzDeriv]

/-- **The spatial Laplacian of a Schwartz slice is a Schwartz map.**  Written as
an explicit three-term sum of second directional derivatives, so that
measurability and square-integrability of the Laplacian factor of the weak
pairing come for free. -/
noncomputable def schwartzLaplacian (f : SchwartzVelocity) : SchwartzVelocity :=
  schwartzDeriv (schwartzDeriv f (basisVector 0)) (basisVector 0)
    + schwartzDeriv (schwartzDeriv f (basisVector 1)) (basisVector 1)
    + schwartzDeriv (schwartzDeriv f (basisVector 2)) (basisVector 2)

theorem schwartzLaplacian_apply (f : SchwartzVelocity) (t : ℝ) (x : Space) :
    schwartzLaplacian f x = laplacian (fun _ => (⇑f : Space → Space)) t x := by
  have hg : ∀ e : Space, (fun y : Space => fderiv ℝ (⇑f) y e) = ⇑(schwartzDeriv f e) := by
    intro e
    funext y
    rw [schwartzDeriv_apply]
  unfold laplacian
  rw [Fin.sum_univ_three]
  simp only [schwartzLaplacian, SchwartzMap.add_apply]
  rw [hg (basisVector 0), hg (basisVector 1), hg (basisVector 2),
    schwartzDeriv_apply, schwartzDeriv_apply, schwartzDeriv_apply]

set_option maxHeartbeats 1000000 in
/-- **The full fixed-time spatial limit passage for the weak-form density.**
Steps (a), (b), (c) of the Leray limit passage, assembled: for velocity slices
converging in `L²` on every ball with a uniform global `L²` bound, the whole
weak-pairing density integral converges.  The linear legs go by the `L²`-tail
estimate, the quadratic convection leg by the dominated `L²_loc` estimate. -/
theorem tendsto_integral_weakPairingDensity_of_l2loc (ν : ℝ)
    (φ : DivergenceFreeTestFunction) (t : ℝ) (ht : 0 ≤ t)
    (v : ℕ → Space → Space) (w : Space → Space) (C : ℝ) (hCnn : 0 ≤ C)
    (hvm : ∀ k, Measurable (v k)) (hwm : Measurable w)
    (hv2 : ∀ k, Integrable fun x : Space => ‖v k x‖ ^ 2)
    (hw2 : Integrable fun x : Space => ‖w x‖ ^ 2)
    (hvC : ∀ k, (∫ x : Space, ‖v k x‖ ^ 2) ≤ C)
    (hwC : (∫ x : Space, ‖w x‖ ^ 2) ≤ C)
    (hdC : ∀ k, (∫ x : Space, ‖v k x - w x‖ ^ 2) ≤ C)
    (hloc : ∀ R : ℝ, Filter.Tendsto
      (fun k => ∫ x in Metric.closedBall (0:Space) R, ‖v k x - w x‖ ^ 2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∫ x : Space, weakPairingDensity ν (fun _ => v k) φ t x)
      Filter.atTop (nhds (∫ x : Space, weakPairingDensity ν (fun _ => w) φ t x)) := by
  classical
  set b1 : SchwartzVelocity := φ.timeDerivSchwartz t with hb1def
  set b3 : SchwartzVelocity := ν • schwartzLaplacian (φ.field t) with hb3def
  have hdec : ∀ (u : Space → Space) (x : Space),
      weakPairingDensity ν (fun _ => u) φ t x
        = officialInner (u x) (b1 x)
          + officialInner (u x) (fderiv ℝ (⇑(φ.field t)) x (u x))
          + officialInner (u x) (b3 x) := by
    intro u x
    unfold weakPairingDensity
    rw [officialInner_add_right, officialInner_add_right]
    congr 1
    · congr 1
      · congr 1
        exact φ.timeDeriv_eq t ht x
    · congr 1
      rw [hb3def]
      show ν • laplacian (fun s => (φ.field s : Space → Space)) t x
        = (ν • schwartzLaplacian (φ.field t) : SchwartzVelocity) x
      rw [SchwartzMap.smul_apply, schwartzLaplacian_apply (φ.field t) t x]
      rfl
  have hint1 : ∀ u : Space → Space, Measurable u → (Integrable fun x : Space => ‖u x‖ ^ 2) →
      Integrable fun x : Space => officialInner (u x) (b1 x) := fun u hu hu2 =>
    integrable_officialInner_pairing hu b1.continuous.measurable hu2
      (integrable_norm_sq_schwartz b1)
  have hint3 : ∀ u : Space → Space, Measurable u → (Integrable fun x : Space => ‖u x‖ ^ 2) →
      Integrable fun x : Space => officialInner (u x) (b3 x) := fun u hu hu2 =>
    integrable_officialInner_pairing hu b3.continuous.measurable hu2
      (integrable_norm_sq_schwartz b3)
  have hint2 : ∀ u : Space → Space, Measurable u → (Integrable fun x : Space => ‖u x‖ ^ 2) →
      Integrable fun x : Space =>
        officialInner (u x) (fderiv ℝ (⇑(φ.field t)) x (u x)) := fun u hu hu2 =>
    integrable_convection_pairing (φ.field t) hu hu2
  have hsplit : ∀ u : Space → Space, Measurable u → (Integrable fun x : Space => ‖u x‖ ^ 2) →
      (∫ x : Space, weakPairingDensity ν (fun _ => u) φ t x)
        = (∫ x : Space, officialInner (u x) (b1 x))
          + (∫ x : Space, officialInner (u x) (fderiv ℝ (⇑(φ.field t)) x (u x)))
          + ∫ x : Space, officialInner (u x) (b3 x) := by
    intro u hu hu2
    calc (∫ x : Space, weakPairingDensity ν (fun _ => u) φ t x)
        = ∫ x : Space, (officialInner (u x) (b1 x)
            + officialInner (u x) (fderiv ℝ (⇑(φ.field t)) x (u x))
            + officialInner (u x) (b3 x)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hdec u x)
      _ = (∫ x : Space, (officialInner (u x) (b1 x)
            + officialInner (u x) (fderiv ℝ (⇑(φ.field t)) x (u x))))
          + ∫ x : Space, officialInner (u x) (b3 x) :=
          integral_add ((hint1 u hu hu2).add (hint2 u hu hu2)) (hint3 u hu hu2)
      _ = (∫ x : Space, officialInner (u x) (b1 x))
          + (∫ x : Space, officialInner (u x) (fderiv ℝ (⇑(φ.field t)) x (u x)))
          + ∫ x : Space, officialInner (u x) (b3 x) := by
          rw [integral_add (hint1 u hu hu2) (hint2 u hu hu2)]
  have hL1 : Filter.Tendsto (fun k => ∫ x : Space, officialInner (v k x) (b1 x))
      Filter.atTop (nhds (∫ x : Space, officialInner (w x) (b1 x))) :=
    tendsto_integral_officialInner_of_l2loc v w (⇑b1) C hvm hwm b1.continuous.measurable
      hv2 hw2 (integrable_norm_sq_schwartz b1) hdC hloc
  have hL3 : Filter.Tendsto (fun k => ∫ x : Space, officialInner (v k x) (b3 x))
      Filter.atTop (nhds (∫ x : Space, officialInner (w x) (b3 x))) :=
    tendsto_integral_officialInner_of_l2loc v w (⇑b3) C hvm hwm b3.continuous.measurable
      hv2 hw2 (integrable_norm_sq_schwartz b3) hdC hloc
  have hL2 : Filter.Tendsto
      (fun k => ∫ x : Space, officialInner (v k x) (fderiv ℝ (⇑(φ.field t)) x (v k x)))
      Filter.atTop
      (nhds (∫ x : Space, officialInner (w x) (fderiv ℝ (⇑(φ.field t)) x (w x)))) :=
    tendsto_integral_convection_of_l2loc (φ.field t) v w C hCnn hvm hwm hv2 hw2 hvC hwC
      hdC hloc
  have hsum := (hL1.add hL2).add hL3
  rw [hsplit w hwm hw2]
  exact hsum.congr fun k => (hsplit (v k) (hvm k) (hv2 k)).symm

/-!
### `L¹`-to-a.e. extraction: from the time-integrated error to a fixed time

`StrongL2LocLimit` controls the **time-integrated** local `L²` error, while the
fixed-time passage `tendsto_integral_weakPairingDensity_of_l2loc` above consumes
the error at a **single** time.  The bridge is Markov's inequality: a sequence of
nonnegative functions whose integrals vanish converges to `0` in measure, hence
a.e. along a subsequence.  Diagonalising over the countably many integer radii
and using monotonicity of `R ↦ ∫_{B_R}` upgrades this to a single subsequence
along which, for a.e. time, the local error vanishes at *every* radius — exactly
the pointwise hypothesis `tendsto_integral_weakPairingDensity_of_l2loc` needs.

These two theorems are the analytic content that the frontier note on
`exists_lerayLimitData` records as the pointwise input of the limit passage; they
are stated for a general set and a general nonnegative sequence, so they carry no
Navier–Stokes-specific hypothesis and cannot be vacuous.
-/

/-- **Measurability of a nonnegative spatial set-integral in the time variable,
with no slicewise integrability hypothesis.**  `inner_sq_measurable` needs
`Integrable` at *every* `t`, which a velocity evolution supplies only for
`0 ≤ t`; the Bochner junk value rescues the statement instead.  For a
nonnegative jointly measurable integrand the Bochner integral agrees with
`(∫⁻ …).toReal` **everywhere**: on the integrable locus by
`ofReal_integral_eq_lintegral_ofReal`, and off it because both sides are `0`
(Bochner by `integral_undef`, the lower integral because it is `⊤`). -/
theorem measurable_setIntegral_of_jointlyMeasurable_nonneg
    {B : Set Space} (hB : MeasurableSet B)
    {F : ℝ → Space → ℝ} (hF : Measurable fun z : ℝ × Space => F z.1 z.2)
    (hnn : ∀ (t : ℝ) (x : Space), 0 ≤ F t x) :
    Measurable fun t : ℝ => ∫ x in B, F t x := by
  classical
  have hFind : Measurable fun z : ℝ × Space =>
      if z.2 ∈ B then ENNReal.ofReal (F z.1 z.2) else 0 := by
    refine Measurable.ite (measurable_snd hB) hF.ennreal_ofReal measurable_const
  have hlint : Measurable fun t : ℝ => ∫⁻ x in B, ENNReal.ofReal (F t x) := by
    have h1 : Measurable fun t : ℝ =>
        ∫⁻ x : Space, (if x ∈ B then ENNReal.ofReal (F t x) else 0) :=
      Measurable.lintegral_prod_right
        (ν := volume)
        (f := fun (t : ℝ) (x : Space) => if x ∈ B then ENNReal.ofReal (F t x) else 0)
        hFind
    have h2 : (fun t : ℝ => ∫⁻ x : Space, (if x ∈ B then ENNReal.ofReal (F t x) else 0))
        = fun t : ℝ => ∫⁻ x in B, ENNReal.ofReal (F t x) := by
      funext t
      rw [← lintegral_indicator hB]
      rfl
    rw [← h2]
    exact h1
  have heq : (fun t : ℝ => ∫ x in B, F t x)
      = fun t : ℝ => (∫⁻ x in B, ENNReal.ofReal (F t x)).toReal := by
    funext t
    by_cases hi : IntegrableOn (F t) B volume
    · rw [← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun x => hnn t x),
        ENNReal.toReal_ofReal (integral_nonneg fun x => hnn t x)]
    · have hae : AEStronglyMeasurable (F t) (volume.restrict B) :=
        (hF.comp measurable_prodMk_left).aestronglyMeasurable
      have hnf : ¬ HasFiniteIntegral (F t) (volume.restrict B) := fun h => hi ⟨hae, h⟩
      have htop : ∫⁻ x in B, ENNReal.ofReal (F t x) = ⊤ := by
        have hne : ¬ (∫⁻ x in B, ‖F t x‖ₑ) < ⊤ := by
          simpa [HasFiniteIntegral] using hnf
        have hcongr : ∫⁻ x in B, ‖F t x‖ₑ = ∫⁻ x in B, ENNReal.ofReal (F t x) :=
          lintegral_congr_ae (Filter.Eventually.of_forall fun x =>
            Real.enorm_eq_ofReal (hnn t x))
        rw [← hcongr]
        exact top_le_iff.mp (not_lt.mp hne)
      rw [integral_undef hi, htop, ENNReal.toReal_top]
  rw [heq]
  exact hlint.ennreal_toReal

/-- **Markov + Riesz.**  If nonnegative measurable functions have set integrals
tending to `0` over `s`, then some subsequence tends to `0` almost everywhere on
`s`.  (`L¹`-null ⟹ null in measure ⟹ a.e.-null along a subsequence.) -/
theorem exists_subseq_ae_tendsto_zero_of_tendsto_setIntegral
    (s : Set ℝ) (g : ℕ → ℝ → ℝ)
    (hgm : ∀ k, Measurable (g k)) (hg0 : ∀ k t, 0 ≤ g k t)
    (hgi : ∀ k, IntegrableOn (g k) s)
    (hg : Filter.Tendsto (fun k => ∫ t in s, g k t) Filter.atTop (nhds 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ t ∂(volume.restrict s),
        Filter.Tendsto (fun j => g (ψ j) t) Filter.atTop (nhds 0) := by
  classical
  set μ : Measure ℝ := volume.restrict s with hμdef
  have hmeas : ∀ k, AEStronglyMeasurable (g k) μ := fun k => (hgm k).aestronglyMeasurable
  have hrw : ∀ k, eLpNorm (g k - fun _ : ℝ => (0 : ℝ)) 1 μ
      = ENNReal.ofReal (∫ t in s, g k t) := by
    intro k
    have hsub : (g k - fun _ : ℝ => (0 : ℝ)) = g k := by
      funext t; simp
    rw [hsub, eLpNorm_one_eq_lintegral_enorm]
    have hcongr : ∫⁻ x : ℝ, ‖g k x‖ₑ ∂μ = ∫⁻ x : ℝ, ENNReal.ofReal (g k x) ∂μ :=
      lintegral_congr_ae (Filter.Eventually.of_forall fun t =>
        Real.enorm_eq_ofReal (hg0 k t))
    rw [hcongr]
    exact (ofReal_integral_eq_lintegral_ofReal (hgi k)
      (Filter.Eventually.of_forall fun t => hg0 k t)).symm
  have hL1 : Filter.Tendsto (fun k => eLpNorm (g k - fun _ : ℝ => (0 : ℝ)) 1 μ)
      Filter.atTop (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hg
    simp only [ENNReal.ofReal_zero] at this
    exact this.congr fun k => (hrw k).symm
  have hTIM : TendstoInMeasure μ g Filter.atTop (fun _ : ℝ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hmeas
      aestronglyMeasurable_const hL1
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
  exact ⟨ns, hns, hae⟩

/-- **Cantor diagonal over the radius ladder: `StrongL2LocLimit` upgrades to
a.e.-fixed-time local `L²` convergence at *every* radius.**

`StrongL2LocLimit` is a statement about the time-integrated error on each
window; `tendsto_integral_weakPairingDensity_of_l2loc` consumes the error at a
single time and at every radius simultaneously.  Radius by radius the previous
theorem extracts an a.e.-convergent subsequence, `exists_diagonal_subseq`
(already used for the window-Cauchy ladder) threads those extractions into one
subsequence, and monotonicity of `R ↦ ∫_{B_R}` on a nonnegative integrand
passes from the integer radii to all real radii.

The bound hypothesis `hbd` is the uniform `L²` displacement bound the Galerkin
energy estimate supplies (`≤ 4·G.bound`); it is what makes the time integrals
genuine rather than Bochner junk values, so it cannot be dropped. -/
theorem exists_subseq_ae_tendsto_l2loc_slices
    (uSeq : ℕ → VelocityEvolution) (u : VelocityEvolution) (T C : ℝ)
    (hmeas : JointlyMeasurable uSeq)
    (humeas : Measurable fun z : ℝ × Space => u z.1 z.2)
    (hint : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → Integrable fun x : Space => ‖uSeq k t x‖ ^ 2)
    (huint : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖u t x‖ ^ 2)
    (hbd : ∀ (k : ℕ) (t : ℝ), 0 < t → (∫ x : Space, ‖uSeq k t x - u t x‖ ^ 2) ≤ C)
    (hlim : StrongL2LocLimit uSeq u) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) T)), ∀ R : ℝ,
        Filter.Tendsto
          (fun j => ∫ x in Metric.closedBall (0:Space) R, ‖uSeq (ψ j) t x - u t x‖ ^ 2)
          Filter.atTop (nhds 0) := by
  classical
  set F : ℝ → ℕ → ℝ → ℝ := fun R k t =>
    ∫ x in Metric.closedBall (0:Space) R, ‖uSeq k t x - u t x‖ ^ 2 with hFdef
  have hdmeas : ∀ k, Measurable fun z : ℝ × Space => ‖uSeq k z.1 z.2 - u z.1 z.2‖ ^ 2 :=
    fun k => (((hmeas k).sub humeas).norm.pow_const 2)
  have hFm : ∀ (R : ℝ) (k : ℕ), Measurable (F R k) := fun R k =>
    measurable_setIntegral_of_jointlyMeasurable_nonneg measurableSet_closedBall
      (hdmeas k) (fun t x => by positivity)
  have hFnn : ∀ (R : ℝ) (k : ℕ) (t : ℝ), 0 ≤ F R k t := fun R k t =>
    integral_nonneg fun x => by positivity
  have hdint : ∀ (k : ℕ) (t : ℝ), 0 ≤ t →
      Integrable fun x : Space => ‖uSeq k t x - u t x‖ ^ 2 := by
    intro k t ht
    exact integrable_norm_sub_sq (uSeq k t) (u t)
      (((hmeas k).comp measurable_prodMk_left).sub (humeas.comp measurable_prodMk_left))
      (hint k t ht) (huint t ht)
  have hFle : ∀ (R : ℝ) (k : ℕ) (t : ℝ), t ∈ Set.Ioc (0:ℝ) T → F R k t ≤ C := by
    intro R k t ht
    refine le_trans ?_ (hbd k t ht.1)
    exact setIntegral_le_integral (hdint k t ht.1.le)
      (Filter.Eventually.of_forall fun x => by positivity)
  have hFi : ∀ (R : ℝ) (k : ℕ), IntegrableOn (F R k) (Set.Ioc (0:ℝ) T) := by
    intro R k
    have hb : IntegrableOn (fun _ : ℝ => C) (Set.Ioc (0:ℝ) T) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    refine hb.mono' (hFm R k).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn R k t)]
    exact hFle R k t ht
  set Q : ℕ → (ℕ → ℕ) → Prop := fun n τ =>
    ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) T)),
      Filter.Tendsto (fun j => F (n:ℝ) (τ j) t) Filter.atTop (nhds 0) with hQdef
  have hsub : ∀ (n : ℕ) (τ ρ : ℕ → ℕ), Q n τ → StrictMono ρ → Q n (τ ∘ ρ) := by
    intro n τ ρ hQn hρ
    filter_upwards [hQn] with t ht
    exact ht.comp hρ.tendsto_atTop
  have htail : ∀ (n N : ℕ) (τ : ℕ → ℕ), Q n (fun k => τ (k + N)) → Q n τ := by
    intro n N τ hQn
    filter_upwards [hQn] with t ht
    exact (Filter.tendsto_add_atTop_iff_nat N).mp ht
  have hstep : ∀ (n : ℕ) (τ : ℕ → ℕ), StrictMono τ → ∃ ρ, StrictMono ρ ∧ Q n (τ ∘ ρ) := by
    intro n τ hτ
    have hgo : Filter.Tendsto (fun k => ∫ t in Set.Ioc (0:ℝ) T, F (n:ℝ) (τ k) t)
        Filter.atTop (nhds 0) := (hlim T (n:ℝ)).comp hτ.tendsto_atTop
    obtain ⟨ρ, hρ, hae⟩ :=
      exists_subseq_ae_tendsto_zero_of_tendsto_setIntegral (Set.Ioc (0:ℝ) T)
        (fun k => F (n:ℝ) (τ k)) (fun k => hFm _ _) (fun k t => hFnn _ _ t)
        (fun k => hFi _ _) hgo
    exact ⟨ρ, hρ, hae⟩
  obtain ⟨ψ, hψ, hQψ⟩ := exists_diagonal_subseq Q hsub htail hstep
  refine ⟨ψ, hψ, ?_⟩
  have hall : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0:ℝ) T)), ∀ n : ℕ,
      Filter.Tendsto (fun j => F (n:ℝ) (ψ j) t) Filter.atTop (nhds 0) :=
    ae_all_iff.mpr hQψ
  filter_upwards [hall, ae_restrict_mem measurableSet_Ioc] with t ht htmem R
  obtain ⟨n, hn⟩ := exists_nat_ge R
  refine squeeze_zero (fun j => hFnn R (ψ j) t) (fun j => ?_) (ht n)
  exact setIntegral_mono_set ((hdint (ψ j) t htmem.1.le).integrableOn)
    (Filter.Eventually.of_forall fun x => by positivity)
    (Metric.closedBall_subset_closedBall hn).eventuallyLE

/-- **The compactness subsequence now feeds the quadratic time limit.**

For a jointly measurable, uniformly energy-bounded family converging strongly
in spacetime `L²_loc`, one subsequence has a.e. fixed-time `L²_loc`
convergence on the test's certified compact window.  The fixed-time convection
limit and the explicit-window dominated-convergence engine then give convergence
of the time-integrated signed convection pairing.  This discharges the
quadratic leg of the Galerkin weak-density assembly; the two linear legs remain
separate consumers.

-- Citation: Leray, Acta Math. 63 (1934), §§21–23; Temam III.3.3. -/
theorem DivergenceFreeTestFunction.exists_subseq_timeWindow_tendsto_integral_convection_pairing
    (φ : DivergenceFreeTestFunction) (uSeq : ℕ → VelocityEvolution)
    (u : VelocityEvolution) (E : ℝ) (hE : 0 ≤ E)
    (humeas : JointlyMeasurable uSeq)
    (humeasU : Measurable fun z : ℝ × Space => u z.1 z.2)
    (huint : ∀ (k : ℕ) (t : ℝ), 0 ≤ t → Integrable fun x : Space => ‖uSeq k t x‖ ^ 2)
    (huintU : ∀ t : ℝ, 0 ≤ t → Integrable fun x : Space => ‖u t x‖ ^ 2)
    (huE : ∀ (k : ℕ) (t : ℝ), 0 < t → (∫ x : Space, ‖uSeq k t x‖ ^ 2) ≤ E)
    (huEU : ∀ t : ℝ, 0 < t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ E)
    (hlim : StrongL2LocLimit uSeq u) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ T : ℝ, 0 < T ∧
      Filter.Tendsto
        (fun j : ℕ => ∫ t in Set.Ioc (0 : ℝ) T, ∫ x : Space,
          officialInner (uSeq (ψ j) t x)
            (fderiv ℝ (⇑(φ.field t)) x (uSeq (ψ j) t x)))
        Filter.atTop
        (nhds (∫ t in Set.Ioc (0 : ℝ) T, ∫ x : Space,
          officialInner (u t x) (fderiv ℝ (⇑(φ.field t)) x (u t x)))) := by
  obtain ⟨T, B, hT, _hB, hBint, hbound⟩ :=
    φ.exists_integrable_convection_pairing_majorant_family uSeq E hE humeas huint huE
  have hdint : ∀ (k : ℕ) (t : ℝ), 0 ≤ t →
      Integrable fun x : Space => ‖uSeq k t x - u t x‖ ^ 2 := by
    intro k t ht
    exact integrable_norm_sub_sq (uSeq k t) (u t)
      (((humeas k).comp measurable_prodMk_left).sub
        (humeasU.comp measurable_prodMk_left))
      (huint k t ht) (huintU t ht)
  have hbd : ∀ (k : ℕ) (t : ℝ), 0 < t →
      (∫ x : Space, ‖uSeq k t x - u t x‖ ^ 2) ≤ 4 * E := by
    intro k t ht
    have hb : (∫ x : Space, ‖uSeq k t x - u t x‖ ^ 2)
        ≤ ∫ x : Space, (2 * ‖uSeq k t x‖ ^ 2 + 2 * ‖u t x‖ ^ 2) := by
      refine integral_mono (hdint k t ht.le)
        (((huint k t ht.le).const_mul 2).add ((huintU t ht.le).const_mul 2)) fun x => ?_
      exact sq_norm_sub_le_two _ _
    rw [integral_add ((huint k t ht.le).const_mul 2) ((huintU t ht.le).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hb
    linarith [huE k t ht, huEU t ht]
  obtain ⟨ψ, hψ, hae⟩ := exists_subseq_ae_tendsto_l2loc_slices
    uSeq u T (4 * E) humeas humeasU huint huintU hbd hlim
  have hpairMeas : ∀ j : ℕ, AEStronglyMeasurable
      (fun t : ℝ => ∫ x : Space,
        officialInner (uSeq (ψ j) t x)
          (fderiv ℝ (⇑(φ.field t)) x (uSeq (ψ j) t x)))
      (volume.restrict (Set.Ioc (0 : ℝ) T)) := fun j =>
    φ.aestronglyMeasurable_convection_pairing_restrict_Ioc
      (uSeq (ψ j)) (humeas (ψ j)) T
  have hpairLim : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), Filter.Tendsto
      (fun j : ℕ => ∫ x : Space,
        officialInner (uSeq (ψ j) t x)
          (fderiv ℝ (⇑(φ.field t)) x (uSeq (ψ j) t x)))
      Filter.atTop
      (nhds (∫ x : Space,
        officialInner (u t x) (fderiv ℝ (⇑(φ.field t)) x (u t x)))) := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioc] with t htloc htmem
    refine tendsto_integral_convection_of_l2loc (φ.field t)
      (fun j => uSeq (ψ j) t) (u t) (4 * E) (mul_nonneg (by norm_num) hE)
      (fun j => (humeas (ψ j)).comp measurable_prodMk_left)
      (humeasU.comp measurable_prodMk_left)
      (fun j => huint (ψ j) t htmem.1.le) (huintU t htmem.1.le)
      (fun j => le_trans (huE (ψ j) t htmem.1) (by nlinarith))
      (le_trans (huEU t htmem.1) (by nlinarith))
      (fun j => hbd (ψ j) t htmem.1) htloc
  refine ⟨ψ, hψ, T, hT, ?_⟩
  exact φ.tendsto_integral_convection_pairing_on_timeWindow_of_ae
    (fun j => uSeq (ψ j)) u T B hpairMeas hBint (fun j => hbound (ψ j)) hpairLim

/-- **[CERTIFIED — the residue of `exists_lerayLimitData`, isolated.]**  Once
the limit weak-form identity is supplied for a compactness limit of the
Galerkin sequence, `LerayLimitData` follows.  The energy clauses come from
`exists_galerkinLimit_energy_le`; both pairing-integrability clauses are now
certified consequences of the test's genuine Schwartz time derivative. -/
theorem exists_lerayLimitData_of_weakClauses (ν : ℝ) (u₀ : SchwartzVelocity)
    (G : GalerkinApproximation ν u₀)
    (hweak : ∀ (u : VelocityEvolution) (σ : ℕ → ℕ), StrictMono σ →
      Measurable (fun z : ℝ × Space => u z.1 z.2) →
      (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) →
      StrongL2LocLimit (fun k => G.approx (σ k)) u →
      ∀ φ : DivergenceFreeTestFunction,
        (∫ t in Set.Ici (0:ℝ), ∫ x : Space, weakPairingDensity ν u φ t x) =
          -(∫ x : Space, officialInner (u₀ x) ((φ.field 0) x))) :
    Nonempty (LerayLimitData ν u₀) := by
  obtain ⟨u, σ, hσ, humeas, huint, huoff, hlim⟩ :=
    exists_galerkinLimit_energy_le ν u₀ G
  have hform := hweak u σ hσ humeas huint hlim
  exact ⟨{ limit := u
           sq_integrable := fun t ht => huint t ht.le
           datum_sq_integrable := integrable_norm_sq_schwartz u₀
           energy_le := fun t ht => huoff t ht.le
           pairing_integrable := pairing_integrable ν u humeas huint
           datum_pairing_integrable := datum_pairing_integrable ν u₀
           weak_form := hform }⟩

/-- **[NAMED RESIDUAL — Galerkin limit passage; Leray, Acta Math. 63 (1934)
§§21–23; Temam III.3.3; Constantin–Foias, *NSE* II; est ~700 LOC.]**  From a
Galerkin approximation, `aubin_lions_l2loc_compactness` (invoked on the
`kinetic_bounded`, `enstrophy_bounded`, `time_equicontinuous`,
`space_equicontinuous`, `jointly_measurable` and `sq_integrable` fields — the
last two being the Pattern-A additions without which that theorem is FALSE)
extracts a strong `L²_loc` limit `u` that is jointly measurable with slicewise
square-integrable slices.  The linear weak-form terms pass by weak-* convergence in `L^∞_t L²_x`,
the quadratic convection term by the strong `L²_loc` convergence (weak × strong
on the test's compact support), and weak lower-semicontinuity of the norm gives
`energy_le`.  `datum_sq_integrable` is `integrable_norm_sq_schwartz` (BANKED).

Stated at `0 < t` rather than `0 ≤ t`: the limit of an `L²`-convergent
subsequence is pinned only off null sets in time, so requiring the clauses at
the single instant `t = 0` would be a strictly stronger — and false-for-the-
constructed-object — demand.  The `t = 0` bookkeeping is now carried by the
certified `isLerayHopfWeakSolution_patchInitial`.

**Audit item (0) is now CLOSED, and its earlier diagnosis was wrong twice
over.**  That item read: "`energy_le` is not derivable; repair by adding
`bound_le : bound ≤ ∫ ‖u₀‖²` to the two Galerkin structures, and strengthen
`aubin_lions_l2loc_compactness`, which does not re-export the kinetic
conjunct."  Both premises were false when written: `bound_le` was already a
field of `GalerkinApproximation` and `GalerkinModeData`, and
`aubin_lions_l2loc_compactness` already re-exported `∫‖u t‖² ≤ C`.  And the
prescription would not have worked anyway: `UniformKineticBound` and `bound_le`
are stated in the inherited **sup** norm of `Space = Fin 3 → ℝ`, whereas
`kineticEnergy` is the **Euclidean** `∫ ∑ᵢ uᵢ²`, so that route delivers only
`kineticEnergy u t ≤ 3 ∫ ∑ᵢ (u₀)ᵢ²` — the dimension factor `3` from
`EnergyNormBridge` is irreducible on a sup-norm bundle, and `energy_le` demands
the exact constant.  The actual repair, now in place, is the Euclidean bound
carried as data (`official_kinetic_bounded`, true at the exact constant in the
finite-mode construction) and transported through Fischer–Riesz by the same
Fatou step as the sup-norm bound.  `energy_le`, `sq_integrable` and
`datum_sq_integrable` are consequently **discharged** —
`exists_galerkinLimit_energy_le` and `exists_lerayLimitData_of_weakClauses`
(both CERTIFIED, immediately above) reduce this residual to the pairing-side
clauses alone.  The genuine residue is
`weak_form`, together with `pairing_integrable`/`datum_pairing_integrable`
(Cauchy–Schwarz against the Schwartz test factors, not banked):
(a) spacetime Cauchy–Schwarz on windows `(0,T₀] ×ˢ B̄(0,R)`, with
`T₀` from `φ.compact_time`; (b) uniform-in-`m` spatial tails
`∫_{|x|>R} ‖u_m‖²·ψ ≤ C·sup_{|x|>R} ψ → 0` for each bounded Schwartz test factor
`ψ` — mathlib's `SchwartzMap.decay` gives the decay, the uniform kinetic bound
the rest; (c) the convection split
`⟨u,(u·∇)φ⟩ − ⟨u_m,(u_m·∇)φ⟩ = ⟨u−u_m,(u·∇)φ⟩ + ⟨u_m,((u−u_m)·∇)φ⟩`, each leg
`≤ (∫_{window}‖u−u_m‖²)^{1/2}·(∫‖·‖²ψ)^{1/2}` by (a), the first factor `→ 0`
by `StrongL2LocLimit`, the second uniformly bounded by (b) and `energy_le`;
(d) assembly of the linear terms by the same estimate, then `m → ∞` along `σ`
against `G.weak_consistent φ` composed with `hσ.tendsto_atTop`.

**Banked this wave (the Cauchy–Schwarz layer, certified above).**  The pairing
clauses are now reduced to the *time-derivative factor alone*:
`integrable_weakPairingDensity_of_timeDeriv` /
`pairing_integrable_of_timeDeriv` / `datum_pairing_integrable_of_timeDeriv`
discharge `pairing_integrable` and `datum_pairing_integrable` from
measurability plus square-integrability of `x ↦ ∂ₜφ(t, x)`, with the
convection and Laplacian legs closed unconditionally
(`integrable_convection_pairing`, `integrable_laplacian_pairing`,
`abs_officialInner_le_three`: the spatial factors of a Schwartz slice are
Schwartz via `SchwartzMap.fderivCLM`/`evalCLM`).

**Banked this wave: steps (a), (b), (c) in full, at fixed time.**  The earlier
time-derivative-decay obstruction recorded here was removed by the
`timeDerivSchwartz`/`timeDeriv_eq`/`compact_time_deriv` repair, so both pairing
clauses are now unconditional and the residue is the weak form alone.  Against
that repaired interface the following are now proved above, kernel-clean:
`weakForm_time_integral_eq_Ioc` (the half-line weak-form time integral IS a
finite-window integral, by vanishing past the test's horizon);
`tendsto_integral_officialInner_of_l2loc` (the linear legs, with the far field
carried by the test's own `L²` tail rather than by any local convergence);
`tendsto_integral_of_dominated_l2loc` and
`tendsto_integral_convection_of_l2loc` (the quadratic leg, whose far field
cannot use the test's `L²` tail — the pairing field is the velocity — and is
carried instead by the Schwartz decay `‖x‖·‖∇φ(x)‖ ≤ K`); and their assembly
`tendsto_integral_weakPairingDensity_of_l2loc`, the complete spatial limit
passage for `∫ₓ weakPairingDensity` at each fixed time.

**The statement-level obstruction is repaired (lane N1, 2026-08-22).**  The
test-function record now requires one compact spatial carrier for all slices
and one for all time-derivative slices.  Together with the existing common
time horizon, `exists_compact_spacetime_carrier` combines them into a single
compact-spacetime carrier on the nonnegative half-space.  This excludes the
previous counterexample, whose supports escaped to spatial infinity as time
approached the horizon.

**The time-derivative majorant is now certified (lane N2, 2026-08-22).**
`exists_uniform_timeDeriv_bound` derives joint continuity of `∂ₜφ` from the
existing half-space smoothness, `timeDeriv_norm_sq_le_volume_mul_bound` turns
compact support into a uniform squared `L²_x` bound, and
`exists_integrable_timeDeriv_l2_majorant` makes that bound integrable on the
test horizon.  Finally `abs_integral_officialInner_le_three_halves` and
`exists_integrable_timeDeriv_pairing_majorant` combine it with a uniform
velocity-energy bound to majorize the complete linear `⟨u,∂ₜφ⟩` leg.

**The quadratic time assembly is now certified (lane N4, 2026-08-23).**
`exists_integrable_convection_pairing_majorant_family` supplies one constant
integrable majorant for every member of an energy-bounded Galerkin family, and
`exists_timeWindow_tendsto_integral_convection_pairing_of_ae` consumes a.e.
fixed-time convergence with Mathlib's dominated-convergence theorem.
`aestronglyMeasurable_convection_pairing_restrict_Ioc` supplies the signed
pairing's missing time measurability, while
`exists_subseq_timeWindow_tendsto_integral_convection_pairing` extracts the
a.e. fixed-time subsequence and feeds it into that DCT engine.  The remaining
assembly edge is to combine this quadratic result with time limits for the two
linear legs.

**The pointwise half is now certified (lane N3, 2026-08-21).**  That extraction
is no longer a gap: `exists_subseq_ae_tendsto_zero_of_tendsto_setIntegral`
(Markov + Riesz) and `exists_subseq_ae_tendsto_l2loc_slices` (Cantor diagonal
over the integer radius ladder, then all real radii by monotonicity) produce a
single subsequence along which, for a.e. `t ∈ (0,T]`, the local `L²` error
vanishes at **every** radius — exactly the `hloc` hypothesis of
`tendsto_integral_weakPairingDensity_of_l2loc`, which previously had no
producer.  Their measurability leaf
`measurable_setIntegral_of_jointlyMeasurable_nonneg` is what makes the
time-integrand measurable without an integrability hypothesis at negative
times.  The quadratic DCT theorem above now consumes this subsequence through
the signed-pairing measurability leaf.  The full weak-density time assembly's
two linear time-limit legs remain. -/


theorem exists_lerayLimitData (ν : ℝ) (hν : 0 < ν)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀)
    (G : GalerkinApproximation ν u₀) :
    Nonempty (LerayLimitData ν u₀) := by
  sorry

theorem leray_of_galerkinApproximation (ν : ℝ) (hν : 0 < ν)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀)
    (G : GalerkinApproximation ν u₀) :
    ∃ u : VelocityEvolution, IsLerayHopfWeakSolution ν u₀ u :=
  (exists_lerayLimitData ν hν u₀ hu₀ G).elim
    (fun D => ⟨patchInitial D.limit u₀, isLerayHopfWeakSolution_patchInitial ν u₀ D⟩)

/-!
## Existence skeleton

**RELOCATED 2026-08-18 (lane NK2).**  `leray_weak_existence` now lives in
`Navier.Analysis.LerayWeakExistence` (same namespace, same name, same type),
downstream of `GalerkinBasis`: it composes the relocated
`galerkin_approximation_exists` with `leray_of_galerkinApproximation` above.
Its remaining `sorryAx` reach is exactly the named residuals
`hspace`/`htime`/`hweak` (GalerkinBasis) and `exists_lerayLimitData` (here).
-/

end Navier.Analysis.LerayWeak
