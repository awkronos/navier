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
* `leray_weak_existence`, `galerkin_approximation_exists`, and
  `leray_of_galerkinApproximation` are now **compositions**, with no `sorry` of
  their own.

## Named residuals (honest `sorry`, strictly-lower leaves)

* `exists_galerkinModeData` — the finite-mode Galerkin construction (ODE on the
  first `m` divergence-free modes + time-regularity bookkeeping); depends on
  `Navier.Analysis.GalerkinBasis.GalerkinBasisFamily` [Temam III.3;
  Constantin–Foias II; Leray 1934 §§18–20; est ~350 LOC].
* `exists_subseq_windowCauchy` — Riesz–Fréchet–Kolmogorov total boundedness on
  the single bounded window `(0,n] × B̄(0,n)` [Brezis 2011 Thm 4.26 + Cor 4.27;
  Simon 1987 Thm 1; est ~400 LOC].  This and the next leaf replace the former
  monolithic `aubin_lions_l2loc_compactness` residual, whose hypothesis list was
  FALSE as stated — no divergence-freeness, hence no spatial control, and no
  joint measurability; the checked curl-free witness is in that theorem's
  docstring and in `experiments/aubin_lions_curlfree_witness.py`.
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

/-!
## Test functions
-/

/-- A divergence-free, Schwartz-sliced, compact-in-time test function on
nonnegative spacetime. -/
structure DivergenceFreeTestFunction where
  /-- The Schwartz slice at each time. -/
  field : ℝ → SchwartzVelocity
  /-- Joint spacetime smoothness on the nonnegative-time half-space, in the
  repo's within-derivative convention. -/
  smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × Space => (field z.1) z.2)
    ((Set.Ici (0:ℝ)) ×ˢ (Set.univ : Set Space))
  /-- The test function vanishes beyond a finite horizon. -/
  compact_time : ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → field t = 0
  /-- Every slice is divergence-free. -/
  divergence_free : ∀ t : ℝ, DivergenceFreeInitial (field t)

/-- The zero test function (inhabitant of the test class). -/
def zeroTestFunction : DivergenceFreeTestFunction where
  field := fun _ => 0
  smooth := by
    have : (fun z : ℝ × Space => ((0 : SchwartzVelocity)) z.2) =
        fun _ : ℝ × Space => (0 : Space) := by
      funext z; simp
    simpa [this] using contDiffOn_const
  compact_time := ⟨1, one_pos, fun _ _ => rfl⟩
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
  bound_le : bound ≤ ∫ x : Space, ‖u₀ x‖ ^ 2
  /-- Uniform `L^∞_t L²_x` bound. -/
  kinetic_bounded : UniformKineticBound approx bound
  /-- Uniform `L²(0,T; H¹)` dissipation bound. -/
  enstrophy_bounded : UniformEnstrophyBound approx bound
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
  bound_le : bound ≤ ∫ x : Space, ‖u₀ x‖ ^ 2
  /-- Uniform `L^∞_t L²_x` bound. -/
  kinetic_bounded : UniformKineticBound approx bound
  /-- Uniform `L²(0,T; H¹)` dissipation bound. -/
  enstrophy_bounded : UniformEnstrophyBound approx bound
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
            kinetic_bounded := D.kinetic_bounded, enstrophy_bounded := D.enstrophy_bounded,
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
  kinetic_bounded := by intro m t _; simp [kineticEnergy]
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

/-- **[NAMED RESIDUAL — finite-mode Galerkin construction; Temam, *NSE* III.3;
Constantin–Foias, *NSE* II; Leray, Acta Math. 63 (1934) §§18–20; est ~350 LOC.]**
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
skew-symmetry of `B`, `finiteDim_dissipative_ode_global` (BANKED, above) gives the
global coefficient curve, `galerkin_apriori_bound` and
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
now certified (`galerkinApproximation_of_modeData`). -/
theorem exists_galerkinModeData (ν : ℝ) (hν : 0 < ν)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀) :
    Nonempty (GalerkinModeData ν u₀) := by
  sorry

/-- **Galerkin approximants exist** — now a composition of the finite-mode data
residual with the certified transport `galerkinApproximation_of_modeData`. -/
theorem galerkin_approximation_exists (ν : ℝ) (hν : 0 < ν)
    (u₀ : SchwartzVelocity) (hu₀ : DivergenceFreeInitial u₀) :
    Nonempty (GalerkinApproximation ν u₀) :=
  galerkinApproximation_of_modeData ν u₀ (exists_galerkinModeData ν hν u₀ hu₀).some

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
  · intro m t _; simp [kineticEnergy]
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

/-- **[NAMED RESIDUAL — Riesz–Fréchet–Kolmogorov compactness on one window;
Brezis, *Functional Analysis, Sobolev Spaces and PDE*, Springer 2011, Thm 4.26
+ Cor 4.27; Simon, *Ann. Mat. Pura Appl.* **146** (1987) 65–96, Thm 1; est ~400
LOC.]**  On the single bounded window `Q = (0,n] × B̄(0,n) ⊂ ℝ × ℝ³`, a family
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

**What is left, stated exactly.**  Two mechanical steps plus one bridge:
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
[Brezis Thm 4.26 + Cor 4.27; Simon Thm 1; est ~300 LOC with the two repairs.] -/
theorem exists_subseq_windowCauchy
    (uSeq : ℕ → VelocityEvolution) (C : ℝ) (hC : 0 ≤ C)
    (hkin : UniformKineticBound uSeq C)
    (htime : TimeEquicontinuous uSeq) (hspace : SpaceEquicontinuous uSeq)
    (hmeas : JointlyMeasurable uSeq)
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2))
    (n : ℕ) (τ : ℕ → ℕ) (hτ : StrictMono τ) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ WindowCauchy uSeq n (τ ∘ ρ) := by
  sorry

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
    (hcauchy : ∀ n : ℕ, WindowCauchy vSeq n id) :
    ∃ u : VelocityEvolution,
      Measurable (fun z : ℝ × Space => u z.1 z.2) ∧
      (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
      (∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ C) ∧
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
  refine ⟨u, humeas, huint, hukin, ?_⟩

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

/-- **[NAMED RESIDUAL — Aubin–Lions–Simon compactness, PATTERN-A REPAIRED
STATEMENT; Aubin (*C. R. Acad. Sci.* **256**, 1963); Lions (*Quelques méthodes de
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

Remaining route, all four steps: **(i)+(ii)** Riesz–Fréchet–Kolmogorov total
boundedness on the single window `(0,n] × B̄(0,n)` from (H-space) + (H-time) +
the `L²` bound, giving an `L²`-Cauchy refinement of any subsequence
[Brezis Thm 4.26 + Cor 4.27; Simon Thm 1; est ~400 LOC]; **(iii)** the nested
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
    (hint : ∀ (m : ℕ) (t : ℝ), 0 ≤ t → Integrable (fun x : Space => ‖uSeq m t x‖ ^ 2)) :
    ∃ (u : VelocityEvolution) (σ : ℕ → ℕ), StrictMono σ ∧
      Measurable (fun z : ℝ × Space => u z.1 z.2) ∧
      (∀ t : ℝ, 0 ≤ t → Integrable (fun x : Space => ‖u t x‖ ^ 2)) ∧
      (∀ t : ℝ, 0 ≤ t → (∫ x : Space, ‖u t x‖ ^ 2) ≤ C) ∧
      StrongL2LocLimit (fun k => uSeq (σ k)) u := by
  obtain ⟨σ, hσ, hσC⟩ := exists_subseq_forall_windowCauchy uSeq
    fun n τ hτ => exists_subseq_windowCauchy uSeq C hC hkin htime hspace hmeas hint n τ hτ
  have hmeas' : JointlyMeasurable (fun k => uSeq (σ k)) := fun k => hmeas (σ k)
  have hint' : ∀ (m : ℕ) (t : ℝ), 0 ≤ t →
      Integrable (fun x : Space => ‖uSeq (σ m) t x‖ ^ 2) := fun m t ht => hint (σ m) t ht
  have hkin' : UniformKineticBound (fun k => uSeq (σ k)) C := fun m t ht => hkin (σ m) t ht
  obtain ⟨u, humeas, huint, hukin, huwin⟩ :=
    exists_limit_of_forall_windowCauchy (fun k => uSeq (σ k)) C hC hkin' hmeas' hint'
      fun n => hσC n
  refine ⟨u, σ, hσ, humeas, huint, hukin,
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
  /-- The Leray energy bound for positive times. -/
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

**Audit findings: one structural gap plus the itemized analytic residue.**
(0) *`energy_le` is NOT derivable from the packaged bundle.*  The compactness
route bounds the limit by the bundle's constant: `kineticEnergy u t ≤ G.bound`
(`exists_limit_of_forall_windowCauchy` proves exactly this, though
`aubin_lions_l2loc_compactness` does not re-export the conjunct — strengthen its
conclusion or call the internal steps directly).  But `energy_le` demands the
*exact* datum constant `∫ ‖u₀‖²`, and no field of `GalerkinApproximation`
relates `bound` to `u₀`: `initial_converges` pins only the `t = 0` slices, and
nothing records energy monotonicity of the approximants.  Repair (one line each):
add `bound_le : bound ≤ ∫ x : Space, ‖u₀ x‖ ^ 2` to `GalerkinApproximation` and to
`GalerkinModeData` — true with equality in the finite-mode construction
(`bound = ‖u₀‖²_{L²}`), true in `zeroGalerkinModeData` (`0 ≤ 0`), carried
verbatim by `galerkinApproximation_of_modeData`.  With (0) in place,
`sq_integrable`, `datum_sq_integrable` (`integrable_norm_sq_schwartz`),
`energy_le` and `pairing_integrable` (Cauchy–Schwarz against the Schwartz test
factors) are immediate from the compactness output.  The genuine residue is
`weak_form`: (a) spacetime Cauchy–Schwarz on windows `(0,T₀] ×ˢ B̄(0,R)`, with
`T₀` from `φ.compact_time`; (b) uniform-in-`m` spatial tails
`∫_{|x|>R} ‖u_m‖²·ψ ≤ C·sup_{|x|>R} ψ → 0` for each bounded Schwartz test factor
`ψ` — mathlib's `SchwartzMap.decay` gives the decay, the uniform kinetic bound
the rest; (c) the convection split
`⟨u,(u·∇)φ⟩ − ⟨u_m,(u_m·∇)φ⟩ = ⟨u−u_m,(u·∇)φ⟩ + ⟨u_m,((u−u_m)·∇)φ⟩`, each leg
`≤ (∫_{window}‖u−u_m‖²)^{1/2}·(∫‖·‖²ψ)^{1/2}` by (a), the first factor `→ 0`
by `StrongL2LocLimit`, the second uniformly bounded by (b) and `energy_le`;
(d) assembly of the linear terms by the same estimate, then `m → ∞` along `σ`
against `G.weak_consistent φ` composed with `hσ.tendsto_atTop`.  None of (a)–(d)
is banked; each is standard. -/


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
-/

/-- **Leray weak existence** [Leray, Acta Math. 63 (1934); Temam, *Navier–
Stokes Equations* Ch. III].  For every viscosity `ν > 0` and every
divergence-free Schwartz datum there is a global Leray–Hopf weak solution.

This is now a genuine composition of the Galerkin decomposition above:
`galerkin_approximation_exists` builds the uniformly-bounded approximants and
`leray_of_galerkinApproximation` (via `aubin_lions_l2loc_compactness`) passes
to the limit.  The remaining `sorry`s live in named, reference-grounded,
strictly-lower leaves — not here. -/
theorem leray_weak_existence :
    ∀ ν : ℝ, 0 < ν →
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∃ u : VelocityEvolution, IsLerayHopfWeakSolution ν u₀ u := by
  intro ν hν u₀ hu₀
  exact (galerkin_approximation_exists ν hν u₀ hu₀).elim
    (fun G => leray_of_galerkinApproximation ν hν u₀ hu₀ G)

end Navier.Analysis.LerayWeak






