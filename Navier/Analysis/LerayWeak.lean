import Navier.Analysis.Enstrophy

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

## Skeletons (honest `sorry`)

* `leray_weak_existence` — global existence of a Leray–Hopf weak solution for
  every `ν > 0` and divergence-free Schwartz datum
  [Leray, Acta Math. 63 (1934); Temam, *NSE* Ch. III (Galerkin + compactness
  + energy inequality); est ~1500 LOC].
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory intervalIntegral

namespace Navier.Analysis.LerayWeak

open scoped ContDiff

open Navier
open Navier.Analysis.Enstrophy
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
## Existence skeleton
-/

/-- **[SKELETON — Leray weak existence; Leray, Acta Math. 63 (1934); Temam,
*Navier–Stokes Equations* Ch. III; est ~1500 LOC.]**  For every viscosity
`ν > 0` and every divergence-free Schwartz datum there is a global
Leray–Hopf weak solution.

Closure route (Galerkin): finite-mode projection (the multi-frequency layer
of `MultiFrequencyMild` is the frequency-side laboratory), uniform energy
bounds from the skew-symmetry of the projected nonlinearity, Aubin–Lions
compactness to pass to the limit in the quadratic term, then the weak-form
identity against each Schwartz test.  Genuinely Mathlib-absent inputs:
Aubin–Lions, `L²`-Sobolev interpolation, weak compactness bookkeeping for
Bochner spaces. -/
theorem leray_weak_existence :
    ∀ ν : ℝ, 0 < ν →
    ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
      ∃ u : VelocityEvolution, IsLerayHopfWeakSolution ν u₀ u := by
  sorry

end Navier.Analysis.LerayWeak
