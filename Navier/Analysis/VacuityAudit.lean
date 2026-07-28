import Navier.Analysis.BealeKatoMajda

/-!
# Vacuity audit: the `fderiv` junk value in the vorticity hypotheses

This module is a soundness audit, not a proof lane.  It certifies one further
instance of the defect class already witnessed elsewhere in this repository
(`ConditionalRegularity.massBracket_vacuous_of_infiniteMass`,
`serrinMixedNorm_vacuous_of_nonIntegrableTime`, `depletedCrossProduct_vacuous`,
`LerayWeak.enstrophy_stepField_eq_zero`): **a hypothesis that looks constraining
and is satisfied by everything.**

## The junk source audited here

`Navier.Analysis.Vorticity.staticCurl u x = ∑ i, e_i ⨯₃ (fderiv ℝ u x e_i)` is
built entirely from `fderiv`, and Mathlib's `fderiv` returns the **junk value
`0`** at every point where `u` is not differentiable
(`fderiv_zero_of_not_differentiableAt`).  `VelocityEvolution = ℝ → Space →
Space` is the bare function type and carries no regularity, so any hypothesis of
the shape

  `∀ t x, officialEuclideanNorm (vorticity u t x) ≤ rate t`

is satisfied at `rate ≡ 0` by every field whose slices are nowhere
differentiable — and, independently, by every genuinely smooth **curl-free**
field, since nothing in such a bundle forces `u` to be divergence-free.  This is
the same shape as the Aubin–Lions defect: `enstrophy` integrates `‖curl u‖²`
only, so the curl-free family is invisible to it.

## What is certified here (no sorry)

* `ballStep` — the indicator of the open unit ball in the direction `e₀`: a
  bounded, compactly supported, **discontinuous** velocity field.
* `fderiv_ballStep_eq_zero` — its Fréchet derivative is `0` at *every* point of
  `ℝ³`: by local constancy off the unit sphere, and by the junk convention on
  it (`not_differentiableAt_ballStep_of_mem_sphere` proves genuine
  non-differentiability there, so no null-set escape is needed).
* `staticCurl_ballStep_eq_zero`, `staticDivergence_ballStep_eq_zero` — the
  repository curl *and* divergence of that discontinuous field vanish
  identically.  It is therefore "incompressible" and "irrotational" in the
  repository's sense while being discontinuous across the unit sphere.
* `PreRepairBKMFields` — the eight `BealeKatoMajda.BKMControl` fields as they
  stood before the Pattern-A repair, written out verbatim as a standalone
  predicate so this witness is stable under later edits to the structure.
* `preRepairBKMFields_vacuous_of_curlFree` — **the vacuity engine.**  *Every*
  curl-free field that is uniformly bounded by `B` satisfies the entire
  pre-repair BKM field list, with `rate ≡ 0`, `control ≡ B + 1` and the
  criterion's own hypothesis `∃ B, ∀ t < T, ∫₀ᵗ rate ≤ B` discharged at
  `B = 0`.  No differentiability, no incompressibility, no relation to
  Navier–Stokes is used.
* `preRepairBKMFields_vacuous_of_ballStep` — the discontinuous instance.

## Consequence, and the Pattern-A repair

On the pre-repair field list the two vorticity fields of `BKMControl` do no
work: `finite_vorticity_integral` is free, and the criterion degenerates to a
statement about the abstract control `Y`.  `BealeKatoMajda.BKMControl` is
repaired by *adding* two fields — `velocity_differentiable` (excludes
`ballStep`, by `ballStep_not_differentiable` below) and `incompressible`
(excludes the smooth curl-free gradient fields `∇φ`, whose curl vanishes by
Clairaut but whose divergence `Δφ` does not).  Together they leave only fields
for which `vorticity` is the honest curl of a genuine incompressible flow;
by Liouville the bounded smooth ones with `rate ≡ 0` are exactly the constants.

The identical defect is present in
`Navier.Analysis.BKMLogBootstrap.LogBKMControl`
(`rate_dominates_vorticity` / `finite_vorticity_integral`), which is owned by
another lane and is reported rather than edited here.

References: Beale–Kato–Majda, *Comm. Math. Phys.* **94** (1984) 61–66;
Constantin–Fefferman, *Indiana Univ. Math. J.* **42** (1993) 775–789;
Simon, *Ann. Mat. Pura Appl.* **146** (1987) 65–96.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.VacuityAudit

open Navier
open Navier.Analysis.Vorticity
open Navier.Analysis.OfficialABEncoding

/-! ## A bounded, discontinuous field with identically vanishing repo curl -/

/-- The indicator of the open unit ball in the fixed direction `e₀`.  Bounded by
`1`, compactly supported, and discontinuous across the unit sphere. -/
def ballStep : VelocityField :=
  Set.indicator (Metric.ball (0 : Space) 1) (fun _ => basisVector 0)

theorem basisVector_zero_ne_zero : (basisVector 0 : Space) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [basisVector] at h0

/-- `ballStep` is not the zero field. -/
theorem ballStep_ne_zero : ballStep ≠ (fun _ => 0) := by
  intro h
  have h0 : ballStep 0 = 0 := by rw [h]
  rw [ballStep, Set.indicator_of_mem
    (by simp : (0 : Space) ∈ Metric.ball (0 : Space) 1)] at h0
  exact basisVector_zero_ne_zero h0

/-- `ballStep` is uniformly bounded by `1`. -/
theorem norm_ballStep_le (x : Space) : ‖ballStep x‖ ≤ 1 := by
  by_cases hx : x ∈ Metric.ball (0 : Space) 1
  · rw [ballStep, Set.indicator_of_mem hx]
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    by_cases hi : i = 0 <;> simp [basisVector, hi]
  · rw [ballStep, Set.indicator_of_notMem hx]
    simp

/-- Off the unit sphere `ballStep` is locally constant, so its derivative
genuinely vanishes. -/
theorem fderiv_ballStep_of_notMem_sphere (x : Space)
    (hx : x ∉ Metric.sphere (0 : Space) 1) : fderiv ℝ ballStep x = 0 := by
  rcases lt_or_gt_of_ne
      (show ‖x‖ ≠ 1 by simpa [Metric.mem_sphere, dist_zero_right] using hx) with hlt | hgt
  · have hmem : x ∈ Metric.ball (0 : Space) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hlt
    have hEq : ballStep =ᶠ[nhds x] (fun _ : Space => basisVector 0) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with y hy
      simp [ballStep, Set.indicator_of_mem hy]
    rw [hEq.fderiv_eq]; simp
  · have hopen : IsOpen {y : Space | 1 < ‖y‖} := isOpen_lt continuous_const continuous_norm
    have hEq : ballStep =ᶠ[nhds x] (fun _ : Space => (0 : Space)) := by
      filter_upwards [hopen.mem_nhds hgt] with y hy
      have hnm : y ∉ Metric.ball (0 : Space) 1 := by
        simp only [Metric.mem_ball, dist_zero_right, not_lt]; exact le_of_lt hy
      simp [ballStep, Set.indicator_of_notMem hnm]
    rw [hEq.fderiv_eq]; simp

/-- On the unit sphere `ballStep` is genuinely non-differentiable: it takes the
value `0` there while being constantly `e₀` on the ball, which clusters at every
sphere point.  So the vanishing of `fderiv` there is Mathlib's junk value, not a
derivative. -/
theorem not_differentiableAt_ballStep_of_mem_sphere {x : Space}
    (hx : x ∈ Metric.sphere (0 : Space) 1) : ¬ DifferentiableAt ℝ ballStep x := by
  intro hd
  have hnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
  have hnm : x ∉ Metric.ball (0 : Space) 1 := by
    simp [Metric.mem_ball, dist_zero_right, hnorm]
  have hzero : ballStep x = 0 := by simp [ballStep, Set.indicator_of_notMem hnm]
  have hclos : x ∈ closure (Metric.ball (0 : Space) 1) := by
    rw [closure_ball (0 : Space) (by norm_num : (1 : ℝ) ≠ 0)]
    simp [Metric.mem_closedBall, dist_zero_right, hnorm]
  have hne : (nhdsWithin x (Metric.ball (0 : Space) 1)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hclos
  have h1 : Filter.Tendsto ballStep (nhdsWithin x (Metric.ball (0 : Space) 1))
      (nhds (0 : Space)) := by
    have hcw := hd.continuousAt.continuousWithinAt (s := Metric.ball (0 : Space) 1)
    rw [ContinuousWithinAt, hzero] at hcw
    exact hcw
  have h2 : Filter.Tendsto ballStep (nhdsWithin x (Metric.ball (0 : Space) 1))
      (nhds (basisVector 0 : Space)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp [ballStep, Set.indicator_of_mem hy]
  exact basisVector_zero_ne_zero (tendsto_nhds_unique h2 h1)

/-- **The junk value, everywhere.**  `fderiv ℝ ballStep x = 0` at every `x`:
honestly off the sphere, by Mathlib's convention on it. -/
theorem fderiv_ballStep_eq_zero (x : Space) : fderiv ℝ ballStep x = 0 := by
  by_cases hx : x ∈ Metric.sphere (0 : Space) 1
  · exact fderiv_zero_of_not_differentiableAt
      (not_differentiableAt_ballStep_of_mem_sphere hx)
  · exact fderiv_ballStep_of_notMem_sphere x hx

/-- The repository curl of the discontinuous field vanishes identically. -/
theorem staticCurl_ballStep_eq_zero (x : Space) : staticCurl ballStep x = 0 := by
  simp [staticCurl, fderiv_ballStep_eq_zero]

/-- So does its repository divergence: `ballStep` is "incompressible" in the
repository's sense while being discontinuous. -/
theorem staticDivergence_ballStep_eq_zero (x : Space) :
    staticDivergence ballStep x = 0 := by
  simp [staticDivergence, fderiv_ballStep_eq_zero]

theorem norm_basisVector_zero : ‖(basisVector 0 : Space)‖ = 1 := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_) ?_
  · by_cases hi : i = 0 <;> simp [basisVector, hi]
  · simpa [basisVector] using norm_le_pi_norm (basisVector 0 : Space) 0

/-- **The repair is effective**: `ballStep` fails the added differentiability
field, so `BKMControl`'s `velocity_differentiable` excludes exactly this
inhabitant. -/
theorem ballStep_not_differentiable :
    ¬ (∀ x : Space, DifferentiableAt ℝ ballStep x) := by
  intro h
  refine not_differentiableAt_ballStep_of_mem_sphere
    (x := (basisVector 0 : Space)) ?_ (h _)
  simpa [Metric.mem_sphere, dist_zero_right] using norm_basisVector_zero

/-! ## The pre-repair BKM field list, and its vacuity -/

/-- The eight fields of `Navier.Analysis.BealeKatoMajda.BKMControl` as they stood
before the Pattern-A repair, written out verbatim as a standalone predicate.
Stating them here rather than through the structure keeps the witnesses below
valid after the structure is repaired. -/
def PreRepairBKMFields (u : VelocityEvolution) (T : ℝ)
    (control controlDeriv rate : ℝ → ℝ) : Prop :=
  ContinuousOn rate (Set.Ico 0 T) ∧
  ContinuousOn control (Set.Ico 0 T) ∧
  (∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt control (controlDeriv t) t) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, 0 < control t) ∧
  (∀ t ∈ Set.Ioo (0 : ℝ) T, controlDeriv t ≤ rate t * control t) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Space,
      officialEuclideanNorm (vorticity u t x) ≤ rate t) ∧
  (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Space, ‖u t x‖ ≤ control t) ∧
  (∃ B : ℝ, ∀ t ∈ Set.Ico (0 : ℝ) T, (∫ s in (0 : ℝ)..t, rate s) ≤ B)

/-- **VACUITY WITNESS (engine).**  Every uniformly bounded field with
identically vanishing repository curl satisfies the *entire* pre-repair BKM
field list, at `rate ≡ 0` and `control ≡ B + 1`, with the criterion's own
hypothesis `∃ B, ∀ t < T, ∫₀ᵗ rate ≤ B` discharged at `B = 0`.

Nothing about Navier–Stokes, differentiability, or incompressibility is used.
Two disjoint families are covered: the nowhere-differentiable fields (whose
`vorticity` is the `fderiv` junk value — `ballStep` below), and the smooth
gradient fields `∇φ` (whose curl vanishes by Clairaut but whose divergence
`Δφ` need not, so they are not Navier–Stokes velocities at all). -/
theorem preRepairBKMFields_vacuous_of_curlFree
    (u : VelocityEvolution) (T B : ℝ) (hB : 0 ≤ B)
    (hcurl : ∀ (t : ℝ) (x : Space), vorticity u t x = 0)
    (hbd : ∀ (t : ℝ) (x : Space), ‖u t x‖ ≤ B) :
    PreRepairBKMFields u T (fun _ => B + 1) (fun _ => 0) (fun _ => 0) := by
  refine ⟨continuousOn_const, continuousOn_const,
    fun t _ => hasDerivAt_const t (B + 1),
    fun t _ => by linarith, fun t _ => by norm_num, ?_, ?_, ⟨0, ?_⟩⟩
  · intro t _ x
    rw [hcurl t x, (officialEuclideanNorm_eq_zero_iff 0).mpr rfl]
  · intro t _ x
    linarith [hbd t x]
  · intro t _
    simp

/-- **VACUITY WITNESS (discontinuous instance).**  The bounded discontinuous
field `ballStep` — which is not even continuous, let alone a classical solution
— satisfies the whole pre-repair BKM field list on every horizon, with the
vorticity rate identically `0`.  The Beale–Kato–Majda criterion as previously
packaged therefore said nothing at all about the vorticity of `u`. -/
theorem preRepairBKMFields_vacuous_of_ballStep (T : ℝ) :
    PreRepairBKMFields (fun _ => ballStep) T (fun _ => 2) (fun _ => 0)
      (fun _ => 0) := by
  have h := preRepairBKMFields_vacuous_of_curlFree (fun _ => ballStep) T 1 zero_le_one
    (fun _ x => staticCurl_ballStep_eq_zero x) (fun _ x => norm_ballStep_le x)
  have he : (fun _ : ℝ => (1 : ℝ) + 1) = (fun _ : ℝ => (2 : ℝ)) := by
    funext t; norm_num
  rwa [he] at h

end Navier.Analysis.VacuityAudit

end
