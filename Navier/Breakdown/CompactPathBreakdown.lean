/-
The negative-power and remaining-time arguments below adapt
NavierStokes/BlowupImplication.lean from OpenAI/NavierStokesAndEuler,
revision 8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538 (Apache-2.0).
Adaptations: Lean 4.31, native carriers, compact-path and official consumers.
See references/licenses/OpenAI-Apache-2.0.txt for the upstream license.
The remaining original additions are covered by the repository LICENSE.
-/
import Navier.Breakdown.MaximalNonextension
import Navier.Analysis.ViscosityEndpoints
import Navier.Breakdown.CompactSmoothForce
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Compact-region and moving-path breakdown

This module strengthens the point-evaluation breakdown consumer to match a
singular profile whose large values may move in space.  A global classical
solution is jointly continuous, hence uniformly bounded on the finite-time,
compact-space cylinder `[0, T] × K`.  Therefore unbounded velocity anywhere
in a fixed compact `K` before `T` rules out a global extension.

The final section proves the negative-real-power implication used by
finite-time similarity profiles: a positive leading coefficient times
`(T - t) ^ (-A)`, up to an error tending to zero, supplies the required
moving-path unboundedness.  The construction and local uniqueness hypotheses
remain explicit; this module does not postulate a Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace Navier.Breakdown

/-- Joint smoothness on nonnegative time uniformly bounds velocity on every
finite-time, compact-space cylinder. -/
theorem bounded_compactEvaluation_of_smooth
    {u : VelocityEvolution} {T : ℝ} (K : Set Space)
    (hK : IsCompact K) (hu : SmoothVelocityOnNonnegativeTime u) :
    ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ x ∈ K, ‖u t x‖ ≤ M := by
  have hsub : Set.Icc (0 : ℝ) T ×ˢ K ⊆ nonnegativeSpacetime := by
    rintro ⟨t, x⟩ ht
    exact ⟨ht.1.1, Set.mem_univ x⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hu.continuousOn.mono hsub)
  exact ⟨M, fun t ht0 htT x hx => hM (t, x) ⟨⟨ht0, htT⟩, hx⟩⟩

/-- A breakdown certificate whose large velocity can occur at different
points of one fixed compact spatial region. -/
structure CompactRegionBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : VelocityField) (T : ℝ)
    (GlobalSolution : VelocityEvolution → PressureEvolution → Prop) where
  localSolution : PartialClassicalSolution ν f u₀ T
  region : Set Space
  region_compact : IsCompact region
  agrees_with_global :
    ∀ u p, GlobalSolution u p →
      VelocityAgreesBefore T localSolution.velocity u
  region_norm_unbounded :
    ∀ M : ℝ, ∃ t : ℝ, ∃ x ∈ region,
      0 ≤ t ∧ t < T ∧ M < ‖localSolution.velocity t x‖

/-- Compact-region velocity blowup contradicts the boundedness forced by a
globally smooth extension. -/
theorem noGlobal_of_compactRegionBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    {GlobalSolution : VelocityEvolution → PressureEvolution → Prop}
    (w : CompactRegionBreakdownWitness ν f u₀ T GlobalSolution)
    (global_velocity_smooth :
      ∀ u p, GlobalSolution u p → SmoothVelocityOnNonnegativeTime u) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution), GlobalSolution u p := by
  rintro ⟨u, p, hglobal⟩
  obtain ⟨M, hbound⟩ := bounded_compactEvaluation_of_smooth
    w.region w.region_compact (global_velocity_smooth u p hglobal)
  obtain ⟨t, x, hx, ht0, htT, hlarge⟩ := w.region_norm_unbounded M
  have hagree := w.agrees_with_global u p hglobal t ht0 htT
  have hle := hbound t ht0 htT.le x hx
  rw [hagree] at hlarge
  exact (not_lt_of_ge hle) hlarge

/-- A moving-path breakdown certificate.  The path requires no continuity:
remaining in a fixed compact region is precisely what the compact-cylinder
argument uses. -/
structure CompactPathBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : VelocityField) (T : ℝ)
    (GlobalSolution : VelocityEvolution → PressureEvolution → Prop) where
  localSolution : PartialClassicalSolution ν f u₀ T
  region : Set Space
  region_compact : IsCompact region
  path : ℝ → Space
  path_mem : ∀ t : ℝ, 0 ≤ t → t < T → path t ∈ region
  agrees_with_global :
    ∀ u p, GlobalSolution u p →
      VelocityAgreesBefore T localSolution.velocity u
  path_norm_unbounded :
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ t < T ∧
      M < ‖localSolution.velocity t (path t)‖

/-- Forgetting the selected path gives the compact-region certificate used by
the contradiction theorem. -/
def CompactPathBreakdownWitness.toCompactRegion
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    {GlobalSolution : VelocityEvolution → PressureEvolution → Prop}
    (w : CompactPathBreakdownWitness ν f u₀ T GlobalSolution) :
    CompactRegionBreakdownWitness ν f u₀ T GlobalSolution where
  localSolution := w.localSolution
  region := w.region
  region_compact := w.region_compact
  agrees_with_global := w.agrees_with_global
  region_norm_unbounded := by
    intro M
    obtain ⟨t, ht0, htT, hlarge⟩ := w.path_norm_unbounded M
    exact ⟨t, w.path t, w.path_mem t ht0 htT, ht0, htT, hlarge⟩

/-- Moving-path velocity blowup in a compact region rules out a globally
smooth extension. -/
theorem noGlobal_of_compactPathBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : VelocityField} {T : ℝ}
    {GlobalSolution : VelocityEvolution → PressureEvolution → Prop}
    (w : CompactPathBreakdownWitness ν f u₀ T GlobalSolution)
    (global_velocity_smooth :
      ∀ u p, GlobalSolution u p → SmoothVelocityOnNonnegativeTime u) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution), GlobalSolution u p :=
  noGlobal_of_compactRegionBreakdown w.toCompactRegion global_velocity_smooth

/-! ## Negative-power profiles supply moving-path unboundedness -/

/-- A positive scale tending to zero has divergent negative real power. -/
theorem negativePower_tendsto_atTop {I : Type*} {l : Filter I}
    {q : I → ℝ} {A : ℝ} (hA : 0 < A)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ))) :
    Tendsto (fun t => q t ^ (-A)) l atTop := by
  have h := (tendsto_rpow_atTop hA).comp
    (tendsto_inv_nhdsGT_zero.comp hq)
  refine h.congr' ?_
  filter_upwards [hq.eventually self_mem_nhdsWithin] with t ht
  change (q t)⁻¹ ^ A = q t ^ (-A)
  rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]

/-- A positive leading profile with a vanishing relative error diverges after
negative-power scaling. -/
theorem positiveProfile_tendsto_atTop {I : Type*} {l : Filter I}
    {q error : I → ℝ} {A E : ℝ} (hA : 0 < A) (hE : 0 < E)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0)) :
    Tendsto (fun t => q t ^ (-A) * (E + error t)) l atTop := by
  have hfactor : Tendsto (fun t => E + error t) l (𝓝 E) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  exact (negativePower_tendsto_atTop hA hq).atTop_mul_pos hE hfactor

/-- A velocity bounded below by a positive negative-power profile has
divergent norm. -/
theorem pathNorm_tendsto_atTop_of_profileLowerBound
    {I V : Type*} [NormedAddCommGroup V] {l : Filter I}
    {q error : I → ℝ} {v : I → V} {A E : ℝ}
    (hA : 0 < A) (hE : 0 < E)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0))
    (hlower : ∀ᶠ t in l, q t ^ (-A) * (E + error t) ≤ ‖v t‖) :
    Tendsto (fun t => ‖v t‖) l atTop :=
  tendsto_atTop_mono' l hlower
    (positiveProfile_tendsto_atTop hA hE hq herror)

/-- Remaining time tends to zero through positive values at a finite terminal
time. -/
theorem remainingTime_tendsto (T : ℝ) :
    Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have htime : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ => T) (𝓝[<] T) (𝓝 T) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub htime
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (show 0 < T - t from sub_pos.mpr ht)

/-- Divergence at a positive finite terminal time produces the exact
unboundedness quantifiers required by a moving-path witness. -/
theorem pathNorm_unboundedBefore_of_tendsto_atTop
    {V : Type*} [NormedAddCommGroup V] {T : ℝ} {v : ℝ → V}
    (hT : 0 < T) (hv : Tendsto (fun t => ‖v t‖) (𝓝[<] T) atTop) :
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ M < ‖v t‖ := by
  intro M
  have hlarge := hv.eventually_gt_atTop M
  have hinterval : Set.Ioo (T / 2) T ∈ 𝓝[<] T :=
    Ioo_mem_nhdsLT (by linarith)
  obtain ⟨t, hbig, ht⟩ := (hlarge.and hinterval).exists
  exact ⟨t, (by linarith [ht.1]), ht.2, hbig⟩

/-- The finite-time negative-power asymptotic from the singular-profile
construction supplies moving-path unboundedness directly. -/
theorem pathNorm_unboundedBefore_of_negativePowerProfile
    {V : Type*} [NormedAddCommGroup V]
    {T A E : ℝ} {error : ℝ → ℝ} {v : ℝ → V}
    (hT : 0 < T) (hA : 0 < A) (hE : 0 < E)
    (herror : Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T,
      (T - t) ^ (-A) * (E + error t) ≤ ‖v t‖) :
    ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ M < ‖v t‖ :=
  pathNorm_unboundedBefore_of_tendsto_atTop hT
    (pathNorm_tendsto_atTop_of_profileLowerBound hA hE
      (remainingTime_tendsto T) herror hlower)

/-! ## Exact whole-space consumers -/

abbrev WholeSpaceCompactRegionBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : SchwartzVelocity) (T : ℝ) :=
  CompactRegionBreakdownWitness ν f (fun x => u₀ x) T
    (fun u p => IsClassicalSolution ν f u₀ u p)

abbrev WholeSpaceCompactPathBreakdownWitness
    (ν : ℝ) (f : ForceField) (u₀ : SchwartzVelocity) (T : ℝ) :=
  CompactPathBreakdownWitness ν f (fun x => u₀ x) T
    (fun u p => IsClassicalSolution ν f u₀ u p)

theorem noWholeSpaceGlobal_of_compactRegionBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity} {T : ℝ}
    (w : WholeSpaceCompactRegionBreakdownWitness ν f u₀ T) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution ν f u₀ u p :=
  noGlobal_of_compactRegionBreakdown w
    (fun _ _ hglobal => hglobal.velocity_smooth)

theorem noWholeSpaceGlobal_of_compactPathBreakdown
    {ν : ℝ} {f : ForceField} {u₀ : SchwartzVelocity} {T : ℝ}
    (w : WholeSpaceCompactPathBreakdownWitness ν f u₀ T) :
    ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution ν f u₀ u p :=
  noGlobal_of_compactPathBreakdown w
    (fun _ _ hglobal => hglobal.velocity_smooth)

/-- A viscosity-one moving-path breakdown, together with the official datum
and force admissibility proofs, inhabits the full all-positive-viscosity
alternative C through the repository's viscosity transport. -/
theorem wholeSpaceBreakdown_of_compactPathBreakdown
    {f : ForceField} {u₀ : SchwartzVelocity} {T : ℝ}
    (hdiv : DivergenceFreeInitial u₀) (hforce : ForcedDataRapidDecay f)
    (w : WholeSpaceCompactPathBreakdownWitness 1 f u₀ T) :
    ProblemStatements.WholeSpaceBreakdown := by
  apply Navier.Analysis.ViscosityEndpoints.wholeSpaceBreakdown_iff_atViscosityOne.mpr
  exact ⟨u₀, hdiv, f, hforce, noWholeSpaceGlobal_of_compactPathBreakdown w⟩

/-- Construct the official whole-space moving-path certificate from a concrete
negative-power lower profile.  The remaining inputs are the actual local PDE
solution, its compact path, and uniqueness against a global competitor. -/
def wholeSpaceCompactPathBreakdownWitness_of_negativePowerProfile
    {ν T A E : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    (localSolution : PartialClassicalSolution ν f (fun x => u₀ x) T)
    (region : Set Space) (region_compact : IsCompact region)
    (path : ℝ → Space)
    (path_mem : ∀ t : ℝ, 0 ≤ t → t < T → path t ∈ region)
    (agrees_with_global :
      ∀ u p, IsClassicalSolution ν f u₀ u p →
        VelocityAgreesBefore T localSolution.velocity u)
    (error : ℝ → ℝ) (hA : 0 < A) (hE : 0 < E)
    (herror : Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T,
      (T - t) ^ (-A) * (E + error t) ≤
        ‖localSolution.velocity t (path t)‖) :
    WholeSpaceCompactPathBreakdownWitness ν f u₀ T where
  localSolution := localSolution
  region := region
  region_compact := region_compact
  path := path
  path_mem := path_mem
  agrees_with_global := agrees_with_global
  path_norm_unbounded :=
    pathNorm_unboundedBefore_of_negativePowerProfile
      localSolution.terminalTime_pos hA hE herror hlower

/-- The complete native bridge for the compact-force singular-profile route:
global smoothness plus compact spacetime support proves force admissibility,
while the negative-power moving profile proves the compact-region breakdown
needed for official alternative C. -/
theorem wholeSpaceBreakdown_of_compactSmooth_negativePowerProfile
    {T A E : ℝ} {f : ForceField} {u₀ : SchwartzVelocity}
    (hforce_smooth : ContDiff ℝ ∞ (fun z : ℝ × Space => f z.1 z.2))
    (hforce_compact : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2))
    (hdiv : DivergenceFreeInitial u₀)
    (localSolution : PartialClassicalSolution 1 f (fun x => u₀ x) T)
    (region : Set Space) (region_compact : IsCompact region)
    (path : ℝ → Space)
    (path_mem : ∀ t : ℝ, 0 ≤ t → t < T → path t ∈ region)
    (agrees_with_global :
      ∀ u p, IsClassicalSolution 1 f u₀ u p →
        VelocityAgreesBefore T localSolution.velocity u)
    (error : ℝ → ℝ) (hA : 0 < A) (hE : 0 < E)
    (herror : Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T,
      (T - t) ^ (-A) * (E + error t) ≤
        ‖localSolution.velocity t (path t)‖) :
    ProblemStatements.WholeSpaceBreakdown :=
  wholeSpaceBreakdown_of_compactPathBreakdown hdiv
    (CompactSmoothForce.forcedDataRapidDecay_of_smooth_compactSupport
      f hforce_smooth hforce_compact)
    (wholeSpaceCompactPathBreakdownWitness_of_negativePowerProfile
      localSolution region region_compact path path_mem agrees_with_global
      error hA hE herror hlower)

end Navier.Breakdown

#print axioms Navier.Breakdown.bounded_compactEvaluation_of_smooth
#print axioms Navier.Breakdown.noGlobal_of_compactPathBreakdown
#print axioms Navier.Breakdown.negativePower_tendsto_atTop
#print axioms Navier.Breakdown.pathNorm_unboundedBefore_of_negativePowerProfile
#print axioms Navier.Breakdown.wholeSpaceBreakdown_of_compactSmooth_negativePowerProfile
