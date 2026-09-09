/-
Adapted from OpenAI/NavierStokesAndEuler, revision
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538, under Apache-2.0.
Upstream source: NavierStokes/R3FiniteEnergyComparison.lean
Changes: native module namespace; further compatibility edits are in Git history.
License: references/licenses/OpenAI-Apache-2.0.txt.
-/
import Navier.Construction.R3.WholeSpaceUniqueness
import Navier.Construction.R3CompactCandidate
import Navier.Construction.ComparatorR3Bridge

/-!
# Comparison with the compact candidate on all of R³

The whole-space uniqueness proof is ported from the verified R³ development.
The competitor retains exactly the smoothness and finite-energy conditions
of the comparator. The candidate's compact support supplies the reference
solution's bounds on each closed interval before time one.
-/

noncomputable section

namespace Navier.Construction.ComparatorBridge

open Set MeasureTheory ProblemStatement
open scoped ContDiff

theorem GlobalSolutionRn.uniformFiniteEnergy {f v : VelocityField} {q : PressureField}
    (h : GlobalSolutionRn f v q) (T : ℝ) :
    Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v := by
  obtain ⟨E, hE⟩ := h.globally_bounded_energy
  refine ⟨max 0 (E / 2), le_max_left _ _, ?_⟩
  intro t ht
  constructor
  · simpa only [Navier.ConstructionR3.ProblemStatement.SquareIntegrableAtTime, norm_norm] using!
      (memLp_two_iff_integrable_sq_norm (h.integrable t ht.1).1).mp (h.integrable t ht.1)
  · change (1 / 2 : ℝ) * (∫ x : Space, ‖v (t, x)‖ ^ 2) ≤ max 0 (E / 2)
    have hb := (hE t ht.1).le
    have hm := le_max_right 0 (E / 2)
    linarith

/-- The compact candidate is the unique smooth finite-energy solution on every
closed slab ending strictly before the singular time.  The competitor is
required to be smooth and finite-energy only on that slab; no future-time
extension, global energy bound, spatial support, or decay condition is used. -/
theorem compact_candidate_unique_on_Icc
    {u v f : VelocityField} {p q : PressureField}
    (h : R3CompactCandidate.Properties u p f) {T : ℝ}
    (hT1 : T < 1)
    (hv : ContDiffOn ℝ ∞ v (Navier.ConstructionR3.Comparison.slab 0 T))
    (hq : ContDiffOn ℝ ∞ q (Navier.ConstructionR3.Comparison.slab 0 T))
    (hev : Navier.ConstructionR3.ProblemStatement.UniformFiniteEnergy (Icc 0 T) v)
    (hdv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, spatialDivergence v t x = 0)
    (hNSv : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, navierStokesResidual v q t x = f (t, x))
    (hvzero : ∀ x, v (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, u (t, x) = v (t, x) := by
  by_cases hTpos : 0 < T
  · have hpre : Navier.ConstructionR3.Comparison.slab 0 T ⊆ preSingularDomain := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2.trans_lt hT1⟩, hz.2⟩
    obtain ⟨K, hK, hs⟩ := h.velocity_support
    have hsupport : ∀ r ∈ Icc (0 : ℝ) T, tsupport (fun y => u (r, y)) ⊆ K := by
      intro r hr
      apply closure_minimal _ hK.isClosed
      intro y hy
      by_contra hyK
      exact hy (hs r ⟨hr.1, hr.2.trans_lt hT1⟩ y hyK)
    exact Navier.ConstructionR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc hTpos
      (h.velocity_smooth.mono hpre) hv (h.pressure_smooth.mono hpre) hq
      hK hsupport hev
      (fun r hr => h.divergence_free r ⟨hr.1.le, hr.2.trans hT1⟩)
      hdv
      (fun r hr y => by
        simpa only [Navier.ConstructionR3.ProblemStatement.navierStokesResidual,
          navierStokesResidual, one_smul] using
          (h.navier_stokes r ⟨hr.1, hr.2.trans hT1⟩ y).trans (hNSv r hr y).symm)
      (fun y => (h.zero_initial_velocity y).trans (hvzero y).symm)
  · intro t ht x
    have htEq : t = 0 := le_antisymm (ht.2.trans (le_of_not_gt hTpos)) ht.1
    rw [htEq, h.zero_initial_velocity, hvzero]

/-- A compact candidate with unbounded speed excludes every global smooth
solution having the comparator's finite-energy bound. -/
theorem compact_candidate_excludes_global_solution
    {u v f : VelocityField} {p q : PressureField}
    (h : R3CompactCandidate.Properties u p f) (hv : GlobalSolutionRn f v q) : False := by
  apply h.not_global_agreement hv.velocity_smooth
  intro t ht x
  have hfuture : Navier.ConstructionR3.Comparison.slab 0 t ⊆ futureDomain := by
    intro z hz
    exact ⟨hz.1.1, hz.2⟩
  exact compact_candidate_unique_on_Icc h ht.2
    (hv.velocity_smooth.mono hfuture) (hv.pressure_smooth.mono hfuture)
    (hv.uniformFiniteEnergy t)
    (fun r hr => hv.divergence_free r hr.1.le)
    (fun r hr y => hv.navier_stokes r hr.1 y)
    hv.initial_velocity t ⟨ht.1, le_rfl⟩ x

end Navier.Construction.ComparatorBridge

#print axioms Navier.ConstructionR3.WholeSpaceUniqueness.classical_uniqueness_on_Icc
#print axioms Navier.Construction.ComparatorBridge.compact_candidate_unique_on_Icc
#print axioms Navier.Construction.ComparatorBridge.compact_candidate_excludes_global_solution
