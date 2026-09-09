import Navier.Analysis.ViscosityEndpoints
import Navier.Breakdown.MaximalNonextension

/-!
# Compact smooth forcing supplies the official decay premise

The compact forcing construction in OpenAI's *Finite time blowup for
Navier–Stokes*, Section 10, suggests a useful native interface: global
smoothness and compact spacetime support imply every weighted mixed derivative
bound in `ForcedDataRapidDecay`. No external formalization is imported.

This discharges force admissibility when a compact smooth force has actually
been constructed. It does not construct the singular velocity or its force.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace Navier.Breakdown.CompactSmoothForce

/-- Compact spacetime support controls every polynomially weighted force jet,
including the within derivatives at initial time. -/
theorem forcedDataRapidDecay_of_smooth_compactSupport
    (f : ForceField)
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => f z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2)) :
    ForcedDataRapidDecay f := by
  refine ⟨hs.contDiffOn, ?_⟩
  intro n K
  let g : (ℝ × Space) → ℝ := fun z =>
    (1 + ‖z.2‖ + z.1) ^ K *
      ‖iteratedFDeriv ℝ n (fun w : ℝ × Space => f w.1 w.2) z‖
  have hgc : Continuous g := by
    apply Continuous.mul (by fun_prop)
    exact (hs.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
  have hgs : HasCompactSupport g := (hc.iteratedFDeriv n).norm.mul_left
  obtain ⟨z, hz⟩ := hgc.exists_forall_ge_of_hasCompactSupport hgs
  refine ⟨max 0 (g z), le_max_left _ _, ?_⟩
  intro t ht x
  have hd : UniqueDiffOn ℝ nonnegativeSpacetime :=
    (uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (x := (t, x)) hd
    ((hs.of_le (by exact_mod_cast le_top)).contDiffAt) ⟨ht, Set.mem_univ x⟩]
  exact (hz (t, x)).trans (le_max_right _ _)

/-- A viscosity-one observable breakdown witness with a compact smooth force
feeds the original all-positive-viscosity alternative C. The decay premise is
proved above and viscosity transport is the repository's existing theorem. -/
theorem wholeSpaceBreakdown_of_compact_observable
    {f : ForceField} {u₀ : SchwartzVelocity} {T : ℝ}
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Space => f z.1 z.2))
    (hc : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2))
    (hdiv : DivergenceFreeInitial u₀)
    (w : WholeSpaceObservableBreakdownWitness 1 f u₀ T) :
    ProblemStatements.WholeSpaceBreakdown := by
  apply Navier.Analysis.ViscosityEndpoints.wholeSpaceBreakdown_iff_atViscosityOne.mpr
  exact ⟨u₀, hdiv, f, forcedDataRapidDecay_of_smooth_compactSupport f hs hc,
    noWholeSpaceGlobal_of_observableBreakdown w⟩

end Navier.Breakdown.CompactSmoothForce

#print axioms Navier.Breakdown.CompactSmoothForce.forcedDataRapidDecay_of_smooth_compactSupport
#print axioms Navier.Breakdown.CompactSmoothForce.wholeSpaceBreakdown_of_compact_observable
