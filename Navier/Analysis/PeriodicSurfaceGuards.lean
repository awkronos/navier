import Navier.OfficialProblem

/-!
# Two-pole satisfiability guards for the periodic surfaces B and D

Mirrors the statement-A guards of `Navier/Problem.lean:285-320`
(`divergenceFreeInitial_zero`, `isClassicalSolution_zero`,
`wholeSpaceGlobalRegularity_body_at_zero_datum`) on the official periodic
contract `IsPeriodicClassicalSolution` / `PeriodicInitialDatum`.

A universally quantified endpoint fails soundness at either of two poles and
both are invisible to the kernel.  If the periodic datum class
`{u₀ : PeriodicInitialDatum u₀}` were empty, `PeriodicGlobalRegularity` would
be vacuously TRUE and provable without any analysis.  If the conclusion
bundle `IsPeriodicClassicalSolution` were uninhabitable, the endpoint — and
the proven alternative D stated against the same bundle — would be about a
formal artifact rather than a fluid-mechanical proposition.

The three declarations below close both poles at the zero periodic field.
The field proofs are exactly the tactics already used inline (and
unregistered) at `Navier/Analysis/PeriodicConstructedBreakdown.lean:191-192`
for the D-surface witness datum: `contDiff_const`, `simp [staticDivergence]`,
and reflexivity of periodicity for a constant field.  They are guards, not
progress: the zero datum is the one periodic datum whose global smooth
solution is elementary, and nothing here bears on any nonzero datum.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PeriodicSurfaceGuards

open Navier

/-- **Pole (a): the periodic datum class is nonempty.**  The zero velocity
field is smooth, statically divergence-free, and spatially periodic, so the
outer `∀` of `ProblemStatements.PeriodicGlobalRegularity` does not range over
an empty class. -/
theorem periodicInitialDatum_zero : PeriodicInitialDatum (0 : VelocityField) :=
  ⟨contDiff_const, fun x => by simp [staticDivergence], fun x i => rfl⟩

/-- **Pole (b): the periodic solution contract is inhabitable.**  The zero
velocity and zero pressure satisfy every field of
`IsPeriodicClassicalSolution` simultaneously, at every viscosity, with zero
force — including both periodicity fields, which hold by definition for a
constant field.  The seven clauses are therefore jointly satisfiable, so no
theorem taking `IsPeriodicClassicalSolution` (alternatives B and D, the
viscosity-one endpoints, the DC-1 zero-force twins) is vacuously true for
that reason. -/
theorem isPeriodicClassicalSolution_zero (ν : ℝ) :
    IsPeriodicClassicalSolution ν zeroForce 0 (fun _ _ => 0) (fun _ _ => 0) where
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial_condition := by intro x; simp
  incompressible := by
    intro t _ x
    simp [divergence, spatialDerivative]
  equation := by
    intro t _ x
    have hpg : pressureGradient (fun _ _ => (0 : ℝ)) t x = 0 := by
      funext i
      simp [pressureGradient]
    simp [timeDerivative, convection, spatialDerivative, laplacian, zeroForce, hpg]
  velocity_periodic := by
    intro t ht x i
    rfl
  pressure_periodic := by
    intro t ht x i
    rfl

/-- The body of `ProblemStatements.PeriodicGlobalRegularity` holds at the zero
datum, for every positive viscosity.  This is the B endpoint's own shape
evaluated at an admissible point of its quantifier range; it settles both
satisfiability poles at once and proves nothing about
`PeriodicGlobalRegularity` itself, whose content is the nonzero data (FR-5). -/
theorem periodicGlobalRegularity_body_at_zero_datum (ν : ℝ) (_hν : 0 < ν) :
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsPeriodicClassicalSolution ν zeroForce 0 u p :=
  ⟨fun _ _ => 0, fun _ _ => 0, isPeriodicClassicalSolution_zero ν⟩

end Navier.Analysis.PeriodicSurfaceGuards

#print axioms Navier.Analysis.PeriodicSurfaceGuards.periodicInitialDatum_zero
#print axioms Navier.Analysis.PeriodicSurfaceGuards.isPeriodicClassicalSolution_zero
#print axioms Navier.Analysis.PeriodicSurfaceGuards.periodicGlobalRegularity_body_at_zero_datum
