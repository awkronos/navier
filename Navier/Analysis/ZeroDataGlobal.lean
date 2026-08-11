import Navier.Breakdown.ForceRecovery

/-!
# The whole-space zero-data slice

This is a genuine, unconditional instance of the statement-A solution
predicate: for zero Schwartz data the identically zero velocity and pressure
are a global smooth finite-energy solution.  It deliberately does not weaken
the universal quantifier in `WholeSpaceGlobalRegularity`; arbitrary data remain
the scientific frontier.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.ZeroDataGlobal

open MeasureTheory
open Navier Navier.Breakdown

/-- The zero Schwartz datum has an unconditional global classical solution at
every positive viscosity. -/
theorem zeroData_wholeSpace_classical_solution (ν : ℝ) (_hν : 0 < ν) :
    ∃ (u : VelocityEvolution) (p : PressureEvolution),
      IsClassicalSolution ν zeroForce (0 : SchwartzVelocity) u p := by
  refine ⟨zeroVelocityEvolution, zeroPressureEvolution, ?_⟩
  refine
    { velocity_smooth := by
        simp only [SmoothVelocityOnNonnegativeTime, zeroVelocityEvolution]
        fun_prop
      pressure_smooth := by
        simp only [SmoothPressureOnNonnegativeTime, zeroPressureEvolution]
        fun_prop
      initial_condition := by intro x; rfl
      incompressible := by
        intro t ht x
        simp [divergence, spatialDerivative]
      equation := by
        intro t ht x
        ext i
        simp [zeroVelocityEvolution, timeDerivative,
          convection, spatialDerivative, laplacian, pressureGradient, zeroForce]
      finite_energy := by
        intro t ht
        have hz : (fun x : Space => ‖zeroVelocityEvolution t x‖ ^ 2) =
            fun _ => (0 : ℝ) := by
          funext x
          simp [zeroVelocityEvolution]
        rw [hz]
        exact integrable_zero Space ℝ volume
      uniformly_bounded_energy := by
        refine ⟨1, one_pos, ?_⟩
        intro t ht
        simp [kineticEnergy, zeroVelocityEvolution] }

end Navier.Analysis.ZeroDataGlobal

#print axioms Navier.Analysis.ZeroDataGlobal.zeroData_wholeSpace_classical_solution
