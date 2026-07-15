import Navier.Analysis.VectorCalculus

/-!
# Pointwise pressure-work cancellation

For an incompressible differentiable velocity, pressure work is exactly the
divergence of the pressure flux.  This is the local algebraic leaf used by the
smooth energy identity.  No spatial integral is taken here: decay,
integrability, and removal of the boundary flux remain separate obligations.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Navier

/-- The pressure-work density of an incompressible field is the divergence of
the pressure flux at every nonnegative time. -/
theorem pressure_work_eq_staticDivergence
    (u : VelocityEvolution) (p : PressureEvolution)
    (t : ℝ) (ht : 0 ≤ t) (x : Space)
    (hu : Incompressible u)
    (hdu : DifferentiableAt ℝ (u t) x)
    (hdp : DifferentiableAt ℝ (p t) x) :
    (∑ i : Fin 3, pressureGradient p t x i * u t x i) =
      staticDivergence (fun y => p t y • u t y) x := by
  have hdiv : staticDivergence (u t) x = 0 := by
    simpa only [divergence, spatialDerivative, staticDivergence] using
      hu t ht x
  rw [staticDivergence_smul (p t) (u t) x hdp hdu]
  simp only [hdiv, mul_zero, add_zero]
  rfl

end Navier
