import Navier.Analysis.SeeleySynthesis
import Navier.OfficialSurfaceSignatures

/-!
# Consume Seeley extension in the official solution surfaces

`SeeleySynthesis` proves that Mathlib smoothness within the closed
nonnegative-time half-space is equivalent to restriction of a globally smooth
spacetime field.  This file threads that equivalence through the actual
velocity, pressure, and force consumers used by alternatives A--D.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.HalfSpaceConsumerBridge

open Navier
open Navier.Analysis.HalfSpaceSmoothnessBridge

/-- A velocity is smooth on nonnegative time exactly when it is the restriction
of a globally smooth spacetime velocity. -/
theorem smoothVelocity_iff_globalExtension (u : VelocityEvolution) :
    SmoothVelocityOnNonnegativeTime u ↔ Nonempty (HalfSpaceSmoothExtension u) :=
  (smoothVelocityOnNonnegativeTime_iff_halfSpaceSmooth u).trans
    (halfSpaceSmooth_iff_extension u)

/-- A pressure is smooth on nonnegative time exactly when it is the restriction
of a globally smooth spacetime pressure. -/
theorem smoothPressure_iff_globalExtension (p : PressureEvolution) :
    SmoothPressureOnNonnegativeTime p ↔ Nonempty (HalfSpaceSmoothExtension p) :=
  (smoothPressureOnNonnegativeTime_iff_halfSpaceSmooth p).trans
    (halfSpaceSmooth_iff_extension p)

/-- The force smoothness predicate uses the same half-space convention and has
the same exact extension characterization. -/
theorem smoothForce_iff_globalExtension (f : ForceField) :
    SmoothForceOnNonnegativeTime f ↔ Nonempty (HalfSpaceSmoothExtension f) := by
  change HalfSpaceSmooth f ↔ Nonempty (HalfSpaceSmoothExtension f)
  exact halfSpaceSmooth_iff_extension f

/-- The whole-space classical-solution contract with both half-space
smoothness premises replaced by actual globally smooth extension witnesses. -/
theorem classicalSolution_iff_globalExtensions
    (nu : ℝ) (f : ForceField) (u₀ : SchwartzVelocity)
    (u : VelocityEvolution) (p : PressureEvolution) :
    IsClassicalSolution nu f u₀ u p ↔
      Nonempty (HalfSpaceSmoothExtension u) ∧
      Nonempty (HalfSpaceSmoothExtension p) ∧
      (∀ x : Space, u 0 x = u₀ x) ∧
      Incompressible u ∧
      SatisfiesNavierStokes nu f u p ∧
      (∀ t : ℝ, 0 ≤ t → MeasureTheory.Integrable (fun x : Space ↦ ‖u t x‖ ^ 2)) ∧
      (∃ E : ℝ, 0 < E ∧ ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E) := by
  rw [Navier.OfficialSurfaceSignatures.classicalSolution_signature]
  simp only [smoothVelocity_iff_globalExtension, smoothPressure_iff_globalExtension]

/-- The periodic classical-solution contract with its velocity and pressure
smoothness premises replaced by globally smooth extension witnesses. -/
theorem periodicClassicalSolution_iff_globalExtensions
    (nu : ℝ) (f : ForceField) (u₀ : VelocityField)
    (u : VelocityEvolution) (p : PressureEvolution) :
    IsPeriodicClassicalSolution nu f u₀ u p ↔
      Nonempty (HalfSpaceSmoothExtension u) ∧
      Nonempty (HalfSpaceSmoothExtension p) ∧
      (∀ x : Space, u 0 x = u₀ x) ∧
      Incompressible u ∧
      SatisfiesNavierStokes nu f u p ∧
      SpatiallyPeriodicVelocity u ∧
      SpatiallyPeriodicPressure p := by
  rw [Navier.OfficialSurfaceSignatures.periodicClassicalSolution_signature]
  simp only [smoothVelocity_iff_globalExtension, smoothPressure_iff_globalExtension]

/-- The whole-space admissible-force contract with its half-space smoothness
premise replaced by a globally smooth extension witness. -/
theorem forcedDataRapidDecay_iff_globalExtension (f : ForceField) :
    ForcedDataRapidDecay f ↔
      Nonempty (HalfSpaceSmoothExtension f) ∧
      ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
          (1 + ‖x‖ + t) ^ K *
              ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space ↦ f z.1 z.2)
                nonnegativeSpacetime (t, x)‖ ≤ C := by
  simp only [ForcedDataRapidDecay, smoothForce_iff_globalExtension]

/-- The periodic admissible-force contract with its half-space smoothness
premise replaced by a globally smooth extension witness. -/
theorem periodicForcedDataRapidDecay_iff_globalExtension (f : ForceField) :
    PeriodicForcedDataRapidDecay f ↔
      SpatiallyPeriodicForce f ∧
      Nonempty (HalfSpaceSmoothExtension f) ∧
      ∀ (n K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
          (1 + t) ^ K *
              ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Space ↦ f z.1 z.2)
                nonnegativeSpacetime (t, x)‖ ≤ C := by
  simp only [PeriodicForcedDataRapidDecay, smoothForce_iff_globalExtension]

end Navier.Analysis.HalfSpaceConsumerBridge
