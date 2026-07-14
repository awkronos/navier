import Navier.OfficialProblem

/-!
# Definitional signatures for the official Clay surfaces

These theorems pin the exact outer quantifiers of alternatives A--D and the
fields of the whole-space and periodic solution contracts.  They are
regression guards for semantic drift, not inhabitants of any Clay statement.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.OfficialSurfaceSignatures

/-- The whole-space contract contains smoothness, trace, incompressibility,
the forced pointwise equation, integrability, and one uniform energy bound. -/
theorem classicalSolution_signature
    (nu : ℝ) (f : ForceField) (u₀ : SchwartzVelocity)
    (u : VelocityEvolution) (p : PressureEvolution) :
    IsClassicalSolution nu f u₀ u p ↔
      SmoothVelocityOnNonnegativeTime u ∧
      SmoothPressureOnNonnegativeTime p ∧
      (∀ x : Space, u 0 x = u₀ x) ∧
      Incompressible u ∧
      SatisfiesNavierStokes nu f u p ∧
      (∀ t : ℝ, 0 ≤ t →
        MeasureTheory.Integrable (fun x : Space ↦ ‖u t x‖ ^ 2)) ∧
      (∃ E : ℝ, 0 < E ∧
        ∀ t : ℝ, 0 ≤ t → kineticEnergy u t < E) := by
  constructor
  · intro h
    exact ⟨h.velocity_smooth, h.pressure_smooth, h.initial_condition,
      h.incompressible, h.equation, h.finite_energy,
      h.uniformly_bounded_energy⟩
  · rintro ⟨hu, hp, hinit, hdiv, heq, hfinite, hbound⟩
    exact
      { velocity_smooth := hu
        pressure_smooth := hp
        initial_condition := hinit
        incompressible := hdiv
        equation := heq
        finite_energy := hfinite
        uniformly_bounded_energy := hbound }

/-- The periodic contract has the official smoothness, trace, equation, and
velocity/pressure periodicity fields, with no whole-space energy field. -/
theorem periodicClassicalSolution_signature
    (nu : ℝ) (f : ForceField) (u₀ : VelocityField)
    (u : VelocityEvolution) (p : PressureEvolution) :
    IsPeriodicClassicalSolution nu f u₀ u p ↔
      SmoothVelocityOnNonnegativeTime u ∧
      SmoothPressureOnNonnegativeTime p ∧
      (∀ x : Space, u 0 x = u₀ x) ∧
      Incompressible u ∧
      SatisfiesNavierStokes nu f u p ∧
      SpatiallyPeriodicVelocity u ∧
      SpatiallyPeriodicPressure p := by
  constructor
  · intro h
    exact ⟨h.velocity_smooth, h.pressure_smooth, h.initial_condition,
      h.incompressible, h.equation, h.velocity_periodic,
      h.pressure_periodic⟩
  · rintro ⟨hu, hp, hinit, hdiv, heq, huPeriodic, hpPeriodic⟩
    exact
      { velocity_smooth := hu
        pressure_smooth := hp
        initial_condition := hinit
        incompressible := hdiv
        equation := heq
        velocity_periodic := huPeriodic
        pressure_periodic := hpPeriodic }

/-- Exact outer signature of Fefferman alternative A. -/
theorem statementA_signature :
    Clay.StatementA =
      (∀ nu : ℝ, 0 < nu →
        ∀ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ →
          ∃ (u : VelocityEvolution) (p : PressureEvolution),
            IsClassicalSolution nu zeroForce u₀ u p) := rfl

/-- Exact outer signature of Fefferman alternative B. -/
theorem statementB_signature :
    Clay.StatementB =
      (∀ nu : ℝ, 0 < nu →
        ∀ u₀ : VelocityField, PeriodicInitialDatum u₀ →
          ∃ (u : VelocityEvolution) (p : PressureEvolution),
            IsPeriodicClassicalSolution nu zeroForce u₀ u p) := rfl

/-- Exact outer signature of Fefferman alternative C. -/
theorem statementC_signature :
    Clay.StatementC =
      (∀ nu : ℝ, 0 < nu →
        ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ ∧
          ∃ f : ForceField, ForcedDataRapidDecay f ∧
            ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
              IsClassicalSolution nu f u₀ u p) := rfl

/-- Exact outer signature of Fefferman alternative D. -/
theorem statementD_signature :
    Clay.StatementD =
      (∀ nu : ℝ, 0 < nu →
        ∃ u₀ : VelocityField, PeriodicInitialDatum u₀ ∧
          ∃ f : ForceField, PeriodicForcedDataRapidDecay f ∧
            ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
              IsPeriodicClassicalSolution nu f u₀ u p) := rfl

end Navier.OfficialSurfaceSignatures
