import Navier.Analysis.ViscosityEndpoints
import Navier.Analysis.ForceCoordinateDecayBridge
set_option autoImplicit false
noncomputable section
namespace Navier.Analysis.TypedCoordinateEndpoints
open Navier
open Navier.Analysis.ViscosityEndpoints
open Navier.Analysis.ForceCoordinateDecayBridge
open Navier.Breakdown.OfficialCDEncoding
def WholeSpaceTypedCoordinateBreakdownAtViscosityOne : Prop :=
  ∃ u₀ : SchwartzVelocity, DivergenceFreeInitial u₀ ∧
    ∃ f : ForceField, (SmoothForceOnNonnegativeTime f ∧ WholeSpaceCoordinatewiseForceDecay f) ∧
      ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution), IsClassicalSolution 1 f u₀ u p
theorem wholeSpaceBreakdownAtViscosityOne_iff_typedCoordinate :
    WholeSpaceBreakdownAtViscosityOne ↔ WholeSpaceTypedCoordinateBreakdownAtViscosityOne := by
  constructor
  · rintro ⟨u₀, hu₀, f, hf, hno⟩
    exact ⟨u₀, hu₀, f, (forcedDataRapidDecay_iff_typedCoordinatewise f).1 hf, hno⟩
  · rintro ⟨u₀, hu₀, f, hf, hno⟩
    exact ⟨u₀, hu₀, f, (forcedDataRapidDecay_iff_typedCoordinatewise f).2 hf, hno⟩

def PeriodicTypedCoordinateBreakdownAtViscosityOne : Prop :=
  ∃ u₀ : VelocityField, PeriodicInitialDatum u₀ ∧
    ∃ f : ForceField,
      (SpatiallyPeriodicForce f ∧ SmoothForceOnNonnegativeTime f ∧
        PeriodicCoordinatewiseForceDecay f) ∧
      ¬ ∃ (u : VelocityEvolution) (p : PressureEvolution),
        IsPeriodicClassicalSolution 1 f u₀ u p

/-- Alternative D has the same exact interface replacement: periodic force
admissibility is expressed by its periodicity, smoothness, and typed-coordinate
decay fields, with the nonexistence witness unchanged. -/
theorem periodicBreakdownAtViscosityOne_iff_typedCoordinate :
    PeriodicBreakdownAtViscosityOne ↔
      PeriodicTypedCoordinateBreakdownAtViscosityOne := by
  constructor
  · rintro ⟨u₀, hu₀, f, hf, hno⟩
    exact ⟨u₀, hu₀, f,
      (periodicForcedDataRapidDecay_iff_typedCoordinatewise f).1 hf, hno⟩
  · rintro ⟨u₀, hu₀, f, hf, hno⟩
    exact ⟨u₀, hu₀, f,
      (periodicForcedDataRapidDecay_iff_typedCoordinatewise f).2 hf, hno⟩
end Navier.Analysis.TypedCoordinateEndpoints
