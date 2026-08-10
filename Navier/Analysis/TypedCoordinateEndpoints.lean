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
end Navier.Analysis.TypedCoordinateEndpoints
