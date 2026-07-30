import Navier.Analysis.CriticalMildHeatTimeKernel

/-!
# Positive-time completed heat lift

The actual completed heat lift is extended by zero at nonpositive time so it
has a total time-function type.  The singular estimate is used only on the
positive-time branch.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildHeatBochner

open MeasureTheory Set
open Navier
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.FrequencyHeatLeray
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatSmoothing
open Navier.Analysis.CriticalMildHeatCarrierLift
open Navier.Analysis.CriticalMildHeatTimeKernel

/-- The actual two-weight heat carrier, made total by its zero extension at
nonpositive elapsed time. -/
def positiveTimeHeatLift (ν : ℝ) (hν : 0 < ν) (u : WeightedLatticeBanach) :
    ℝ → LatticeWeightTwoCarrier := fun τ =>
  if hτ : 0 < τ then heatLift ν τ hν hτ u else 0

/-- On positive time, the total integrand is definitionally the actual
completed heat lift. -/
theorem positiveTimeHeatLift_of_pos (ν : ℝ) (hν : 0 < ν) (u : WeightedLatticeBanach)
    {τ : ℝ} (hτ : 0 < τ) :
    positiveTimeHeatLift ν hν u τ = heatLift ν τ hν hτ u := by
  simp [positiveTimeHeatLift, hτ]

/-- The explicit singular scalar majorant controls the actual carrier on its
positive-time branch. -/
theorem norm_positiveTimeHeatLift_le (ν : ℝ) (hν : 0 < ν)
    (u : WeightedLatticeBanach) {τ : ℝ} (hτ : 0 < τ) :
    ‖positiveTimeHeatLift ν hν u τ‖ ≤ heatTimeMajorant ν τ * ‖u‖ := by
  rw [positiveTimeHeatLift_of_pos ν hν u hτ, heatTimeMajorant_eq ν τ hν hτ]
  exact norm_heatLift_le ν τ hν hτ u

/-- Every physical Fourier coordinate of the actual heat--Leray evolution is
continuous in time.  This is the coordinatewise input to the missing `lp`
measurability bridge. -/
theorem continuous_heatLiftCoefficient_apply (ν : ℝ) (u : WeightedLatticeBanach)
    (m : LatticeMode) (i : Fin 3) :
    Continuous fun τ : ℝ => heatLiftCoefficient ν τ u m i := by
  rw [show (fun τ : ℝ => heatLiftCoefficient ν τ u m i) =
      fun τ => (complexHeatDecay ν τ (latticeFrequency m) : ℂ) *
        complexLeray (latticeFrequency m) (weightedLatticeCoefficient u m) i by
    funext τ
    exact complexFrequencyHeatLeray_apply_coordinate ν τ (latticeFrequency m)
      (weightedLatticeCoefficient u m) i]
  unfold complexHeatDecay heatDecay
  fun_prop

/-- The scalar heat majorant is interval-integrable on every finite horizon. -/
theorem intervalIntegrable_heatTimeMajorant (ν T : ℝ) :
    IntervalIntegrable (heatTimeMajorant ν) volume 0 T := by
  unfold heatTimeMajorant
  exact intervalIntegral.intervalIntegrable_const.add
    ((inverseSqrtTime_intervalIntegrable T).const_mul _)

/-- The scalar budget governing the positive-time carrier has the exact
finite-horizon value. -/
theorem integral_heatTimeMajorant_positiveTime (ν T : ℝ) (hT : 0 ≤ T) :
    (∫ τ in (0 : ℝ)..T, heatTimeMajorant ν τ) =
      T + 2 * Real.sqrt T / Real.sqrt ν :=
  integral_heatTimeMajorant_zero ν T hT

end Navier.Analysis.CriticalMildHeatBochner
