import Navier.Analysis.CriticalMildPathFixedPoint
import Navier.Analysis.CriticalMildHeatCarrierAlgebra

/-!
# Shifted critical mild Duhamel algebra

This module isolates the pointwise heat covariance needed to restart a mild
trajectory after a positive elapsed time.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildRestart

open MeasureTheory Set
open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildHeatCarrierAlgebra
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildObservationContinuity

/-- Advancing a positive-lag nonlinear Duhamel integrand by `r` is the same
as advancing its observation time by `r`. -/
theorem weightedHeatFlow_criticalMildPathIntegrand_covariant
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t s r : ℝ) (hr : 0 ≤ r) (hst : s < t) :
    weightedHeatFlow ν r hν.le hr
        (criticalMildPathIntegrand ν hν u hu t s) =
      criticalMildPathIntegrand ν hν u hu (t + r) s := by
  ext m i
  rw [weightedHeatFlow_apply]
  unfold weightedHeatFlowCoordinate criticalMildPathIntegrand
  have hlag : 0 < t - s := sub_pos.mpr hst
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν _ _ (hu s) hlag]
  rw [weightedLatticeCoefficient_heatRegularizedSpectralOutput]
  have hlag' : 0 < t + r - s := by linarith
  rw [positiveTimeHeatRegularizedSpectralOutput_of_pos ν hν _ _ (hu s) hlag']
  rw [heatRegularizedSpectralOutput_apply]
  unfold heatRegularizedSpectralOutputFiber
  rw [show t + r - s = r + (t - s) by ring]
  rw [ComplexFrequencyHeatLeray.complexFrequencyHeatLeray_semigroup]

/-- The nonlinear contribution on a shifted horizon, written in elapsed-time
coordinates from the restart time. -/
def criticalMildDuhamelRestartTail
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t r : ℝ) : WeightedLatticeBanach :=
  ∫ σ in Ioc 0 r, criticalMildPathIntegrand ν hν u hu (t + r) (t + σ)

/-- Changing variables from absolute time to elapsed restart time identifies
the restart tail with the literal moving Duhamel tail. -/
theorem criticalMildDuhamelRestartTail_eq_tail
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t r : ℝ) (hr : 0 ≤ r) :
    criticalMildDuhamelRestartTail ν hν u hu t r =
      criticalMildDuhamelTail ν hν u hu t (t + r) := by
  unfold criticalMildDuhamelRestartTail criticalMildDuhamelTail
  rw [← intervalIntegral.integral_of_le hr,
    ← intervalIntegral.integral_of_le (show t ≤ t + r by linarith)]
  simpa [add_comm, add_left_comm, add_assoc] using
    (intervalIntegral.integral_comp_add_right
      (fun s => criticalMildPathIntegrand ν hν u hu (t + r) s) t)

/-- The literal Duhamel integral on a horizon ending at `t + r` splits into
the pre-restart history and the elapsed-time restart tail. -/
theorem criticalMildDuhamel_split_restart
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t r : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (hr : 0 ≤ r)
    (huR : ∀ s ∈ Ioc (0 : ℝ) (t + r), ‖u s‖ ≤ R) :
    criticalMildDuhamel ν hν u hu (t + r) =
      (∫ s in Ioc 0 t, criticalMildPathIntegrand ν hν u hu (t + r) s) +
        criticalMildDuhamelRestartTail ν hν u hu t r := by
  rw [criticalMildDuhamelRestartTail_eq_tail ν hν u hu t r hr]
  exact criticalMildDuhamel_eq_truncated_add_tail
    ν hν u huc hu hR ht (by linarith) huR

/-- The terminal carrier value serving as initial data for a prospective
local restart. -/
def criticalMildTerminalData
    (u : ℝ → WeightedLatticeBanach) (t : ℝ) : WeightedLatticeBanach := u t

/-- The candidate restarted mild value: heat evolution of the terminal data
plus the elapsed-time nonlinear tail.  Its equality to the original path
requires the separate result that heat flow commutes with the Bochner prefix
integral. -/
def criticalMildRestartImage
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t r : ℝ) (hr : 0 ≤ r) : WeightedLatticeBanach :=
  weightedHeatFlow ν r hν.le hr (criticalMildTerminalData u t) +
    criticalMildDuhamelRestartTail ν hν u hu t r

theorem criticalMildRestartImage_zero
    (ν : ℝ) (hν : 0 < ν)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) :
    criticalMildRestartImage ν hν u hu t 0 le_rfl =
      weightedHeatFlow ν 0 hν.le le_rfl (criticalMildTerminalData u t) := by
  simp [criticalMildRestartImage, criticalMildDuhamelRestartTail,
    criticalMildPathIntegrand, positiveTimeHeatRegularizedSpectralOutput]

end Navier.Analysis.CriticalMildRestart

#print axioms Navier.Analysis.CriticalMildRestart.weightedHeatFlow_criticalMildPathIntegrand_covariant
#print axioms Navier.Analysis.CriticalMildRestart.criticalMildDuhamelRestartTail_eq_tail
#print axioms Navier.Analysis.CriticalMildRestart.criticalMildDuhamel_split_restart
#print axioms Navier.Analysis.CriticalMildRestart.criticalMildRestartImage_zero
