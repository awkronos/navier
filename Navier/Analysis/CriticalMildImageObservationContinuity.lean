import Navier.Analysis.CriticalMildSelfMap
import Navier.Analysis.CriticalMildObservationContinuity

/-!
# Positive-time continuity of the critical mild image

The linear heat path and the nonlinear Bochner Duhamel path combine to give
continuity of the assembled critical mild image on the positive-time subtype.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildImageObservationContinuity

open MeasureTheory Set Topology
open Navier
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildObservationContinuity

/-- A total representative of the mild image which agrees with it on positive
times.  The `max` only supplies a harmless heat-flow value away from `Ioi 0`. -/
def criticalMildImagePositiveExtension
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s)) (t : ℝ) :
    WeightedLatticeBanach :=
  weightedHeatFlow ν (max t 0) hν.le (le_max_right _ _) u₀ +
    criticalMildDuhamel ν hν u hu t

theorem criticalMildImagePositiveExtension_eq
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {t : ℝ} (ht : 0 < t) :
    criticalMildImagePositiveExtension ν hν u₀ u hu t =
      criticalMildImage ν hν u₀ u hu t ht.le := by
  simp [criticalMildImagePositiveExtension, criticalMildImage, max_eq_left ht.le]

/-- The full critical mild image is continuous on strictly positive times for
a continuous divergence-free path with a global radius bound. -/
theorem continuous_criticalMildImage_positive
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R : ℝ} (hR : 0 ≤ R) (huR : ∀ s, ‖u s‖ ≤ R) :
    Continuous fun τ : {t : ℝ // 0 < t} =>
      criticalMildImage ν hν u₀ u hu τ.1 τ.2.le := by
  have htime : Continuous fun τ : {t : ℝ // 0 < t} =>
      (⟨τ.1, τ.2.le⟩ : NNReal) :=
    continuous_subtype_val.subtype_mk fun τ => τ.2.le
  rw [continuous_iff_continuousAt]
  intro τ
  have hlinear : ContinuousAt (fun σ : {t : ℝ // 0 < t} =>
      weightedHeatFlow ν σ.1 hν.le σ.2.le u₀) τ := by
    have h := (continuous_weightedHeatFlow_nnreal ν hν.le u₀).comp htime
    convert h.continuousAt using 1
    funext σ
    congr
  have hduhamel : ContinuousAt (fun σ : {t : ℝ // 0 < t} =>
      criticalMildDuhamel ν hν u hu σ.1) τ := by
    have h := tendsto_criticalMildDuhamel_observation
      ν hν u huc hu hR τ.2 huR
    exact (h.comp continuous_subtype_val.continuousAt)
  change ContinuousAt
    ((fun σ : {t : ℝ // 0 < t} => weightedHeatFlow ν σ.1 hν.le σ.2.le u₀) +
      fun σ => criticalMildDuhamel ν hν u hu σ.1) τ
  exact hlinear.add hduhamel

/-- In ordinary `ContinuousOn` form, the full mild image is continuous on
`Ioi 0`; the extension agrees with `criticalMildImage` there. -/
theorem continuousOn_criticalMildImage_positiveExtension
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R : ℝ} (hR : 0 ≤ R) (huR : ∀ s, ‖u s‖ ≤ R) :
    ContinuousOn (criticalMildImagePositiveExtension ν hν u₀ u hu) (Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous fun τ : {t : ℝ // 0 < t} =>
    criticalMildImagePositiveExtension ν hν u₀ u hu τ.1
  convert continuous_criticalMildImage_positive ν hν u₀ u huc hu hR huR using 1
  funext τ
  exact criticalMildImagePositiveExtension_eq ν hν u₀ u hu τ.2

end Navier.Analysis.CriticalMildImageObservationContinuity

#print axioms Navier.Analysis.CriticalMildImageObservationContinuity.continuous_criticalMildImage_positive
#print axioms Navier.Analysis.CriticalMildImageObservationContinuity.continuousOn_criticalMildImage_positiveExtension
