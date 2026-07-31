import Navier.Analysis.CriticalMildPathIntegrand

/-!
# Pointwise critical mild self-map

This file assembles the completed same-weight heat flow and the literal
time-dependent nonlinear Bochner integral.  Continuity in the observation
time and the two-path contraction estimate remain separate analytic rungs.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.CriticalMildSelfMap

open MeasureTheory Set
open Navier
open Navier.Analysis.ComplexLerayProjection
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildWeightedBilinear
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatFlow
open Navier.Analysis.CriticalMildPathIntegrand

/-- Divergence freedom is stable under addition in the completed carrier. -/
theorem LatticeDivergenceFree.add {u v : WeightedLatticeBanach}
    (hu : LatticeDivergenceFree u) (hv : LatticeDivergenceFree v) :
    LatticeDivergenceFree (u + v) := by
  intro m
  rw [show weightedLatticeCoefficient (u + v) m =
      weightedLatticeCoefficient u m + weightedLatticeCoefficient v m by
    exact congrFun (weightedLatticeCoefficient_add u v) m]
  have hpoint (a b : ComplexSpace) :
      complexEuclideanPoint (a + b) =
        complexEuclideanPoint a + complexEuclideanPoint b := by
    ext j
    rfl
  rw [hpoint, inner_add_right, hu m, hv m, add_zero]

/-- The completed critical mild image at a nonnegative observation time:
linear heat--Leray evolution plus the actual evolving-path Duhamel integral. -/
def criticalMildImage
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (t : ℝ) (ht : 0 ≤ t) : WeightedLatticeBanach :=
  weightedHeatFlow ν t hν.le ht u₀ +
    criticalMildDuhamel ν hν u hu t

/-- The assembled mild image remains divergence-free. -/
theorem criticalMildImage_divergenceFree
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    LatticeDivergenceFree (criticalMildImage ν hν u₀ u hu t ht) := by
  apply LatticeDivergenceFree.add
  · exact weightedHeatFlow_divergenceFree ν t hν.le ht u₀
  · exact criticalMildDuhamel_divergenceFree ν hν u huc hu hR ht huR

/-- Pointwise radius estimate for the actual assembled mild image. -/
theorem norm_criticalMildImage_le
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R) :
    ‖criticalMildImage ν hν u₀ u hu t ht‖ ≤
      ‖u₀‖ + (2 * Real.sqrt t / Real.sqrt ν) * R ^ 2 := by
  unfold criticalMildImage
  calc
    ‖weightedHeatFlow ν t hν.le ht u₀ +
        criticalMildDuhamel ν hν u hu t‖ ≤
      ‖weightedHeatFlow ν t hν.le ht u₀‖ +
        ‖criticalMildDuhamel ν hν u hu t‖ :=
      norm_add_le _ _
    _ ≤ ‖u₀‖ + (2 * Real.sqrt t / Real.sqrt ν) * R ^ 2 :=
      add_le_add
        (norm_weightedHeatFlow_le ν t hν.le ht u₀)
        (norm_criticalMildDuhamel_le ν hν u huc hu hR ht huR)

/-- A short-horizon quadratic budget makes the assembled pointwise mild image
preserve a radius-`R` ball. -/
theorem norm_criticalMildImage_le_radius
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (htT : t ≤ T)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hbudget :
      ‖u₀‖ + (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 ≤ R) :
    ‖criticalMildImage ν hν u₀ u hu t ht‖ ≤ R := by
  have hsqrt : Real.sqrt t ≤ Real.sqrt T :=
    Real.sqrt_le_sqrt htT
  have hcoef : 0 ≤ (2 / Real.sqrt ν) * R ^ 2 := by
    positivity
  have htime :
      (2 * Real.sqrt t / Real.sqrt ν) * R ^ 2 ≤
        (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 := by
    calc
      (2 * Real.sqrt t / Real.sqrt ν) * R ^ 2 =
          ((2 / Real.sqrt ν) * R ^ 2) * Real.sqrt t := by ring
      _ ≤ ((2 / Real.sqrt ν) * R ^ 2) * Real.sqrt T :=
        mul_le_mul_of_nonneg_left hsqrt hcoef
      _ = (2 * Real.sqrt T / Real.sqrt ν) * R ^ 2 := by ring
  exact (norm_criticalMildImage_le ν hν u₀ u huc hu hR ht huR).trans
    ((add_le_add_right htime ‖u₀‖).trans hbudget)

/-- Two continuous divergence-free paths in the radius-`R` ball are sent,
pointwise, at most `4 sqrt(t) R / sqrt(ν)` times their uniform separation
apart by the actual assembled mild map. -/
theorem norm_criticalMildImage_sub_le
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u v : ℝ → WeightedLatticeBanach)
    (huc : Continuous u) (hvc : Continuous v)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    (hv : ∀ s, LatticeDivergenceFree (v s))
    {R D t : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (huR : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s‖ ≤ R)
    (hvR : ∀ s ∈ Ioc (0 : ℝ) t, ‖v s‖ ≤ R)
    (huvD : ∀ s ∈ Ioc (0 : ℝ) t, ‖u s - v s‖ ≤ D) :
    ‖criticalMildImage ν hν u₀ u hu t ht -
        criticalMildImage ν hν u₀ v hv t ht‖ ≤
      (4 * Real.sqrt t / Real.sqrt ν) * R * D := by
  simpa only [criticalMildImage, add_sub_add_left_eq_sub] using
    norm_criticalMildDuhamel_sub_le
      ν hν u v huc hvc hu hv hR hD ht huR hvR huvD

/-- At observation time zero the assembled mild image has no nonlinear
Duhamel contribution: the literal Bochner interval is empty. -/
theorem criticalMildImage_zero_nonlinear
    (ν : ℝ) (hν : 0 < ν)
    (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach)
    (hu : ∀ s, LatticeDivergenceFree (u s)) :
    criticalMildImage ν hν u₀ u hu 0 le_rfl =
      weightedHeatFlow ν 0 hν.le le_rfl u₀ := by
  unfold criticalMildImage criticalMildDuhamel
  simp

end Navier.Analysis.CriticalMildSelfMap

#print axioms Navier.Analysis.CriticalMildSelfMap.criticalMildImage_divergenceFree
#print axioms Navier.Analysis.CriticalMildSelfMap.norm_criticalMildImage_le_radius
#print axioms Navier.Analysis.CriticalMildSelfMap.norm_criticalMildImage_sub_le
#print axioms Navier.Analysis.CriticalMildSelfMap.criticalMildImage_zero_nonlinear
