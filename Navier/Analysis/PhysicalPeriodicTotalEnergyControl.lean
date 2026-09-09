import Navier.Analysis.PhysicalPeriodicEnergyBalance
import Navier.Analysis.PhysicalPeriodicHighEnergyContinuity

/-! Datum-only total spectral energy control for the actual physical mild flow.
The estimate is independent of the chart radius and horizon. It controls energy,
not the stronger graph moment required for global continuation. -/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.PhysicalPeriodicTotalEnergyControl

open Set Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildPathIntegrand
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PeriodicGlobalCriticalControl
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicEnergyEvolution
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicEnergyBalance
open Navier.Analysis.PhysicalPeriodicHighEnergyContinuity

theorem rawHighFrequencyEnergyFlux_zero_cutoff
    (u : WeightedLatticeBanach) (hreal : PhysicalAntiHermitian u)
    (hdiv : LatticeDivergenceFree u) :
    rawHighFrequencyEnergyFlux 0 u = 0 := by
  simpa only [rawHighFrequencyEnergyFlux, projectedHighTriadEnergy,
    if_pos (latticeModeSize_nonneg _)] using
    tsum_projectedPhysicalTriadEnergy_eq_zero u hreal hdiv

theorem rawHighSpectralDissipation_nonneg (N : ℝ)
    (u : WeightedLatticeBanach) : 0 ≤ rawHighSpectralDissipation N u := by
  apply tsum_nonneg
  intro k
  unfold rawSpectralDissipationDensity
  split_ifs <;> positivity

theorem offZeroSpectralEnergy_le_total (u : WeightedLatticeBanach) :
    offZeroSpectralEnergy u ≤ rawHighSpectralEnergy 0 u := by
  have hsum := summable_rawSpectralEnergyDensity u
  have hpoint (k : LatticeMode) :
      amplitudeOffZero u k ^ 2 ≤ rawSpectralEnergyDensity u k := by
    by_cases hk : k = 0
    · simp [amplitudeOffZero, hk, rawSpectralEnergyDensity, sq_nonneg]
    · simp [amplitudeOffZero, hk, rawSpectralEnergyDensity]
  have hsmall : Summable (fun k : LatticeMode => amplitudeOffZero u k ^ 2) :=
    hsum.of_nonneg_of_le (fun k => sq_nonneg _) hpoint
  have h := hsmall.tsum_le_tsum hpoint hsum
  simpa only [offZeroSpectralEnergy, rawHighSpectralEnergy,
    if_pos (latticeModeSize_nonneg _)] using h

/-- Every bounded physical mild chart has nonincreasing total spectral energy,
including its endpoints by continuity. No derivative hypothesis is assumed. -/
theorem antitoneOn_mild_totalEnergy
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    AntitoneOn (fun s => rawHighSpectralEnergy 0 (A s)) (Icc (0 : ℝ) T) := by
  have hd (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) T) :=
    hasDerivAt_mild_highEnergy_flux_dissipation μ hμ a ha A hAc hdiv
      hR (N := 0) le_rfl hs hbound hmild
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    (continuousOn_rawHighSpectralEnergy_comp 0 A hAc _)
  · intro s hs
    rw [interior_Icc] at hs
    exact (hd s hs).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(hd s hs).deriv, rawHighFrequencyEnergyFlux_zero_cutoff
      (A s) (hreal s) (hdiv s)]
    have hD := rawHighSpectralDissipation_nonneg 0 (A s)
    nlinarith

/-- Uniform energy bound on every actual chart: the right side is the energy
at its initial time, with no horizon or radius dependence. -/
theorem mild_totalEnergy_le_initial
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Icc (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    rawHighSpectralEnergy 0 (A t) ≤ rawHighSpectralEnergy 0 a := by
  have h0 : A 0 = a := by
    rw [hmild 0 ⟨le_rfl, ht.1.trans ht.2⟩]
    simp only [criticalMildImage, criticalMildDuhamel, Ioc_self,
      MeasureTheory.setIntegral_empty, add_zero]
    exact weightedHeatFlow_zero_of_divergenceFree μ hμ.le a ha
  have h := antitoneOn_mild_totalEnergy μ hμ a ha A hAc hdiv hreal hR hbound hmild
    ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simpa only [h0] using h

/-- The energy term used by the off-zero continuation split is bounded by
the datum's total energy on every physical mild chart. The graph term remains
a separate analytic obligation. -/
theorem mild_offZeroEnergy_le_initial
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Icc (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    offZeroSpectralEnergy (A t) ≤ rawHighSpectralEnergy 0 a :=
  (offZeroSpectralEnergy_le_total (A t)).trans
    (mild_totalEnergy_le_initial μ hμ a ha A hAc hdiv hreal hR ht hbound hmild)

#print axioms Navier.Analysis.PhysicalPeriodicTotalEnergyControl.rawHighFrequencyEnergyFlux_zero_cutoff
#print axioms Navier.Analysis.PhysicalPeriodicTotalEnergyControl.mild_totalEnergy_le_initial
#print axioms Navier.Analysis.PhysicalPeriodicTotalEnergyControl.mild_offZeroEnergy_le_initial

end Navier.Analysis.PhysicalPeriodicTotalEnergyControl
