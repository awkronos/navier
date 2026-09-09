import Navier.Analysis.CriticalMildEnergyEvolution
import Navier.Analysis.RawHighEnergyRateIdentity

/-! Exact high-frequency energy balance for the actual mild trajectory.
Raw energy has the fixed physical conversion factor documented by its carrier. -/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.PhysicalPeriodicEnergyBalance

open Set Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildEnergyEvolution
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.RawHighEnergyRateIdentity

theorem hasDerivAt_mild_highEnergy_flux_dissipation
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t N : ℝ} (hR : 0 ≤ R) (hN : 0 ≤ N) (ht : t ∈ Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    HasDerivAt (fun s => rawHighSpectralEnergy N (A s))
      (2 * rawHighFrequencyEnergyFlux N (A t) -
        2 * μ * rawHighSpectralDissipation N (A t)) t := by
  have h := hasDerivAt_mild_rawHighSpectralEnergy μ hμ a ha A hAc hdiv hR hN ht hbound hmild
  rw [tsum_rawHighModeEnergyRate_mildRawTimeDerivative μ N A hdiv t] at h
  exact h

end Navier.Analysis.PhysicalPeriodicEnergyBalance
