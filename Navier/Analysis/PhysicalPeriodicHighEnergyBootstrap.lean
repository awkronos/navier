import Navier.Analysis.PhysicalPeriodicHighEnergyContinuity
import Navier.Analysis.CriticalMildLocalUniformBootstrap

/-!
# Fully internal positive-time high-energy bootstrap

The local half-generator bound used by the physical high-energy comparison is
already a consequence of the literal mild equation.  This module performs
that substitution.  The resulting estimate has no assumed tail, moment,
mode-sum derivative, or continuity premise.

The chart bound `R` still enters the explicit compact-window budget.  A bound
for `R` depending only on the initial datum and viscosity, uniformly over all
horizons, remains exactly the large-data global-control step.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicHighEnergyBootstrap

open Set Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildLocalUniformBootstrap
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicHighEnergyContinuity

/-- Fully internal high-frequency energy decay on a compact positive-time
window.  The half-generator constant is the repository's explicit bootstrap
budget, derived from the actual mild path. -/
theorem exists_mild_highEnergy_decay_add_explicitBootstrap
    (mu : ℝ) (hmu : 0 < mu) (a0 : WeightedLatticeBanach)
    (ha0 : LatticeDivergenceFree a0)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R delta T N : ℝ}
    (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hdeltaT : delta ≤ T) (hN : 0 < N)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage mu hmu a0 A hdiv s hs.1) :
    ∃ b0 : ℝ,
      0 < b0 ∧ b0 < delta ∧ delta - b0 ≤ 1 ∧
      Real.sqrt (delta - b0) < b0 ∧
      ∀ t ∈ Icc delta T,
        rawHighSpectralEnergy N (A t) ≤
          Real.exp (-(2 * mu * N ^ 2) * (t - delta)) *
              rawHighSpectralEnergy N (A delta) +
            4 * R ^ 2 *
                compactHalfGeneratorBudget mu a0 R delta b0 T /
              (mu * N ^ 3) := by
  obtain ⟨b0, hb0, hb0delta, hunit, hinterior, hbudget, huniform⟩ :=
    exists_uniform_halfGenerator_on_compactPositiveInterval
      mu hmu a0 ha0 A hAc hdiv hR hdelta hdeltaT hbound hmild
  refine ⟨b0, hb0, hb0delta, hunit, hinterior, ?_⟩
  exact mild_highEnergy_le_decay_add_equilibrium_of_continuousPath
    mu hmu a0 ha0 A hAc hdiv hR hbudget hdelta hdeltaT hN hbound hmild
      (fun s hs => (huniform s hs).1)
      (fun s hs => (huniform s hs).2.2.2.2.2)

end Navier.Analysis.PhysicalPeriodicHighEnergyBootstrap
