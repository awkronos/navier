import Navier.Analysis.RawHighEnergyDifferentiation

/-! Actual countable energy differentiation along the repository's mild flow.
The local derivative mass bound is derived from the mild equation. -/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.CriticalMildEnergyEvolution

open Set Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildModeDifferentiation
open Navier.Analysis.CriticalMildLocalUniformBootstrap
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.RawHighEnergyDifferentiation

theorem hasDerivAt_mild_rawHighSpectralEnergy
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R T t N : ℝ} (hR : 0 ≤ R) (hN : 0 ≤ N) (ht : t ∈ Ioo (0 : ℝ) T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    HasDerivAt (fun s => rawHighSpectralEnergy N (A s))
      (∑' k, rawHighModeEnergyRate N (A t) (mildRawTimeDerivative μ A t) k) t := by
  have hhalf : 0 < t / 2 := by linarith [ht.1]
  have hhalfT : t / 2 ≤ T := by linarith [ht.1, ht.2]
  obtain ⟨b, _, _, _, _, hbudget, huniform⟩ :=
    exists_uniform_halfGenerator_on_compactPositiveInterval μ hμ a ha A hAc hdiv
      hR hhalf hhalfT hbound hmild
  let M := (R + |μ|) * (R + compactHalfGeneratorBudget μ a R (t / 2) b T)
  have hM : 0 ≤ M := mul_nonneg (add_nonneg hR (abs_nonneg μ)) (add_nonneg hR hbudget)
  apply hasDerivAt_rawHighSpectralEnergy_of_uniform_mass A
    (mildRawTimeDerivative μ A) (s := Ioo (t / 2) T) isOpen_Ioo hN hR hM
  · exact ⟨by linarith [ht.1], ht.2⟩
  · intro r hr
    exact hbound r ⟨hhalf.trans hr.1, hr.2.le⟩
  · intro r hr
    exact (huniform r ⟨hr.1.le, hr.2.le⟩).2.2.2.1
  · intro r hr
    exact (huniform r ⟨hr.1.le, hr.2.le⟩).2.2.2.2.1
  · intro r hr k i
    exact hasDerivAt_mildPath_coefficient_eq_mildRawTimeDerivative μ hμ a A hAc hdiv
      hR ⟨hhalf.trans hr.1, hr.2⟩ hbound hmild k i

end Navier.Analysis.CriticalMildEnergyEvolution
