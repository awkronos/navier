import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Navier.Analysis.PhysicalPeriodicDissipationBudget

/-!
# Datum-controlled good times on physical periodic mild trajectories

The exact integrated dissipation law selects a time in every nondegenerate
window where total dissipation, and hence every spectral energy tail, is
quantitatively controlled by the initial datum.  This is a simultaneous
all-cutoff restart-time estimate; it does not convert the quadratic spectral
control into the critical weighted `ℓ¹` graph norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicGoodTimeSelection

open scoped Interval
open Set MeasureTheory intervalIntegral Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.PhysicalPeriodicGlobalControl
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicTotalEnergyControl
open Navier.Analysis.PhysicalPeriodicDissipationBudget

/-- In every nondegenerate time window, an actual physical mild trajectory
has a time whose viscosity-weighted dissipation is controlled by the datum's
energy divided by the window length. -/
theorem exists_goodDissipationTime
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T δ t : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδt : δ < t) (htT : t ≤ T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    ∃ c ∈ Icc δ t,
      2 * μ * (t - δ) * rawHighSpectralDissipation 0 (A c) ≤
        rawHighSpectralEnergy 0 a := by
  let D : ℝ → ℝ := fun s => rawHighSpectralDissipation 0 (A s)
  have hcontD : Continuous D :=
    (continuous_rawHighSpectralDissipation 0).comp hAc
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume δ t :=
    intervalIntegrable_const
  have hone : ∀ s ∈ Ι δ t, 0 ≤ (1 : ℝ) := by
    intro s hs
    positivity
  obtain ⟨c, hc, hmean⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg
      hcontD.continuousOn hconst hone
  have hIcc : Icc δ t = uIcc δ t := by
    rw [uIcc_of_le hδt.le]
  have hmean' :
      (∫ s in δ..t, D s) = D c * (t - δ) := by
    simpa only [mul_one, intervalIntegral.integral_const, one_mul,
      smul_eq_mul] using hmean
  have hbudget := mild_integratedDissipation_le_initial
    μ hμ a ha A hAc hdiv hreal hR hδ hδt.le htT hbound hmild
  refine ⟨c, ?_, ?_⟩
  · rwa [hIcc]
  · dsimp [D] at hmean' hbudget
    rw [hmean'] at hbudget
    nlinarith

/-- The selected time controls all nonnegative sharp cutoffs at once.  This
is stronger than selecting a separate mean-value time for each cutoff. -/
theorem exists_goodDissipationTime_all_highEnergy_cutoffs
    (μ : ℝ) (hμ : 0 < μ) (a : WeightedLatticeBanach)
    (ha : LatticeDivergenceFree a)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    (hreal : ∀ s, PhysicalAntiHermitian (A s))
    {R T δ t : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hδt : δ < t) (htT : t ≤ T)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage μ hμ a A hdiv s hs.1) :
    ∃ c ∈ Icc δ t, ∀ N : ℝ, 0 ≤ N →
      2 * μ * (t - δ) * N ^ 2 * rawHighSpectralEnergy N (A c) ≤
        rawHighSpectralEnergy 0 a := by
  obtain ⟨c, hc, hcD⟩ := exists_goodDissipationTime
    μ hμ a ha A hAc hdiv hreal hR hδ hδt htT hbound hmild
  refine ⟨c, hc, ?_⟩
  intro N hN
  have hcoercive := cutoff_sq_mul_highEnergy_le_highDissipation N hN (A c)
  have htotal := rawHighSpectralDissipation_le_total N (A c)
  have hpoint := hcoercive.trans htotal
  have hfactor : 0 ≤ 2 * μ * (t - δ) := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hpoint hfactor
  nlinarith

end Navier.Analysis.PhysicalPeriodicGoodTimeSelection
