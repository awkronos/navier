import Navier.Analysis.PhysicalPeriodicEnergyBalance
import Navier.Analysis.PhysicalPeriodicTailMomentControl

/-!
# Quantitative high-frequency energy on a positive-time mild window

This module consumes the actual countable Fourier energy derivative and the
physical high-tail flux estimate.  On any positive-time window where the
completed-carrier norm and half-generator moment have common bounds, high
energy decays toward an explicit cutoff-dependent equilibrium.

The result is a genuine trajectory estimate, rather than a static frequency
split.  Its constants still depend on the chosen finite window through the
available carrier and moment bounds.  Making those constants depend only on
the datum and viscosity, uniformly over all future windows, is the remaining
global periodic control problem.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicHighEnergyWindow

open Set Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.PhysicalPeriodicHighTailFlux
open Navier.Analysis.PhysicalPeriodicEnergyBalance
open Navier.Analysis.PhysicalPeriodicTailMomentControl

/-- Damped affine comparison on an arbitrary compact interval. -/
theorem damped_affine_apriori_Icc
    {Y Y' : ℝ → ℝ} {c B a b : ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hYc : ContinuousOn Y (Icc a b))
    (hYderiv : ∀ t ∈ Ioo a b, HasDerivAt Y (Y' t) t)
    (hbound : ∀ t ∈ Ioo a b, Y' t ≤ -c * Y t + B) :
    ∀ t ∈ Icc a b,
      Y t ≤ Real.exp (-c * (t - a)) * Y a +
        (B / c) * (1 - Real.exp (-c * (t - a))) := by
  let q : ℝ := B / c
  let W : ℝ → ℝ := fun t => (Y t - q) * Real.exp (c * t)
  have hWc : ContinuousOn W (Icc a b) := by
    exact hYc.sub continuousOn_const |>.mul
      ((continuousOn_const.mul continuousOn_id).rexp)
  have hWd : ∀ t ∈ Ioo a b,
      HasDerivAt W ((Y' t + c * (Y t - q)) * Real.exp (c * t)) t := by
    intro t ht
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (c * r))
        (c * Real.exp (c * t)) t := by
      simpa only [id_eq, mul_one, mul_comm] using
        ((hasDerivAt_id t).const_mul c).exp
    have hprod := ((hYderiv t ht).sub_const q).mul hexp
    change HasDerivAt (fun r => (Y r - q) * Real.exp (c * r))
      ((Y' t + c * (Y t - q)) * Real.exp (c * t)) t
    exact hprod.congr_deriv (by ring)
  have hWanti : AntitoneOn W (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hWc
    · rw [interior_Icc]
      intro t ht
      exact (hWd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hWd t ht).deriv]
      have hrate : Y' t + c * (Y t - q) ≤ 0 := by
        dsimp [q]
        have hcq : c * (B / c) = B := by field_simp
        rw [mul_sub, hcq]
        linarith [hbound t ht]
      exact mul_nonpos_of_nonpos_of_nonneg hrate (Real.exp_pos _).le
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hWt : W t ≤ W a := hWanti ha ht ht.1
  have hexp : 0 < Real.exp (c * t) := Real.exp_pos _
  have hcore : Y t - q ≤ (Y a - q) * Real.exp (-c * (t - a)) := by
    have hWt' : (Y t - q) * Real.exp (c * t) ≤
        (Y a - q) * Real.exp (c * a) := by simpa [W] using hWt
    have hdiv : Y t - q ≤
        ((Y a - q) * Real.exp (c * a)) / Real.exp (c * t) :=
      (le_div_iff₀ hexp).2 hWt'
    calc
      Y t - q ≤ ((Y a - q) * Real.exp (c * a)) /
          Real.exp (c * t) := hdiv
      _ = (Y a - q) * Real.exp (-c * (t - a)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  dsimp [q] at hcore ⊢
  linarith

/-- Actual high-frequency energy comparison on a positive-time mild window.
The source constant uses only the common carrier bound `R` and common
half-generator bound `H` on that window. -/
theorem mild_highEnergy_le_damped_window
    (mu : ℝ) (hmu : 0 < mu) (a0 : WeightedLatticeBanach)
    (ha0 : LatticeDivergenceFree a0)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R H delta T N : ℝ}
    (hR : 0 ≤ R) (hdelta : 0 < delta)
    (hdeltaT : delta ≤ T) (hN : 0 < N)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage mu hmu a0 A hdiv s hs.1)
    (hhalf : ∀ s ∈ Icc delta T, Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖A s k‖)
    (hmoment : ∀ s ∈ Icc delta T,
      heatHalfGeneratorMoment (A s) ≤ H)
    (henergyContinuous : ContinuousOn
      (fun s => rawHighSpectralEnergy N (A s)) (Icc delta T)) :
    ∀ t ∈ Icc delta T,
      rawHighSpectralEnergy N (A t) ≤
        Real.exp (-(2 * mu * N ^ 2) * (t - delta)) *
            rawHighSpectralEnergy N (A delta) +
          (((8 / N) * R ^ 2 * H) / (2 * mu * N ^ 2)) *
            (1 - Real.exp (-(2 * mu * N ^ 2) * (t - delta))) := by
  let Y : ℝ → ℝ := fun s => rawHighSpectralEnergy N (A s)
  let Y' : ℝ → ℝ := fun s =>
    2 * rawHighFrequencyEnergyFlux N (A s) -
      2 * mu * rawHighSpectralDissipation N (A s)
  let c : ℝ := 2 * mu * N ^ 2
  let B : ℝ := (8 / N) * R ^ 2 * H
  have hc : 0 < c := by dsimp [c]; positivity
  have hderiv : ∀ s ∈ Ioo delta T, HasDerivAt Y (Y' s) s := by
    intro s hs
    have hs0T : s ∈ Ioo (0 : ℝ) T := ⟨hdelta.trans hs.1, hs.2⟩
    exact hasDerivAt_mild_highEnergy_flux_dissipation
      mu hmu a0 ha0 A hAc hdiv hR hN.le hs0T hbound hmild
  have hdiff : ∀ s ∈ Ioo delta T, Y' s ≤ -c * Y s + B := by
    intro s hs
    have hsclosed : s ∈ Icc delta T := ⟨hs.1.le, hs.2.le⟩
    have hgen := highEnergyGenerator_le_damping_add_halfGeneratorMoment
      mu N hmu.le hN (A s) (hdiv s) (hhalf s hsclosed)
    have hs0T : s ∈ Ioc (0 : ℝ) T := ⟨hdelta.trans hs.1, hs.2.le⟩
    have hnorm := hbound s hs0T
    have hnormsq : ‖A s‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (A s)]
    have hmoment0 := heatHalfGeneratorMoment_nonneg (A s)
    have hsource : (8 / N) * ‖A s‖ ^ 2 *
        heatHalfGeneratorMoment (A s) ≤ (8 / N) * R ^ 2 * H := by
      have hfactor : 0 ≤ 8 / N := by positivity
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hnormsq hfactor)
        (hmoment s hsclosed) hmoment0
        (mul_nonneg hfactor (sq_nonneg R))
    dsimp [Y, Y', c, B]
    exact hgen.trans (add_le_add_right hsource _)
  exact damped_affine_apriori_Icc hdeltaT hc henergyContinuous hderiv hdiff

/-- The same trajectory estimate with the forcing convolution bounded by its
equilibrium value.  The residual scale is `4 R² H / (mu N³)`. -/
theorem mild_highEnergy_le_decay_add_equilibrium
    (mu : ℝ) (hmu : 0 < mu) (a0 : WeightedLatticeBanach)
    (ha0 : LatticeDivergenceFree a0)
    (A : ℝ → WeightedLatticeBanach) (hAc : Continuous A)
    (hdiv : ∀ s, LatticeDivergenceFree (A s))
    {R H delta T N : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hdelta : 0 < delta)
    (hdeltaT : delta ≤ T) (hN : 0 < N)
    (hbound : ∀ s ∈ Ioc (0 : ℝ) T, ‖A s‖ ≤ R)
    (hmild : ∀ s (hs : s ∈ Icc (0 : ℝ) T),
      A s = criticalMildImage mu hmu a0 A hdiv s hs.1)
    (hhalf : ∀ s ∈ Icc delta T, Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖A s k‖)
    (hmoment : ∀ s ∈ Icc delta T,
      heatHalfGeneratorMoment (A s) ≤ H)
    (henergyContinuous : ContinuousOn
      (fun s => rawHighSpectralEnergy N (A s)) (Icc delta T)) :
    ∀ t ∈ Icc delta T,
      rawHighSpectralEnergy N (A t) ≤
        Real.exp (-(2 * mu * N ^ 2) * (t - delta)) *
            rawHighSpectralEnergy N (A delta) +
          4 * R ^ 2 * H / (mu * N ^ 3) := by
  intro t ht
  have h := mild_highEnergy_le_damped_window
    mu hmu a0 ha0 A hAc hdiv hR hdelta hdeltaT hN
      hbound hmild hhalf hmoment henergyContinuous t ht
  have hB : 0 ≤ ((8 / N) * R ^ 2 * H) / (2 * mu * N ^ 2) := by positivity
  have hsource :
      (((8 / N) * R ^ 2 * H) / (2 * mu * N ^ 2)) *
          (1 - Real.exp (-(2 * mu * N ^ 2) * (t - delta))) ≤
        ((8 / N) * R ^ 2 * H) / (2 * mu * N ^ 2) := by
    have hexp := Real.exp_pos (-(2 * mu * N ^ 2) * (t - delta))
    nlinarith
  have heq : ((8 / N) * R ^ 2 * H) / (2 * mu * N ^ 2) =
      4 * R ^ 2 * H / (mu * N ^ 3) := by field_simp; ring
  rw [heq] at h
  rw [heq] at hsource
  exact h.trans (add_le_add_right hsource _)

end Navier.Analysis.PhysicalPeriodicHighEnergyWindow
