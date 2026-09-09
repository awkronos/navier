import Navier.Analysis.PhysicalPeriodicHighTailFlux
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Positive-time moment control of the physical periodic energy tail

The physical high-frequency flux estimate is expressed through the moving
completed-carrier tail.  On the half-generator domain, that tail has an
explicit inverse-cutoff bound.  Combining the two statements gives a
damped high-energy generator inequality whose source is suppressed by one
additional power of the cutoff.

The final scalar lemma records the exact comparison for a damped differential
inequality.  Once the evolving high-energy series has been differentiated,
it turns local uniform carrier and half-generator bounds into a quantitative
high-frequency energy estimate.  These bounds are presently available on
compact positive-time windows.  A datum-dependent choice uniform over every
future window remains the global-control obligation.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.PhysicalPeriodicTailMomentControl

open Set Navier
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.PeriodicGlobalCriticalControl
open Navier.Analysis.PhysicalPeriodicHighTailFlux

/-- Above a positive cutoff, the completed-carrier tail is controlled by the
half-generator moment with one inverse power of the cutoff. -/
theorem carrierHighTail_le_inv_mul_halfGeneratorMoment
    (N : ℝ) (hN : 0 < N) (u : WeightedLatticeBanach)
    (hhalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :
    carrierHighTail N u ≤ N⁻¹ * heatHalfGeneratorMoment u := by
  let f : LatticeMode → ℝ := fun k =>
    if N ≤ latticeModeSize k then ‖u k‖ else 0
  let g : LatticeMode → ℝ := fun k =>
    N⁻¹ * (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖)
  have hf : Summable f := summable_carrierHighTail N u
  have hg : Summable g := hhalf.mul_left N⁻¹
  have hpoint : ∀ k, f k ≤ g k := by
    intro k
    dsimp [f, g]
    split_ifs with hk
    · have hsize : N ≤ ‖complexFrequency (latticeFrequency k)‖ := by
        simpa [latticeModeSize] using hk
      have hnorm : 0 ≤ ‖u k‖ := norm_nonneg _
      have hinv : 0 < N⁻¹ := inv_pos.mpr hN
      have hmul := mul_le_mul_of_nonneg_right hsize hnorm
      calc
        ‖u k‖ = N⁻¹ * (N * ‖u k‖) := by field_simp
        _ ≤ N⁻¹ *
            (‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :=
          mul_le_mul_of_nonneg_left hmul hinv.le
    · exact mul_nonneg (inv_nonneg.mpr hN.le)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  change (∑' k, f k) ≤ N⁻¹ * heatHalfGeneratorMoment u
  calc
    (∑' k, f k) ≤ ∑' k, g k := hf.tsum_le_tsum hpoint hg
    _ = N⁻¹ * heatHalfGeneratorMoment u := by
      rw [tsum_mul_left]
      rfl

/-- At the half-cutoff appearing in the nonlinear flux split, the same
estimate has the explicit factor `2 / N`. -/
theorem carrierHighTail_half_le_two_div_mul_halfGeneratorMoment
    (N : ℝ) (hN : 0 < N) (u : WeightedLatticeBanach)
    (hhalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :
    carrierHighTail (N / 2) u ≤
      (2 / N) * heatHalfGeneratorMoment u := by
  have hNh : 0 < N / 2 := div_pos hN (by norm_num)
  have h := carrierHighTail_le_inv_mul_halfGeneratorMoment (N / 2) hNh u hhalf
  convert h using 1
  field_simp

/-- The moving-tail generator estimate after using positive-time
half-generator regularity.  The source is `O(N⁻¹)` for fixed current norm
and moment; no uniform-in-time bound for those two quantities is assumed. -/
theorem highEnergyGenerator_le_damping_add_halfGeneratorMoment
    (mu N : ℝ) (hmu : 0 ≤ mu) (hN : 0 < N)
    (u : WeightedLatticeBanach) (hdiv : LatticeDivergenceFree u)
    (hhalf : Summable fun k : LatticeMode =>
      ‖complexFrequency (latticeFrequency k)‖ * ‖u k‖) :
    2 * rawHighFrequencyEnergyFlux N u -
        2 * mu * rawHighSpectralDissipation N u ≤
      -(2 * mu * N ^ 2) * rawHighSpectralEnergy N u +
        (8 / N) * ‖u‖ ^ 2 * heatHalfGeneratorMoment u := by
  have hgen := highEnergyGenerator_le_damping_add_movingTail
    mu N hmu hN.le u hdiv
  have htail := carrierHighTail_half_le_two_div_mul_halfGeneratorMoment
    N hN u hhalf
  have hnorm : 0 ≤ 4 * ‖u‖ ^ 2 := by positivity
  have hsource := mul_le_mul_of_nonneg_left htail hnorm
  calc
    2 * rawHighFrequencyEnergyFlux N u -
          2 * mu * rawHighSpectralDissipation N u ≤
        -(2 * mu * N ^ 2) * rawHighSpectralEnergy N u +
          4 * ‖u‖ ^ 2 * carrierHighTail (N / 2) u := hgen
    _ ≤ -(2 * mu * N ^ 2) * rawHighSpectralEnergy N u +
          4 * ‖u‖ ^ 2 *
            ((2 / N) * heatHalfGeneratorMoment u) :=
      add_le_add_right hsource _
    _ = -(2 * mu * N ^ 2) * rawHighSpectralEnergy N u +
          (8 / N) * ‖u‖ ^ 2 * heatHalfGeneratorMoment u := by ring

/-! ## Scalar damped comparison -/

/-- Exact constant-source comparison for a damped differential inequality.
This formulation does not discard the negative high-frequency dissipation. -/
theorem damped_affine_apriori
    {Y Y' : ℝ → ℝ} {c B T : ℝ}
    (hT : 0 ≤ T) (hc : 0 < c)
    (hYc : ContinuousOn Y (Icc 0 T))
    (hYderiv : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, Y' t ≤ -c * Y t + B) :
    ∀ t ∈ Icc 0 T,
      Y t ≤ Real.exp (-c * t) * Y 0 +
        (B / c) * (1 - Real.exp (-c * t)) := by
  let q : ℝ := B / c
  let W : ℝ → ℝ := fun t => (Y t - q) * Real.exp (c * t)
  have hWc : ContinuousOn W (Icc 0 T) := by
    exact hYc.sub continuousOn_const |>.mul
      ((continuousOn_const.mul continuousOn_id).rexp)
  have hWd : ∀ t ∈ Ioo 0 T,
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
  have hWanti : AntitoneOn W (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hWc
    · rw [interior_Icc]
      intro t ht
      exact (hWd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hWd t ht).deriv]
      have hrate : Y' t + c * (Y t - q) ≤ 0 := by
        dsimp [q]
        have hc0 : c ≠ 0 := ne_of_gt hc
        have hcq : c * (B / c) = B := by field_simp
        rw [mul_sub, hcq]
        linarith [hbound t ht]
      exact mul_nonpos_of_nonpos_of_nonneg hrate (Real.exp_pos _).le
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hWt : W t ≤ W 0 := hWanti h0 ht ht.1
  have hexp : 0 < Real.exp (c * t) := Real.exp_pos _
  have hcore : Y t - q ≤ (Y 0 - q) * Real.exp (-c * t) := by
    have hWt' : (Y t - q) * Real.exp (c * t) ≤ Y 0 - q := by
      simpa [W] using hWt
    have hdiv : Y t - q ≤ (Y 0 - q) / Real.exp (c * t) :=
      (le_div_iff₀ hexp).2 hWt'
    calc
      Y t - q ≤ (Y 0 - q) / Real.exp (c * t) := hdiv
      _ = (Y 0 - q) * Real.exp (-c * t) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 2
        ring
  dsimp [q] at hcore ⊢
  linarith

/-- A simpler equilibrium form of the damped comparison when the source and
initial energy are nonnegative. -/
theorem damped_affine_apriori_le_equilibrium
    {Y Y' : ℝ → ℝ} {c B T : ℝ}
    (hT : 0 ≤ T) (hc : 0 < c) (hB : 0 ≤ B)
    (hYc : ContinuousOn Y (Icc 0 T))
    (hYderiv : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, Y' t ≤ -c * Y t + B) :
    ∀ t ∈ Icc 0 T,
      Y t ≤ Real.exp (-c * t) * Y 0 + B / c := by
  intro t ht
  have h := damped_affine_apriori hT hc hYc hYderiv hbound t ht
  have ht0 : 0 ≤ t := ht.1
  have hexp : Real.exp (-c * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hq : 0 ≤ B / c := div_nonneg hB hc.le
  have hsource : (B / c) * (1 - Real.exp (-c * t)) ≤ B / c := by
    nlinarith [Real.exp_pos (-c * t)]
  exact h.trans (add_le_add_right hsource (Real.exp (-c * t) * Y 0))

end Navier.Analysis.PhysicalPeriodicTailMomentControl
