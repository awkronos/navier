import Navier.Analysis.LeiLinPositiveRestartBootstrap

/-!
# Fractional-integral route for the positive restart

The critical `L¹` endpoint does not control multiplication by
`(t-s)⁻¹ᐟ²`.  This module replaces that false step by the sharp weighted
`L²`/Hardy route.  A backward weight `(t-s)⁻ᵝ`, with any `β > 0`, supplies
both ordinary time-integrability of the graph moment and integrability after
multiplication by the Volterra kernel.

The unweighted `β = 0` endpoint remains unavailable: its kernel square is
exactly the nonintegrable inverse-time function already isolated in
`LeiLinTimeMixed`.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.LeiLinPositiveRestartFractional

open Filter
open MeasureTheory
open Set
open Navier
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ComplexFrequencyHeatLeray
open Navier.Analysis.CriticalMildDuhamelBochner
open Navier.Analysis.CriticalMildHeatTimeKernel
open Navier.Analysis.CriticalMildHeatFlowLinear
open Navier.Analysis.CriticalMildRestart
open Navier.Analysis.CriticalMildSelfMap
open Navier.Analysis.CriticalMildSeries
open Navier.Analysis.CriticalMildWeightedBanach
open Navier.Analysis.LeiLinCoerciveTerminal
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinTimeMixed
open Navier.Analysis.LeiLinPositiveRestartBootstrap

/-- Nonnegative backward time, used to make the Hardy weights globally
nonnegative while agreeing with `t-s` on `s ≤ t`. -/
def backwardTime (t s : ℝ) : ℝ := max (t - s) 0

/-- Local integrability of every real power strictly above the `-1`
threshold. -/
theorem intervalIntegrable_rpow_zero {δ r : ℝ}
    (hδ : 0 ≤ δ) (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => x ^ r) volume 0 δ := by
  have hc : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) ^ (r : ℂ)) volume 0 δ := by
    apply intervalIntegral.intervalIntegrable_cpow'
    simpa using hr
  have hcOn : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (r : ℂ)) (Ioc 0 δ) volume := by
    simpa [uIoc_of_le hδ] using intervalIntegrable_iff.mp hc
  have hreOn : IntegrableOn
      (fun x : ℝ => ((x : ℂ) ^ (r : ℂ)).re) (Ioc 0 δ) volume :=
    hcOn.re
  apply intervalIntegrable_iff.mpr
  simpa [uIoc_of_le hδ] using
    hreOn.congr_fun (fun x hx => by
      have hx0 : 0 ≤ x := hx.1.le
      have hcx := Complex.ofReal_cpow hx0 r
      exact (congrArg Complex.re hcx).symm) measurableSet_Ioc

/-- Square-root factorization underlying the weighted Hardy estimate. -/
theorem sqrt_backwardWeight_factor
    {x M α β : ℝ} (hx : 0 < x) (hM : 0 ≤ M) :
    Real.sqrt (x ^ (2 * α + β)) *
        Real.sqrt (x ^ (-β) * M ^ 2) =
      x ^ α * M := by
  have hxpow : 0 ≤ x ^ (-β) := Real.rpow_nonneg hx.le _
  rw [Real.sqrt_mul hxpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hM]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le]
  rw [← mul_assoc, ← Real.rpow_add hx]
  congr 2
  ring

/-- Weighted `L²` control transports to an `L¹` fractional moment whenever
the complementary power is above the local-integrability threshold. -/
theorem intervalIntegrable_backwardRpow_mul_of_weightedL2
    {a t α β : ℝ} {M : ℝ → ℝ}
    (hat : a ≤ t) (hthreshold : -1 < 2 * α + β)
    (hM0 : ∀ s ∈ Ioc a t, 0 ≤ M s)
    (henergy : IntervalIntegrable
      (fun s => backwardTime t s ^ (-β) * M s ^ 2) volume a t) :
    IntervalIntegrable
      (fun s => backwardTime t s ^ α * M s) volume a t := by
  have hpow0 := intervalIntegrable_rpow_zero
    (δ := t - a) (r := 2 * α + β) (sub_nonneg.mpr hat) hthreshold
  have hraw : IntervalIntegrable
      (fun s => (t - s) ^ (2 * α + β)) volume a t := by
    have h := (hpow0.comp_sub_left t).symm
    convert h using 1 <;> ring
  have hleft : IntervalIntegrable
      (fun s => backwardTime t s ^ (2 * α + β)) volume a t := by
    apply hraw.congr
    intro s hs
    have hsIoc : s ∈ Ioc a t := by simpa [uIoc_of_le hat] using hs
    have hst : s ≤ t := hsIoc.2
    change (t - s) ^ (2 * α + β) = max (t - s) 0 ^ (2 * α + β)
    rw [max_eq_left (sub_nonneg.mpr hst)]
  have hleftOn : IntegrableOn
      (fun s => backwardTime t s ^ (2 * α + β)) (Ioc a t) volume := by
    simpa [uIoc_of_le hat] using intervalIntegrable_iff.mp hleft
  have hrightOn : IntegrableOn
      (fun s => backwardTime t s ^ (-β) * M s ^ 2) (Ioc a t) volume := by
    simpa [uIoc_of_le hat] using intervalIntegrable_iff.mp henergy
  have hprod := integrableOn_sqrt_mul
    (fun s => Real.rpow_nonneg (le_max_right _ _) (2 * α + β))
    (fun s => mul_nonneg
      (Real.rpow_nonneg (le_max_right _ _) (-β)) (sq_nonneg (M s)))
    hleftOn hrightOn
  have hne : ∀ᵐ s : ℝ ∂volume.restrict (Ioc a t), s ≠ t := by
    rw [ae_iff]
    simp
  have heq :
      (fun s => Real.sqrt (backwardTime t s ^ (2 * α + β)) *
        Real.sqrt (backwardTime t s ^ (-β) * M s ^ 2)) =ᵐ[
          volume.restrict (Ioc a t)]
      (fun s => backwardTime t s ^ α * M s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with s hs heq
    have hst : s < t := lt_of_le_of_ne hs.2 heq
    change Real.sqrt (max (t - s) 0 ^ (2 * α + β)) *
        Real.sqrt (max (t - s) 0 ^ (-β) * M s ^ 2) =
      max (t - s) 0 ^ α * M s
    rw [max_eq_left (sub_nonneg.mpr hst.le)]
    exact sqrt_backwardWeight_factor (sub_pos.mpr hst) (hM0 s hs)
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hat]
  exact hprod.congr heq

/-- **Sharp fractional-integral route.**  Every positive Hardy weight exponent
places the inverse-square-root Volterra factor below its critical endpoint. -/
theorem intervalIntegrable_inverseSqrtTime_mul_of_weightedL2
    {a t β : ℝ} {M : ℝ → ℝ}
    (hat : a ≤ t) (hβ : 0 < β)
    (hM0 : ∀ s ∈ Ioc a t, 0 ≤ M s)
    (henergy : IntervalIntegrable
      (fun s => backwardTime t s ^ (-β) * M s ^ 2) volume a t) :
    IntervalIntegrable
      (fun s => inverseSqrtTime (t - s) * M s) volume a t := by
  have h := intervalIntegrable_backwardRpow_mul_of_weightedL2
    (α := -(1 / 2 : ℝ)) hat (by linarith) hM0 henergy
  apply h.congr
  intro s hs
  have hsIoc : s ∈ Ioc a t := by simpa [uIoc_of_le hat] using hs
  have hst : s ≤ t := hsIoc.2
  change max (t - s) 0 ^ (-(1 / 2 : ℝ)) * M s =
    (t - s) ^ (-(1 / 2 : ℝ)) * M s
  rw [max_eq_left (sub_nonneg.mpr hst)]

/-- The same weighted `L²` datum supplies ordinary `L¹` control of the graph
moment, so it strictly strengthens the former `hmoment` premise. -/
theorem intervalIntegrable_of_backwardWeightedL2
    {a t β : ℝ} {M : ℝ → ℝ}
    (hat : a ≤ t) (hβ : 0 < β)
    (hM0 : ∀ s ∈ Ioc a t, 0 ≤ M s)
    (henergy : IntervalIntegrable
      (fun s => backwardTime t s ^ (-β) * M s ^ 2) volume a t) :
    IntervalIntegrable M volume a t := by
  have h := intervalIntegrable_backwardRpow_mul_of_weightedL2
    (α := 0) hat (by linarith) hM0 henergy
  apply h.congr
  intro s hs
  simp [Real.rpow_zero]

/-- The unweighted `L²` Hölder route is exactly critical: the square of the
inverse-square-root kernel is not interval-integrable. -/
theorem not_intervalIntegrable_inverseSqrtTime_sq :
    ¬ IntervalIntegrable
      (fun τ => inverseSqrtTime τ * inverseSqrtTime τ) volume 0 1 :=
  inverseSqrtTime_L1_product_endpoint_obstruction.2

/-- **Terminal consumer sharpened to a weighted Hardy premise.**

The weighted `L²` graph-moment energy now constructs the former ordinary
`hmoment` input.  It also gives the endpoint-weighted integrability required
to justify the literal Duhamel estimate at `T`; the pointwise split-Volterra
inequality remains explicit because the completed fixed-point API does not
yet expose a finite-mode energy identity from which to derive it. -/
theorem positiveRestart_graph_X2_and_terminal_X1_of_weightedHardy
    (ν : ℝ) (hν : 0 < ν) (u₀ : WeightedLatticeBanach)
    (u : ℝ → WeightedLatticeBanach) (huc : Continuous u)
    (hu : ∀ s, LatticeDivergenceFree (u s))
    {R T δ A β : ℝ} (hR : 0 ≤ R)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hδT : δ ≤ T) (hβ : 0 < β)
    (huR : ∀ s ∈ Ioc (0 : ℝ) T, ‖u s‖ ≤ R)
    (hmild : ∀ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T),
      u s = criticalMildImage ν hν u₀ u hu s hs.1)
    (hhalf : ∀ s ∈ Icc (T - δ) T, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖)
    (henergy : IntervalIntegrable
      (fun s => backwardTime T s ^ (-β) *
        heatHalfGeneratorMoment (u s) ^ 2) volume (T - δ) T)
    (hintX1 : IntervalIntegrable
      (fun s => normX1 latticeModeSize (weightedAmplitude (u s)))
      volume (T - δ) T)
    (hmassX1 : (∫ s in (T - δ)..T,
      normX1 latticeModeSize (weightedAmplitude (u s))) ≤ A)
    (hsmall : (4 * R / Real.sqrt ν) * Real.sqrt δ < 1)
    (hpoint : ∀ t ∈ Icc (T - δ) T,
      heatHalfGeneratorMoment (u t) ≤
        restartFreeHalfMomentMajorant ν (T - δ) (u (T - δ)) t +
          (2 * (Real.sqrt ν)⁻¹ * R) *
            truncatedVolterraConvolution (T - δ) T
              (fun s => heatHalfGeneratorMoment (u s)) t) :
    (∀ r (hr : r ∈ Icc (0 : ℝ) δ),
      criticalMildRestartImage ν hν u hu (T - δ) r hr.1 =
        u (T - δ + r)) ∧
    (∀ s ∈ Icc (T - δ) T, Summable fun m : LatticeMode =>
      ‖complexFrequency (latticeFrequency m)‖ * ‖u s m‖) ∧
    IntervalIntegrable
      (fun s => normX2 latticeModeSize (weightedAmplitude (u s)))
      volume (T - δ) T ∧
    (∫ s in (T - δ)..T,
      normX2 latticeModeSize (weightedAmplitude (u s))) ≤
        (2 * Real.sqrt δ / Real.sqrt ν * ‖u (T - δ)‖) /
          (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ) ∧
    normX1 latticeModeSize (weightedAmplitude (u T)) ≤
      (A + (Real.sqrt ν *
          ((2 * Real.sqrt δ / Real.sqrt ν * ‖u (T - δ)‖) /
            (1 - (4 * R / Real.sqrt ν) * Real.sqrt δ))) *
          Real.sqrt δ) / δ +
        (2 * R ^ 2 / Real.sqrt ν) * Real.sqrt δ := by
  have hat : T - δ ≤ T := sub_le_self T hδ.le
  have hM0 : ∀ s ∈ Ioc (T - δ) T,
      0 ≤ heatHalfGeneratorMoment (u s) := by
    intro s _hs
    exact heatHalfGeneratorMoment_nonneg (u s)
  have hmoment := intervalIntegrable_of_backwardWeightedL2
    hat hβ hM0 henergy
  exact positiveRestart_graph_X2_and_terminal_X1_of_literalSplitVolterra
    ν hν u₀ u huc hu hR hT hδ hδT huR hmild hhalf hmoment
    hintX1 hmassX1 hsmall hpoint

end Navier.Analysis.LeiLinPositiveRestartFractional

#print axioms Navier.Analysis.LeiLinPositiveRestartFractional.intervalIntegrable_rpow_zero
#print axioms Navier.Analysis.LeiLinPositiveRestartFractional.intervalIntegrable_inverseSqrtTime_mul_of_weightedL2
#print axioms Navier.Analysis.LeiLinPositiveRestartFractional.intervalIntegrable_of_backwardWeightedL2
#print axioms Navier.Analysis.LeiLinPositiveRestartFractional.not_intervalIntegrable_inverseSqrtTime_sq
#print axioms Navier.Analysis.LeiLinPositiveRestartFractional.positiveRestart_graph_X2_and_terminal_X1_of_weightedHardy
