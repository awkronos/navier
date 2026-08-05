import Navier.Problem

/-!
# Continuity of a parametrised integral from locally uniform decay

A family `F t : Space → ℝ` of nonnegative integrands has a continuous integral
`t ↦ ∫ F t x dx` as soon as two things hold: the integrand is continuous in `t`
for each fixed `x`, and *near every parameter value* the family obeys one common
algebraic decay bound `F t x ≤ K·(1 + ‖x‖)^{-4}`.

The exponent `4` is not cosmetic: `(1 + ‖x‖)^{-r}` is `volume`-integrable on
`Space = ℝ³` exactly when `r > 3 = Module.finrank ℝ Space`, so `4` is the
smallest integer exponent that works in three dimensions.  This is the same
`4 > 3` dimensional fact that underlies the Bessel weight in
`Navier.Analysis.BKMLogBootstrap`.

## Why locally uniform, and why this cannot be dropped

The decay hypothesis is genuinely load-bearing rather than bookkeeping.  Joint
smoothness of `(t, x) ↦ F t x` plus Schwartz decay of every individual slice
does **not** suffice: on `ℝ³` with `ψ(y) = exp(-‖y‖²)` the family
`v t x := t³·ψ(t²x)` is `C^∞` on all of `ℝ × ℝ³` with every slice Schwartz
(identically `0` at `t = 0`), yet `∫‖v t ·‖² = ‖ψ‖²_{L²}` for every `t ≠ 0`
while the value at `t = 0` is `0`.  Mass escapes to spatial infinity at exactly
the rate that preserves the `L²` norm, so no dominating function exists for that
family and the integral jumps.  Any consumer must therefore supply the decay
bound from genuine structure (for a Navier–Stokes solution, from the equation),
not from smoothness alone.

## Placement

Upstream of the whole analysis DAG: imports only `Navier.Problem` (for `Space`)
and Mathlib, and no other `Navier.Analysis` module, so any consumer can import
it without creating a cycle.

## Certified here (no sorry)

* `integrable_one_add_norm_inv_four` — `(1 + ‖x‖)^{-4}` is integrable on `ℝ³`.
* `continuousOn_integral_of_locallyUniformDecay` — the continuity transfer.

Reference: the dominated-convergence engine is Mathlib's
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`; the decay
weight is `MeasureTheory.integrable_one_add_norm` (the "Japanese bracket"
estimate).  See L. Hörmander, *The Analysis of Linear Partial Differential
Operators I*, 2nd ed. Springer 1990, §7.1, for the Schwartz-seminorm calculus
that produces such bounds.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Module

namespace Navier.Analysis.UniformDecayDominated

open Navier

/-- **The decay weight is integrable on `ℝ³` (certified, no sorry).**
`(1 + ‖x‖)^{-4}` is `volume`-integrable on `Space` because the exponent `4`
strictly exceeds `Module.finrank ℝ Space = 3`. -/
theorem integrable_one_add_norm_inv_four :
    Integrable (fun x : Space => (1 + ‖x‖) ^ (-4 : ℝ)) := by
  have hr4 : (finrank ℝ Space : ℝ) < 4 := by
    have h3 : finrank ℝ Space = 3 := by simp
    rw [h3]; norm_num
  exact integrable_one_add_norm (E := Space) (μ := volume) hr4

/-- **Continuity of a parametrised integral from locally uniform decay
(certified, no sorry).**

If every `F t` is measurable and nonnegative, if `t ↦ F t x` is continuous on
`s` for each fixed `x`, and if near every `t₀ ∈ s` the whole family is dominated
by one multiple of `(1 + ‖x‖)^{-4}`, then `t ↦ ∫ F t x dx` is continuous on `s`.

The bound is only required **locally in `t`**, which is what a Schwartz-seminorm
estimate along a flow actually delivers; a globally uniform bound is not needed.
Proof: at each `t₀` the local bound holds eventually along `𝓝[s] t₀`, the weight
is integrable by `integrable_one_add_norm_inv_four`, and dominated convergence
along that filter gives `ContinuousWithinAt`. -/
theorem continuousOn_integral_of_locallyUniformDecay
    {F : ℝ → Space → ℝ} {s : Set ℝ}
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable (F t) volume)
    (hnn : ∀ (t : ℝ) (x : Space), 0 ≤ F t x)
    (hcont : ∀ x : Space, ContinuousOn (fun t => F t x) s)
    (hdecay : ∀ t₀ ∈ s, ∃ r K : ℝ, 0 < r ∧
        ∀ t ∈ s ∩ Metric.ball t₀ r, ∀ x : Space,
          F t x ≤ K * (1 + ‖x‖) ^ (-4 : ℝ)) :
    ContinuousOn (fun t => ∫ x : Space, F t x) s := by
  intro t₀ ht₀
  obtain ⟨r, K, hr, hb⟩ := hdecay t₀ ht₀
  have hbound_int : Integrable (fun x : Space => K * (1 + ‖x‖) ^ (-4 : ℝ)) volume :=
    integrable_one_add_norm_inv_four.const_mul K
  have hmem : s ∩ Metric.ball t₀ r ∈ nhdsWithin t₀ s :=
    inter_mem_nhdsWithin s (Metric.ball_mem_nhds t₀ hr)
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun x : Space => K * (1 + ‖x‖) ^ (-4 : ℝ)) ?_ ?_ hbound_int ?_
  · exact Filter.Eventually.of_forall fun t => hmeas t
  · filter_upwards [hmem] with t ht
    filter_upwards with x
    rw [Real.norm_of_nonneg (hnn t x)]
    exact hb t ht x
  · filter_upwards with x
    exact hcont x t₀ ht₀

end Navier.Analysis.UniformDecayDominated

