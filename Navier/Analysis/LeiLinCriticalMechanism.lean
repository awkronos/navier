import Mathlib

/-!
# The two mechanisms the fixed-radius restart discards

`CriticalMildQuantitativeRestart` propagates the norm across a restart interval
with

  `‖u(t+r)‖ ≤ ‖u(t)‖ + (2√r/√ν)·R²`,

obtained from `‖e^{νrΔ}v‖ ≤ ‖v‖`.  The heat semigroup contributes **nothing**.
That is why `criticalMildBoundedHorizon ν M = (√ν/(8(M+1)²))²` scales like
`M⁻⁴`, why the restart horizons are summable, and why
`criticalMildBoundedHorizon_restart_budget` cannot preserve a fixed radius.  The
certified obstruction is a consequence of discarding dissipation, not of the
equation.

Two mechanisms are missing, and this module supplies both.

**1. The dissipation is scale-free when spent once, globally.**
`dissipation_integral_eq_one` : for every mode `k ≠ 0` and every `ν > 0`,

  `∫₀^∞ ν|k|² e^{-ν|k|² t} dt = 1`.

The constant is `1` — independent of `k` and of `ν`.  Integrating the
dissipation once over `[0,∞)` costs a scale-free constant; re-spending it on
every restart interval, as the fixed-radius scheme does, throws that away.  This
is the mechanism behind the `L¹` in time norm.

**2. The weight must be homogeneous of degree `-1`, not `1 + |k|`.**
`CriticalMildWeightedSpace.latticeModeWeight m = 1 + ‖ξ_m‖` is inhomogeneous,
so it is not scale-invariant and it does not cancel the derivative in
`∇·(u ⊗ u)`.  The homogeneous weight does, exactly:
`homogeneous_weight_cancels_derivative` records `|k|⁻¹ · |k| = 1`, while
`inhomogeneous_weight_loses_derivative` records that `|k| / (1 + |k|) < 1`
strictly, with no compensating gain, for every mode.

The pairing of the two is what makes the critical space work: `𝒳^{-1}` measured
in `L^∞` in time against `𝒳^{1}` measured in `L¹` in time, joined by the
Cauchy-Schwarz interpolation `‖u‖²_{𝒳⁰} ≤ ‖u‖_{𝒳^{-1}} · ‖u‖_{𝒳¹}`
(`interpolation_sq_le`), with `𝒳⁰` a Banach algebra under convolution.

Scope.  This module supplies the two mechanisms and the interpolation
inequality.  It does NOT construct the Lei-Lin solution, and it makes no
global-regularity claim.  Assembling these into
`‖u₀‖_{𝒳^{-1}} < ν ⟹ global mild solution` requires the Wiener-algebra
convolution estimate and the Duhamel fixed point in the `L^∞_t 𝒳^{-1} ∩
L¹_t 𝒳¹` norm, neither of which is built here.

Reference: Z. Lei and F. Lin, "Global mild solutions of Navier-Stokes
equations", Comm. Pure Appl. Math. 64 (2011) 1297-1304.  The space is
`𝒳^{-1} = {u : ∫ |ξ|^{-1} |û(ξ)| dξ < ∞}` and the theorem is that
`‖u₀‖_{𝒳^{-1}} < ν` gives a global mild solution in
`C([0,∞), 𝒳^{-1}) ∩ L¹(0,∞; 𝒳¹)`.  Mathlib inputs:
`intervalIntegral.integral_comp_mul_left_Ioi`, `integral_exp_neg_Ioi`,
`Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy-Schwarz).
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.LeiLinCriticalMechanism

open MeasureTheory intervalIntegral

/-! ## Mechanism 1: the scale-free dissipation integral -/

/-- **The dissipation integrates to one, for every mode and every viscosity.**

`∫₀^∞ a e^{-a t} dt = 1` for `a > 0`; with `a = ν|k|²` this is the statement
that the heat dissipation at mode `k`, integrated once over all of `[0,∞)`,
costs the scale-free constant `1`.

This is the gain the fixed-radius restart discards by bounding
`‖e^{νrΔ}v‖ ≤ ‖v‖`, and it is what the `L¹`-in-time norm collects. -/
theorem dissipation_integral_eq_one (a : ℝ) (ha : 0 < a) :
    ∫ t in Set.Ioi (0 : ℝ), a * Real.exp (-(a * t)) = 1 := by
  have hcomp := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) 0 ha
  simp only [mul_zero] at hcomp
  rw [MeasureTheory.integral_const_mul, hcomp, integral_exp_neg_Ioi]
  simp only [neg_zero, Real.exp_zero, smul_eq_mul, mul_one]
  field_simp

/-- The same statement at a concrete mode: with `a = ν * |k|²` for `ν > 0` and
`k ≠ 0`, the constant is `1`, independent of both. -/
theorem dissipation_integral_mode_eq_one (ν nk : ℝ) (hν : 0 < ν) (hk : 0 < nk) :
    ∫ t in Set.Ioi (0 : ℝ), (ν * nk ^ 2) * Real.exp (-((ν * nk ^ 2) * t)) = 1 :=
  dissipation_integral_eq_one _ (by positivity)

/-! ## Mechanism 2: the weight must be homogeneous -/

/-- **The homogeneous weight cancels the derivative exactly.**

The critical space `𝒳^{-1}` carries weight `|k|⁻¹`; the derivative in
`∇·(u ⊗ u)` contributes `|k|`.  Their product is exactly `1`, with no loss. -/
theorem homogeneous_weight_cancels_derivative (nk : ℝ) (hk : 0 < nk) :
    nk⁻¹ * nk = 1 := inv_mul_cancel₀ (ne_of_gt hk)

/-- **The inhomogeneous weight loses the derivative.**

`CriticalMildWeightedSpace.latticeModeWeight` is `1 + |k|`.  Against the
derivative factor `|k|` the ratio is `|k| / (1 + |k|)`, which is strictly less
than `1` at every mode, so the derivative is never absorbed and no gain is
available.  The weight is also not homogeneous, hence not scale-invariant, so
the norm it defines is not scale-critical. -/
theorem inhomogeneous_weight_loses_derivative (nk : ℝ) (hk : 0 ≤ nk) :
    nk / (1 + nk) < 1 := by
  rw [div_lt_one (by linarith)]
  linarith

/-- The inhomogeneous weight is not homogeneous: rescaling `k ↦ c·k` does not
rescale `1 + |k|` by `c`, except in the degenerate case.  Concrete witness at
`c = 2`, `|k| = 1`: `1 + 2 = 3 ≠ 4 = 2·(1 + 1)`. -/
theorem inhomogeneous_weight_not_homogeneous :
    (1 : ℝ) + 2 * 1 ≠ 2 * (1 + 1) := by norm_num

/-- The homogeneous weight IS homogeneous of degree `-1`: `(c·|k|)⁻¹ = c⁻¹|k|⁻¹`.
This is what makes the `𝒳^{-1}` norm scale-invariant, i.e. genuinely critical
for three-dimensional Navier-Stokes. -/
theorem homogeneous_weight_is_homogeneous (c nk : ℝ) (_hc : 0 < c) (_hk : 0 < nk) :
    (c * nk)⁻¹ = c⁻¹ * nk⁻¹ := mul_inv c nk

/-! ## The interpolation joining the two norms -/

/-- **Cauchy-Schwarz interpolation between the two critical norms.**

For finitely many modes with coefficients `f k ≥ 0` and weights `w k > 0`,

  `(∑ f)² ≤ (∑ w⁻¹ f) · (∑ w f)`,

which at `w k = |k|` is `‖u‖²_{𝒳⁰} ≤ ‖u‖_{𝒳^{-1}} · ‖u‖_{𝒳¹}` -- the estimate
that closes the Lei-Lin bilinear bound and produces the smallness threshold
`‖u₀‖_{𝒳^{-1}} < ν`.

Proof: `f = (w⁻¹ f)^{1/2} · (w f)^{1/2}` pointwise, then Cauchy-Schwarz. -/
theorem interpolation_sq_le {ι : Type*} (s : Finset ι) (f w : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, f i) ^ 2 ≤ (∑ i ∈ s, (w i)⁻¹ * f i) * (∑ i ∈ s, w i * f i) := by
  have hsplit : ∀ i ∈ s, f i = Real.sqrt ((w i)⁻¹ * f i) * Real.sqrt (w i * f i) := by
    intro i hi
    have hwi := hw i hi
    have hfi := hf i hi
    rw [← Real.sqrt_mul (by positivity)]
    have hprod : (w i)⁻¹ * f i * (w i * f i) = f i * f i := by
      field_simp
    rw [hprod, Real.sqrt_mul_self hfi]
  calc (∑ i ∈ s, f i) ^ 2
      = (∑ i ∈ s, Real.sqrt ((w i)⁻¹ * f i) * Real.sqrt (w i * f i)) ^ 2 := by
        rw [Finset.sum_congr rfl hsplit]
    _ ≤ (∑ i ∈ s, Real.sqrt ((w i)⁻¹ * f i) ^ 2) * (∑ i ∈ s, Real.sqrt (w i * f i) ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ = (∑ i ∈ s, (w i)⁻¹ * f i) * (∑ i ∈ s, w i * f i) := by
        congr 1
        · exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (by
            have := hw i hi; have := hf i hi; positivity)
        · exact Finset.sum_congr rfl fun i hi => Real.sq_sqrt (by
            have := hw i hi; have := hf i hi; positivity)

end Navier.Analysis.LeiLinCriticalMechanism

#print axioms Navier.Analysis.LeiLinCriticalMechanism.dissipation_integral_eq_one
#print axioms Navier.Analysis.LeiLinCriticalMechanism.dissipation_integral_mode_eq_one
#print axioms Navier.Analysis.LeiLinCriticalMechanism.inhomogeneous_weight_loses_derivative
#print axioms Navier.Analysis.LeiLinCriticalMechanism.homogeneous_weight_is_homogeneous
#print axioms Navier.Analysis.LeiLinCriticalMechanism.interpolation_sq_le
