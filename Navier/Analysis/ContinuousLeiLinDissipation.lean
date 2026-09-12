import Navier.Analysis.ContinuousLeiLinSpace
import Navier.Analysis.ContinuousLeiLinTimeDuhamel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous Lei--Lin dissipation budgets on `R³`

The lattice small-data theorem `CriticalMildSmallDataGlobal.smallDataGlobalMild`
closes its fixed point on two budget facts: the free term decays
(`exp (-ν*t) * ‖a‖`) and the time-integrated dissipation costs exactly
`ν⁻¹` (`(3 * ν⁻¹) * (2 * ‖a‖)²`).  This module supplies the exact
continuous-space analogues on the literal Fourier carrier of
`ContinuousLeiLinSpace`.  It is the missing input named in the header of
`ContinuousLeiLinTimeDuhamel` ("a further `X⁻¹/X¹` mixed estimate needs a
continuous weighted interpolation and Bochner/Fubini bridge").

Contents:

* `normXm1_heatMode_le` — the heat multiplier is a contraction of the
  homogeneous `X⁻¹` mass.
* `tendsto_normXm1_heatMode` — the free term tends to `0` at large time
  (dominated convergence).  This is the honest replacement for the lattice's
  exponential decay `exp (-ν*t)`: the continuum carrier has **no spectral
  gap** at `ξ = 0`, so no uniform exponential rate survives; the limit
  statement itself is exactly what the fixed point consumes.
* `integral_normX1_heatMode_le` — the main budget:
  `∫₀ᵗ ‖e^{ν s Δ} g‖_{X¹} ≤ ν⁻¹ * ‖g‖_{X⁻¹}`.  The constant `ν⁻¹` is the
  literal continuous analogue of the lattice's `3 * ν⁻¹` factor (the `3`
  there is the coordinate aggregation of the bilinear, which re-enters only
  at the fixed-point assembly, not in the linear budget).
* Vector aggregation over the three velocity coordinates:
  `coordinateXm1Mass_heatVec_le` and
  `integral_coordinateX1Mass_heatVec_le` — the same budgets summed over
  coordinates, in the exact mass shape consumed by the bilinear estimates of
  `ContinuousLeiLinTimeDuhamel`.
* Bochner/Fubini bridge `normXm1_setIntegral_le` — the weighted `X⁻¹` mass
  passes through a time integral up to inequality (Minkowski for Bochner
  integrals plus Fubini), and its corollary
  `normXm1_continuousDuhamel_le` — the Duhamel term has finite `X⁻¹` mass
  bounded by the time integral of the source masses.

All budgets are unconditional measure-theoretic facts on the continuous
carrier; no lattice, no Dirac comb, and no sampling step is used (the
sampling route is separately kernel-falsified in
`ContinuousLeiLinTimeDuhamel.not_pointwise_controlled_by_coordinateXm1X1`).

Reference: Z. Lei and F. Lin, "Global mild solutions of Navier--Stokes
equations", Comm. Pure Appl. Math. 64 (2011), Sec. 2--3 (the
`X^{-1}` dissipation identity); H. Fujita and T. Kato, Arch. Ration. Mech.
Anal. 60 (1975) for the small-data scheme whose constant this file supplies.
Mathlib inputs: `integral_prod`, `integral_prod_symm`, `integrable_prod_iff`,
`intervalIntegral.integral_comp_mul_left`, `integral_exp`,
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinDissipation

open MeasureTheory Set Filter
open scoped Topology BigOperators
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel

/-!
## Scalar interval identities for the heat multiplier
-/

private theorem exp_pos_heat (a : ℝ) : 0 < Real.exp (-a) := by
  rw [Real.exp_neg]
  exact inv_pos.mpr (Real.exp_pos _)

/-- `∫₀ᵗ exp(-c s) = (1 - exp(-c t)) / c` for `c > 0`, `0 ≤ t`, as a set
integral over `Icc`. -/
private theorem integral_exp_neg_Icc (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    (∫ s in Icc (0 : ℝ) t, Real.exp (-(c * s))) = c⁻¹ * (1 - Real.exp (-(c * t))) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  rw [show (fun s : ℝ => Real.exp (-(c * s))) = fun s => Real.exp ((-c) * s) by
    ext s; rw [neg_mul]]
  rw [intervalIntegral.integral_comp_mul_left (hc := neg_ne_zero.mpr hc.ne')]
  rw [integral_exp]
  simp only [neg_mul, mul_zero, smul_eq_mul, Real.exp_zero, inv_neg]
  ring

/-- The gap form: `1 - exp(-c t) = c * ∫₀ᵗ exp(-c s)`. -/
private theorem one_sub_exp_eq (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    1 - Real.exp (-(c * t)) = c * ∫ s in Icc (0 : ℝ) t, Real.exp (-(c * s)) := by
  rw [integral_exp_neg_Icc c t hc ht]
  field_simp [hc.ne']

/-!
## Pointwise heat facts
-/

/-- The heat multiplier evaluated pointwise on the complex carrier. -/
private theorem norm_heatMode (ν t : ℝ) (f : ES → ℂ) (ξ : ES) :
    ‖heatMode ν t f ξ‖ = Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖f ξ‖ := by
  show ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * f ξ‖ = _
  rw [Complex.norm_mul, Complex.norm_real]
  exact congrArg (fun e : ℝ => e * ‖f ξ‖) (Real.norm_of_nonneg (exp_pos_heat _).le)

/-- The multiplier never exceeds one on forward time. -/
private theorem exp_le_one_heat (ν t ξ : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    Real.exp (-(ν * ξ ^ 2 * t)) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ξ, mul_nonneg hν.le ht])

/-- The weighted heat integrand factors through the multiplier. -/
private theorem heat_integrand (ν t : ℝ) (g : ES → ℂ) (ξ : ES) :
    ‖ξ‖⁻¹ * ‖heatMode ν t g ξ‖ = Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖g ξ‖) := by
  rw [norm_heatMode, ← mul_assoc, mul_comm (‖ξ‖⁻¹), ← mul_assoc]

private theorem weight_nonneg (ξ : ES) : 0 ≤ (‖ξ‖⁻¹ : ℝ) := inv_nonneg.mpr (norm_nonneg _)

/-- The heat multiplier is a.e. strongly measurable in the frequency variable. -/
private theorem aesm_exp_heat (ν t : ℝ) :
    AEStronglyMeasurable (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) :=
  ((Real.continuous_exp.comp
      (Continuous.neg
        (Continuous.mul (Continuous.mul continuous_const (continuous_norm.pow 2))
          continuous_const))).measurable).aestronglyMeasurable

/-!
## Contraction of the `X⁻¹` mass
-/

/-- The homogeneous `X⁻¹` mass is non-increasing along the heat flow. -/
theorem normXm1_heatMode_le (g : ES → ℂ) (hg : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    normXm1 (heatMode ν t g) ≤ normXm1 g := by
  unfold normXm1
  have hmaj : ∀ ξ, ‖ξ‖⁻¹ * ‖heatMode ν t g ξ‖ ≤ ‖ξ‖⁻¹ * ‖g ξ‖ := by
    intro ξ
    rw [heat_integrand]
    have hw : 0 ≤ ‖ξ‖⁻¹ * ‖g ξ‖ := mul_nonneg (weight_nonneg ξ) (norm_nonneg _)
    have := exp_le_one_heat ν t ‖ξ‖ hν ht
    nlinarith
  have hn : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖) := hg.aestronglyMeasurable
  have hexp : AEStronglyMeasurable (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) :=
    aesm_exp_heat ν t
  have hfi : Integrable (fun ξ : ES =>
      Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖g ξ‖)) := by
    refine ⟨hexp.mul hn, HasFiniteIntegral.mono hg.hasFiniteIntegral (Eventually.of_forall fun ξ => ?_)⟩
    rw [Real.norm_of_nonneg (mul_nonneg (exp_pos_heat _).le
        (mul_nonneg (weight_nonneg ξ) (norm_nonneg _))),
      Real.norm_of_nonneg (mul_nonneg (weight_nonneg ξ) (norm_nonneg _)),
      ← heat_integrand ν t g ξ]
    exact hmaj ξ
  have hfi2 : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖heatMode ν t g ξ‖) :=
    hfi.congr (Eventually.of_forall fun ξ => (heat_integrand ν t g ξ).symm)
  exact integral_mono hfi2 hg hmaj

/-!
## No-gap decay of the free `X⁻¹` mass
-/

/-- Honest continuum replacement of the lattice free-term decay
`exp (-ν*t) * ‖a‖`: the heat flow tends to `0` in the homogeneous `X⁻¹` mass.
The carrier has **no spectral gap** at `ξ = 0`, so no uniform exponential rate
survives; the limit statement is exactly what the fixed-point scheme consumes.
The proof is dominated convergence against the `X⁻¹` majorant itself. -/
theorem tendsto_normXm1_heatMode (g : ES → ℂ)
    (hg : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖)) (ν : ℝ) (hν : 0 < ν) :
    Tendsto (fun t => normXm1 (heatMode ν t g)) atTop (𝓝 0) := by
  have hF : (fun t : ℝ => normXm1 (heatMode ν t g)) =
      fun t => ∫ ξ : ES, Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖g ξ‖) := by
    funext t
    show (∫ ξ : ES, ‖ξ‖⁻¹ * ‖heatMode ν t g ξ‖) = _
    rw [integral_congr_ae (Eventually.of_forall fun ξ => heat_integrand ν t g ξ)]
  have hw : ∀ ξ, 0 ≤ ‖ξ‖⁻¹ * ‖g ξ‖ :=
    fun ξ => mul_nonneg (weight_nonneg ξ) (norm_nonneg _)
  rw [hF]
  have hmeasF : ∀ᶠ t in atTop,
      AEStronglyMeasurable (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖g ξ‖)) :=
    eventually_atTop.mpr ⟨0, fun t _ => (aesm_exp_heat ν t).mul hg.aestronglyMeasurable⟩
  have hbndF : ∀ᶠ t in atTop, ∀ᵐ ξ ∂(volume : Measure ES),
      ‖Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖g ξ‖)‖ ≤ ‖ξ‖⁻¹ * ‖g ξ‖ :=
    eventually_atTop.mpr ⟨0, fun t ht => Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (mul_nonneg (exp_pos_heat _).le (hw ξ))]
      have := exp_le_one_heat ν t ‖ξ‖ hν ht
      nlinarith [hw ξ]⟩
  have hlimF : ∀ᵐ ξ ∂(volume : Measure ES),
      Tendsto (fun t : ℝ => Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖g ξ‖)) atTop (𝓝 0) :=
    Eventually.of_forall fun ξ => by
      by_cases hx : (ξ : ES) = 0
      · have : (fun t : ℝ =>
            Real.exp (-(ν * ‖(0 : ES)‖ ^ 2 * t)) * (‖(0 : ES)‖⁻¹ * ‖g 0‖)) = fun _ => 0 := by
          funext t; simp
        subst hx
        rw [this]
        exact tendsto_const_nhds
      · have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hx
        have hc : 0 < ν * ‖ξ‖ ^ 2 := mul_pos hν (pow_pos hr 2)
        have hmul : Tendsto (fun t : ℝ => ν * ‖ξ‖ ^ 2 * t) atTop atTop := by
          convert Filter.Tendsto.atTop_mul_const hc (tendsto_id (x := atTop)) using 1
          ext t
          simp only [id_eq]
          ring
        have he0 : Tendsto (fun t : ℝ => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) atTop (𝓝 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
        simpa using he0.mul tendsto_const_nhds
  simpa using tendsto_integral_filter_of_dominated_convergence
      (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖) hmeasF hbndF hg hlimF

/-!
## The main linear budget: `∫₀ᵗ ‖e^{ν s Δ} g‖_{X¹} ≤ ν⁻¹ * ‖g‖_{X⁻¹}`
-/

/-- Scalar algebra step of the budget: for `r > 0`,
`r * q * ((ν r²)⁻¹ * (1 - exp (-(ν r² t)))) ≤ ν⁻¹ * (r⁻¹ * q)`. -/
private theorem heat_budget_pointwise (ν r q t : ℝ) (hν : 0 < ν) (_ht : 0 ≤ t)
    (hr : 0 < r) (hq : 0 ≤ q) :
    r * q * ((ν * r ^ 2)⁻¹ * (1 - Real.exp (-(ν * r ^ 2 * t)))) ≤ ν⁻¹ * (r⁻¹ * q) := by
  have e1 : 1 - Real.exp (-(ν * r ^ 2 * t)) ≤ 1 := by nlinarith [exp_pos_heat (ν * r ^ 2 * t)]
  have hc : 0 < ν * r ^ 2 := mul_pos hν (pow_pos hr 2)
  have hA : 0 ≤ r * q := mul_nonneg hr.le hq
  calc r * q * ((ν * r ^ 2)⁻¹ * (1 - Real.exp (-(ν * r ^ 2 * t))))
      ≤ r * q * ((ν * r ^ 2)⁻¹ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 (inv_nonneg.mpr hc.le)) hA
    _ = r * q * (ν * r ^ 2)⁻¹ := by ring
    _ = ν⁻¹ * (r⁻¹ * q) := by field_simp [hν.ne', hr.ne']

/-- The main dissipation budget.  Time-integrating the `X¹` norm of the heat
flow costs exactly `ν⁻¹` times the initial `X⁻¹` mass, uniformly in the
horizon `t`.  This is the literal continuous analogue of the lattice budget
constant in `CriticalMildSmallDataGlobal.smallDataGlobalMild`; the `3` of the
lattice `(3 * ν⁻¹)` is the coordinate aggregation of the bilinear and re-enters
only at the fixed-point assembly.  Proof: Tonelli/Fubini swap of the joint
integrable majorized integrand `J (ξ, s) = ‖ξ‖ * exp (-(ν ‖ξ‖² s)) * ‖g ξ‖`
on `ES × [0, t]`, evaluated sectionwise by `integral_exp_neg_Icc`. -/
theorem integral_normX1_heatMode_le (g : ES → ℂ)
    (hg : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    ∫ s in Icc (0 : ℝ) t, normX1 (heatMode ν s g) ≤ ν⁻¹ * normXm1 g := by
  set μ := volume.restrict (Icc (0 : ℝ) t) with hμdef
  have hm1 : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
  haveI : SFinite μ := by infer_instance
  set J : ES × ℝ → ℝ :=
    fun p => ‖p.1‖ * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2)) * ‖g p.1‖ with hJdef
  have hJfst (s : ℝ) : (fun ξ : ES => ‖ξ‖ * ‖heatMode ν s g ξ‖) = fun ξ => J (ξ, s) := by
    ext ξ
    show ‖ξ‖ * ‖heatMode ν s g ξ‖ = ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖
    rw [norm_heatMode]
    ring
  have hJnn : ∀ (ξ : ES) (s : ℝ), 0 ≤ J (ξ, s) := by
    intro ξ s
    show 0 ≤ ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (exp_pos_heat _).le) (norm_nonneg _)
  have h1f : AEStronglyMeasurable J (volume.prod μ) := by
    have hcont : Continuous (fun p : ES × ℝ =>
        ‖p.1‖ ^ 2 * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2))) := by
      refine Continuous.mul (continuous_fst.norm.pow 2)
        (Real.continuous_exp.comp (Continuous.neg ?_))
      exact Continuous.mul (continuous_const.mul (continuous_fst.norm.pow 2)) continuous_snd
    have hprod : AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ * ‖g p.1‖) (volume.prod μ) :=
      hg.aestronglyMeasurable.comp_fst
    convert (hcont.aestronglyMeasurable).mul hprod using 1
    ext p
    show ‖p.1‖ * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2)) * ‖g p.1‖ =
        ‖p.1‖ ^ 2 * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2)) * (‖p.1‖⁻¹ * ‖g p.1‖)
    rcases eq_or_ne (‖p.1‖ : ℝ) 0 with h | h
    · rw [h]
      simp
    · field_simp [h]
  -- `s`-sections are continuous, hence integrable on `[0, t]`, for every `ξ`
  have hsec (ξ : ES) : Integrable (fun s : ℝ => J (ξ, s)) μ := by
    show Integrable (fun s : ℝ => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖)
        (volume.restrict (Icc (0 : ℝ) t))
    exact ((continuous_const.mul
        (Real.continuous_exp.comp (Continuous.neg (continuous_const.mul continuous_id)))).mul
        continuous_const).integrableOn_Icc
  -- the sectionwise `s`-integral is computable and budget-bounded
  have hseceq (ξ : ES) : ∫ s, J (ξ, s) ∂μ =
      ‖ξ‖ * ‖g ξ‖ * ∫ s, Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) ∂μ := by
    have hf : (fun s : ℝ => J (ξ, s)) =
        fun s : ℝ => (‖ξ‖ * ‖g ξ‖ : ℝ) • Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) := by
      ext s
      show ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖ = _
      rw [smul_eq_mul]
      ring
    rw [hf, integral_smul, smul_eq_mul]
  have hsecle (ξ : ES) : ∫ s, J (ξ, s) ∂μ ≤ ν⁻¹ * (‖ξ‖⁻¹ * ‖g ξ‖) := by
    by_cases hx : (ξ : ES) = 0
    · have : (fun s : ℝ => J (ξ, s)) = fun _ => 0 := by
        funext s
        show ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖ = 0
        rw [hx]
        simp
      rw [this, integral_zero]
      exact mul_nonneg (inv_nonneg.mpr hν.le) (mul_nonneg (weight_nonneg ξ) (norm_nonneg _))
    · have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hx
      have hc : 0 < ν * ‖ξ‖ ^ 2 := mul_pos hν (pow_pos hr 2)
      rw [hseceq, integral_exp_neg_Icc _ _ hc ht]
      exact heat_budget_pointwise ν ‖ξ‖ ‖g ξ‖ t hν ht hr (norm_nonneg _)
  have hJnorm (ξ : ES) : ∫ s, J (ξ, s) ∂μ = ∫ s, ‖J (ξ, s)‖ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    show J (ξ, s) = ‖J (ξ, s)‖
    exact (Real.norm_of_nonneg (hJnn ξ s)).symm
  -- the parametric integral `ξ ↦ ∫ s, ‖J (ξ, s)‖ ∂μ` is integrable
  have hsecI : Integrable (fun ξ : ES => ∫ s, ‖J (ξ, s)‖ ∂μ) volume := by
    refine ⟨(h1f.norm).integral_prod_right',
      HasFiniteIntegral.mono (hg.const_mul ν⁻¹).hasFiniteIntegral ?_⟩
    filter_upwards with ξ
    have hn1 : 0 ≤ ∫ s, ‖J (ξ, s)‖ ∂μ :=
      integral_nonneg (fun s => norm_nonneg _)
    have hn2 : 0 ≤ ν⁻¹ * (‖ξ‖⁻¹ * ‖g ξ‖) :=
      mul_nonneg (inv_nonneg.mpr hν.le) (mul_nonneg (weight_nonneg ξ) (norm_nonneg _))
    rw [Real.norm_of_nonneg hn1, Real.norm_of_nonneg hn2, ← hJnorm ξ]
    exact hsecle ξ
  have hint : Integrable J (volume.prod μ) :=
    (integrable_prod_iff h1f).mpr ⟨Eventually.of_forall hsec, hsecI⟩
  have hsecInt : Integrable (fun ξ : ES => ∫ s, J (ξ, s) ∂μ) volume :=
    hsecI.congr (Eventually.of_forall fun ξ => (hJnorm ξ).symm)
  show (∫ s, (∫ ξ : ES, ‖ξ‖ * ‖heatMode ν s g ξ‖ ∂volume) ∂μ) ≤ ν⁻¹ * normXm1 g
  rw [show (fun s : ℝ => ∫ ξ : ES, ‖ξ‖ * ‖heatMode ν s g ξ‖ ∂volume) =
      (fun s : ℝ => ∫ ξ : ES, J (ξ, s) ∂volume) from by
        funext s
        rw [hJfst s]]
  rw [← integral_prod_symm J hint, integral_prod J hint]
  refine le_trans (integral_mono hsecInt (hg.const_mul ν⁻¹) fun ξ => hsecle ξ) ?_
  rw [show (fun ξ : ES => ν⁻¹ * (‖ξ‖⁻¹ * ‖g ξ‖)) = fun ξ => (ν⁻¹ : ℝ) • (‖ξ‖⁻¹ * ‖g ξ‖) from rfl,
    integral_smul, smul_eq_mul]
  rfl

/-!
## Vector aggregation over the three velocity coordinates
-/

/-- The heat flow applied coordinatewise to a vector Fourier profile. -/
def heatVec (ν t : ℝ) (a : ES → ComplexSpace) : ES → ComplexSpace :=
  fun ξ i => heatMode ν t (fun ζ : ES => a ζ i) ξ

/-- The coordinate `X⁻¹` mass is non-increasing along the coordinatewise heat
flow. -/
theorem coordinateXm1Mass_heatVec_le (a : ES → ComplexSpace)
    (ha : ∀ i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    coordinateXm1Mass (heatVec ν t a) ≤ coordinateXm1Mass a := by
  unfold coordinateXm1Mass
  refine Finset.sum_le_sum fun i _ => ?_
  exact normXm1_heatMode_le (fun ζ : ES => a ζ i) (ha i) ν t hν ht

/-- The `X¹` budget integrand is time-integrable on every finite horizon. -/
private theorem heatBudgetIntegrable (g : ES → ℂ)
    (hg : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    Integrable (fun s : ℝ => normX1 (heatMode ν s g))
      (volume.restrict (Icc (0 : ℝ) t)) := by
  set μ := volume.restrict (Icc (0 : ℝ) t) with hμdef
  have hm1 : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
  haveI : SFinite μ := by infer_instance
  set J : ES × ℝ → ℝ :=
    fun p => ‖p.1‖ * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2)) * ‖g p.1‖ with hJdef
  have hJfst (s : ℝ) : (fun ξ : ES => ‖ξ‖ * ‖heatMode ν s g ξ‖) = fun ξ => J (ξ, s) := by
    ext ξ
    show ‖ξ‖ * ‖heatMode ν s g ξ‖ = ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖
    rw [norm_heatMode]
    ring
  have hJnn : ∀ (ξ : ES) (s : ℝ), 0 ≤ J (ξ, s) := by
    intro ξ s
    show 0 ≤ ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (exp_pos_heat _).le) (norm_nonneg _)
  have h1f : AEStronglyMeasurable J (volume.prod μ) := by
    have hcont : Continuous (fun p : ES × ℝ =>
        ‖p.1‖ ^ 2 * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2))) := by
      refine Continuous.mul (continuous_fst.norm.pow 2)
        (Real.continuous_exp.comp (Continuous.neg ?_))
      exact Continuous.mul (continuous_const.mul (continuous_fst.norm.pow 2)) continuous_snd
    have hprod : AEStronglyMeasurable (fun p : ES × ℝ => ‖p.1‖⁻¹ * ‖g p.1‖) (volume.prod μ) :=
      hg.aestronglyMeasurable.comp_fst
    convert (hcont.aestronglyMeasurable).mul hprod using 1
    ext p
    show ‖p.1‖ * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2)) * ‖g p.1‖ =
        ‖p.1‖ ^ 2 * Real.exp (-(ν * ‖p.1‖ ^ 2 * p.2)) * (‖p.1‖⁻¹ * ‖g p.1‖)
    rcases eq_or_ne (‖p.1‖ : ℝ) 0 with h | h
    · rw [h]
      simp
    · field_simp [h]
  have hsec (ξ : ES) : Integrable (fun s : ℝ => J (ξ, s)) μ := by
    show Integrable (fun s : ℝ => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖)
        (volume.restrict (Icc (0 : ℝ) t))
    exact ((continuous_const.mul
        (Real.continuous_exp.comp (Continuous.neg (continuous_const.mul continuous_id)))).mul
        continuous_const).integrableOn_Icc
  have hseceq (ξ : ES) : ∫ s, J (ξ, s) ∂μ =
      ‖ξ‖ * ‖g ξ‖ * ∫ s, Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) ∂μ := by
    have hf : (fun s : ℝ => J (ξ, s)) =
        fun s : ℝ => (‖ξ‖ * ‖g ξ‖ : ℝ) • Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) := by
      ext s
      show ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖ = _
      rw [smul_eq_mul]
      ring
    rw [hf, integral_smul, smul_eq_mul]
  have hsecle (ξ : ES) : ∫ s, J (ξ, s) ∂μ ≤ ν⁻¹ * (‖ξ‖⁻¹ * ‖g ξ‖) := by
    by_cases hx : (ξ : ES) = 0
    · have : (fun s : ℝ => J (ξ, s)) = fun _ => 0 := by
        funext s
        show ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖g ξ‖ = 0
        rw [hx]
        simp
      rw [this, integral_zero]
      exact mul_nonneg (inv_nonneg.mpr hν.le) (mul_nonneg (weight_nonneg ξ) (norm_nonneg _))
    · have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hx
      have hc : 0 < ν * ‖ξ‖ ^ 2 := mul_pos hν (pow_pos hr 2)
      rw [hseceq, integral_exp_neg_Icc _ _ hc ht]
      exact heat_budget_pointwise ν ‖ξ‖ ‖g ξ‖ t hν ht hr (norm_nonneg _)
  have hJnorm (ξ : ES) : ∫ s, J (ξ, s) ∂μ = ∫ s, ‖J (ξ, s)‖ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    show J (ξ, s) = ‖J (ξ, s)‖
    exact (Real.norm_of_nonneg (hJnn ξ s)).symm
  have hsecI : Integrable (fun ξ : ES => ∫ s, ‖J (ξ, s)‖ ∂μ) volume := by
    refine ⟨(h1f.norm).integral_prod_right',
      HasFiniteIntegral.mono (hg.const_mul ν⁻¹).hasFiniteIntegral ?_⟩
    filter_upwards with ξ
    have hn1 : 0 ≤ ∫ s, ‖J (ξ, s)‖ ∂μ :=
      integral_nonneg (fun s => norm_nonneg _)
    have hn2 : 0 ≤ ν⁻¹ * (‖ξ‖⁻¹ * ‖g ξ‖) :=
      mul_nonneg (inv_nonneg.mpr hν.le) (mul_nonneg (weight_nonneg ξ) (norm_nonneg _))
    rw [Real.norm_of_nonneg hn1, Real.norm_of_nonneg hn2, ← hJnorm ξ]
    exact hsecle ξ
  have hint : Integrable J (volume.prod μ) :=
    (integrable_prod_iff h1f).mpr ⟨Eventually.of_forall hsec, hsecI⟩
  have hi := hint.integral_prod_right
  convert hi using 1
  funext s
  show normX1 (heatMode ν s g) = ∫ ξ : ES, J (ξ, s) ∂volume
  rw [← hJfst s]
  rfl

/-- The coordinate-aggregated dissipation budget: the time integral of the
`X¹` mass of the coordinatewise heat flow is at most `ν⁻¹` times the `X⁻¹`
coordinate mass, in the exact shape consumed by
`integral_normXm1_continuousNavierSource_le`. -/
theorem integral_coordinateX1Mass_heatVec_le (a : ES → ComplexSpace)
    (ha : ∀ i, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) :
    ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (heatVec ν s a) ≤
      ν⁻¹ * coordinateXm1Mass a := by
  set μ := volume.restrict (Icc (0 : ℝ) t)
  have hb (i : Fin 3) :
      Integrable (fun s : ℝ => normX1 (fun ξ : ES => heatVec ν s a ξ i)) μ := by
    have key :
        Integrable (fun s : ℝ => normX1 (heatMode ν s (fun ζ : ES => a ζ i))) μ :=
      heatBudgetIntegrable (fun ζ : ES => a ζ i) (ha i) ν t hν ht
    exact key.congr (Eventually.of_forall fun s => rfl)
  unfold coordinateX1Mass coordinateXm1Mass
  calc (∫ s, ∑ i : Fin 3, normX1 (fun ξ : ES => heatVec ν s a ξ i) ∂μ)
      _ = ∑ i : Fin 3, ∫ s, normX1 (fun ξ : ES => heatVec ν s a ξ i) ∂μ :=
        integral_finsetSum (f := fun i (s : ℝ) => normX1 (fun ξ : ES => heatVec ν s a ξ i))
          Finset.univ (fun i _ => hb i)
      _ ≤ ∑ i : Fin 3, ν⁻¹ * normXm1 (fun ξ : ES => a ξ i) :=
        Finset.sum_le_sum fun i _ =>
          integral_normX1_heatMode_le (fun ζ : ES => a ζ i) (ha i) ν t hν ht
      _ = ν⁻¹ * ∑ i : Fin 3, normXm1 (fun ξ : ES => a ξ i) := by rw [← Finset.mul_sum]

/-!
## Bochner/Fubini bridge: `X⁻¹` mass under a time integral
-/

/-- The weighted `X⁻¹` mass commutes with a Bochner time integral up to
inequality (Minkowski for integrals plus Fubini): the mass of the time
integral of the heat-propagated source family is bounded by the time integral
of the masses. The joint weighted integrability of the integrand is carried as
an explicit hypothesis, following the convention of
`ContinuousLeiLinTimeDuhamel`. -/
theorem normXm1_setIntegral_le (b : ℝ → ES → ℂ) (ν t : ℝ)
    (hb : Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) • heatMode ν (t - p.2) (b p.2) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t)))) :
    normXm1 (fun ξ : ES => ∫ s in Icc (0 : ℝ) t, heatMode ν (t - s) (b s) ξ) ≤
      ∫ s in Icc (0 : ℝ) t, normXm1 (heatMode ν (t - s) (b s)) := by
  set μ := volume.restrict (Icc (0 : ℝ) t)
  show (∫ ξ : ES, ‖ξ‖⁻¹ * ‖∫ s, heatMode ν (t - s) (b s) ξ ∂μ‖ ∂volume) ≤
      ∫ s, normXm1 (heatMode ν (t - s) (b s)) ∂μ
  set L : ES × ℝ → ℂ :=
    fun p => (‖p.1‖⁻¹ : ℝ) • heatMode ν (t - p.2) (b p.2) p.1 with hLdef
  have hbL : Integrable L (volume.prod μ) := hb
  have hP : Integrable (fun ξ : ES => ∫ s, L (ξ, s) ∂μ) volume := hbL.integral_prod_left
  have hQ : Integrable (fun ξ : ES => ∫ s, ‖L (ξ, s)‖ ∂μ) volume :=
    hbL.norm.integral_prod_left
  have hnorm : Integrable (fun ξ : ES => ‖∫ s, L (ξ, s) ∂μ‖) volume :=
    ⟨hP.aestronglyMeasurable.norm, HasFiniteIntegral.mono hQ.hasFiniteIntegral
      (Eventually.of_forall fun ξ => by
        rw [Real.norm_of_nonneg (norm_nonneg (∫ (s : ℝ), L (ξ, s) ∂μ)),
          Real.norm_of_nonneg (integral_nonneg (fun s => norm_nonneg (L (ξ, s))))]
        exact norm_integral_le_integral_norm (fun s : ℝ => L (ξ, s)))⟩
  have heq : (fun ξ : ES => ‖ξ‖⁻¹ * ‖∫ s, heatMode ν (t - s) (b s) ξ ∂μ‖) =
      fun ξ : ES => ‖∫ s, L (ξ, s) ∂μ‖ := by
    funext ξ
    rw [← Real.norm_of_nonneg (weight_nonneg ξ), ← norm_smul, ← integral_smul]
  rw [heq]
  refine le_trans (integral_mono hnorm hQ
    (fun ξ => norm_integral_le_integral_norm (fun s : ℝ => L (ξ, s)))) ?_
  have hn : Integrable (fun p : ES × ℝ => ‖L p‖) (volume.prod μ) := hbL.norm
  rw [← integral_prod (fun p : ES × ℝ => ‖L p‖) hn,
    integral_prod_symm (fun p : ES × ℝ => ‖L p‖) hn]
  have hsec (s : ℝ) :
      (∫ ξ : ES, ‖L (ξ, s)‖ ∂volume) = normXm1 (heatMode ν (t - s) (b s)) := by
    show (∫ ξ : ES, ‖(‖ξ‖⁻¹ : ℝ) • heatMode ν (t - s) (b s) ξ‖ ∂volume) = _
    rw [integral_congr_ae (Eventually.of_forall fun ξ => by
      rw [norm_smul, Real.norm_of_nonneg (weight_nonneg ξ)])]
    rfl
  rw [integral_congr_ae (Eventually.of_forall hsec)]

/-- One Duhamel coordinate has finite weighted `X⁻¹` mass controlled by the
time integral of the source masses: the heat propagator first contracts each
`X⁻¹` mass (`normXm1_heatMode_le`) and the mass then passes through the time
integral via the Fubini bridge. The joint and per-time integrabilities are
explicit hypotheses, matching the convention of
`ContinuousLeiLinTimeDuhamel.integral_normXm1_continuousNavierSource_le`. -/
theorem normXm1_continuousDuhamel_le (u v : ℝ → ES → ComplexSpace) (ν t : ℝ) (i : Fin 3)
    (hν : 0 < ν)
    (hb : Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) •
          heatMode ν (t - p.2) (fun ζ : ES => continuousNavierSource u v p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u v s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hg : Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource u v s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousNavierSource u v s ξ i‖)) :
    normXm1 (fun ξ : ES => continuousDuhamel ν u v t ξ i) ≤
      ∫ s in Icc (0 : ℝ) t, normXm1 (fun ξ : ES => continuousNavierSource u v s ξ i) := by
  set μ := volume.restrict (Icc (0 : ℝ) t)
  have hm1 : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
  have key := normXm1_setIntegral_le
      (fun s : ℝ => fun ζ : ES => continuousNavierSource u v s ζ i) ν t hb
  refine le_trans key ?_
  refine integral_mono_ae hf hg ?_
  filter_upwards [ae_restrict_mem hm1] with s hs
  exact normXm1_heatMode_le (fun ζ : ES => continuousNavierSource u v s ζ i) (hb0 s hs)
    ν (t - s) hν (sub_nonneg.mpr hs.2)

end Navier.Analysis.ContinuousLeiLinDissipation

#print axioms Navier.Analysis.ContinuousLeiLinDissipation.heatVec
#print axioms Navier.Analysis.ContinuousLeiLinDissipation.normXm1_heatMode_le
#print axioms Navier.Analysis.ContinuousLeiLinDissipation.tendsto_normXm1_heatMode
#print axioms Navier.Analysis.ContinuousLeiLinDissipation.integral_normX1_heatMode_le
#print axioms Navier.Analysis.ContinuousLeiLinDissipation.coordinateXm1Mass_heatVec_le
#print axioms Navier.Analysis.ContinuousLeiLinDissipation.integral_coordinateX1Mass_heatVec_le
#print axioms Navier.Analysis.ContinuousLeiLinDissipation.normXm1_setIntegral_le
#print axioms Navier.Analysis.ContinuousLeiLinDissipation.normXm1_continuousDuhamel_le
