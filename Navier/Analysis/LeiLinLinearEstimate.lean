import Mathlib
import Navier.Analysis.LeiLinSpace

/-!
# The Lei-Lin linear estimate: the heat semigroup in the mixed norm

Step 2 of the Lei-Lin assembly.  On the Fourier side the heat semigroup
`e^{νtΔ}` is the multiplier `k ↦ e^{-ν|k|²t}`.  Two facts are needed, and both
are proved here.

* `heat_contracts_Xm1` : `‖e^{νtΔ}f‖_{𝒳^{-1}} ≤ ‖f‖_{𝒳^{-1}}` for `t ≥ 0`.
  The semigroup is a contraction on the critical space.

* `heat_L1_time_eq` : `ν ∫₀^∞ ‖e^{νtΔ}f‖_{𝒳¹} dt = ‖f‖_{𝒳^{-1}}`, an
  **equality**, with no constant.

The second is the mechanism `CriticalMildQuantitativeRestart` discards.  Mode by
mode it is `∫₀^∞ ν|k| e^{-ν|k|²t} dt = |k|⁻¹`, i.e.
`LeiLinCriticalMechanism.dissipation_integral_eq_one` divided by `|k|`; the
dissipation is spent once over `[0,∞)` at scale-free cost, instead of being
re-spent on each restart interval where it contributes nothing.

Scope.  The linear (Stokes) half of the Lei-Lin argument.  The nonlinearity is
not treated here and nothing in this file claims global regularity.

Reference: Z. Lei and F. Lin, CPAM 64 (2011) 1297-1304.
-/

set_option autoImplicit false

noncomputable section

namespace Navier.Analysis.LeiLinLinearEstimate

open MeasureTheory Set LeiLinSpace

variable {G : Type*}

/-- The heat semigroup on Fourier coefficients: `e^{νtΔ}` acts on the mode `k`
by multiplication with `e^{-ν|k|²t}`. -/
def heatMode (ν : ℝ) (σ : G → ℝ) (t : ℝ) (f : G → ℝ) (k : G) : ℝ :=
  Real.exp (-(ν * (σ k) ^ 2 * t)) * f k

/-- **The heat semigroup contracts the critical norm.**

`‖e^{νtΔ}f‖_{𝒳^{-1}} ≤ ‖f‖_{𝒳^{-1}}` for every `t ≥ 0` and `ν ≥ 0`.  This is
the only linear input to the `L^∞_t 𝒳^{-1}` half of the mixed norm. -/
theorem heat_contracts_Xm1 {ν : ℝ} {σ f : G → ℝ} (hν : 0 ≤ ν) (hσ : ∀ k, 0 ≤ σ k)
    {t : ℝ} (ht : 0 ≤ t) (hf : InW (fun k => (σ k)⁻¹) f) :
    normXm1 σ (heatMode ν σ t f) ≤ normXm1 σ f := by
  have hle : ∀ k, (σ k)⁻¹ * |heatMode ν σ t f k| ≤ (σ k)⁻¹ * |f k| := by
    intro k
    have hexp : Real.exp (-(ν * (σ k) ^ 2 * t)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ ν * (σ k) ^ 2 * t := by positivity
      linarith
    have hpos : (0:ℝ) < Real.exp (-(ν * (σ k) ^ 2 * t)) := Real.exp_pos _
    have : |heatMode ν σ t f k| = Real.exp (-(ν * (σ k) ^ 2 * t)) * |f k| := by
      rw [heatMode, abs_mul, abs_of_pos hpos]
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [abs_nonneg (f k)]) (inv_nonneg.mpr (hσ k))
  have hsum : Summable fun k => (σ k)⁻¹ * |heatMode ν σ t f k| :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (inv_nonneg.mpr (hσ k)) (abs_nonneg _)) hle hf
  exact hsum.tsum_le_tsum hle hf

/-! ## The per-mode dissipation integral -/

/-- The time integrand at a single mode, `ν |k| |e^{-ν|k|²t} f k|`. -/
theorem heatMode_abs (ν : ℝ) (σ f : G → ℝ) (t : ℝ) (k : G) :
    |heatMode ν σ t f k| = Real.exp (-(ν * (σ k) ^ 2 * t)) * |f k| := by
  rw [heatMode, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- **Integrability of the single-mode dissipation integrand on `(0,∞)`.** -/
theorem integrableOn_mode {ν : ℝ} {σ f : G → ℝ} (hν : 0 < ν) (k : G) (hk : 0 < σ k) :
    IntegrableOn (fun t => ν * (σ k * |heatMode ν σ t f k|)) (Ioi (0:ℝ)) := by
  have hb : (0:ℝ) < ν * (σ k) ^ 2 := by positivity
  have hbase : IntegrableOn (fun t : ℝ => Real.exp (-(ν * (σ k) ^ 2) * t)) (Ioi (0:ℝ)) :=
    exp_neg_integrableOn_Ioi 0 hb
  have hmul : IntegrableOn
      (fun t : ℝ => ν * σ k * |f k| * Real.exp (-(ν * (σ k) ^ 2) * t)) (Ioi (0:ℝ)) :=
    hbase.const_mul (ν * σ k * |f k|)
  refine MeasureTheory.IntegrableOn.congr_fun hmul (fun t _ => ?_) measurableSet_Ioi
  rw [heatMode_abs]
  ring_nf

/-- **The single-mode `L¹`-in-time identity.**

`∫₀^∞ ν |k| e^{-ν|k|²t} |f k| dt = |k|⁻¹ |f k|`.

This is `LeiLinCriticalMechanism.dissipation_integral_eq_one` with the factor
`|k|⁻¹ |f k|` pulled out: the `𝒳¹` weight `|k|` against the dissipation rate
`ν|k|²` produces exactly the `𝒳^{-1}` weight `|k|⁻¹`, with constant `1`.  It is
also true at the zero mode, where both sides vanish. -/
theorem integral_mode_eq {ν : ℝ} {σ f : G → ℝ} (hν : 0 < ν) (hσ : ∀ k, 0 ≤ σ k) (k : G) :
    (∫ t in Ioi (0:ℝ), ν * (σ k * |heatMode ν σ t f k|)) = (σ k)⁻¹ * |f k| := by
  rcases eq_or_lt_of_le (hσ k) with h0 | hk
  · simp [heatMode_abs, ← h0]
  · have hdiss := LeiLinCriticalMechanism.dissipation_integral_eq_one
      (ν * (σ k) ^ 2) (by positivity)
    have hrw : ∀ t : ℝ, ν * (σ k * |heatMode ν σ t f k|)
        = ((σ k)⁻¹ * |f k|) * ((ν * (σ k) ^ 2) * Real.exp (-((ν * (σ k) ^ 2) * t))) := by
      intro t
      rw [heatMode_abs]
      field_simp
    calc (∫ t in Ioi (0:ℝ), ν * (σ k * |heatMode ν σ t f k|))
        = ∫ t in Ioi (0:ℝ), ((σ k)⁻¹ * |f k|) *
            ((ν * (σ k) ^ 2) * Real.exp (-((ν * (σ k) ^ 2) * t))) := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun t => hrw t)
      _ = ((σ k)⁻¹ * |f k|) * ∫ t in Ioi (0:ℝ),
            ((ν * (σ k) ^ 2) * Real.exp (-((ν * (σ k) ^ 2) * t))) := integral_const_mul _ _
      _ = (σ k)⁻¹ * |f k| := by rw [hdiss, mul_one]


/-- Integrability of the single-mode integrand, including the zero mode where it
vanishes identically. -/
theorem integrableOn_mode_all {ν : ℝ} {σ f : G → ℝ} (hν : 0 < ν) (hσ : ∀ k, 0 ≤ σ k)
    (k : G) : IntegrableOn (fun t => ν * (σ k * |heatMode ν σ t f k|)) (Ioi (0:ℝ)) := by
  rcases eq_or_lt_of_le (hσ k) with h0 | hk
  · simp [← h0]
  · exact integrableOn_mode hν k hk

/-! ## The `L¹`-in-time linear estimate -/

/-- **`ν ∫₀^∞ ‖e^{νtΔ}f‖_{𝒳¹} dt = ‖f‖_{𝒳^{-1}}`.**

An exact identity, with constant `1`, for every viscosity `ν > 0`.  The
dissipation is spent once over the whole half-line and pays for a full
derivative: the `𝒳¹` norm of the heat flow is integrable in time with total
mass exactly the `𝒳^{-1}` norm of the datum.

This is the linear estimate of Lei-Lin.  Contrast
`CriticalMildQuantitativeRestart`, which bounds `‖e^{νrΔ}v‖ ≤ ‖v‖` on each
restart interval and therefore extracts nothing from the semigroup.

Hypotheses: `G` countable (the mode lattice), `ν > 0`, `σ ≥ 0`, and `f ∈ 𝒳^{-1}`.

Scope: linear equation only. -/
theorem heat_L1_time_eq [Countable G] {ν : ℝ} {σ f : G → ℝ} (hν : 0 < ν)
    (hσ : ∀ k, 0 ≤ σ k) (hf : InW (fun k => (σ k)⁻¹) f) :
    (∫ t in Ioi (0:ℝ), ν * normX1 σ (heatMode ν σ t f)) = normXm1 σ f := by
  set F : G → ℝ → ℝ := fun k t => ν * (σ k * |heatMode ν σ t f k|) with hF
  have hpt : ∀ t : ℝ, ν * normX1 σ (heatMode ν σ t f) = ∑' k, F k t := by
    intro t
    rw [normX1, wNorm, hF]
    exact (tsum_mul_left).symm
  have hnn : ∀ k t, 0 ≤ F k t := by
    intro k t
    exact mul_nonneg hν.le (mul_nonneg (hσ k) (abs_nonneg _))
  have hint : ∀ k, IntegrableOn (F k) (Ioi (0:ℝ)) := fun k =>
    integrableOn_mode_all hν hσ k
  have hmeas : ∀ k, AEStronglyMeasurable (F k) (volume.restrict (Ioi (0:ℝ))) :=
    fun k => (hint k).aestronglyMeasurable
  have hval : ∀ k, (∫ t in Ioi (0:ℝ), F k t) = (σ k)⁻¹ * |f k| := fun k =>
    integral_mode_eq hν hσ k
  have hlint : ∀ k, (∫⁻ t in Ioi (0:ℝ), ‖F k t‖₊) = ENNReal.ofReal ((σ k)⁻¹ * |f k|) := by
    intro k
    have h1 : (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (F k t))
        = ENNReal.ofReal (∫ t in Ioi (0:ℝ), F k t) :=
      (ofReal_integral_eq_lintegral_ofReal (hint k)
        (Filter.Eventually.of_forall fun t => hnn k t)).symm
    rw [← hval k, ← h1]
    refine lintegral_congr fun t => ?_
    rw [Real.nnnorm_of_nonneg (hnn k t), ENNReal.ofReal]
    exact congrArg _ (Real.toNNReal_of_nonneg (hnn k t)).symm
  have hfinite : (∑' k, ∫⁻ t in Ioi (0:ℝ), ‖F k t‖₊) ≠ ⊤ := by
    have hnn' : ∀ k, 0 ≤ (σ k)⁻¹ * |f k| := fun k =>
      mul_nonneg (inv_nonneg.mpr (hσ k)) (abs_nonneg _)
    have : (∑' k, ∫⁻ t in Ioi (0:ℝ), ‖F k t‖₊)
        = ENNReal.ofReal (∑' k, (σ k)⁻¹ * |f k|) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hnn' hf]
      exact tsum_congr hlint
    rw [this]
    exact ENNReal.ofReal_ne_top
  calc (∫ t in Ioi (0:ℝ), ν * normX1 σ (heatMode ν σ t f))
      = ∫ t in Ioi (0:ℝ), ∑' k, F k t := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun t => hpt t)
    _ = ∑' k, ∫ t in Ioi (0:ℝ), F k t := integral_tsum hmeas hfinite
    _ = ∑' k, (σ k)⁻¹ * |f k| := tsum_congr hval
    _ = normXm1 σ f := rfl

end Navier.Analysis.LeiLinLinearEstimate

#print axioms Navier.Analysis.LeiLinLinearEstimate.heat_contracts_Xm1
#print axioms Navier.Analysis.LeiLinLinearEstimate.integral_mode_eq
#print axioms Navier.Analysis.LeiLinLinearEstimate.heat_L1_time_eq

