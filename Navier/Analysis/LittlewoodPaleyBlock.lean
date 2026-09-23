import Navier.Analysis.WienerGradLog
import Navier.Analysis.WienerPhysicalAssembly
import Navier.Analysis.Vorticity
import Navier.Analysis.WienerPointwiseODE
import Navier.Analysis.WienerReality
import Navier.Analysis.FourierL2Agree
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Data.Complex.BigOperators

/-!
# Littlewood–Paley block machinery, part I (mechanical slice, lane f28)

This module begins the proof of `Navier.Analysis.WienerGradLog.GradSupLogHyp`
(the consumed `‖∇u‖∞` log bound) assigned by `WienerGradLog.lean` to this file.

**It assumes** only the `Rep`/`WDatum` carriers of `WienerRestartLeaf` and the
inverse-Fourier derivative API of `WienerSmoothPath` / `WienerPhysicalAssembly`.

**It does NOT prove** `GradSupLogHyp`.  Per the 0923 triage, the remaining
dependency chain is:

* `LP2` (`blockKernel_L1_uniform`) — the HARD analytic leaf: the block kernel
  `K_j = 𝓕⁻[(ξₖξᵢ/|ξ|²)ψ_j]` has uniformly bounded `L¹` norm (oscillatory-integral
  decay `|K₀(x)| ≤ C⟨x⟩⁻⁴`).  NOT here; this is the named hard leaf.
* `LP1` (dyadic partition + block reconstruction on the `Rep` carrier),
  `LP3` (low-band block bound via `staticCurl` + Young), `LP4` (Sobolev block
  decay via Plancherel + Cauchy–Schwarz), `LP5` (bottom-band bound) —
  mechanical follow-up consuming `LP2`.
* The assembly step `Σ_j ∂ₖvᵢ = Σ_j Δ_j ∂ₖvᵢ` term-by-term.

**Landed here** (each a proved declaration, no consumer yet — the consumer
`WienerHigherEnergy` step 2 is unwritten):

* `D1` — `Rep.integrable_profH3_integrand` / `Rep.integrable_profL2_integrand`:
  the header's finiteness claim for `profH3`/`profL2` becomes a proved lemma, so
  the Bochner-integral `0` convention for non-integrable functions never applies
  on represented profiles.
* `LP0` — `rep_fderiv_coord`: the `fderiv` ↔ derivative-tower bridge on the `Rep`
  carrier, from `WienerSmoothPath.hasFDerivAt_fourierInv` to the coordinate
  derivative appearing in `GradSupLogHyp`.
* `LP6` — `shellSum_log`: the shell-sum envelope `Σ_j min(y, Y·4⁻ʲ)` to the two
  log terms, as a standalone `ℝ`-statement with no carrier (see the T-003 probe
  note at `shellSum_log`).  The single-envelope form `shellSum_log_high` carries
  the canonical name `blockEnvelopeLogBound` (coordinator packet 0923).
* `LP7` — `rep_curlfree_grad_zero`: the `y = 0` curl-free edge case, via the new
  `L¹` Fourier-injection lemma `fourierInv_eq_zero` (built with the repo's
  self-adjointness `FourierL2Agree.integral_fourierInv_smul_eq` plus the
  fundamental lemma; Mathlib has no `Real.fourierInjective` at this pinning).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators FourierTransform SchwartzMap Matrix
open scoped Topology ComplexConjugate ContDiff

namespace Navier.Analysis.LittlewoodPaleyBlock

open Navier Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.WienerGradLog
open Navier.Analysis.WienerDatumSmooth
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPhysicalAssembly
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.WienerReality
open Navier.Analysis.Vorticity (staticCurl)
open Navier.Analysis.FourierL2Agree (integral_fourierInv_smul_eq)

/-! ## D1 — finiteness of the profile integrands (defect repair) -/

/-- Master `D1` bound: for a `WDatum` profile with a.e. coordinate bound `A` and
every Fourier moment, `ξ ↦ ‖ξ‖ⁿ ∑ᵢ ‖a ξ i‖²` is integrable for every `n`
(the `mom n` moment absorbs it: `∑ᵢ ‖aξi‖² ≤ 3A‖aξ‖`). -/
theorem integrable_profile_integrand {a : ES → ComplexSpace} (hd : WDatum a) {A : ℝ}
    (hA : 0 ≤ A) (n : ℕ)
    (hb : ∀ᵐ ξ ∂(volume : Measure ES), ∀ i : Fin 3, ‖a ξ i‖ ≤ A) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ n * ∑ i : Fin 3, ‖a ξ i‖ ^ 2) := by
  have hmeas : AEStronglyMeasurable (fun ξ : ES => ‖ξ‖ ^ n * ∑ i : Fin 3, ‖a ξ i‖ ^ 2)
    volume := by
    refine .mul ?_ ?_
    · exact (continuous_norm.pow n).aestronglyMeasurable
    · refine Measurable.aestronglyMeasurable ?_
      exact Finset.measurable_sum _ fun i _ =>
        (((measurable_pi_apply i).comp hd.meas).norm).pow_const 2
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have hrew : (fun ξ : ES => ‖‖ξ‖ ^ n * ∑ i : Fin 3, ‖a ξ i‖ ^ 2‖ₑ) =ᵐ[volume]
      fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * ENNReal.ofReal (∑ i : Fin 3, ‖a ξ i‖ ^ 2) := by
    refine Eventually.of_forall fun ξ => ?_
    show ‖‖ξ‖ ^ n * ∑ i : Fin 3, ‖a ξ i‖ ^ 2‖ₑ =
      ENNReal.ofReal (‖ξ‖ ^ n) * ENNReal.ofReal (∑ i : Fin 3, ‖a ξ i‖ ^ 2)
    have hn : 0 ≤ ‖ξ‖ ^ n * ∑ i : Fin 3, ‖a ξ i‖ ^ 2 :=
      mul_nonneg (pow_nonneg (norm_nonneg _) n)
        (Finset.sum_nonneg fun i _ => pow_nonneg (norm_nonneg _) 2)
    rw [Real.enorm_eq_ofReal hn, ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) n)]
  have hle : (fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * ENNReal.ofReal (∑ i : Fin 3,
      ‖a ξ i‖ ^ 2)) ≤ᵐ[volume]
      fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * (ENNReal.ofReal (3 * A) * ‖a ξ‖ₑ) := by
    filter_upwards [hb] with ξ h
    conv_rhs => rw [← ofReal_norm,
      ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 3 * A)]
    refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
    calc ∑ i : Fin 3, ‖a ξ i‖ ^ 2 ≤ ∑ i : Fin 3, ‖a ξ i‖ * A :=
          Finset.sum_le_sum fun i _ => by
            rw [pow_two]
            exact mul_le_mul_of_nonneg_left (h i) (norm_nonneg _)
      _ ≤ ∑ i : Fin 3, ‖a ξ‖ * A :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (norm_le_pi_norm (a ξ) i) hA
      _ = 3 * A * ‖a ξ‖ := by simp; ring
  have hameas : AEMeasurable (fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ‖ₑ) volume :=
    ((ENNReal.measurable_ofReal.comp (continuous_norm.pow n).measurable).aemeasurable).mul
      (AEMeasurable.congr ((ENNReal.measurable_ofReal.comp hd.meas.norm).aemeasurable)
        (ae_of_all volume fun ξ => ofReal_norm (a ξ)))
  have htrans : ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * (ENNReal.ofReal (3 * A) * ‖a ξ‖ₑ)
      = ENNReal.ofReal (3 * A) * ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ‖ₑ := by
    calc _ = ∫⁻ ξ, ENNReal.ofReal (3 * A) * (ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ‖ₑ) :=
          MeasureTheory.lintegral_congr fun ξ => mul_left_comm _ _ _
      _ = _ := MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal (3 * A)) hameas
  calc (∫⁻ ξ : ES, ‖‖ξ‖ ^ n * ∑ i : Fin 3, ‖a ξ i‖ ^ 2‖ₑ ∂volume)
      = ∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖ ^ n) * ENNReal.ofReal (∑ i : Fin 3, ‖a ξ i‖ ^ 2) ∂volume :=
          lintegral_congr_ae hrew
    _ ≤ ∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖ ^ n) * (ENNReal.ofReal (3 * A) * ‖a ξ‖ₑ) ∂volume :=
          lintegral_mono_ae hle
    _ = ENNReal.ofReal (3 * A) * ∫⁻ ξ : ES, ENNReal.ofReal (‖ξ‖ ^ n) * ‖a ξ‖ₑ ∂volume := htrans
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top (hd.mom n).lt_top

/- The `Rep`-namespace declarations of this module are written OUTSIDE the
`LittlewoodPaleyBlock` namespace: a multi-component `theorem Rep.foo` inside
`namespace Navier.Analysis.LittlewoodPaleyBlock` lands RELATIVE (duplication of
the `Navier.Analysis` prefix), so the `end`/`namespace` pair below brackets
these regions and the fully-qualified names at root resolve absolutely. -/
end Navier.Analysis.LittlewoodPaleyBlock

open Navier Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.WienerGradLog
open Navier.Analysis.WienerDatumSmooth
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPhysicalAssembly
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.WienerReality
open Navier.Analysis.Vorticity (staticCurl)
open Navier.Analysis.FourierL2Agree (integral_fourierInv_smul_eq)
open Navier.Analysis.LittlewoodPaleyBlock

/-- **D1 (Ḣ³ side).**  The `profH3` integrand is integrable for a represented
profile: the `WienerGradLog` header's finiteness claim is now a lemma, and the
Bochner-integral `0` convention cannot fire. -/
theorem Navier.Analysis.WienerRestartLeaf.Rep.integrable_profH3_integrand
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a) :
    Integrable (fun ξ : ES => ‖ξ‖ ^ 6 * ∑ i : Fin 3, ‖a ξ i‖ ^ 2) := by
  obtain ⟨A, hA, hb⟩ := hr.bdd
  exact integrable_profile_integrand hr.datum hA 6 hb

/-- **D1 (Fourier `L²` side).**  The `profL2` integrand is integrable. -/
theorem Navier.Analysis.WienerRestartLeaf.Rep.integrable_profL2_integrand
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a) :
    Integrable (fun ξ : ES => ∑ i : Fin 3, ‖a ξ i‖ ^ 2) := by
  obtain ⟨A, hA, hb⟩ := hr.bdd
  simpa using integrable_profile_integrand hr.datum hA 0 hb

/-- The `profH3` profile integral is finite in the lintegral sense. -/
theorem Navier.Analysis.WienerRestartLeaf.Rep.lintegral_profH3_integrand_lt_top
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a) :
    (∫⁻ ξ : ES, ‖‖ξ‖ ^ 6 * ∑ i : Fin 3, ‖a ξ i‖ ^ 2‖ₑ ∂volume) < ⊤ :=
  hasFiniteIntegral_iff_enorm.mp hr.integrable_profH3_integrand.hasFiniteIntegral

/-- The `profL2` profile integral is finite in the lintegral sense. -/
theorem Navier.Analysis.WienerRestartLeaf.Rep.lintegral_profL2_integrand_lt_top
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a) :
    (∫⁻ ξ : ES, ‖∑ i : Fin 3, ‖a ξ i‖ ^ 2‖ₑ ∂volume) < ⊤ :=
  hasFiniteIntegral_iff_enorm.mp hr.integrable_profL2_integrand.hasFiniteIntegral

namespace Navier.Analysis.LittlewoodPaleyBlock

/-! ## LP0 — the `fderiv` ↔ derivative-tower bridge on the `Rep` carrier -/

/-- First moments of a datum are integrable: `‖ξⱼ aᵢ‖ₑ ≤ ‖ξ‖ₑ ‖aᵢ‖ₑ` and the
`WDatum` first moment (`mom_coord 1`) absorbs it. -/
theorem integrable_moment {a : ES → ComplexSpace} (hd : WDatum a) (i j : Fin 3) :
    Integrable (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) := by
  have hmeas : AEStronglyMeasurable (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) volume :=
    ((Complex.measurable_ofReal.comp
        ((PiLp.continuous_apply 2 _ j).comp continuous_id).measurable).aestronglyMeasurable).mul
      (((measurable_pi_apply i).comp hd.meas).aestronglyMeasurable)
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have hle : (fun ξ : ES => ‖((ξ j : ℝ) : ℂ) * a ξ i‖ₑ) ≤ᵐ[volume]
      fun ξ : ES => ENNReal.ofReal ‖ξ‖ * ‖a ξ i‖ₑ := by
    refine Eventually.of_forall fun ξ => ?_
    show ‖((ξ j : ℝ) : ℂ) * a ξ i‖ₑ ≤ ENNReal.ofReal ‖ξ‖ * ‖a ξ i‖ₑ
    rw [enorm_mul]
    exact mul_le_mul' ((Navier.Analysis.WienerPointwiseODE.enorm_coord_le_norm ξ j).trans
      (ofReal_norm ξ).symm.le) le_rfl
  calc (∫⁻ ξ : ES, ‖↑(ξ.ofLp j) * a ξ i‖ₑ ∂volume)
      ≤ ∫⁻ ξ : ES, ENNReal.ofReal ‖ξ‖ * ‖a ξ i‖ₑ ∂volume := lintegral_mono_ae hle
    _ < ⊤ := by
        have hpow : (fun ξ : ES => ENNReal.ofReal ‖ξ‖ * ‖a ξ i‖ₑ)
            = (fun ξ : ES => ENNReal.ofReal (‖ξ‖ ^ 1) * ‖a ξ i‖ₑ) := by
              funext ξ
              rw [pow_one]
        rw [hpow]
        exact (hd.mom_coord 1 i).lt_top

end Navier.Analysis.LittlewoodPaleyBlock

open Navier Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.WienerGradLog
open Navier.Analysis.WienerDatumSmooth
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPhysicalAssembly
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.WienerReality
open Navier.Analysis.Vorticity (staticCurl)
open Navier.Analysis.FourierL2Agree (integral_fourierInv_smul_eq)
open Navier.Analysis.LittlewoodPaleyBlock

/-- The coordinate derivative of a represented field against the inverse-Fourier
derivative tower: the full complex derivative of the `i`-th profile linearity. -/
theorem Navier.Analysis.WienerRestartLeaf.Rep.fderiv_fourierInv_coord
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a) (x : Space) (i j : Fin 3) :
    fderiv ℝ (fun z : ES => 𝓕⁻ (fun ξ : ES => a ξ i) z) (euclidPoint x)
        (euclidPoint (basisVector j)) =
      (2 * Real.pi : ℂ) * Complex.I *
        𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) (euclidPoint x) := by
  have hfd := hasFDerivAt_fourierInv (hr.datum.integrable i)
    (fun jj => fun ξ : ES => ((ξ jj : ℝ) : ℂ) * a ξ i)
    (fun jj => ae_of_all volume fun _ξ => rfl) (fun jj => integrable_moment hr.datum i jj)
    (euclidPoint x)
  have hsum : ∑ b : Fin 3, (EuclideanSpace.proj b : ES →L[ℝ] ℝ)
        (EuclideanSpace.single j 1) •
        ((2 * Real.pi : ℂ) * Complex.I *
          𝓕⁻ (fun ξ : ES => ((ξ b : ℝ) : ℂ) * a ξ i) (euclidPoint x)) =
      (2 * Real.pi : ℂ) * Complex.I *
        𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) (euclidPoint x) := by
    refine (Finset.sum_eq_single j
      (fun b _ hb => by
        rw [show (EuclideanSpace.proj b : ES →L[ℝ] ℝ) (EuclideanSpace.single j 1) = 0
          from by simp [hb], zero_smul])
      (fun hn => absurd (Finset.mem_univ j) hn)).trans ?_
    rw [show (EuclideanSpace.proj j : ES →L[ℝ] ℝ) (EuclideanSpace.single j 1) = (1 : ℝ)
      from by simp, one_smul]
  have h := congrArg (fun L : ES →L[ℝ] ℂ => L (euclidPoint (basisVector j))) hfd.fderiv
  rw [euclidPoint_basisVector] at h
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply] at h
  exact h.trans hsum

namespace Navier.Analysis.LittlewoodPaleyBlock

/-- **LP0.**  For a represented field `v` (profile `a`), the coordinate derivative
appearing in `GradSupLogHyp` is the real part of the moment-profile inverse
transform: `∂ⱼvᵢ(x) = -(2π)⁻¹ Re (2πi · 𝓕⁻(ξⱼaᵢ)(x))` in Euclidean coordinates.
Bridge from `WienerSmoothPath.hasFDerivAt_fourierInv` through
`WienerPhysicalAssembly.fderiv_reCompVec_apply`. -/
theorem rep_fderiv_coord {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    (x : Space) (i j : Fin 3) :
    fderiv ℝ v x (basisVector j) i =
      -(1 / (2 * Real.pi)) * ((2 * Real.pi : ℂ) * Complex.I *
        𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) (euclidPoint x)).re := by
  have hG : ∀ k : Fin 3, ∀ y : ES,
      DifferentiableAt ℝ (fun z : ES => 𝓕⁻ (fun ξ : ES => a ξ k) z) y := by
    intro k y
    exact (hasFDerivAt_fourierInv (hr.datum.integrable k)
      (fun jj => fun ξ : ES => ((ξ jj : ℝ) : ℂ) * a ξ k)
      (fun jj => ae_of_all volume fun _ξ => rfl) (fun jj => integrable_moment hr.datum k jj)
      y).differentiableAt
  have key : fderiv ℝ (fun x' k => -(1 / (2 * Real.pi)) *
      ((fun z : ES => 𝓕⁻ (fun ξ : ES => a ξ k) z) (euclidPoint x')).re) x (basisVector j) i
      = -(1 / (2 * Real.pi)) *
        (fderiv ℝ (fun z : ES => 𝓕⁻ (fun ξ : ES => a ξ i) z) (euclidPoint x)
          (euclidPoint (basisVector j))).re :=
    fderiv_reCompVec_apply hG (-(1 / (2 * Real.pi))) x (basisVector j) i
  have hpe : DifferentiableAt ℝ (fun x' : Space => fun k : Fin 3 => -(1 / (2 * Real.pi)) *
      ((fun z : ES => 𝓕⁻ (fun ξ : ES => a ξ k) z) (euclidPoint x')).re) x := by
    refine differentiableAt_pi.mpr fun k => ?_
    exact (hasFDerivAt_reComp (hG k (euclidPoint x)) (-(1 / (2 * Real.pi)))).differentiableAt
  have hwv : v =ᶠ[𝓝 x] (fun x' k => -(1 / (2 * Real.pi)) *
      ((fun z : ES => 𝓕⁻ (fun ξ : ES => a ξ k) z) (euclidPoint x')).re) := by
    refine Eventually.of_forall fun x' => ?_
    show v x' = _
    rw [hr.eq x']
    show physOf a x' = _
    funext k
    rfl
  have hcv := hpe.hasFDerivAt.congr_of_eventuallyEq hwv
  rw [← hcv.fderiv] at key
  rw [hr.fderiv_fourierInv_coord x i j] at key
  exact key

/-! ## LP6 — the shell-sum envelope (standalone real analysis, no carrier) -/

/-- `min(1, X) ≤ Xᶿ` for `0 < θ ≤ 1`, `0 ≤ X`: the standard two-point check
(`X ≥ 1`: right side `≥ 1`; `X < 1`: antitonicity of the exponent on `[0,1]`). -/
theorem min_one_le_rpow {X : ℝ} (hX : 0 ≤ X) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    min 1 X ≤ X ^ θ := by
  by_cases h : (1 : ℝ) ≤ X
  · rw [min_eq_left h]
    have : (1 : ℝ) ^ θ ≤ X ^ θ := Real.rpow_le_rpow (by linarith) h (by linarith)
    rwa [Real.one_rpow] at this
  · rw [min_eq_right (le_of_lt (lt_of_not_ge h))]
    have : X ^ (1 : ℝ) ≤ X ^ θ :=
      Real.rpow_le_rpow_of_exponent_ge' hX (le_of_lt (lt_of_not_ge h)) hθ0.le hθ1
    rwa [Real.rpow_one] at this

/-- **LP6 (high-shell envelope).**  For `y > 0`, `Y ≥ 0`:
`Σ'ⱼ min(y, Y·4⁻ʲ) ≤ 8·y·(1 + log(1 + Y/y))`.  The `θ = 1/log(1+a)` trick turns
each `min` into a power and the sum into a geometric series
(`min(1, a·4⁻ʲ) ≤ (a·4⁻ʲ)ᶿ`, `∑' = aᶿ/(1−4⁻ᶿ)`), so the envelope grows
logarithmically, matching the `GradSupLogHyp` right side.  (An earlier
`√(yY)`-tally attempt is *rejected*: `√t` dominates `log t`, so it cannot bound
a logarithmic envelope from above.) -/
theorem shellSum_log_high {y Y : ℝ} (hy : 0 < y) (hY : 0 ≤ Y) :
    (∑' j : ℕ, min y (Y * ((1 : ℝ) / 4) ^ j)) ≤
      8 * y * (1 + Real.log (1 + Y / y)) := by
  have hf : (∑' j : ℕ, min y (Y * ((1 : ℝ) / 4) ^ j))
      = y * ∑' j : ℕ, min 1 ((Y / y) * ((1 : ℝ) / 4) ^ j) := by
    refine (tsum_congr fun j => ?_).trans tsum_mul_left
    have hc : Y * ((1 : ℝ) / 4) ^ j = y * ((Y / y) * ((1 : ℝ) / 4) ^ j) := by
      field_simp [hy.ne']
    calc min y (Y * ((1 : ℝ) / 4) ^ j) = min (y * 1) (Y * ((1 : ℝ) / 4) ^ j) := by rw [mul_one]
      _ = min (y * 1) (y * ((Y / y) * ((1 : ℝ) / 4) ^ j)) := by rw [hc]
      _ = y * min 1 ((Y / y) * ((1 : ℝ) / 4) ^ j) := (mul_min_of_nonneg 1 _ hy.le).symm
  rw [hf]
  set a := Y / y
  have ha0 : 0 ≤ a := div_nonneg hY hy.le
  have hL0 : 0 ≤ Real.log (1 + a) :=
    Real.log_nonneg (le_add_of_nonneg_right ha0)
  suffices hmain : (∑' j : ℕ, min 1 (a * ((1 : ℝ) / 4) ^ j)) ≤
      8 * (1 + Real.log (1 + a)) by
    refine le_trans (mul_le_mul_of_nonneg_left hmain hy.le) ?_
    rw [← mul_assoc, mul_comm y 8]
  by_cases h4 : a ≤ 4
  · -- `a ≤ 4`: direct geometric majorization of `min 1 (a·4⁻ʲ) ≤ a·4⁻ʲ`
    have hsumm : Summable (fun j : ℕ => a * ((1 : ℝ) / 4) ^ j) :=
      Summable.mul_left a (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    have hle : ∀ j : ℕ, min 1 (a * ((1 : ℝ) / 4) ^ j) ≤ a * ((1 : ℝ) / 4) ^ j :=
      fun j => min_le_right 1 _
    have h1 : (∑' j : ℕ, min 1 (a * ((1 : ℝ) / 4) ^ j)) ≤
        ∑' j : ℕ, a * ((1 : ℝ) / 4) ^ j := by
      refine (Summable.of_nonneg_of_le (fun j => ?_) hle hsumm).tsum_le_tsum hle hsumm
      exact le_min (by norm_num) (mul_nonneg ha0 (pow_nonneg (by norm_num) j))
    have h2 : (∑' j : ℕ, a * ((1 : ℝ) / 4) ^ j) = a * ((1 - (1 : ℝ) / 4)⁻¹) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    have h3 : a * ((1 - (1 : ℝ) / 4)⁻¹) ≤ 4 * (4 / 3) := by
      rw [show ((1 - (1 : ℝ) / 4)⁻¹ : ℝ) = 4 / 3 by norm_num]
      nlinarith
    have h4' : (4 : ℝ) * (4 / 3) ≤ 8 := by norm_num
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ 8 := h3.trans h4'
      _ ≤ 8 * (1 + Real.log (1 + a)) := by nlinarith [hL0]
  · -- `4 < a`: the θ-trick
    set L := Real.log (1 + a) with hL
    have hL1 : 1 ≤ L := by
      have h5 : Real.log (1 + a) ≥ Real.log 5 := Real.log_le_log (by linarith) (by linarith)
      have he : Real.exp 1 ≤ 5 := by
        have := Real.exp_one_lt_d9
        linarith
      have h51 : 1 ≤ Real.log 5 := by
        have h := Real.log_le_log (Real.exp_pos 1) he
        rwa [Real.log_exp] at h
      linarith
    set θ := 1 / L with hθ
    have hθ0 : 0 < θ := by rw [hθ]; positivity
    have hθ1 : θ ≤ 1 := by rw [hθ]; exact (div_le_one (by linarith)).mpr hL1
    have ha' : 0 < a := by linarith
    have hterm : ∀ j : ℕ, min 1 (a * ((1 : ℝ) / 4) ^ j) ≤
        (a * ((1 : ℝ) / 4) ^ j) ^ θ :=
      fun j => min_one_le_rpow (mul_nonneg ha0 (pow_nonneg (by norm_num) j)) hθ0 hθ1
    have hpow : ∀ j : ℕ, (a * ((1 : ℝ) / 4) ^ j) ^ θ =
        a ^ θ * (((1 : ℝ) / 4) ^ θ) ^ j := by
      intro j
      rw [Real.mul_rpow ha0 (pow_nonneg (by norm_num) j)]
      have hr4 : (((1 : ℝ) / 4) ^ (j : ℕ)) ^ θ = (((1 : ℝ) / 4) ^ θ) ^ (j : ℕ) :=
        (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4) θ j).symm
      rw [hr4]
    have hrpowθ : ((1 : ℝ) / 4) ^ θ < 1 := by
      have h : ((1 : ℝ) / 4) ^ θ = Real.exp (-(θ * Real.log 4)) := by
        rw [Real.rpow_def_of_pos (by norm_num), show Real.log ((1 : ℝ) / 4) = -(Real.log 4)
          by rw [Real.log_div (by norm_num) (by norm_num)]; norm_num]
        ring_nf
      rw [h]
      have hu : 0 < θ * Real.log 4 := mul_pos hθ0 (Real.log_pos (by norm_num))
      have := Real.exp_lt_exp.mpr (by linarith : -(θ * Real.log 4) < (0 : ℝ))
      simpa using this
    have hsumm : Summable (fun j : ℕ => (a * ((1 : ℝ) / 4) ^ j) ^ θ) := by
      have hsum0 : Summable (fun j : ℕ => (((1 : ℝ) / 4) ^ θ) ^ j) :=
        summable_geometric_of_lt_one
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4) θ) hrpowθ
      have : (fun j : ℕ => (a * ((1 : ℝ) / 4) ^ j) ^ θ) = fun j => a ^ θ * (((1 : ℝ) / 4) ^ θ) ^ j :=
        funext hpow
      rw [this]
      exact Summable.mul_left (a ^ θ) hsum0
    have h1 : (∑' j : ℕ, min 1 (a * ((1 : ℝ) / 4) ^ j)) ≤
        ∑' j : ℕ, (a * ((1 : ℝ) / 4) ^ j) ^ θ :=
      (Summable.of_nonneg_of_le
          (fun j => le_min (by norm_num) (mul_nonneg ha0 (pow_nonneg (by norm_num) j)))
          hterm hsumm).tsum_le_tsum hterm hsumm
    have h2 : (∑' j : ℕ, (a * ((1 : ℝ) / 4) ^ j) ^ θ) =
        a ^ θ * (1 - ((1 : ℝ) / 4) ^ θ)⁻¹ := by
      rw [tsum_congr hpow, tsum_mul_left,
        tsum_geometric_of_lt_one
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4) θ) hrpowθ]
    have h3 : a ^ θ ≤ 3 := by
      have h : a ^ θ = Real.exp (Real.log a * (1 / L)) := by
        rw [Real.rpow_def_of_pos ha', hθ]
      rw [h]
      refine (Real.exp_le_exp.mpr ?_).trans (show Real.exp 1 ≤ 3 from ?_)
      · have h2 : Real.log a ≤ L := by
          have := Real.log_le_log (by linarith) (by linarith : a ≤ 1 + a)
          rwa [← hL] at this
        have hL0' : 0 < L := by linarith [hL1]
        rw [one_div]
        exact (div_le_one hL0').mpr h2
      · linarith [Real.exp_one_lt_d9]
    have hu0 : 0 < θ * Real.log 4 := mul_pos hθ0 (Real.log_pos (by norm_num))
    have hu1 : θ * Real.log 4 ≤ 1 := by
      have hlog : θ * Real.log 4 = Real.log 4 / L := by
        rw [hθ]; ring
      rw [hlog]
      refine (div_le_one (by linarith)).mpr ?_
      have h45 : Real.log 4 ≤ Real.log (1 + a) :=
        Real.log_le_log (by norm_num) (by linarith)
      rw [← hL] at h45
      linarith
    have hden : 1 - ((1 : ℝ) / 4) ^ θ ≥ (θ * Real.log 4) / 2 := by
      have hr : ((1 : ℝ) / 4) ^ θ = Real.exp (-(θ * Real.log 4)) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
        rw [show Real.log ((1 : ℝ) / 4) = -(Real.log 4)
          by rw [Real.log_div (by norm_num) (by norm_num)]; norm_num]
        ring_nf
      rw [hr]
      have hexp : Real.exp (θ * Real.log 4) ≥ 1 + θ * Real.log 4 :=
        by linarith [Real.add_one_le_exp (θ * Real.log 4)]
      have hinv : Real.exp (-(θ * Real.log 4)) ≤ (1 + θ * Real.log 4)⁻¹ := by
        rw [Real.exp_neg]
        refine inv_le_inv₀ (by positivity) (by positivity) |>.mpr ?_
        linarith
      have h20 : 1 - Real.exp (-(θ * Real.log 4)) ≥
          (θ * Real.log 4) / (1 + θ * Real.log 4) := by
        have : 1 - (1 + θ * Real.log 4)⁻¹ = (θ * Real.log 4) / (1 + θ * Real.log 4) := by
          field_simp
          ring
        linarith
      have hmid : (θ * Real.log 4) / 2 ≤ (θ * Real.log 4) / (1 + θ * Real.log 4) := by
        refine (div_le_div_iff₀ (by norm_num) (by linarith [hu0])).mpr ?_
        nlinarith [hu0, hu1]
      exact hmid.trans h20
    have h4 : (1 - ((1 : ℝ) / 4) ^ θ)⁻¹ ≤ 2 / (θ * Real.log 4) := by
      have hp : 0 < 1 - ((1 : ℝ) / 4) ^ θ := by nlinarith [hden, hu0]
      have hu2 : 0 < θ * Real.log 4 / 2 := by nlinarith
      calc (1 - ((1 : ℝ) / 4) ^ θ)⁻¹ ≤ (θ * Real.log 4 / 2)⁻¹ := (inv_le_inv₀ hp hu2).mpr hden
        _ = 2 / (θ * Real.log 4) := by field_simp
    have h5 : a ^ θ * (1 - ((1 : ℝ) / 4) ^ θ)⁻¹ ≤ 3 * (2 / (θ * Real.log 4)) := by
      refine (mul_le_mul_of_nonneg_right h3 ?_).trans
        (mul_le_mul_of_nonneg_left h4 (by norm_num))
      have hp : 0 < 1 - ((1 : ℝ) / 4) ^ θ := by nlinarith [hden, hu0]
      exact inv_nonneg.mpr hp.le
    have h6 : 3 * (2 / (θ * Real.log 4)) = 6 * L / Real.log 4 := by
      have hθ2 : θ = 1 / L := rfl
      rw [hθ2]
      field_simp
      norm_num
    have h7 : 6 * L / Real.log 4 ≤ 6 * L := by
      have h14 : 1 ≤ Real.log 4 := by
        have h := Real.log_le_log (Real.exp_pos 1)
          (by have := Real.exp_one_lt_d9; linarith : Real.exp 1 ≤ 4)
        rwa [Real.log_exp] at h
      refine (div_le_iff₀ (by linarith [h14])).mpr ?_
      nlinarith [h14, hL1]
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h5
      _ = _ := h6
      _ ≤ 6 * L := h7
      _ ≤ 8 * (1 + L) := by nlinarith [hL0]

/-- **Canonical LP6 name (coordinator packet 2026-09-23).**  `blockEnvelopeLogBound`
is the single-envelope LP6 statement `Σ'ⱼ min(y, Y·4⁻ʲ) ≤ 8·y·(1 + log(1 + Y/y))`;
it binds to `shellSum_log_high` (the `4⁻ʲ` shell base absorbs the constant relative
to the triage's `2⁻ᵏ` convention, so `C = 8`).  The two-shell double-sum corollary
is `shellSum_log`. -/
theorem blockEnvelopeLogBound {y Y : ℝ} (hy : 0 < y) (hY : 0 ≤ Y) :
    (∑' j : ℕ, min y (Y * ((1 : ℝ) / 4) ^ j)) ≤ 8 * y * (1 + Real.log (1 + Y / y)) :=
  shellSum_log_high hy hY

/-- **LP6.**  Shell-sum optimization to the two log terms of `GradSupLogHyp`:
there is one constant `C ≥ 0` such that for every scale budget `y > 0` and
envelopes `Y, E ≥ 0`,
`Σⱼ min(y, Y·4⁻ʲ) + Σⱼ min(y, E·4⁻ʲ) ≤ C·y·(1 + log(1+Y/y) + log(1+E/y))`.

**T-003 probe note (BARRIERS R5 kill class).**  The adversarial probe
`experiments/exact_symmetrized_triad_scan.py` was run before this statement was
fixed (2026-09-23): status `FALSIFICATION_ONLY`, 44 triads, and its two kill
witnesses (an equal-radius configuration where the selected output transfer
cancels exactly, `constant_weight_sum = 0` with `squared_frequency_weighted_sum
= 0`; and an unequal-radius configuration where it does not, `squared_frequency_
weighted_sum = 1` with rates `(0, -1, 1)`).  Both target claims about *signed*
shell-to-shell transfer/gain.  This envelope contains no sign: every term is a
nonnegative `min` of absolute quantities and the bound is monotone in each
shell, so no cancellation is claimed and the R5 kill class cannot fire — the
statement is kept in its naive summation form.  The unequal-radius witness is
recorded as positive evidence for the LP2 direction: the envelope cannot be
improved by cancellation, which is exactly why the block kernels must be bounded
in `L¹` (LP2), not their signed sums.  Consistent with F-025, this is the
*physical-side* envelope; no Fourier-`L¹`-mass form of the bound is asserted
here. -/
theorem shellSum_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y Y E : ℝ), 0 < y → 0 ≤ Y → 0 ≤ E →
      (∑' j : ℕ, min y (Y * ((1 : ℝ) / 4) ^ j)) +
          (∑' j : ℕ, min y (E * ((1 : ℝ) / 4) ^ j)) ≤
        C * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) := by
  refine ⟨16, by positivity, fun y Y E hy hY hE => ?_⟩
  have h1 := shellSum_log_high hy hY
  have h2 := shellSum_log_high hy hE
  have L1 : 0 ≤ Real.log (1 + Y / y) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hY hy.le))
  have L2 : 0 ≤ Real.log (1 + E / y) :=
    Real.log_nonneg (le_add_of_nonneg_right (div_nonneg hE hy.le))
  calc (∑' j : ℕ, min y (Y * ((1 : ℝ) / 4) ^ j)) + _ ≤ _ + _ := add_le_add h1 h2
    _ ≤ 8 * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) +
        8 * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) := by
      refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity))
        (mul_le_mul_of_nonneg_left ?_ (by positivity)) <;> nlinarith
    _ = 16 * y * (1 + Real.log (1 + Y / y) + Real.log (1 + E / y)) := by ring

/-! ## The `L¹` Fourier injection (needed for LP7; Mathlib has none at this pinning) -/

theorem fourierInv_neg_fn {f : ES → ℂ} (_hf : Integrable f) (x : ES) :
    𝓕⁻ (fun ξ => -f ξ) x = -𝓕⁻ f x := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, ← integral_neg]
  exact integral_congr_ae (Eventually.of_forall fun v => smul_neg _ _)

theorem fourierInv_sub_fn {f g : ES → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ES) :
    𝓕⁻ (fun ξ => f ξ - g ξ) x = 𝓕⁻ f x - 𝓕⁻ g x := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq,
    ← integral_sub (integrable_fourierChar_smul hf x) (integrable_fourierChar_smul hg x)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  show 𝐞 (inner ℝ v x) • (f v - g v) = 𝐞 (inner ℝ v x) • f v - 𝐞 (inner ℝ v x) • g v
  rw [smul_sub]

/-- **`L¹` Fourier injection.**  If the integral inverse transform of an
integrable profile vanishes everywhere, the profile vanishes almost everywhere.
Route: the repo's self-adjointness `FourierL2Agree.integral_fourierInv_smul_eq`
against Schwartz images of test bumps (`fourierInv_fourier` on `𝓢`) plus the
fundamental lemma `ae_eq_of_integral_contDiff_smul_eq`; this mirrors
`FourierL2Agree.fourierInv_toLp_ae_eq` without the `L²` side. -/
theorem fourierInv_eq_zero {f : ES → ℂ} (hf : Integrable f) (hz : ∀ x, 𝓕⁻ f x = 0) :
    f =ᵐ[volume] (0 : ES → ℂ) := by
  refine ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable locallyIntegrable_zero ?_
  intro g hg hsupp
  set gc : ES → ℂ := fun x => (g x : ℂ) with hgc
  have hgcd : ContDiff ℝ ∞ gc := Complex.ofRealCLM.contDiff.comp hg
  have hgcs : HasCompactSupport gc := hsupp.comp_left Complex.ofReal_zero
  set G : 𝓢(ES, ℂ) := hgcs.toSchwartzMap hgcd with hG
  have hGapp : ∀ x, G x = (g x : ℂ) := fun x => rfl
  set H : 𝓢(ES, ℂ) := 𝓕 G with hH
  have hphi : ∀ x, 𝓕⁻ (⇑H) x = (g x : ℂ) := by
    intro x
    have hfun : (fun ξ : ES => 𝓕 G ξ) = 𝓕 (⇑G) := by
      funext ξ
      simp only [SchwartzMap.fourier_coe]
    have hfI : Integrable (⇑G) volume := G.integrable
    have hfcI : Integrable (𝓕 ⇑G) volume := by
      rw [← hfun]
      exact (𝓕 G).integrable
    have hinv : 𝓕⁻ (𝓕 ⇑G) = ⇑G :=
      Continuous.fourierInv_fourier_eq G.continuous hfI hfcI
    calc 𝓕⁻ (⇑H) x = 𝓕⁻ (fun ξ : ES => 𝓕 G ξ) x := by rw [hH]
      _ = 𝓕⁻ (𝓕 ⇑G) x := congrArg (fun k : ES → ℂ => 𝓕⁻ k x) hfun
      _ = ⇑G x := congrFun hinv x
      _ = (g x : ℂ) := hGapp x
  calc ∫ x, g x • f x = ∫ x, gc x • f x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        rw [hgc]
        simp only [Complex.real_smul, smul_eq_mul]
      _ = ∫ x, G x • f x := integral_congr_ae
        (Eventually.of_forall fun x => congrArg (fun c => c • f x) (hGapp x))
      _ = ∫ x, 𝓕⁻ (⇑H) x • f x := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show G x • f x = 𝓕⁻ (⇑H) x • f x
        rw [hphi x, hGapp x]
      _ = ∫ x, H x • 𝓕⁻ f x := integral_fourierInv_smul_eq H hf
      _ = 0 := by
        have heq : (fun x => H x • 𝓕⁻ f x) = fun _ => 0 := by
          funext x
          rw [hz x, smul_zero]
        rw [heq]
        simp
      _ = ∫ x, g x • (0 : ES → ℂ) x := by simp

/-! ## LP7 — the `y = 0` curl-free edge case -/

/-- Antisymmetry of the moment profile of real data: `reflC(ξⱼaᵢ) =ᵐ -ξⱼaᵢ`
(the Fourier image of a real field has Hermitian symmetry; the real factor `ξⱼ`
is odd). -/
theorem reflC_moment {a : ES → ComplexSpace} (hd : WDatum a) (i j : Fin 3) :
    reflC (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) =ᵐ[volume]
      fun ξ : ES => -(((ξ j : ℝ) : ℂ) * a ξ i) := by
  filter_upwards [hd.sym i] with ξ h
  show reflC (fun ξ => ((ξ j : ℝ) : ℂ) * a ξ i) ξ = _
  rw [reflC]
  show conj ((((-ξ) j : ℝ) : ℂ) * a (-ξ) i) = -(((ξ j : ℝ) : ℂ) * a ξ i)
  have hj : (((-ξ) j : ℝ) : ℂ) = -((ξ j : ℝ) : ℂ) := by
    have h1 : (-ξ) j = -ξ j := rfl
    rw [h1, Complex.ofReal_neg]
  rw [hj, h, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal, neg_mul]

/-- The inverse transform of a real datum's moment profile is purely imaginary. -/
theorem moment_im {a : ES → ComplexSpace} (hd : WDatum a) (i j : Fin 3) (z : ES) :
    (𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) z).re = 0 := by
  have hi := integrable_moment hd i j
  have hconj : conj (𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) z) =
      𝓕⁻ (fun ξ : ES => -(((ξ j : ℝ) : ℂ) * a ξ i)) z := by
    rw [conj_fourierInv, ← fourierInv_congr (reflC_moment hd i j) z]
  rw [fourierInv_neg_fn hi z] at hconj
  have hre := congrArg Complex.re hconj
  rw [Complex.conj_re, Complex.neg_re] at hre
  linarith

/-- Component `0` of `staticCurl` in Mathlib's `⨯₃` convention. -/
theorem staticCurl_comp_zero (u : VelocityField) (x : Space) :
    staticCurl u x 0 =
      (fderiv ℝ u x (basisVector 1)) 2 - (fderiv ℝ u x (basisVector 2)) 1 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

/-- Component `1` of `staticCurl`. -/
theorem staticCurl_comp_one (u : VelocityField) (x : Space) :
    staticCurl u x 1 =
      (fderiv ℝ u x (basisVector 2)) 0 - (fderiv ℝ u x (basisVector 0)) 2 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

/-- Component `2` of `staticCurl`. -/
theorem staticCurl_comp_two (u : VelocityField) (x : Space) :
    staticCurl u x 2 =
      (fderiv ℝ u x (basisVector 0)) 1 - (fderiv ℝ u x (basisVector 1)) 0 := by
  simp only [staticCurl, Fin.sum_univ_three, Finset.sum_apply]
  simp [basisVector, cross_apply]
  ring

/-- `euclidPoint` is the equivalence `WithLp.equiv`. -/
theorem euclidPoint_surjective : Function.Surjective (euclidPoint) :=
  fun z => ⟨WithLp.ofLp z, rfl⟩

end Navier.Analysis.LittlewoodPaleyBlock

open Navier Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.WienerRestartLeaf
open Navier.Analysis.WienerGradLog
open Navier.Analysis.WienerDatumSmooth
open Navier.Analysis.WienerSmoothPath
open Navier.Analysis.WienerPhysicalAssembly
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity (euclidPoint)
open Navier.Analysis.WienerReality
open Navier.Analysis.Vorticity (staticCurl)
open Navier.Analysis.FourierL2Agree (integral_fourierInv_smul_eq)
open Navier.Analysis.LittlewoodPaleyBlock

/-- The coordinate derivative is the *imaginary part* of the moment inverse
transform: from `rep_fderiv_coord`, `-(2π)⁻¹Re(2πi·w) = w.im`. -/
theorem Navier.Analysis.WienerRestartLeaf.Rep.fderiv_coord_im
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    (x : Space) (i j : Fin 3) :
    fderiv ℝ v x (basisVector j) i =
      (𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) (euclidPoint x)).im := by
  have hw : ∀ w : ℂ,
      -(1 / (2 * Real.pi)) * ((2 * Real.pi : ℂ) * Complex.I * w).re = w.im := by
    intro w
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hc : ((2 * Real.pi : ℂ) * Complex.I * w).re = -(2 * Real.pi) * w.im := by
      have h2 : (2 : ℂ) = ↑(2 : ℝ) := by norm_cast
      rw [h2, ← Complex.ofReal_mul, mul_assoc, Complex.mul_re, Complex.mul_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hc]
    field_simp [hpi]
  rw [rep_fderiv_coord hr x i j, hw]

/-- For a curl-free represented field, the moment profiles commute almost surely:
`∀ᵐ ξ, ξᵣ·aᵢ = ξᵢ·aᵣ` (Jacobian symmetry through
`fourierInv_eq_zero`). -/
theorem Navier.Analysis.WienerRestartLeaf.Rep.moment_pair_ae
    {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    (hcurl : ∀ x : Space, staticCurl v x = 0) :
    ∀ᵐ ξ ∂(volume : Measure ES), ∀ r i : Fin 3,
      ((ξ r : ℝ) : ℂ) * a ξ i = ((ξ i : ℝ) : ℂ) * a ξ r := by
  have hd : WDatum a := hr.datum
  have pair (p q : Fin 3) (hpq : p ≠ q)
      (hD : ∀ x : Space, fderiv ℝ v x (basisVector p) q = fderiv ℝ v x (basisVector q) p) :
      (fun ξ : ES => ((ξ p : ℝ) : ℂ) * a ξ q) =ᵐ[volume]
        fun ξ : ES => ((ξ q : ℝ) : ℂ) * a ξ p := by
    have hpi := integrable_moment hr.datum q p
    have hqi := integrable_moment hr.datum p q
    have him : ∀ x : Space, (𝓕⁻ (fun ξ : ES => ((ξ p : ℝ) : ℂ) * a ξ q) (euclidPoint x)).im =
        (𝓕⁻ (fun ξ : ES => ((ξ q : ℝ) : ℂ) * a ξ p) (euclidPoint x)).im := by
      intro x
      rw [← hr.fderiv_coord_im x q p, ← hr.fderiv_coord_im x p q, hD x]
    have hz : ∀ z : ES, 𝓕⁻ (fun ξ : ES => ((ξ p : ℝ) : ℂ) * a ξ q -
        ((ξ q : ℝ) : ℂ) * a ξ p) z = 0 := by
      intro z
      obtain ⟨x, hx⟩ := Navier.Analysis.LittlewoodPaleyBlock.euclidPoint_surjective z
      subst hx
      rw [fourierInv_sub_fn hpi hqi]
      refine Complex.ext ?_ ?_
      · rw [Complex.sub_re, moment_im hd q p, moment_im hd p q]; simp
      · rw [Complex.sub_im, Complex.zero_im]; linarith [him x]
    filter_upwards [fourierInv_eq_zero (hpi.sub hqi) hz] with ξ h
    exact sub_eq_zero.mp h
  have h0 : ∀ x : Space, fderiv ℝ v x (basisVector 1) 2 = fderiv ℝ v x (basisVector 2) 1 := by
    intro x
    have hx := congrFun (hcurl x) 0
    rw [Navier.Analysis.LittlewoodPaleyBlock.staticCurl_comp_zero, Pi.zero_apply, sub_eq_zero] at hx
    exact hx
  have h1 : ∀ x : Space, fderiv ℝ v x (basisVector 2) 0 = fderiv ℝ v x (basisVector 0) 2 := by
    intro x
    have hx := congrFun (hcurl x) 1
    rw [Navier.Analysis.LittlewoodPaleyBlock.staticCurl_comp_one, Pi.zero_apply, sub_eq_zero] at hx
    exact hx
  have h2 : ∀ x : Space, fderiv ℝ v x (basisVector 0) 1 = fderiv ℝ v x (basisVector 1) 0 := by
    intro x
    have hx := congrFun (hcurl x) 2
    rw [Navier.Analysis.LittlewoodPaleyBlock.staticCurl_comp_two, Pi.zero_apply, sub_eq_zero] at hx
    exact hx
  filter_upwards [pair 1 2 (by decide) h0, pair 2 0 (by decide) h1, pair 0 1 (by decide) h2]
    with ξ hA hB hC
  intro r i
  fin_cases r <;> fin_cases i <;>
    first
      | rfl
      | exact hA
      | exact hB
      | exact hC
      | exact hA.symm
      | exact hB.symm
      | exact hC.symm

namespace Navier.Analysis.LittlewoodPaleyBlock

/-- **LP7.**  The `y = 0` case of `GradSupLogHyp`: a represented field whose
vorticity vanishes pointwise (in the `officialEuclideanNorm` budget at `y = 0`)
has vanishing derivative at every point and coordinate.  Algebra: a symmetric
Jacobian plus transversality forces `(‖ξ‖²:ℂ)·aⱼ = 0` a.e., hence every moment
profile `ξⱼaᵢ` vanishes a.e. — so every derivative, being the imaginary part of
its inverse transform, is zero. -/
theorem rep_curlfree_grad_zero {v : VelocityField} {a : ES → ComplexSpace} (hr : Rep v a)
    (hω : ∀ x : Space, Navier.Analysis.OfficialABEncoding.officialEuclideanNorm
      (staticCurl v x) ≤ 0) :
    ∀ (x : Space) (i j : Fin 3), fderiv ℝ v x (basisVector j) i = 0 := by
  have hcurl : ∀ x : Space, staticCurl v x = 0 := by
    intro x
    exact (Navier.Analysis.Vorticity.officialEuclideanNorm_eq_zero_iff (staticCurl v x)).mp
      (le_antisymm (hω x) (Navier.Analysis.OfficialABEncoding.officialEuclideanNorm_nonneg _))
  have hpair := hr.moment_pair_ae hcurl
  have hzero : ∀ᵐ ξ ∂(volume : Measure ES), ∀ j i : Fin 3,
      ((ξ j : ℝ) : ℂ) * a ξ i = 0 := by
    filter_upwards [hr.div, hpair] with ξ hdiv hp
    intro j i
    by_cases hξ : ξ = 0
    · subst hξ
      simp
    · -- (Σᵣ ξᵣ²:ℂ)·aᵢ = Σᵣ ξᵢ(ξᵣaᵣ) = ξᵢ·0 = 0 and the factor is nonzero
      have hfac : ∑ r : Fin 3, ((ξ r : ℝ) : ℂ) * ((ξ r : ℝ) : ℂ) ≠ 0 := by
        intro h
        have hsum : (∑ r : Fin 3, (ξ r * ξ r : ℝ) : ℂ) = 0 := by
          have h2 : (∑ r : Fin 3, (ξ r * ξ r : ℝ) : ℂ)
              = ∑ r : Fin 3, ((ξ r : ℝ) : ℂ) * ((ξ r : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [Complex.ofReal_mul]
          rw [h2, h]
        have hre : ∑ r : Fin 3, (ξ r * ξ r : ℝ) = 0 := by
          rw [← Complex.ofReal_eq_zero, Complex.ofReal_sum]
          exact hsum
        apply hξ
        ext r
        have hle := Finset.single_le_sum (f := fun s : Fin 3 => ξ s * ξ s)
          (fun s _ => mul_self_nonneg (ξ s)) (Finset.mem_univ r)
        have hsq : ξ r * ξ r = 0 :=
          le_antisymm (hle.trans_eq hre) (mul_self_nonneg (ξ r))
        rwa [mul_self_eq_zero] at hsq
      have hmul : (∑ r : Fin 3, ((ξ r : ℝ) : ℂ) * ((ξ r : ℝ) : ℂ)) * a ξ i = 0 := by
        calc (∑ r : Fin 3, ((ξ r : ℝ) : ℂ) * ((ξ r : ℝ) : ℂ)) * a ξ i
            = ∑ r : Fin 3, (((ξ r : ℝ) : ℂ) * ((ξ r : ℝ) : ℂ)) * a ξ i :=
                Finset.sum_mul _ _ _
          _ = ∑ r : Fin 3, ((ξ r : ℝ) : ℂ) * (((ξ i : ℝ) : ℂ) * a ξ r) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [mul_assoc, hp r i]
          _ = ((ξ i : ℝ) : ℂ) * ∑ r : Fin 3, ((ξ r : ℝ) : ℂ) * a ξ r := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun r _ => mul_left_comm _ _ _
          _ = ((ξ i : ℝ) : ℂ) * 0 := congrArg _ hdiv
          _ = 0 := mul_zero _
      have hai : a ξ i = 0 := (mul_eq_zero.mp hmul).resolve_left hfac
      rw [hai, mul_zero]
  intro x i j
  have hgz : (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) =ᵐ[volume] (0 : ES → ℂ) := by
    filter_upwards [hzero] with ξ h
    exact h j i
  have hz : ∀ z : ES, 𝓕⁻ (fun ξ : ES => ((ξ j : ℝ) : ℂ) * a ξ i) z = 0 := fun z =>
    (fourierInv_congr hgz z).trans (fourierInv_zero_fun z)
  rw [hr.fderiv_coord_im x i j, hz (euclidPoint x), Complex.zero_im]

end Navier.Analysis.LittlewoodPaleyBlock

set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyBlock.rep_fderiv_coord
set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyBlock.shellSum_log
set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyBlock.shellSum_log_high
set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyBlock.blockEnvelopeLogBound
set_option pp.fullNames true in
#check @Navier.Analysis.LittlewoodPaleyBlock.rep_curlfree_grad_zero
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerRestartLeaf.Rep.integrable_profH3_integrand
set_option pp.fullNames true in
#print axioms Navier.Analysis.WienerRestartLeaf.Rep.integrable_profL2_integrand
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyBlock.rep_fderiv_coord
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyBlock.shellSum_log
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyBlock.shellSum_log_high
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyBlock.blockEnvelopeLogBound
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyBlock.rep_curlfree_grad_zero
set_option pp.fullNames true in
#print axioms Navier.Analysis.LittlewoodPaleyBlock.fourierInv_eq_zero
