import Navier.Analysis.LeiLinBilinear
import Navier.Analysis.LeiLinLinearEstimate
import Navier.Analysis.CriticalMildHeatTimeKernel

/-!
# Spacetime mixed-norm leaves for the Lei–Lin route

`LeiLinBilinear` records the fixed-time estimate with constant `1/(4ν)` and names
the missing time Cauchy–Schwarz step that upgrades it to
`L¹_t 𝒳^{-1}` control of the nonlinearity.  `LeiLinLinearEstimate` supplies the
linear identities.  This module closes those leaves:

1. `integral_sqrt_mul_le` — Hölder/`L²` Cauchy–Schwarz in time for nonnegative
   integrands;
2. `integral_bilinear_Xm1_le` — spacetime bilinear bound
   `∫₀^∞ ‖B(u,v)‖_{𝒳^{-1}} ≤ (1/(4ν)) (Aᵤ + ν∫‖u‖₁)(Aᵥ + ν∫‖v‖₁)`
   under `L∞_t` majorants of the critical norms;
3. `heat_mixedTimeBound` — free evolution satisfies the spacetime mixed majorant
   `‖f‖_{𝒳^{-1}}` on each half (hence sum `2‖f‖_{𝒳^{-1}}`).
4. `terminal_X1_le_of_backward_sqrt_modulus` — the exact repair for terminal
   sampling: trailing integrated `𝒳¹` control plus a backward square-root time
   modulus bounds the terminal `𝒳¹` value.

These feed the coercive critical-norm path for
`CriticalMildMixedTerminalBound` / `navier.bounded-chain-direct-limit`.  No
Navier–Stokes solution is constructed here, and the terminal-bound hypothesis
is not claimed discharged for arbitrary large data.

Reference: Z. Lei and F. Lin, CPAM 64 (2011) 1297–1304, Sec. 2.
-/

set_option autoImplicit false
noncomputable section

namespace Navier.Analysis.LeiLinTimeMixed

open MeasureTheory Set
open Navier.Analysis.LeiLinSpace
open Navier.Analysis.LeiLinBilinear
open Navier.Analysis.LeiLinLinearEstimate
open Navier.Analysis.WienerAlgebraConvolution
open Navier.Analysis.CriticalMildHeatTimeKernel

variable {G : Type*}

/-! ## Time Cauchy–Schwarz -/

/-- **Time Cauchy–Schwarz for geometric means.**

`∫ √f · √g ≤ √(∫ f) · √(∫ g)` on a measurable set, for nonnegative integrable
`f,g`.  This is the named missing step in `LeiLinBilinear`. -/
theorem integral_sqrt_mul_le {f g : ℝ → ℝ} {s : Set ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : IntegrableOn f s) (hgi : IntegrableOn g s) :
    (∫ x in s, Real.sqrt (f x) * Real.sqrt (g x)) ≤
      Real.sqrt (∫ x in s, f x) * Real.sqrt (∫ x in s, g x) := by
  have hpq : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hf_sq : IntegrableOn (fun x => (Real.sqrt (f x)) ^ 2) s := by
    have hrew : (fun x => (Real.sqrt (f x)) ^ 2) = f := by
      funext x; exact Real.sq_sqrt (hf0 x)
    simpa [hrew] using hfi
  have hg_sq : IntegrableOn (fun x => (Real.sqrt (g x)) ^ 2) s := by
    have hrew : (fun x => (Real.sqrt (g x)) ^ 2) = g := by
      funext x; exact Real.sq_sqrt (hg0 x)
    simpa [hrew] using hgi
  have hf_aesm : AEStronglyMeasurable (fun x => Real.sqrt (f x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hfi.aestronglyMeasurable
  have hg_aesm : AEStronglyMeasurable (fun x => Real.sqrt (g x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hgi.aestronglyMeasurable
  have hf_mem : MemLp (fun x => Real.sqrt (f x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hf_aesm).2 hf_sq
  have hg_mem : MemLp (fun x => Real.sqrt (g x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hg_aesm).2 hg_sq
  have hfnn : 0 ≤ᵐ[volume.restrict s] fun x => Real.sqrt (f x) :=
    Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _
  have hnng : 0 ≤ᵐ[volume.restrict s] fun x => Real.sqrt (g x) :=
    Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _
  have hf_mem' : MemLp (fun x => Real.sqrt (f x)) (ENNReal.ofReal 2)
      (volume.restrict s) := by simpa using hf_mem
  have hg_mem' : MemLp (fun x => Real.sqrt (g x)) (ENNReal.ofReal 2)
      (volume.restrict s) := by simpa using hg_mem
  have hCS :=
    integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict s) hpq
      hfnn hnng hf_mem' hg_mem'
  have hrw : ∀ y : ℝ, y ^ (2 : ℝ) = y ^ (2 : ℕ) := by
    intro y; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hf2 : (fun x => (Real.sqrt (f x)) ^ (2 : ℝ)) = f := by
    funext x; rw [hrw, Real.sq_sqrt (hf0 x)]
  have hg2 : (fun x => (Real.sqrt (g x)) ^ (2 : ℝ)) = g := by
    funext x; rw [hrw, Real.sq_sqrt (hg0 x)]
  simp only [hf2, hg2] at hCS
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact hCS

/-- The geometric-mean integrand is integrable when the factors are. -/
theorem integrableOn_sqrt_mul {f g : ℝ → ℝ} {s : Set ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : IntegrableOn f s) (hgi : IntegrableOn g s) :
    IntegrableOn (fun x => Real.sqrt (f x) * Real.sqrt (g x)) s := by
  have hf_sq : IntegrableOn (fun x => (Real.sqrt (f x)) ^ 2) s := by
    have hrew : (fun x => (Real.sqrt (f x)) ^ 2) = f := by
      funext x; exact Real.sq_sqrt (hf0 x)
    simpa [hrew] using hfi
  have hg_sq : IntegrableOn (fun x => (Real.sqrt (g x)) ^ 2) s := by
    have hrew : (fun x => (Real.sqrt (g x)) ^ 2) = g := by
      funext x; exact Real.sq_sqrt (hg0 x)
    simpa [hrew] using hgi
  have hf_aesm : AEStronglyMeasurable (fun x => Real.sqrt (f x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hfi.aestronglyMeasurable
  have hg_aesm : AEStronglyMeasurable (fun x => Real.sqrt (g x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hgi.aestronglyMeasurable
  have hf_mem : MemLp (fun x => Real.sqrt (f x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hf_aesm).2 hf_sq
  have hg_mem : MemLp (fun x => Real.sqrt (g x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hg_aesm).2 hg_sq
  have h := hf_mem.integrable_mul hg_mem
  exact h.congr (Filter.Eventually.of_forall fun x =>
    Pi.mul_apply (fun y => Real.sqrt (f y)) (fun y => Real.sqrt (g y)) x)

/-! ## Spacetime bilinear estimate -/

/-- **Spacetime bilinear bound via time Cauchy–Schwarz.**

Under `L∞_t` majorants `Aᵤ, Aᵥ` of the critical norms and integrable `𝒳¹`
masses,

  `∫₀^∞ ‖|k|(u⋆v)‖_{𝒳^{-1}} dt
      ≤ (1/(4ν)) (Aᵤ + ν∫‖u‖₁)(Aᵥ + ν∫‖v‖₁)`.

This is the `L¹_t 𝒳^{-1}` half of the mixed-norm bilinear estimate named as
missing in `LeiLinBilinear`. -/
theorem integral_bilinear_Xm1_le [AddCommGroup G] {ν : ℝ} {σ : G → ℝ}
    {u v : ℝ → G → ℝ} {Au Av : ℝ}
    (hν : 0 < ν) (hσ : ∀ k, 0 ≤ σ k)
    (hAu0 : 0 ≤ Au) (hAv0 : 0 ≤ Av)
    (hAu : ∀ t ≥ (0 : ℝ), normXm1 σ (u t) ≤ Au)
    (hAv : ∀ t ≥ (0 : ℝ), normXm1 σ (v t) ≤ Av)
    (hzu : ∀ t ≥ (0 : ℝ), ∀ k, σ k = 0 → u t k = 0)
    (hzv : ∀ t ≥ (0 : ℝ), ∀ k, σ k = 0 → v t k = 0)
    (huW : ∀ t ≥ (0 : ℝ), InWiener (u t))
    (hvW : ∀ t ≥ (0 : ℝ), InWiener (v t))
    (hmu : ∀ t ≥ (0 : ℝ), InW (fun k => (σ k)⁻¹) (u t))
    (hpu : ∀ t ≥ (0 : ℝ), InW σ (u t))
    (hmv : ∀ t ≥ (0 : ℝ), InW (fun k => (σ k)⁻¹) (v t))
    (hpv : ∀ t ≥ (0 : ℝ), InW σ (v t))
    (hu1 : IntegrableOn (fun t => normX1 σ (u t)) (Ioi (0 : ℝ)))
    (hv1 : IntegrableOn (fun t => normX1 σ (v t)) (Ioi (0 : ℝ)))
    (hB : IntegrableOn
      (fun t => normXm1 σ (fun k => σ k * conv (u t) (v t) k)) (Ioi (0 : ℝ))) :
    (∫ t in Ioi (0 : ℝ),
        normXm1 σ (fun k => σ k * conv (u t) (v t) k)) ≤
      (1 / (4 * ν)) *
        ((Au + ν * ∫ t in Ioi (0 : ℝ), normX1 σ (u t)) *
          (Av + ν * ∫ t in Ioi (0 : ℝ), normX1 σ (v t))) := by
  set Bu : ℝ → ℝ := fun t =>
    normXm1 σ (fun k => σ k * conv (u t) (v t) k)
  set u1 : ℝ → ℝ := fun t => normX1 σ (u t)
  set v1 : ℝ → ℝ := fun t => normX1 σ (v t)
  have hu10 : ∀ t, 0 ≤ u1 t := fun t => normX1_nonneg hσ (u t)
  have hv10 : ∀ t, 0 ≤ v1 t := fun t => normX1_nonneg hσ (v t)
  have hnnAu : ∀ t, 0 ≤ Au * u1 t := fun t => mul_nonneg hAu0 (hu10 t)
  have hnnAv : ∀ t, 0 ≤ Av * v1 t := fun t => mul_nonneg hAv0 (hv10 t)
  have hAu_u1 : IntegrableOn (fun t => Au * u1 t) (Ioi (0 : ℝ)) := hu1.const_mul Au
  have hAv_v1 : IntegrableOn (fun t => Av * v1 t) (Ioi (0 : ℝ)) := hv1.const_mul Av
  have hmaj_int := integrableOn_sqrt_mul (s := Ioi (0 : ℝ)) hnnAu hnnAv hAu_u1 hAv_v1
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      Bu t ≤ Real.sqrt (Au * u1 t) * Real.sqrt (Av * v1 t) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hsu : normX0 (u t) ≤ Real.sqrt (normXm1 σ (u t) * u1 t) :=
      normX0_le_sqrt hσ (hzu t ht0) (huW t ht0) (hmu t ht0) (hpu t ht0)
    have hsv : normX0 (v t) ≤ Real.sqrt (normXm1 σ (v t) * v1 t) :=
      normX0_le_sqrt hσ (hzv t ht0) (hvW t ht0) (hmv t ht0) (hpv t ht0)
    have hB0 := bilinear_Xm1_le (σ := σ) (u := u t) (v := v t) hσ
      (huW t ht0) (hvW t ht0)
    have hstep : Bu t ≤
        Real.sqrt (normXm1 σ (u t) * u1 t) *
          Real.sqrt (normXm1 σ (v t) * v1 t) :=
      hB0.trans (mul_le_mul hsu hsv (normX0_nonneg (v t)) (Real.sqrt_nonneg _))
    have h1 : Real.sqrt (normXm1 σ (u t) * u1 t) ≤ Real.sqrt (Au * u1 t) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hAu t ht0) (hu10 t))
    have h2 : Real.sqrt (normXm1 σ (v t) * v1 t) ≤ Real.sqrt (Av * v1 t) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hAv t ht0) (hv10 t))
    exact hstep.trans (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hint_le :
      (∫ t in Ioi (0 : ℝ), Bu t) ≤
        (∫ t in Ioi (0 : ℝ), Real.sqrt (Au * u1 t) * Real.sqrt (Av * v1 t)) :=
    setIntegral_mono_on hB hmaj_int measurableSet_Ioi hpoint
  have hCS :=
    integral_sqrt_mul_le (s := Ioi (0 : ℝ)) hnnAu hnnAv hAu_u1 hAv_v1
  have hu1nn : 0 ≤ ∫ t in Ioi (0 : ℝ), u1 t := integral_nonneg fun t => hu10 t
  have hv1nn : 0 ≤ ∫ t in Ioi (0 : ℝ), v1 t := integral_nonneg fun t => hv10 t
  have hAMGM := sqrt_mul_sqrt_le_quarter hν hAu0 hu1nn hAv0 hv1nn
  calc (∫ t in Ioi (0 : ℝ), Bu t)
      ≤ Real.sqrt (∫ t in Ioi (0 : ℝ), Au * u1 t) *
          Real.sqrt (∫ t in Ioi (0 : ℝ), Av * v1 t) := hint_le.trans hCS
    _ = Real.sqrt (Au * ∫ t in Ioi (0 : ℝ), u1 t) *
          Real.sqrt (Av * ∫ t in Ioi (0 : ℝ), v1 t) := by
        rw [integral_const_mul, integral_const_mul]
    _ ≤ (1 / (4 * ν)) *
          ((Au + ν * ∫ t in Ioi (0 : ℝ), u1 t) *
            (Av + ν * ∫ t in Ioi (0 : ℝ), v1 t)) := hAMGM

/-! ## Linear spacetime mixed bound -/

/-- Spacetime mixed majorant: `L∞_t 𝒳^{-1}` plus `ν L¹_t 𝒳¹`. -/
def MixedTimeBound (ν : ℝ) (σ : G → ℝ) (u : ℝ → G → ℝ) (K : ℝ) : Prop :=
  (∀ t ≥ (0 : ℝ), normXm1 σ (u t) ≤ K) ∧
    (∫ t in Ioi (0 : ℝ), ν * normX1 σ (u t)) ≤ K

/-- **A spacetime mixed bound alone has no terminal `𝒳¹` consequence.**

For the fixed unbounded weight `σ(n) = n + 1`, a profile concentrated at one
time and one sufficiently high mode has `L∞_t 𝒳⁻¹` norm at most one
and zero `L¹_t 𝒳¹` mass, but an arbitrarily large `𝒳¹` value at that
time.  Thus `MixedTimeBound` cannot by itself supply the pointwise terminal
`𝒳¹` term used by `CriticalMildMixedTerminalBound`; a valid bridge needs
additional time regularity with quantitative point-evaluation control.  This
falsifies only that overstrong interface, not any Navier--Stokes estimate. -/
theorem not_exists_terminal_X1_bound_of_mixedTimeBound :
    ¬ ∃ C : ℝ, ∀ u : ℝ → ℕ → ℝ,
      MixedTimeBound 1 (fun n : ℕ => (n : ℝ) + 1) u 1 →
        normX1 (fun n : ℕ => (n : ℝ) + 1) (u 1) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let u : ℝ → ℕ → ℝ := fun t n => if t = 1 ∧ n = N then 1 else 0
  have hmixed : MixedTimeBound 1 (fun n : ℕ => (n : ℝ) + 1) u 1 := by
    constructor
    · intro t _ht
      by_cases ht : t = 1
      · subst t
        unfold normXm1 wNorm
        rw [tsum_eq_single N]
        · simp only [u, and_self, if_true, abs_one, mul_one]
          exact (inv_le_one_iff₀).2 (Or.inr (by norm_num))
        · intro n hn
          simp [u, hn]
      · simp [normXm1, wNorm, u, ht]
    · have hae :
          (fun t : ℝ => (1 : ℝ) * normX1 (fun n : ℕ => (n : ℝ) + 1) (u t))
            =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
          filter_upwards [(volume.restrict (Ioi (0 : ℝ))).ae_ne (1 : ℝ)] with t ht
          simp [normX1, wNorm, u, ht]
      rw [integral_congr_ae hae]
      norm_num
  have hterminal := hC u hmixed
  have hvalue :
      normX1 (fun n : ℕ => (n : ℝ) + 1) (u 1) = (N : ℝ) + 1 := by
    unfold normX1 wNorm
    rw [tsum_eq_single N]
    · simp [u]
    · intro n hn
      simp [u, hn]
  rw [hvalue] at hterminal
  linarith

/-- **An a.e. dissipation budget has no terminal trace.**  Nonnegativity and
finite `L¹` mass, even with full interval integrability, cannot control the
chosen endpoint because the integral is insensitive to a singleton.  Any
direct `𝒳¹` energy route therefore needs a quantitative trace/modulus theorem
beyond the a.e. Lei--Lin dissipation inequality. -/
theorem not_exists_terminal_bound_of_nonnegative_integral_budget :
    ¬ ∃ C : ℝ, ∀ f : ℝ → ℝ,
      (∀ t, 0 ≤ f t) →
      IntervalIntegrable f volume 0 1 →
      (∫ t in (0 : ℝ)..1, f t) ≤ 1 →
      f 1 ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let f : ℝ → ℝ := fun t ↦ if t = 1 then (N : ℝ) else 0
  have hf0 : ∀ t, 0 ≤ f t := by
    intro t
    simp only [f]
    split <;> positivity
  have hae : f =ᵐ[volume.restrict (Set.uIoc (0 : ℝ) 1)] 0 := by
    filter_upwards [(volume.restrict (Set.uIoc (0 : ℝ) 1)).ae_ne (1 : ℝ)] with t ht
    simp [f, ht]
  have hfint : IntervalIntegrable f volume 0 1 :=
    intervalIntegrable_const.congr_ae hae.symm
  have hfintegral : (∫ t in (0 : ℝ)..1, f t) = 0 := by
    rw [intervalIntegral.integral_congr_ae_restrict hae]
    simp
  have hterminal := hC f hf0 hfint (by rw [hfintegral]; norm_num)
  simp [f] at hterminal
  linarith

/-- The next homogeneous mode moment, used to model the one-extra-mode
half-generator domain on the physical amplitude. -/
def normX2 (σ f : G → ℝ) : ℝ :=
  wNorm (fun k => (σ k) ^ 2) f

private theorem heatMode_frequency_mul_shift
    (ν : ℝ) (σ f : G → ℝ) (a t : ℝ) (k : G) :
    heatMode ν σ t (fun j => σ j * heatMode ν σ a f j) k =
      σ k * heatMode ν σ (a + t) f k := by
  unfold heatMode
  simp only
  calc
    Real.exp (-(ν * σ k ^ 2 * t)) *
        (σ k * (Real.exp (-(ν * σ k ^ 2 * a)) * f k)) =
      σ k * (Real.exp (-(ν * σ k ^ 2 * t)) *
        Real.exp (-(ν * σ k ^ 2 * a)) * f k) := by ring
    _ = σ k * (Real.exp (-(ν * σ k ^ 2 * (a + t))) * f k) := by
      rw [← Real.exp_add]
      congr 3
      ring

private theorem normX1_heatMode_frequency_mul_shift_eq_normX2
    (ν : ℝ) (σ f : G → ℝ) (hσ : ∀ k, 0 ≤ σ k) (a t : ℝ) :
    normX1 σ (heatMode ν σ t (fun j => σ j * heatMode ν σ a f j)) =
      normX2 σ (heatMode ν σ (a + t) f) := by
  unfold normX1 normX2 wNorm
  apply tsum_congr
  intro k
  rw [heatMode_frequency_mul_shift]
  rw [abs_mul, abs_of_nonneg (hσ k)]
  ring

private theorem shifted_frequency_mul_pointwise
    {ν a : ℝ} {σ f : G → ℝ} (hν : 0 < ν) (ha : 0 < a)
    (hσ : ∀ k, 0 ≤ σ k) (k : G) :
    (σ k)⁻¹ * |σ k * heatMode ν σ a f k| ≤
      (Real.sqrt (ν * a))⁻¹ * ((σ k)⁻¹ * |f k|) := by
  have hε : 0 < ν * a := mul_pos hν ha
  by_cases hk : σ k = 0
  · simp [hk]
  · have hgain := Real.abs_mulExpNegMulSq_le hε (x := σ k)
    rw [Real.mulExpNegSq_apply] at hgain
    have hexp : -(ν * a * σ k * σ k) = -(ν * (σ k) ^ 2 * a) := by ring
    rw [hexp] at hgain
    rw [abs_mul, abs_of_nonneg (hσ k), heatMode_abs]
    rw [show (σ k)⁻¹ * (σ k * (Real.exp (-(ν * (σ k) ^ 2 * a)) * |f k|)) =
        (σ k * Real.exp (-(ν * (σ k) ^ 2 * a))) * ((σ k)⁻¹ * |f k|) by field_simp]
    exact mul_le_mul_of_nonneg_right
      (by simpa [abs_of_nonneg (mul_nonneg (hσ k) (Real.exp_pos _).le)] using hgain)
      (mul_nonneg (inv_nonneg.mpr (hσ k)) (abs_nonneg _))

private theorem shifted_frequency_mul_inW
    {ν a : ℝ} {σ f : G → ℝ} (hν : 0 < ν) (ha : 0 < a)
    (hσ : ∀ k, 0 ≤ σ k) (hf : InW (fun k => (σ k)⁻¹) f) :
    InW (fun k => (σ k)⁻¹)
      (fun k => σ k * heatMode ν σ a f k) := by
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (inv_nonneg.mpr (hσ k)) (abs_nonneg _))
    (shifted_frequency_mul_pointwise hν ha hσ)
    (hf.mul_left (Real.sqrt (ν * a))⁻¹)

private theorem normXm1_shifted_frequency_mul_le
    {ν a : ℝ} {σ f : G → ℝ} (hν : 0 < ν) (ha : 0 < a)
    (hσ : ∀ k, 0 ≤ σ k) (hf : InW (fun k => (σ k)⁻¹) f) :
    normXm1 σ (fun k => σ k * heatMode ν σ a f k) ≤
      (Real.sqrt (ν * a))⁻¹ * normXm1 σ f := by
  have h := Summable.tsum_le_tsum
    (shifted_frequency_mul_pointwise hν ha hσ)
    (shifted_frequency_mul_inW hν ha hσ hf)
    (hf.mul_left _)
  simpa [normXm1, wNorm, tsum_mul_left] using h

private theorem integrableOn_heat_X1
    [Countable G] {ν : ℝ} {σ f : G → ℝ} (hν : 0 < ν)
    (hσ : ∀ k, 0 ≤ σ k) (hf : InW (fun k => (σ k)⁻¹) f) :
    IntegrableOn (fun t => ν * normX1 σ (heatMode ν σ t f)) (Ioi (0 : ℝ)) := by
  let F : G → ℝ → ℝ := fun k t => ν * (σ k * |heatMode ν σ t f k|)
  have hpt : ∀ t : ℝ, ν * normX1 σ (heatMode ν σ t f) = ∑' k, F k t := by
    intro t
    rw [normX1, wNorm]
    exact (tsum_mul_left).symm
  have hnn : ∀ k t, 0 ≤ F k t := by
    intro k t
    exact mul_nonneg hν.le (mul_nonneg (hσ k) (abs_nonneg _))
  have hint : ∀ k, IntegrableOn (F k) (Ioi (0 : ℝ)) := fun k =>
    integrableOn_mode_all hν hσ k
  have hmeas : ∀ k, AEStronglyMeasurable (F k)
      (volume.restrict (Ioi (0 : ℝ))) := fun k => (hint k).aestronglyMeasurable
  have hval : ∀ k, (∫ t in Ioi (0 : ℝ), F k t) = (σ k)⁻¹ * |f k| := fun k =>
    integral_mode_eq hν hσ k
  have hlint : ∀ k, (∫⁻ t in Ioi (0 : ℝ), ‖F k t‖₊) =
      ENNReal.ofReal ((σ k)⁻¹ * |f k|) := by
    intro k
    have h1 : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (F k t)) =
        ENNReal.ofReal (∫ t in Ioi (0 : ℝ), F k t) :=
      (ofReal_integral_eq_lintegral_ofReal (hint k)
        (Filter.Eventually.of_forall fun t => hnn k t)).symm
    rw [← hval k, ← h1]
    refine lintegral_congr fun t => ?_
    rw [Real.nnnorm_of_nonneg (hnn k t), ENNReal.ofReal]
    exact congrArg _ (Real.toNNReal_of_nonneg (hnn k t)).symm
  have hfinite : (∑' k, ∫⁻ t in Ioi (0 : ℝ), ‖F k t‖₊) ≠ ⊤ := by
    have hnn' : ∀ k, 0 ≤ (σ k)⁻¹ * |f k| := fun k =>
      mul_nonneg (inv_nonneg.mpr (hσ k)) (abs_nonneg _)
    have heq : (∑' k, ∫⁻ t in Ioi (0 : ℝ), ‖F k t‖₊) =
        ENNReal.ofReal (∑' k, (σ k)⁻¹ * |f k|) := by
      rw [ENNReal.ofReal_tsum_of_nonneg hnn' hf]
      exact tsum_congr hlint
    rw [heq]
    exact ENNReal.ofReal_ne_top
  refine ⟨?_, ?_⟩
  · exact (AEStronglyMeasurable.tsum hmeas).congr
      (Filter.Eventually.of_forall fun t => (hpt t).symm)
  · rw [hasFiniteIntegral_def]
    have hle : (∫⁻ t in Ioi (0 : ℝ), ‖∑' k, F k t‖ₑ) ≤
        ∑' k, ∫⁻ t in Ioi (0 : ℝ), ‖F k t‖ₑ := by
      calc
        (∫⁻ t in Ioi (0 : ℝ), ‖∑' k, F k t‖ₑ) ≤
            ∫⁻ t in Ioi (0 : ℝ), ∑' k, ‖F k t‖ₑ := by
          gcongr with t
          exact enorm_tsum_le_tsum_enorm
        _ = ∑' k, ∫⁻ t in Ioi (0 : ℝ), ‖F k t‖ₑ := by
          rw [lintegral_tsum fun k => (hmeas k).enorm]
    calc
      (∫⁻ t in Ioi (0 : ℝ), ‖ν * normX1 σ (heatMode ν σ t f)‖ₑ) =
          ∫⁻ t in Ioi (0 : ℝ), ‖∑' k, F k t‖ₑ := by
        apply lintegral_congr
        intro t
        rw [hpt t]
      _ ≤ ∑' k, ∫⁻ t in Ioi (0 : ℝ), ‖F k t‖ₑ := hle
      _ < ⊤ := lt_top_iff_ne_top.mpr (by simpa only [enorm_eq_nnnorm] using hfinite)

private theorem heat_X2_future_mass_le
    [Countable G] {ν a : ℝ} {σ f : G → ℝ}
    (hν : 0 < ν) (ha : 0 < a) (hσ : ∀ k, 0 ≤ σ k)
    (hf : InW (fun k => (σ k)⁻¹) f) :
    (∫ t in Ioi (0 : ℝ), ν * normX2 σ (heatMode ν σ (a + t) f)) ≤
      (Real.sqrt (ν * a))⁻¹ * normXm1 σ f := by
  let g : G → ℝ := fun k => σ k * heatMode ν σ a f k
  have hg : InW (fun k => (σ k)⁻¹) g :=
    shifted_frequency_mul_inW hν ha hσ hf
  have heq := heat_L1_time_eq hν hσ hg
  rw [show (∫ t in Ioi (0 : ℝ), ν * normX2 σ (heatMode ν σ (a + t) f)) =
      ∫ t in Ioi (0 : ℝ), ν * normX1 σ (heatMode ν σ t g) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    dsimp [g]
    rw [normX1_heatMode_frequency_mul_shift_eq_normX2 ν σ f hσ a t]]
  rw [heq]
  exact normXm1_shifted_frequency_mul_le hν ha hσ hf

private theorem integrableOn_heat_X2_future
    [Countable G] {ν a : ℝ} {σ f : G → ℝ}
    (hν : 0 < ν) (ha : 0 < a) (hσ : ∀ k, 0 ≤ σ k)
    (hf : InW (fun k => (σ k)⁻¹) f) :
    IntegrableOn (fun t => ν * normX2 σ (heatMode ν σ (a + t) f))
      (Ioi (0 : ℝ)) := by
  let g : G → ℝ := fun k => σ k * heatMode ν σ a f k
  have hg : InW (fun k => (σ k)⁻¹) g :=
    shifted_frequency_mul_inW hν ha hσ hf
  have hi := integrableOn_heat_X1 hν hσ hg
  apply hi.congr_fun
  · intro t _ht
    dsimp [g]
    rw [normX1_heatMode_frequency_mul_shift_eq_normX2 ν σ f hσ a t]
  · exact measurableSet_Ioi

/-- **Positive-time viscous gain of three mode powers.**  Critical
`𝒳⁻¹` data acquire an integrable future `𝒳²` tail after every waiting time
`a > 0`, at parabolic cost `(νa)⁻¹/²`.  Both integrability and the quantitative
mass estimate are included, so the integral conclusion is non-vacuous. -/
-- Citation: Lei--Lin, CPAM 64 (2011), Fourier heat multiplier estimate.
theorem heat_X2_future_integrable_and_mass_le
    [Countable G] {ν a : ℝ} {σ f : G → ℝ}
    (hν : 0 < ν) (ha : 0 < a) (hσ : ∀ k, 0 ≤ σ k)
    (hf : InW (fun k => (σ k)⁻¹) f) :
    IntegrableOn (fun t => ν * normX2 σ (heatMode ν σ (a + t) f))
        (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), ν * normX2 σ (heatMode ν σ (a + t) f)) ≤
        (Real.sqrt (ν * a))⁻¹ * normXm1 σ f :=
  ⟨integrableOn_heat_X2_future hν ha hσ hf,
    heat_X2_future_mass_le hν ha hσ hf⟩

/-- **Sharp initial-time obstruction for the linear heat flow.**  No constant
controls the full `L¹_t 𝒳²` heat mass by the critical `𝒳⁻¹` norm.  A single
mode `N`, normalized to have critical norm one, has `𝒳²` heat mass `N+1`.
Thus viscosity yields the preceding estimate only away from the initial
endpoint; nonlinear cancellation cannot repair a failure already present in
the free equation. -/
-- Citation: modewise heat identity, Lei--Lin, CPAM 64 (2011), Sec. 2.
theorem not_exists_heat_X2_mass_le_Xm1 :
    ¬ ∃ C : ℝ, ∀ f : ℕ → ℝ,
      InW (fun n : ℕ => ((n : ℝ) + 1)⁻¹) f →
      (∫ t in Ioi (0 : ℝ),
        normX2 (fun n : ℕ => (n : ℝ) + 1)
          (heatMode 1 (fun n : ℕ => (n : ℝ) + 1) t f)) ≤
        C * normXm1 (fun n : ℕ => (n : ℝ) + 1) f := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let σ : ℕ → ℝ := fun n => (n : ℝ) + 1
  let q : ℝ := (N : ℝ) + 1
  let f : ℕ → ℝ := fun n => if n = N then q else 0
  let g : ℕ → ℝ := fun n => σ n * heatMode 1 σ 0 f n
  have hq : 0 < q := by dsimp [q]; positivity
  have hσ : ∀ n, 0 ≤ σ n := by intro n; dsimp [σ]; positivity
  have hf : InW (fun n => (σ n)⁻¹) f := by
    apply summable_of_ne_finset_zero (s := ({N} : Finset ℕ))
    intro n hn
    have hn' : n ≠ N := by simpa using hn
    simp [f, hn']
  have hg : InW (fun n => (σ n)⁻¹) g := by
    apply summable_of_ne_finset_zero (s := ({N} : Finset ℕ))
    intro n hn
    have hn' : n ≠ N := by simpa using hn
    simp [g, f, heatMode, hn']
  have heq := heat_L1_time_eq (ν := (1 : ℝ)) (σ := σ) (f := g)
    zero_lt_one hσ hg
  have hmass : (∫ t in Ioi (0 : ℝ), normX2 σ (heatMode 1 σ t f)) = q := by
    rw [show (∫ t in Ioi (0 : ℝ), normX2 σ (heatMode 1 σ t f)) =
        ∫ t in Ioi (0 : ℝ), (1 : ℝ) * normX1 σ (heatMode 1 σ t g) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      dsimp [g]
      rw [normX1_heatMode_frequency_mul_shift_eq_normX2 1 σ f hσ 0 t]
      simp]
    rw [heq]
    unfold normXm1 wNorm
    rw [tsum_eq_single N]
    · simp [g, f, heatMode, σ, q, hq.ne']
    · intro n hn
      simp [g, f, heatMode, hn]
  have hnorm : normXm1 σ f = 1 := by
    unfold normXm1 wNorm
    rw [tsum_eq_single N]
    · rw [show f N = q by simp [f]]
      change (σ N)⁻¹ * |q| = 1
      rw [show σ N = q by rfl, abs_of_pos hq]
      exact inv_mul_cancel₀ hq.ne'
    · intro n hn
      simp [f, hn]
  have hbound := hC f hf
  change (∫ t in Ioi (0 : ℝ), normX2 σ (heatMode 1 σ t f)) ≤
    C * normXm1 σ f at hbound
  rw [hmass, hnorm, mul_one] at hbound
  dsimp [q] at hbound
  linarith

/-- **Mixed time control does not bound the extra mode moment.**

The same checked measure-zero spike obstruction already appears one mode
moment above `𝒳¹`: `MixedTimeBound` controls no pointwise `𝒳²` value.  This
falsifies that precise functional implication only; an actual mild trajectory
has additional structure which must be used separately. -/
theorem not_exists_terminal_X2_bound_of_mixedTimeBound :
    ¬ ∃ C : ℝ, ∀ u : ℝ → ℕ → ℝ,
      MixedTimeBound 1 (fun n : ℕ => (n : ℝ) + 1) u 1 →
        normX2 (fun n : ℕ => (n : ℝ) + 1) (u 1) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let u : ℝ → ℕ → ℝ := fun t n => if t = 1 ∧ n = N then 1 else 0
  have hmixed : MixedTimeBound 1 (fun n : ℕ => (n : ℝ) + 1) u 1 := by
    constructor
    · intro t _ht
      by_cases ht : t = 1
      · subst t
        unfold normXm1 wNorm
        rw [tsum_eq_single N]
        · simp only [u, and_self, if_true, abs_one, mul_one]
          exact (inv_le_one_iff₀).2 (Or.inr (by norm_num))
        · intro n hn
          simp [u, hn]
      · simp [normXm1, wNorm, u, ht]
    · have hae :
          (fun t : ℝ => (1 : ℝ) * normX1 (fun n : ℕ => (n : ℝ) + 1) (u t))
            =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
          filter_upwards [(volume.restrict (Ioi (0 : ℝ))).ae_ne (1 : ℝ)] with t ht
          simp [normX1, wNorm, u, ht]
      rw [integral_congr_ae hae]
      norm_num
  have hterminal := hC u hmixed
  have hvalue :
      normX2 (fun n : ℕ => (n : ℝ) + 1) (u 1) = ((N : ℝ) + 1) ^ 2 := by
    unfold normX2 wNorm
    rw [tsum_eq_single N]
    · simp [u]
    · intro n hn
      simp [u, hn]
  rw [hvalue] at hterminal
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [sq_nonneg ((N : ℝ) + 1)]

/-- **Mixed time control does not bound even the time integral of the extra
mode moment.**  A unit-length profile at mode `N`, scaled by `(N+1)⁻¹`,
has mixed bound one but integrated `𝒳²` mass `N+1`.  Thus the missing
half-generator mass is a genuine additional product/graph norm, not a
consequence of `MixedTimeBound`. -/
theorem not_exists_integrated_X2_bound_of_mixedTimeBound :
    ¬ ∃ C : ℝ, ∀ u : ℝ → ℕ → ℝ,
      MixedTimeBound 1 (fun n : ℕ ↦ (n : ℝ) + 1) u 1 →
        (∫ t in Ioi (0 : ℝ),
          normX2 (fun n : ℕ ↦ (n : ℝ) + 1) (u t)) ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let q : ℝ := (N : ℝ) + 1
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let u : ℝ → ℕ → ℝ := fun t n ↦
    if t ∈ Ioc (0 : ℝ) 1 ∧ n = N then q⁻¹ else 0
  have hXm1 : ∀ t : ℝ,
      normXm1 (fun n : ℕ ↦ (n : ℝ) + 1) (u t) ≤ 1 := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · unfold normXm1 wNorm
      rw [tsum_eq_single N]
      · simp only [u, ht, true_and, if_true]
        rw [abs_of_pos (inv_pos.mpr hqpos)]
        change q⁻¹ * q⁻¹ ≤ 1
        have hi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hqpos.le
        have hi1 : q⁻¹ ≤ 1 := (inv_le_one_iff₀).2 (Or.inr hq)
        nlinarith
      · intro n hn
        simp [u, hn]
    · have ht' : ¬ (0 < t ∧ t ≤ 1) := by simpa [Set.mem_Ioc] using ht
      simp [normXm1, wNorm, u, ht']
  have hX1 : (fun t : ℝ =>
      (1 : ℝ) * normX1 (fun n : ℕ ↦ (n : ℝ) + 1) (u t)) =
      fun t ↦ (Ioc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) t := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · unfold normX1 wNorm
      rw [tsum_eq_single N]
      · simp only [u, ht, true_and, if_true, one_mul]
        rw [abs_of_pos (inv_pos.mpr hqpos)]
        simp [Set.indicator_of_mem ht, q, hqpos.ne']
      · intro n hn
        simp [u, hn]
    · have ht' : ¬ (0 < t ∧ t ≤ 1) := by simpa [Set.mem_Ioc] using ht
      simp [normX1, wNorm, u, ht', Set.indicator]
  have hX2 : (fun t : ℝ =>
      normX2 (fun n : ℕ ↦ (n : ℝ) + 1) (u t)) =
      fun t ↦ (Ioc (0 : ℝ) 1).indicator (fun _ ↦ q) t := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · unfold normX2 wNorm
      rw [tsum_eq_single N]
      · simp only [u, ht, true_and, if_true]
        rw [abs_of_pos (inv_pos.mpr hqpos)]
        rw [Set.indicator_of_mem ht]
        change q ^ 2 * q⁻¹ = q
        field_simp
      · intro n hn
        simp [u, hn]
    · have ht' : ¬ (0 < t ∧ t ≤ 1) := by simpa [Set.mem_Ioc] using ht
      simp [normX2, wNorm, u, ht', Set.indicator]
  have hmixed : MixedTimeBound 1 (fun n : ℕ ↦ (n : ℝ) + 1) u 1 := by
    constructor
    · intro t _ht
      exact hXm1 t
    · rw [hX1, setIntegral_indicator measurableSet_Ioc]
      have hs : Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 := by ext x; simp
      rw [hs]
      norm_num
  have hbound := hC u hmixed
  have hX2mass : (∫ t in Ioi (0 : ℝ),
      normX2 (fun n : ℕ ↦ (n : ℝ) + 1) (u t)) = q := by
    rw [hX2, setIntegral_indicator measurableSet_Ioc]
    have hs : Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 := by ext x; simp
    rw [hs]
    simp
  rw [hX2mass] at hbound
  dsimp [q] at hbound
  linarith

/-- The inverse-time endpoint majorant produced by one extra derivative of
the Duhamel heat kernel is not interval-integrable at zero. -/
theorem not_intervalIntegrable_inverseTime_zero {δ : ℝ} (hδ : 0 < δ) :
    ¬ IntervalIntegrable (fun τ : ℝ => τ⁻¹) volume 0 δ := by
  simp [intervalIntegrable_inv_iff, hδ.ne]

/-- The square-root kernel is `L¹`, but multiplying it by an arbitrary `L¹`
input can recreate the nonintegrable inverse-time endpoint.  Thus pointwise
Volterra control cannot be obtained from `L¹` input data alone, even though
the double-time average remains the correct integrable target. -/
theorem inverseSqrtTime_L1_product_endpoint_obstruction :
    IntervalIntegrable inverseSqrtTime volume 0 1 ∧
      ¬ IntervalIntegrable
        (fun τ : ℝ => inverseSqrtTime τ * inverseSqrtTime τ) volume 0 1 := by
  refine ⟨inverseSqrtTime_intervalIntegrable 1, ?_⟩
  intro hsq
  have heq : Set.EqOn
      (fun τ : ℝ => inverseSqrtTime τ * inverseSqrtTime τ)
      (fun τ : ℝ => τ⁻¹) (Set.uIoo (0 : ℝ) 1) := by
    intro τ hτ
    have hτpos : 0 < τ := by simpa [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hτ.1
    unfold inverseSqrtTime
    change τ ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 / 2 : ℝ)) = τ⁻¹
    rw [← Real.rpow_add hτpos]
    norm_num [Real.rpow_neg_one]
  have hinv : IntervalIntegrable (fun τ : ℝ => τ⁻¹) volume 0 1 :=
    hsq.congr_uIoo heq
  exact not_intervalIntegrable_inverseTime_zero (δ := 1) zero_lt_one hinv

/-- Scalar absorption for the averaged half-moment Volterra recurrence. -/
theorem le_div_one_sub_of_volterra_sqrt
    {B H c δ : ℝ} (hsmall : c * Real.sqrt δ < 1)
    (hrec : B ≤ H + c * Real.sqrt δ * B) :
    B ≤ H / (1 - c * Real.sqrt δ) := by
  have hden : 0 < 1 - c * Real.sqrt δ := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

/-! ## The minimal terminal-sampling repair -/

/-- **A backward square-root modulus converts trailing integral control into
terminal pointwise control.**

If `f T` differs from every value on the preceding window of length `δ` by
at most `L √(T-s)`, then

`f T ≤ δ⁻¹ ∫_(T-δ)^T f + L √δ`.

This is the smallest extra interface needed to defeat the measure-zero spike
in `not_exists_terminal_X1_bound_of_mixedTimeBound`: it asks only for a
one-sided modulus on the window actually averaged. -/
theorem terminal_le_average_add_of_backward_sqrt_modulus
    {f : ℝ → ℝ} {T δ L A : ℝ}
    (hδ : 0 < δ)
    (hL : 0 ≤ L)
    (hf : IntervalIntegrable f volume (T - δ) T)
    (hmod : ∀ s ∈ Icc (T - δ) T,
      f T ≤ f s + L * Real.sqrt (T - s))
    (hA : (∫ s in (T - δ)..T, f s) ≤ A) :
    f T ≤ A / δ + L * Real.sqrt δ := by
  have hδle : T - δ ≤ T := by linarith
  have hsqrt : ∀ s ∈ Icc (T - δ) T,
      Real.sqrt (T - s) ≤ Real.sqrt δ := by
    intro s hs
    exact Real.sqrt_le_sqrt (by linarith [hs.1])
  have hpoint : ∀ s ∈ Icc (T - δ) T,
      f T - L * Real.sqrt δ ≤ f s := by
    intro s hs
    have hL : L * Real.sqrt (T - s) ≤ L * Real.sqrt δ := by
      exact mul_le_mul_of_nonneg_left (hsqrt s hs) hL
    linarith [hmod s hs]
  have havg : δ * (f T - L * Real.sqrt δ) ≤
      ∫ s in (T - δ)..T, f s := by
    have hmono := intervalIntegral.integral_mono_on hδle
      intervalIntegrable_const hf hpoint
    rw [intervalIntegral.integral_const, sub_sub_self, smul_eq_mul] at hmono
    exact hmono
  have hmul : δ * f T ≤ A + δ * (L * Real.sqrt δ) := by
    linarith
  have hdiv : f T ≤ (A + δ * (L * Real.sqrt δ)) / δ :=
    (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hmul)
  calc
    f T ≤ (A + δ * (L * Real.sqrt δ)) / δ := hdiv
    _ = A / δ + L * Real.sqrt δ := by field_simp

/-- The preceding sampling lemma specialized to the actual `𝒳¹` quantity.
It makes the repaired consumer shape explicit: a trailing `𝒳¹` mass plus a
backward square-root time modulus controls the terminal `𝒳¹` value. -/
theorem terminal_X1_le_of_backward_sqrt_modulus {G : Type*}
    {sigma : G → ℝ} {u : ℝ → G → ℝ} {T δ L A : ℝ}
    (hδ : 0 < δ)
    (hL : 0 ≤ L)
    (hint : IntervalIntegrable (fun t => normX1 sigma (u t)) volume (T - δ) T)
    (hmod : ∀ s ∈ Icc (T - δ) T,
      normX1 sigma (u T) ≤
        normX1 sigma (u s) + L * Real.sqrt (T - s))
    (hmass : (∫ s in (T - δ)..T, normX1 sigma (u s)) ≤ A) :
    normX1 sigma (u T) ≤ A / δ + L * Real.sqrt δ :=
  terminal_le_average_add_of_backward_sqrt_modulus hδ hL hint hmod hmass

/-- **Integrated-coefficient terminal sampler.**

Uniform control of the square-root modulus coefficient is unnecessary.  It
is enough to integrate its nonnegative variable part over the trailing
window.  This is the minimal consumer matching an `L¹` half-generator moment:

`f(T) ≤ (A + B√δ)/δ + L√δ`.
-/
theorem terminal_le_average_add_of_integrated_backward_sqrt_modulus
    {f M : ℝ → ℝ} {T δ L A B : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L)
    (hM0 : ∀ s ∈ Icc (T - δ) T, 0 ≤ M s)
    (hf : IntervalIntegrable f volume (T - δ) T)
    (hM : IntervalIntegrable M volume (T - δ) T)
    (hmod : ∀ s ∈ Icc (T - δ) T,
      f T ≤ f s + (M s + L) * Real.sqrt (T - s))
    (hA : (∫ s in (T - δ)..T, f s) ≤ A)
    (hB : (∫ s in (T - δ)..T, M s) ≤ B) :
    f T ≤ (A + B * Real.sqrt δ) / δ + L * Real.sqrt δ := by
  have hδle : T - δ ≤ T := by linarith
  have hsqrt : ∀ s ∈ Icc (T - δ) T,
      Real.sqrt (T - s) ≤ Real.sqrt δ := by
    intro s hs
    exact Real.sqrt_le_sqrt (by linarith [hs.1])
  have hpoint : ∀ s ∈ Icc (T - δ) T,
      f T - L * Real.sqrt δ ≤ f s + M s * Real.sqrt δ := by
    intro s hs
    have hMs : M s * Real.sqrt (T - s) ≤ M s * Real.sqrt δ :=
      mul_le_mul_of_nonneg_left (hsqrt s hs) (hM0 s hs)
    have hLs : L * Real.sqrt (T - s) ≤ L * Real.sqrt δ :=
      mul_le_mul_of_nonneg_left (hsqrt s hs) hL
    linarith [hmod s hs]
  have hMscaled : IntervalIntegrable (fun s => M s * Real.sqrt δ)
      volume (T - δ) T := hM.mul_const _
  have hsum : IntervalIntegrable (fun s => f s + M s * Real.sqrt δ)
      volume (T - δ) T := hf.add hMscaled
  have havg : δ * (f T - L * Real.sqrt δ) ≤
      ∫ s in (T - δ)..T, (f s + M s * Real.sqrt δ) := by
    have hmono := intervalIntegral.integral_mono_on hδle
      intervalIntegrable_const hsum hpoint
    rw [intervalIntegral.integral_const, sub_sub_self, smul_eq_mul] at hmono
    exact hmono
  have hsplit : (∫ s in (T - δ)..T, (f s + M s * Real.sqrt δ)) =
      (∫ s in (T - δ)..T, f s) +
        (∫ s in (T - δ)..T, M s) * Real.sqrt δ := by
    rw [intervalIntegral.integral_add hf hMscaled,
      intervalIntegral.integral_mul_const]
  rw [hsplit] at havg
  have hbudget : δ * (f T - L * Real.sqrt δ) ≤ A + B * Real.sqrt δ :=
    havg.trans (add_le_add hA
      (mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg δ)))
  have hdiv : f T - L * Real.sqrt δ ≤ (A + B * Real.sqrt δ) / δ :=
    (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hbudget)
  linarith

/-- **Free heat evolution has spacetime mixed majorant `‖f‖_{𝒳^{-1}}`.** -/
theorem heat_mixedTimeBound [Countable G] {ν : ℝ} {σ f : G → ℝ}
    (hν : 0 < ν) (hσ : ∀ k, 0 ≤ σ k)
    (hf : InW (fun k => (σ k)⁻¹) f) :
    MixedTimeBound ν σ (fun t => heatMode ν σ t f) (normXm1 σ f) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact heat_contracts_Xm1 hν.le hσ ht hf
  · exact (heat_L1_time_eq hν hσ hf).le

/-- The two halves of the free evolution sum to at most `2‖f‖_{𝒳^{-1}}`. -/
theorem heat_mixedTime_sum_le [Countable G] {ν : ℝ} {σ f : G → ℝ}
    (hν : 0 < ν) (hσ : ∀ k, 0 ≤ σ k)
    (hf : InW (fun k => (σ k)⁻¹) f) :
    (∀ t ≥ (0 : ℝ), normXm1 σ (heatMode ν σ t f) ≤ normXm1 σ f) ∧
      (∫ t in Ioi (0 : ℝ), ν * normX1 σ (heatMode ν σ t f)) ≤ normXm1 σ f ∧
      normXm1 σ f +
          (∫ t in Ioi (0 : ℝ), ν * normX1 σ (heatMode ν σ t f)) ≤
        2 * normXm1 σ f := by
  have h := heat_mixedTimeBound (ν := ν) (σ := σ) (f := f) hν hσ hf
  refine ⟨h.1, h.2, ?_⟩
  linarith [h.2, normXm1_nonneg hσ f]

end Navier.Analysis.LeiLinTimeMixed

#print axioms Navier.Analysis.LeiLinTimeMixed.integral_sqrt_mul_le
#print axioms Navier.Analysis.LeiLinTimeMixed.integrableOn_sqrt_mul
#print axioms Navier.Analysis.LeiLinTimeMixed.integral_bilinear_Xm1_le
#print axioms Navier.Analysis.LeiLinTimeMixed.terminal_le_average_add_of_backward_sqrt_modulus
#print axioms Navier.Analysis.LeiLinTimeMixed.terminal_X1_le_of_backward_sqrt_modulus
#print axioms Navier.Analysis.LeiLinTimeMixed.terminal_le_average_add_of_integrated_backward_sqrt_modulus
#print axioms Navier.Analysis.LeiLinTimeMixed.heat_mixedTimeBound
#print axioms Navier.Analysis.LeiLinTimeMixed.heat_mixedTime_sum_le
#print axioms Navier.Analysis.LeiLinTimeMixed.not_exists_terminal_X1_bound_of_mixedTimeBound
#print axioms Navier.Analysis.LeiLinTimeMixed.not_exists_terminal_bound_of_nonnegative_integral_budget
#print axioms Navier.Analysis.LeiLinTimeMixed.heat_X2_future_integrable_and_mass_le
#print axioms Navier.Analysis.LeiLinTimeMixed.not_exists_heat_X2_mass_le_Xm1
#print axioms Navier.Analysis.LeiLinTimeMixed.not_exists_terminal_X2_bound_of_mixedTimeBound
#print axioms Navier.Analysis.LeiLinTimeMixed.not_exists_integrated_X2_bound_of_mixedTimeBound
#print axioms Navier.Analysis.LeiLinTimeMixed.not_intervalIntegrable_inverseTime_zero
#print axioms Navier.Analysis.LeiLinTimeMixed.inverseSqrtTime_L1_product_endpoint_obstruction
#print axioms Navier.Analysis.LeiLinTimeMixed.le_div_one_sub_of_volterra_sqrt
