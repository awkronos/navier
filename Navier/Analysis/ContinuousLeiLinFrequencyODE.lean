import Navier.Analysis.ContinuousLeiLinSpace
import Navier.Analysis.ContinuousLeiLinTimeDuhamel
import Navier.Analysis.ContinuousLeiLinDissipation
import Navier.Analysis.ContinuousLeiLinSelfMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Pointwise-in-frequency time derivative of the continuous mild map

Brick (c) remainder — obligation 1 of `NOTES-ns5-20260912.md` (the time-derivative
half of the pointwise `SatisfiesNavierStokes` route on the frequency carrier).
For each frequency `ξ` and coordinate `i`, the mild image satisfies the ODE-form
identity, at every `t₀ > 0`,

    d/dt (mild ν a u t ξ i) = -(ν ‖ξ‖²) • (mild ν a u t₀ ξ i)
                              + continuousNavierSource u u t₀ ξ i,

i.e. the frequency-space image of `∂ₜ u = ν Δu - 𝔽(u·∇)u - 𝔽(∇p)`: the viscous
Laplacian acts on the Fourier carrier as multiplication by `-‖ξ‖²` (which is what
`heatMode`'s multiplier `exp (-ν‖ξ‖²t)` differentiates to), and the Leray-dressed
`continuousNavierBilinear` symbol already absorbs both the convection and the
pressure term (the projection kills the gradient part), so the source term is the
exact forcing of the ODE.  The incompressibility content of the same route is the
transversality layer of `ContinuousLeiLinReality`; this file supplies the missing
derivative clause.

Method (all identities junk-safe, all regularity carried):
* `continuousDuhamel_coord_eq` factors the Duhamel integrand
  `heatMode ν (t - s) f ξ = exp (-ν‖ξ‖²t) • (exp (ν‖ξ‖²s) • f ξ)` and pulls the
  `t`-dependent scalar out of the Bochner integral (`integral_smul`,
  `integral_Icc_eq_integral_Ioc`, `intervalIntegral.integral_of_le` — all
  unconditional).  For `t ≥ 0` the identity holds with NO regularity hypothesis.
* Differentiating `E · J` with the product rule: `J' = G(t₀)` is the moving-boundary
  Bochner FTC `intervalIntegral.integral_hasDerivAt_right`; `E' = -ν‖ξ‖² · E` is the
  scalar chain rule (`hasDerivAt_coe_exp_neg`).  The exponentials satisfy
  `E t₀ * exp (ν‖ξ‖²t₀) = 1`, so the boundary term is exactly the source value.
* The heat term differentiates to `-ν‖ξ‖²` times itself against the constant datum.

## What this file deliberately does NOT claim

* No physical-space derivative: transporting the identity through `𝓕⁻`
  (`physicalCoord`) is the remaining reconstruction obligation, and the Laplacian
  interpretation of the multiplier needs the moment/regularity facts listed as
  obligation 2 in the handoff notes.
* The two-sided derivative statement genuinely needs `t₀ > 0`; at `t₀ = 0` the file
  supplies the RIGHT derivative (`HasDerivWithinAt` for `Ici 0`) via the endpoint
  FTC `intervalIntegral.integral_hasDerivWithinAt_right` and the `FTCFilter`
  one-sided lattice — the value there is `-(ν‖ξ‖²) • a ξ + source`, since
  `mild(0) = a` and the Duhamel term vanishes.
* The three carried hypotheses on the weighted source `weightedSource ν u u ξ i`
  (interval-integrable on `[0, t₀]`, strongly measurable and continuous at `t₀`)
  are NOT verified here: the supplier is the admissible-ball trajectory
  (continuous in `t`, mixed-`X¹` estimates — obligation 4), exactly as the `hKint`
  hypothesis of `ContinuousLeiLinReality` awaits the same discharge.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Navier.Analysis.ContinuousLeiLinFrequencyODE

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Navier
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap

/-- The exponentially reweighted source coordinate `s ↦ exp (ν‖ξ‖²s) • (source s ξ i)`.
This is exactly the integrand the Duhamel factorisation reduces to after the
`exp (-ν‖ξ‖²t)` prefactor is pulled out of the integral; the three regularity
hypotheses below are stated on this function. -/
def weightedSource (ν : ℝ) (u v : ℝ → ES → ComplexSpace) (ξ : ES) (i : Fin 3) : ℝ → ℂ :=
  fun s => ((Real.exp (ν * ‖ξ‖ ^ 2 * s) : ℝ) : ℂ) • continuousNavierSource u v s ξ i

/-- Scalar calculus leaf: the cast exponential `t ↦ ((exp (-k t) : ℝ) : ℂ)` has
derivative `-k` times itself. -/
theorem hasDerivAt_coe_exp_neg (k t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ((Real.exp (-(k * t)) : ℝ) : ℂ))
      (-((k : ℂ)) • ((Real.exp (-(k * t₀)) : ℝ) : ℂ)) t₀ := by
  have h : HasDerivAt (fun t : ℝ => -(k * t)) (-k) t₀ :=
    ((hasDerivAt_id t₀).const_mul k).neg.congr_deriv (by rw [mul_one])
  have h2 := (Real.hasDerivAt_exp (-(k * t₀))).comp t₀ h
  refine' h2.ofReal_comp.congr_deriv _
  rw [smul_eq_mul, neg_mul, Complex.ofReal_mul, Complex.ofReal_neg, mul_neg]
  ring

/-- Heat-factorisation of the Duhamel integrand: the retarded multiplier splits
as `exp (-ν‖ξ‖²(t-s)) = exp (-ν‖ξ‖²t) * exp (ν‖ξ‖²s)`. -/
theorem heatMode_continuousNavierSource_smul (ν : ℝ) (u v : ℝ → ES → ComplexSpace)
    (t s : ℝ) (ξ : ES) (i : Fin 3) :
    heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u v s ζ i) ξ
      = ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ)
        • (weightedSource ν u v ξ i s) := by
  have hex : -(ν * ‖ξ‖ ^ 2 * (t - s)) = -(ν * ‖ξ‖ ^ 2 * t) + (ν * ‖ξ‖ ^ 2 * s) := by ring
  simp only [heatMode, weightedSource, smul_eq_mul]
  rw [hex, Real.exp_add, Complex.ofReal_mul, mul_assoc]

/-- **Pull-out identity** for one Duhamel coordinate, valid for every `t ≥ 0`
with no regularity hypothesis (every rewrite is an unconditional measure
identity).  The exponential prefactor leaves the Bochner integral and the
remaining integrand is exactly `weightedSource`. -/
theorem continuousDuhamel_coord_eq (ν : ℝ) (u v : ℝ → ES → ComplexSpace) (t : ℝ)
    (ht : 0 ≤ t) (ξ : ES) (i : Fin 3) :
    continuousDuhamel ν u v t ξ i =
      ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) *
        ∫ s in (0 : ℝ)..t, weightedSource ν u v ξ i s := by
  show ∫ s in Icc (0 : ℝ) t,
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u v s ζ i) ξ = _
  refine' (integral_congr_ae
    (ae_of_all (volume.restrict (Icc (0 : ℝ) t)) fun s =>
      heatMode_continuousNavierSource_smul ν u v t s ξ i)).trans _
  rw [integral_smul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    smul_eq_mul]

/-- **Per-frequency Duhamel time derivative.**  The three hypotheses are exactly
what the moving-boundary Bochner FTC consumes (`integral_hasDerivAt_right`); a
source profile continuous in time supplies all three.  The boundary term of the
product rule collapses because `exp (-ν‖ξ‖²t₀) · exp (ν‖ξ‖²t₀) = 1`, leaving the
unweighted source value at `t₀`. -/
theorem hasDerivAt_continuousDuhamel_coord (ν : ℝ) (u v : ℝ → ES → ComplexSpace)
    (ξ : ES) (i : Fin 3) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (hG_int : IntervalIntegrable (weightedSource ν u v ξ i) volume 0 t₀)
    (hG_meas : StronglyMeasurableAtFilter (weightedSource ν u v ξ i) (𝓝 t₀))
    (hG_cont : ContinuousAt (weightedSource ν u v ξ i) t₀) :
    HasDerivAt (fun t : ℝ => continuousDuhamel ν u v t ξ i)
      (-(((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • continuousDuhamel ν u v t₀ ξ i
        + continuousNavierSource u v t₀ ξ i) t₀ := by
  set E : ℝ → ℂ := fun t => ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) with hE
  set G : ℝ → ℂ := weightedSource ν u v ξ i with hG
  have key (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      continuousDuhamel ν u v t ξ i = E t * ∫ s in (0 : ℝ)..t, G s := by
    rw [hE, hG]
    exact continuousDuhamel_coord_eq ν u v t (mem_Ici.mp ht) ξ i
  have hJ : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, G s) (G t₀) t₀ := by
    convert intervalIntegral.integral_hasDerivAt_right hG_int hG_meas hG_cont using 1
  have hmul : HasDerivAt (fun t : ℝ => E t * ∫ s in (0 : ℝ)..t, G s)
      (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • (E t₀ * ∫ s in (0 : ℝ)..t₀, G s) + E t₀ * G t₀) t₀ :=
    ((hasDerivAt_coe_exp_neg (ν * ‖ξ‖ ^ 2) t₀).mul hJ).congr_deriv
      (by rw [smul_mul_assoc])
  have hevt : (fun t : ℝ => E t * ∫ s in (0 : ℝ)..t, G s)
      =ᶠ[𝓝 t₀] (fun t : ℝ => continuousDuhamel ν u v t ξ i) := by
    filter_upwards [Ioi_mem_nhds ht₀] with t ht
    exact (key t (mem_Ici.mpr (le_of_lt ht))).symm
  have hg0 : E t₀ * G t₀ = continuousNavierSource u v t₀ ξ i := by
    show ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t₀)) : ℝ) : ℂ) *
        (((Real.exp (ν * ‖ξ‖ ^ 2 * t₀) : ℝ) : ℂ) • continuousNavierSource u v t₀ ξ i)
        = continuousNavierSource u v t₀ ξ i
    have hexp : Real.exp (-(ν * ‖ξ‖ ^ 2 * t₀)) * Real.exp (ν * ‖ξ‖ ^ 2 * t₀) = 1 := by
      have hz : -(ν * ‖ξ‖ ^ 2 * t₀) + ν * ‖ξ‖ ^ 2 * t₀ = 0 := by ring
      rw [← Real.exp_add, hz, Real.exp_zero]
    rw [smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, hexp, Complex.ofReal_one, one_mul]
  exact ((hmul.congr_of_eventuallyEq hevt.symm).congr_deriv
    (by rw [key t₀ (mem_Ici.mpr (le_of_lt ht₀)), hg0]))

/-- Per-frequency heat term derivative: the free evolution solves `∂ₜ = -ν‖ξ‖²`. -/
theorem hasDerivAt_heatVec_coord (ν : ℝ) (a : ES → ComplexSpace) (ξ : ES) (i : Fin 3)
    (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => heatVec ν t a ξ i)
      (-(((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • heatVec ν t₀ a ξ i) t₀ :=
  ((hasDerivAt_coe_exp_neg (ν * ‖ξ‖ ^ 2) t₀).mul_const (a ξ i)).congr_deriv
    (by rw [show heatVec ν t₀ a ξ i = ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t₀)) : ℝ) : ℂ) * a ξ i
        from rfl, ← smul_mul_assoc])

/-- **Frequency ODE for one coordinate of the mild image**: for the self-driven
trajectory `u`, `∂ₜ mild = -(ν‖ξ‖²) • mild + source` at every `t₀ > 0`. -/
theorem hasDerivAt_continuousMildImage_coord (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace)
    (u : ℝ → ES → ComplexSpace) (t₀ : ℝ) (ht₀ : 0 < t₀) (ξ : ES) (i : Fin 3)
    (hG_int : IntervalIntegrable (weightedSource ν u u ξ i) volume 0 t₀)
    (hG_meas : StronglyMeasurableAtFilter (weightedSource ν u u ξ i) (𝓝 t₀))
    (hG_cont : ContinuousAt (weightedSource ν u u ξ i) t₀) :
    HasDerivAt (fun t : ℝ => continuousMildImage ν hν a u t ξ i)
      (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a u t₀ ξ i
        + continuousNavierSource u u t₀ ξ i) t₀ := by
  have h := (hasDerivAt_heatVec_coord ν a ξ i t₀).add
    (hasDerivAt_continuousDuhamel_coord ν u u ξ i t₀ ht₀ hG_int hG_meas hG_cont)
  exact h.congr_deriv (by rw [← add_assoc, ← smul_add, continuousMildImage_coord_apply])

/-- The profile-valued form of the frequency ODE at a fixed frequency. -/
theorem hasDerivAt_continuousMildImage (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace)
    (u : ℝ → ES → ComplexSpace) (t₀ : ℝ) (ht₀ : 0 < t₀) (ξ : ES)
    (hG_int : ∀ i : Fin 3, IntervalIntegrable (weightedSource ν u u ξ i) volume 0 t₀)
    (hG_meas : ∀ i : Fin 3, StronglyMeasurableAtFilter (weightedSource ν u u ξ i) (𝓝 t₀))
    (hG_cont : ∀ i : Fin 3, ContinuousAt (weightedSource ν u u ξ i) t₀) :
    HasDerivAt (fun t : ℝ => continuousMildImage ν hν a u t ξ)
      (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a u t₀ ξ
        + continuousNavierSource u u t₀ ξ) t₀ := by
  have h := (hasDerivAt_pi (ι := Fin 3)).mpr fun i =>
    hasDerivAt_continuousMildImage_coord ν hν a u t₀ ht₀ ξ i (hG_int i) (hG_meas i)
      (hG_cont i)
  refine' h.congr_deriv _
  ext i
  simp only [Pi.smul_apply, Pi.add_apply]

/-- A function is always interval-integrable on a zero-length interval
(`Ι 0 0 = ∅`, integrable on the empty set). -/
theorem intervalIntegrable_zero {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : IntervalIntegrable f volume (0 : ℝ) 0 := by
  rw [intervalIntegrable_iff]
  simp

/-- **Per-frequency Duhamel right derivative at `0`** (`HasDerivWithinAt` on `Ici 0`).
The endpoint FTC is consumed through the `FTCFilter` lattice: the interval-
integrability hypothesis is vacuous at `0` (zero-length interval,
`intervalIntegrable_zero`), so only the measurability and (two-sided, hence
right-)continuity hypotheses on the weighted source are carried. The boundary
value `E 0 * G 0` is the raw source because both carried exponentials vanish. -/
theorem hasDerivWithinAt_zero_continuousDuhamel_coord (ν : ℝ)
    (u v : ℝ → ES → ComplexSpace) (ξ : ES) (i : Fin 3)
    (hG_meas : StronglyMeasurableAtFilter (weightedSource ν u v ξ i) (𝓝 0))
    (hG_cont : ContinuousAt (weightedSource ν u v ξ i) 0) :
    HasDerivWithinAt (fun t : ℝ => continuousDuhamel ν u v t ξ i)
      (continuousNavierSource u v 0 ξ i) (Ici 0) 0 := by
  set E : ℝ → ℂ := fun t => ((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) with hE
  set G : ℝ → ℂ := weightedSource ν u v ξ i with hG
  have key (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      continuousDuhamel ν u v t ξ i = E t * ∫ s in (0 : ℝ)..t, G s := by
    rw [hE, hG]
    exact continuousDuhamel_coord_eq ν u v t (mem_Ici.mp ht) ξ i
  have hf0 : IntervalIntegrable G volume (0 : ℝ) 0 := intervalIntegrable_zero _
  have hmeas : StronglyMeasurableAtFilter G (𝓝[>] (0 : ℝ)) :=
    hG_meas.filter_mono nhdsWithin_le_nhds
  have hcont : ContinuousWithinAt G (Ioi 0) 0 := hG_cont.continuousWithinAt
  have hJ : HasDerivWithinAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, G s) (G 0) (Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right hf0 hmeas hcont
  have hE0 : HasDerivWithinAt E (-(((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • E 0) (Ici 0) 0 :=
    (hasDerivAt_coe_exp_neg (ν * ‖ξ‖ ^ 2) 0).hasDerivWithinAt
  have hg0 : E 0 * G 0 = continuousNavierSource u v 0 ξ i := by
    show ((Real.exp (-(ν * ‖ξ‖ ^ 2 * 0)) : ℝ) : ℂ) *
        (((Real.exp (ν * ‖ξ‖ ^ 2 * 0) : ℝ) : ℂ) • continuousNavierSource u v 0 ξ i)
        = continuousNavierSource u v 0 ξ i
    have hexp : Real.exp (-(ν * ‖ξ‖ ^ 2 * 0)) * Real.exp (ν * ‖ξ‖ ^ 2 * 0) = 1 := by
      have hz : -(ν * ‖ξ‖ ^ 2 * 0) + ν * ‖ξ‖ ^ 2 * 0 = 0 := by ring
      rw [← Real.exp_add, hz, Real.exp_zero]
    rw [smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, hexp, Complex.ofReal_one, one_mul]
  have hmul :=
    (hE0.mul hJ).congr_of_eventuallyEq_of_mem (Filter.Eventually.of_forall (fun _ => rfl))
      (mem_Ici.mpr (le_refl (0 : ℝ)))
  have hevt : (fun t : ℝ => E t * ∫ s in (0 : ℝ)..t, G s)
      =ᶠ[𝓝[Ici (0 : ℝ)] (0 : ℝ)] (fun t : ℝ => continuousDuhamel ν u v t ξ i) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (key t ht).symm
  have hfinal :=
    hmul.congr_of_eventuallyEq_of_mem hevt.symm (mem_Ici.mpr (le_refl (0 : ℝ)))
  exact hfinal.congr_deriv
    (by rw [intervalIntegral.integral_same, mul_zero, zero_add]; exact hg0)

/-- **Frequency ODE at `t₀ = 0`, right derivative**:
`∂ₜ⁺ mild(0) = -(ν‖ξ‖²) • mild(0) + source(0)` with `mild(0) = a ξ` — the same
value form as `hasDerivAt_continuousMildImage_coord`, covering the initial time. -/
theorem hasDerivWithinAt_zero_continuousMildImage_coord (ν : ℝ) (hν : 0 < ν)
    (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace) (ξ : ES) (i : Fin 3)
    (hG_meas : StronglyMeasurableAtFilter (weightedSource ν u u ξ i) (𝓝 0))
    (hG_cont : ContinuousAt (weightedSource ν u u ξ i) 0) :
    HasDerivWithinAt (fun t : ℝ => continuousMildImage ν hν a u t ξ i)
      (-(((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • continuousMildImage ν hν a u 0 ξ i
        + continuousNavierSource u u 0 ξ i) (Ici 0) 0 := by
  have hD0 : continuousDuhamel ν u u 0 ξ i = 0 := by
    rw [continuousDuhamel_coord_eq ν u u 0 (le_refl 0) ξ i, intervalIntegral.integral_same,
      mul_zero]
  have h := (hasDerivAt_heatVec_coord ν a ξ i 0).hasDerivWithinAt.add
    (hasDerivWithinAt_zero_continuousDuhamel_coord ν u u ξ i hG_meas hG_cont)
  exact h.congr_deriv (by rw [continuousMildImage_coord_apply, hD0, add_zero])

/-- Profile-valued right-derivative form of the frequency ODE at `t₀ = 0`. -/
theorem hasDerivWithinAt_zero_continuousMildImage (ν : ℝ) (hν : 0 < ν)
    (a : ES → ComplexSpace) (u : ℝ → ES → ComplexSpace) (ξ : ES)
    (hG_meas : ∀ i : Fin 3, StronglyMeasurableAtFilter (weightedSource ν u u ξ i) (𝓝 0))
    (hG_cont : ∀ i : Fin 3, ContinuousAt (weightedSource ν u u ξ i) 0) :
    HasDerivWithinAt (fun t : ℝ => continuousMildImage ν hν a u t ξ)
      (-(((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ)) • continuousMildImage ν hν a u 0 ξ
        + continuousNavierSource u u 0 ξ) (Ici 0) 0 := by
  have h := hasDerivWithinAt_pi.mpr fun i =>
    hasDerivWithinAt_zero_continuousMildImage_coord ν hν a u ξ i (hG_meas i) (hG_cont i)
  refine' h.congr_deriv _
  ext i
  simp only [Pi.smul_apply, Pi.add_apply]

end Navier.Analysis.ContinuousLeiLinFrequencyODE

#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.hasDerivAt_coe_exp_neg
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.heatMode_continuousNavierSource_smul
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.continuousDuhamel_coord_eq
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.hasDerivAt_continuousDuhamel_coord
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.hasDerivAt_heatVec_coord
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.hasDerivAt_continuousMildImage_coord
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.hasDerivAt_continuousMildImage
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.intervalIntegrable_zero
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.hasDerivWithinAt_zero_continuousDuhamel_coord
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.hasDerivWithinAt_zero_continuousMildImage_coord
#print axioms Navier.Analysis.ContinuousLeiLinFrequencyODE.hasDerivWithinAt_zero_continuousMildImage
