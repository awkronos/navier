import Navier.Analysis.ContinuousLeiLinPhysicalSmoothing
import Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing
import Navier.Analysis.ContinuousLeiLinSelfMap
import Navier.Analysis.ContinuousLeiLinPhysicalVelocity
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Domination for the physical-velocity time ODE (obligation 1)

The frequency-side module (`ContinuousLeiLinFrequencyODE`) already proves, for
each fixed frequency `ξ` and coordinate `i`, that the mild trajectory
`t ↦ continuousMildImage ν hν a u t ξ i` satisfies the pointwise ODE
`d/dt = -(ν‖ξ‖²)•U + src` at positive times.  Inverting the Fourier transform
does NOT commute with a pointwise-in-`ξ` derivative: the crown-level
obligation is the same identity after `𝓕⁻`, and its honest content is the
dominated-convergence package for

```
ξ ↦ 𝐞 ⟪ξ, x⟫ • ( -((ν * ‖ξ‖² : ℝ) : ℂ) • continuousMildImage ν hν a u s ξ i
                 + continuousNavierSource u u s ξ i )
```

uniform for `s` in one neighbourhood of `t` (a *single* set `u ∈ 𝓝 t₀` on
which the derivative and the envelope hold simultaneously for almost every
`ξ`).  This module supplies that package:

* `hasDerivAt_physicalCoord_of_dominated` / `hasDerivAt_physicalVelocity_of_dominated`:
  the abstract transport through `𝓕⁻` (the Bochner
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` fed with the unitary
  kernel `‖𝐞·‖ = 1`) — the obligation is thereby reduced to an explicit
  `∃ g, Integrable g ∧ ∀ᵐ ξ, ∀ s ∈ u, ‖dv s ξ i‖ ≤ g ξ` envelope.
* `exists_integrable_envelope_heatVec_deriv`: the heat-semigroup part of the
  envelope, uniform on `Ioi (t₀/2)`, from the `X¹` moment of the initial
  datum — fully closed here.
* `exists_integrable_envelope_duhamelBefore_deriv`: the strict-past Duhamel
  part, uniform on `Ioi ((t₀+τ)/2)`, from the joint `X⁻¹` spacetime source
  moment over `[0, τ]` — fully closed here via heat-lag monotonicity.

**Visible residual.**  The full obligation-1 envelope is the sum of three
pieces: heat (closed), strict-past Duhamel (closed), and the RECENT TAIL
`∫ s in Icc τ t` together with the source term `ξ ↦
‖continuousNavierSource u u s ξ i‖`, each required uniformly for `s` in a
whole neighbourhood of `t₀`.  Pointwise-in-`s` these are closed
(`integrable_pow_norm_continuousDuhamelRecent_of_source`,
`integrable_pow_norm_continuousNavierSource`); uniform-in-`s` they need the
joint degree-2 spacetime source moment over every window `[τ, t₀+ε]`, which
propagates to degree-3 profile moments (`continuousNavierBilinear` loses one
degree) — the moment-ladder wall named in the swarm notes.
`exists_integrable_envelope_mildImage_deriv` below instantiates the transport
with the residual pieces as explicit premises so the remaining quantifier is
visible, and `hasDerivAt_physicalVelocity_continuousMildImage` is the pointwise
ODE in physical coordinates modulo exactly that envelope.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Topology Filter Set
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace Navier.Analysis.ContinuousLeiLinPhysicalODEDomination

open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinPhysicalCarrier
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ContinuousLeiLinPhysicalSmoothing
open Navier.Analysis.ContinuousLeiLinDuhamelPhysicalSmoothing
open Navier.Analysis.ContinuousLeiLinPhysicalVelocity
open Navier.Analysis.ContinuousLeiLinSelfMap

/-- The heat multiplier evaluated pointwise on the complex carrier.
Reproduces the private `Dissipation.norm_heatMode` at this use site. -/
private theorem norm_heatMode (ν t : ℝ) (f : ES → ℂ) (ξ : ES) :
    ‖heatMode ν t f ξ‖ = Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖f ξ‖ := by
  show ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * f ξ‖ = _
  rw [Complex.norm_mul, Complex.norm_real]
  exact congrArg (fun e : ℝ => e * ‖f ξ‖)
    (Real.norm_of_nonneg (Real.exp_pos _).le)

/-- The Fourier kernel is a unit multiplier on `ℂ`. -/
private theorem norm_smul_fourierChar (t : ℝ) (z : ℂ) : ‖𝐞 t • z‖ = ‖z‖ := by
  simp

/-- The Fourier kernel, coerced to `ℂ`, has norm one. -/
private theorem norm_fourierChar (t : ℝ) : ‖(𝐞 t : ℂ)‖ = 1 := by
  have h : (𝐞 t : ℂ) = 𝐞 t • (1 : ℂ) := by simp [Circle.smul_def, smul_eq_mul]
  rw [h, norm_smul_fourierChar]
  simp

/-! ## 1. The transport: dominated differentiation through `𝓕⁻` -/

/-- **Fourier-inverted dominated time derivative.**  If a frequency
trajectory `w s ξ i` is differentiable in `s` for almost every `ξ` on a
single neighbourhood set `u ∈ 𝓝 t₀`, its derivative is dominated on `u` by a
fixed `L¹` envelope, and `w t₀ ξ i` is itself `L¹`, then the physical
coordinate `physicalCoord (w s) i` is differentiable at `t₀` with derivative
the inverse Fourier transform of the derivative at `t₀`.  This is
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` transported across the
`Real.fourierInv_eq` unfolding; the kernel `𝐞 ⟪ξ, x⟫` is unitary, so the same
envelope dominates the inverted integrand. -/
theorem hasDerivAt_physicalCoord_of_dominated
    (w dv : ℝ → ES → ComplexSpace) (i : Fin 3) (x : ES) (t₀ : ℝ) (u : Set ℝ)
    (hu : u ∈ 𝓝 t₀)
    (hw_meas : ∀ᶠ s in 𝓝 t₀, AEStronglyMeasurable (fun ξ : ES => w s ξ i))
    (hw_int : Integrable (fun ξ : ES => w t₀ ξ i))
    (hdv_meas : AEStronglyMeasurable (fun ξ : ES => dv t₀ ξ i))
    (hdv_bound : ∃ g : ES → ℝ, Integrable g ∧
      ∀ᵐ ξ ∂volume, ∀ s ∈ u, ‖dv s ξ i‖ ≤ g ξ)
    (hdv_diff : ∀ᵐ ξ ∂volume, ∀ s ∈ u,
      HasDerivAt (fun r : ℝ => w r ξ i) (dv s ξ i) s) :
    HasDerivAt (fun s : ℝ => physicalCoord (w s) i x)
      (physicalCoord (dv t₀) i x) t₀ := by
  obtain ⟨g, hg_int, hg_bound⟩ := hdv_bound
  have hker_aesm : AEStronglyMeasurable (fun ξ : ES => (𝐞 ⟪ξ, x⟫ : ℂ)) := by
    fun_prop
  -- measurability and integrability of the inverted integrands
  have hF_meas : ∀ᶠ s in 𝓝 t₀,
      AEStronglyMeasurable (fun ξ : ES => 𝐞 ⟪ξ, x⟫ • w s ξ i) := by
    filter_upwards [hw_meas] with s hs
    have : (fun ξ : ES => 𝐞 ⟪ξ, x⟫ • w s ξ i) =
        fun ξ : ES => (𝐞 ⟪ξ, x⟫ : ℂ) * w s ξ i := by
      funext ξ; rw [Circle.smul_def, smul_eq_mul]
    rw [this]; exact hker_aesm.mul hs
  have hF_int : Integrable (fun ξ : ES => 𝐞 ⟪ξ, x⟫ • w t₀ ξ i) := by
    have : (fun ξ : ES => 𝐞 ⟪ξ, x⟫ • w t₀ ξ i) =
        fun ξ : ES => w t₀ ξ i * (𝐞 ⟪ξ, x⟫ : ℂ) := by
      funext ξ
      rw [Circle.smul_def, smul_eq_mul, mul_comm]
    rw [this]
    refine hw_int.mul_bdd (c := 1) hker_aesm ?_
    exact MeasureTheory.ae_of_all volume fun ξ => (norm_fourierChar _).le
  have hG_meas : AEStronglyMeasurable (fun ξ : ES => 𝐞 ⟪ξ, x⟫ • dv t₀ ξ i) := by
    have : (fun ξ : ES => 𝐞 ⟪ξ, x⟫ • dv t₀ ξ i) =
        fun ξ : ES => dv t₀ ξ i * (𝐞 ⟪ξ, x⟫ : ℂ) := by
      funext ξ
      rw [Circle.smul_def, smul_eq_mul, mul_comm]
    rw [this]; exact hdv_meas.mul hker_aesm
  -- the envelope transfers across the unitary kernel
  have hG_bound : ∀ᵐ ξ ∂volume, ∀ s ∈ u,
      ‖𝐞 ⟪ξ, x⟫ • dv s ξ i‖ ≤ g ξ := by
    filter_upwards [hg_bound] with ξ hξ s hs
    rw [norm_smul_fourierChar]; exact hξ s hs
  -- differentiability transfers across the unitary kernel
  have hG_diff : ∀ᵐ ξ ∂volume, ∀ s ∈ u,
      HasDerivAt (fun r : ℝ => 𝐞 ⟪ξ, x⟫ • w r ξ i) (𝐞 ⟪ξ, x⟫ • dv s ξ i) s := by
    filter_upwards [hdv_diff] with ξ hξ s hs
    have key : HasDerivAt (fun r : ℝ => (𝐞 ⟪ξ, x⟫ : ℂ) * w r ξ i)
        ((𝐞 ⟪ξ, x⟫ : ℂ) * dv s ξ i) s :=
      (hξ s hs).const_mul (𝐞 ⟪ξ, x⟫ : ℂ)
    convert key using 1
    · funext r; simp [Circle.smul_def, smul_eq_mul]
    · simp [Circle.smul_def, smul_eq_mul]
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ES)) hu hF_meas hF_int hG_meas hG_bound hg_int hG_diff
  have hinv : ∀ s : ℝ, physicalCoord (w s) i x =
      ∫ ξ : ES, 𝐞 ⟪ξ, x⟫ • w s ξ i ∂volume := by
    intro s
    rw [physicalCoord, Real.fourierInv_eq]
  have hinv' : physicalCoord (dv t₀) i x =
      ∫ ξ : ES, 𝐞 ⟪ξ, x⟫ • dv t₀ ξ i ∂volume := by
    rw [physicalCoord, Real.fourierInv_eq]
  -- transport the differentiated integral form back to `physicalCoord`
  have hF : HasDerivAt (fun s : ℝ => physicalCoord (w s) i x)
      (∫ ξ : ES, 𝐞 ⟪ξ, x⟫ • dv t₀ ξ i ∂volume) t₀ :=
    hD.2.congr_of_eventuallyEq (Eventually.of_forall hinv)
  exact hF.congr_deriv (hinv').symm

/-- **The physical-velocity dominated time derivative (obligation 1, reduced
form).**  The pointwise ODE in physical coordinates for the
`Navier.VelocityEvolution` built by `physicalVelocity`, modulo the explicit
`∃`-envelope premise.  The real part is taken through the continuous
linear map `Complex.reCLM`. -/
theorem hasDerivAt_physicalVelocity_of_dominated
    (w dv : ℝ → ES → ComplexSpace) (i : Fin 3) (x : Navier.Space) (t₀ : ℝ)
    (u : Set ℝ) (hu : u ∈ 𝓝 t₀)
    (hw_meas : ∀ᶠ s in 𝓝 t₀, AEStronglyMeasurable (fun ξ : ES => w s ξ i))
    (hw_int : Integrable (fun ξ : ES => w t₀ ξ i))
    (hdv_meas : AEStronglyMeasurable (fun ξ : ES => dv t₀ ξ i))
    (hdv_bound : ∃ g : ES → ℝ, Integrable g ∧
      ∀ᵐ ξ ∂volume, ∀ s ∈ u, ‖dv s ξ i‖ ≤ g ξ)
    (hdv_diff : ∀ᵐ ξ ∂volume, ∀ s ∈ u,
      HasDerivAt (fun r : ℝ => w r ξ i) (dv s ξ i) s) :
    HasDerivAt (fun s : ℝ => physicalVelocity w s x i)
      (realPhysicalCoord (dv t₀) i (euclidPoint x)) t₀ := by
  have h := hasDerivAt_physicalCoord_of_dominated w dv i (euclidPoint x) t₀ u
    hu hw_meas hw_int hdv_meas hdv_bound hdv_diff
  have hre : HasDerivAt
      (fun s : ℝ => (physicalCoord (w s) i (euclidPoint x)).re)
      (physicalCoord (dv t₀) i (euclidPoint x)).re t₀ := by
    convert
      (Complex.reCLM.hasStrictFDerivAt.hasFDerivAt.comp _ h.hasFDerivAt).hasDerivAt
      using 1
    · rfl
    · rfl
    · funext s
      exact (Complex.reCLM_apply (physicalCoord (w s) i (euclidPoint x))).symm
    · rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.toSpanSingleton_apply_one, Complex.reCLM_apply]
  exact hre

/-! ## 2. The heat envelope, uniform for positive times -/

/-- **Heat part of the obligation-1 envelope.**  On the fixed neighbourhood
`Ioi (t₀/2)` of `t₀`, the integrand
`ξ ↦ ‖-(ν‖ξ‖²)•heatVec ν s a ξ i‖` is dominated by
`(ν * (√(ν t₀/2))⁻¹) • (fun ξ => ‖ξ‖ * ‖a ξ i‖)`: one power of `‖ξ‖` is
absorbed by the Gaussian, whose decay rate is monotone in `s` on the
neighbourhood. -/
theorem exists_integrable_envelope_heatVec_deriv (ν : ℝ) (hν : 0 < ν)
    (a : ES → ComplexSpace) (i : Fin 3) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (ha1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖)) :
    ∃ u ∈ 𝓝 t₀, ∃ g : ES → ℝ, Integrable g ∧
      ∀ᵐ ξ ∂volume, ∀ s ∈ u,
        ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • heatVec ν s a ξ i‖ ≤ g ξ := by
  set C : ℝ := ν * (Real.sqrt (ν * (t₀ / 2)))⁻¹ with hC
  refine ⟨Ioi (t₀ / 2), Ioi_mem_nhds (by linarith),
    fun ξ => C * (‖ξ‖ * ‖a ξ i‖), ha1.const_mul C, ?_⟩
  refine MeasureTheory.ae_of_all volume fun ξ => ?_
  intro s hs
  have hs0 : t₀ / 2 < s := hs
  have hexp : Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) ≤
      Real.exp (-((ν * (t₀ / 2)) * ‖ξ‖ * ‖ξ‖)) := by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have hz : 0 ≤ ν * ‖ξ‖ ^ 2 :=
      mul_nonneg hν.le (pow_nonneg (norm_nonneg _) 2)
    calc ν * (t₀ / 2) * ‖ξ‖ * ‖ξ‖
        _ = ν * (t₀ / 2) * ‖ξ‖ ^ 2 := by ring_nf
        _ ≤ ν * ‖ξ‖ ^ 2 * s := by
          have h1 := mul_le_mul_of_nonneg_right hs0.le hz
          simpa [mul_comm, mul_left_comm, mul_assoc] using h1
  have hpos : 0 < ν * (t₀ / 2) := by positivity
  have h1 : ‖ξ‖ * Real.exp (-((ν * (t₀ / 2)) * ‖ξ‖ * ‖ξ‖)) ≤
      (Real.sqrt (ν * (t₀ / 2)))⁻¹ := by
    have := pow_mul_exp_neg_mul_sq_le hpos (norm_nonneg ξ) 1
    simpa using this
  show ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • heatVec ν s a ξ i‖ ≤
    C * (‖ξ‖ * ‖a ξ i‖)
  calc ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • heatVec ν s a ξ i‖
      _ = ν * ‖ξ‖ ^ 2 * ‖heatVec ν s a ξ i‖ := by
        rw [norm_smul, norm_neg, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg hν.le (pow_nonneg (norm_nonneg _) 2))]
      _ = ν * ‖ξ‖ ^ 2 * (Real.exp (-(ν * ‖ξ‖ ^ 2 * s)) * ‖a ξ i‖) := by
        rw [show ‖heatVec ν s a ξ i‖ = ‖heatMode ν s (fun ζ : ES => a ζ i) ξ‖
            from rfl, norm_heatMode]
      _ ≤ ν * ‖ξ‖ ^ 2 * (Real.exp (-((ν * (t₀ / 2)) * ‖ξ‖ * ‖ξ‖)) * ‖a ξ i‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
          (mul_nonneg hν.le (pow_nonneg (norm_nonneg _) 2))
      _ = (ν * ‖ξ‖) * (‖ξ‖ *
          Real.exp (-((ν * (t₀ / 2)) * ‖ξ‖ * ‖ξ‖)) * ‖a ξ i‖) := by ring
      _ ≤ (ν * ‖ξ‖) * ((Real.sqrt (ν * (t₀ / 2)))⁻¹ * ‖a ξ i‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
          (mul_nonneg hν.le (norm_nonneg _))
      _ = ν * (Real.sqrt (ν * (t₀ / 2)))⁻¹ * (‖ξ‖ * ‖a ξ i‖) := by ring
      _ = C * (‖ξ‖ * ‖a ξ i‖) := by rw [← hC]

/-- Junk-tolerant pointwise monotonicity for the Bochner integral against an
integrable nonnegative majorant: a dominated function which is not integrable
has integral `0` (`integral_undef`), and the majorant's pointwise
nonnegativity (`integral_nonneg`) closes that case. -/
private theorem integral_mono_ae₀' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hg : Integrable g μ) (hfg : ∀ᵐ x ∂μ, f x ≤ g x)
    (hgnn : ∀ x, 0 ≤ g x) : ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := by
  by_cases hf : Integrable f μ
  · exact integral_mono_ae hf hg hfg
  · rw [integral_undef hf]
    exact integral_nonneg hgnn

/-! ## 3. The strict-past Duhamel envelope, uniform above the midpoint -/

/-- **Strict-past Duhamel part of the obligation-1 envelope.**  Fix `τ < t₀`
and assume the joint `X⁻¹` spacetime source moment over `[0, τ]`.  Then the
integrand `ξ ↦ ‖-(ν‖ξ‖²)•continuousDuhamelBefore ν τ u v s ξ i‖` is dominated
uniformly on `Ioi ((t₀+τ)/2)` by the `L¹` function

```
g ξ = ∫ r in Icc 0 τ, ‖-(ν‖ξ‖²)•heatMode ν (s₀ - r)
        (fun ζ => continuousNavierSource u v r ζ i) ξ‖ ∂r,   s₀ := (t₀+τ)/2
```

whose integrability is `integrable_weighted_heat_on_strict_past` at `s₀`
followed by one Fubini section (`Integrable.integral_prod_left`).  The
domination is heat-lag monotonicity: larger physical time `s` means a longer
lag `s - r ≥ s₀ - r` and a smaller Gaussian; the `∫ r in Icc 0 τ` set integral
of the definition converts definitionally to `∫ r, · ∂μ`. -/
theorem exists_integrable_envelope_duhamelBefore_deriv
    (u v : ℝ → ES → ComplexSpace) (i : Fin 3) (ν τ t₀ : ℝ)
    (hν : 0 < ν) (_hτ : 0 ≤ τ) (hτt : τ < t₀)
    (hmeas : AEStronglyMeasurable (fun p : ES × ℝ =>
      continuousNavierSource u v p.2 p.1 i)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ))))
    (hsrc : Integrable (fun p : ES × ℝ =>
      ‖p.1‖⁻¹ * ‖continuousNavierSource u v p.2 p.1 i‖)
      (volume.prod (volume.restrict (Icc (0 : ℝ) τ)))) :
    ∃ U ∈ 𝓝 t₀, ∃ g : ES → ℝ, Integrable g ∧
      ∀ᵐ ξ ∂volume, ∀ s ∈ U,
        ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) •
          continuousDuhamelBefore ν τ u v s ξ i‖ ≤ g ξ := by
  set μ := volume.restrict (Icc (0 : ℝ) τ)
  set s₀ : ℝ := (t₀ + τ) / 2
  have hs₀t : s₀ < t₀ := by show (t₀ + τ) / 2 < t₀; linarith
  have hs₀τ : τ < s₀ := by show τ < (t₀ + τ) / 2; linarith
  set P : ℝ → ES → ℝ → ℝ := fun s ξ r =>
    ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) •
      heatMode ν (s - r) (fun ζ : ES => continuousNavierSource u v r ζ i) ξ‖
  have hPexp : ∀ s ξ r, P s ξ r = ν * ‖ξ‖ ^ 2 *
      Real.exp (-(ν * ‖ξ‖ ^ 2 * (s - r))) *
      ‖continuousNavierSource u v r ξ i‖ := by
    intro s ξ r
    dsimp only [P]
    rw [norm_smul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hν.le (pow_nonneg (norm_nonneg _) 2)),
      norm_heatMode]
    ring
  have hPnn : ∀ s ξ r, 0 ≤ P s ξ r := fun s ξ r => norm_nonneg _
  have hJ : Integrable (fun p : ES × ℝ =>
      ‖p.1‖ ^ 2 • heatMode ν (s₀ - p.2)
        (fun ζ : ES => continuousNavierSource u v p.2 ζ i) p.1)
      (volume.prod μ) :=
    integrable_weighted_heat_on_strict_past
      (fun r ζ => continuousNavierSource u v r ζ i) ν τ s₀ hν hs₀τ 2 hmeas hsrc
  have hPs₀ : Integrable (fun p : ES × ℝ => P s₀ p.1 p.2) (volume.prod μ) := by
    convert (hJ.norm).const_mul ν using 1
    funext p
    rw [hPexp, norm_smul,
      Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2), norm_heatMode]
    try dsimp only
    ring
  have hsecs₀ : ∀ᵐ ξ ∂volume, Integrable (fun r : ℝ => P s₀ ξ r) μ :=
    ((integrable_prod_iff hPs₀.aestronglyMeasurable).mp hPs₀).1
  refine ⟨Ioi s₀, Ioi_mem_nhds hs₀t,
    fun ξ => ∫ r, P s₀ ξ r ∂μ, hPs₀.integral_prod_left, ?_⟩
  filter_upwards [hsecs₀] with ξ hsec₀
  intro s hs
  show ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamelBefore ν τ u v s ξ i‖ ≤
    ∫ r, P s₀ ξ r ∂μ
  have hmono : ∀ r, P s ξ r ≤ P s₀ ξ r := by
    intro r
    have he1 := hPexp s ξ r
    have he2 := hPexp s₀ ξ r
    rw [he1, he2]
    have hz : 0 ≤ ν * ‖ξ‖ ^ 2 :=
      mul_nonneg hν.le (pow_nonneg (norm_nonneg _) 2)
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg
          (mul_le_mul_of_nonneg_left (sub_le_sub_right hs.le r) hz))) hz)
      (norm_nonneg _)
  have h1 : continuousDuhamelBefore ν τ u v s ξ i =
      ∫ r in Icc (0 : ℝ) τ,
        heatMode ν (s - r)
          (fun ζ : ES => continuousNavierSource u v r ζ i) ξ := rfl
  calc ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamelBefore ν τ u v s ξ i‖
      _ = ‖∫ r : ℝ, -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) •
            heatMode ν (s - r)
              (fun ζ : ES => continuousNavierSource u v r ζ i) ξ ∂μ‖ := by
        rw [h1, ← integral_smul]
      _ ≤ ∫ r, ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) •
            heatMode ν (s - r)
              (fun ζ : ES => continuousNavierSource u v r ζ i) ξ‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = ∫ r, P s ξ r ∂μ := rfl
      _ ≤ ∫ r, P s₀ ξ r ∂μ :=
        integral_mono_ae₀' hsec₀ (MeasureTheory.ae_of_all μ fun r => hmono r)
          (fun r => hPnn s₀ ξ r)

/-! ## 4. Combining the three envelope pieces -/

/-- **The obligation-1 envelope for the full mild image.**  The heat piece is
provided by `exists_integrable_envelope_heatVec_deriv`, and the strict-past
Duhamel piece by `exists_integrable_envelope_duhamelBefore_deriv` after the
`[0, t] = [0, τ] ∪ [τ, t]` split; the RECENT-TAIL Duhamel piece and the
source piece remain as explicit premises — they are the visible residual of
the module header.  The envelope for a sum is the sum of the envelopes
restricted to a common neighbourhood set. -/
theorem exists_integrable_envelope_mildImage_deriv
    (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (i : Fin 3) (t₀ : ℝ) (ht₀ : 0 < t₀)
    (ha1 : Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (hd : ∃ u ∈ 𝓝 t₀, ∃ g : ES → ℝ, Integrable g ∧
        ∀ᵐ ξ ∂volume, ∀ s ∈ u,
          ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamel ν v v s ξ i‖ ≤ g ξ)
    (hsrc : ∃ u ∈ 𝓝 t₀, ∃ g : ES → ℝ, Integrable g ∧
        ∀ᵐ ξ ∂volume, ∀ s ∈ u,
          ‖continuousNavierSource v v s ξ i‖ ≤ g ξ) :
    ∃ u ∈ 𝓝 t₀, ∃ g : ES → ℝ, Integrable g ∧ ∀ᵐ ξ ∂volume, ∀ s ∈ u,
      ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v s ξ i
        + continuousNavierSource v v s ξ i‖ ≤ g ξ := by
  obtain ⟨u₁, hu₁, g₁, hg₁, hb₁⟩ :=
    exists_integrable_envelope_heatVec_deriv ν hν a i t₀ ht₀ ha1
  obtain ⟨u₂, hu₂, g₂, hg₂, hb₂⟩ := hd
  obtain ⟨u₃, hu₃, g₃, hg₃, hb₃⟩ := hsrc
  refine ⟨u₁ ∩ u₂ ∩ u₃, inter_mem (inter_mem hu₁ hu₂) hu₃,
    fun ξ => g₁ ξ + g₂ ξ + g₃ ξ, hg₁.add hg₂ |>.add hg₃, ?_⟩
  filter_upwards [hb₁, hb₂, hb₃] with ξ h1 h2 h3
  intro s hs
  show ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v s ξ i
      + continuousNavierSource v v s ξ i‖ ≤ g₁ ξ + g₂ ξ + g₃ ξ
  have heq : -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v s ξ i
      + continuousNavierSource v v s ξ i =
      (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • heatVec ν s a ξ i)
        + ((-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamel ν v v s ξ i)
          + continuousNavierSource v v s ξ i) := by
    show (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) •
        (heatVec ν s a ξ + continuousDuhamel ν v v s ξ) i)
        + continuousNavierSource v v s ξ i = _
    rw [Pi.add_apply, smul_add, add_assoc]
  rw [heq]
  calc ‖(-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • heatVec ν s a ξ i)
        + ((-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamel ν v v s ξ i)
          + continuousNavierSource v v s ξ i)‖
      _ ≤ ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • heatVec ν s a ξ i‖
        + ‖(-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamel ν v v s ξ i)
          + continuousNavierSource v v s ξ i‖ := norm_add_le _ _
      _ ≤ ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • heatVec ν s a ξ i‖
        + ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamel ν v v s ξ i‖
        + ‖continuousNavierSource v v s ξ i‖ := by
        have hx : ‖(-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamel ν v v s ξ i)
            + continuousNavierSource v v s ξ i‖
            ≤ ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousDuhamel ν v v s ξ i‖
              + ‖continuousNavierSource v v s ξ i‖ := norm_add_le _ _
        linarith
      _ ≤ g₁ ξ + g₂ ξ + g₃ ξ :=
        add_le_add (add_le_add (h1 s hs.1.1) (h2 s hs.1.2)) (h3 s hs.2)

/-! ## 5. The pointwise physical ODE, modulo the envelope -/

/-- **Pointwise ODE for the physical velocity of the continuous Lei-Lin mild
image (obligation 1, physical form).**  Given the frequency-side pointwise ODE
on a common neighbourhood set (`hdv_diff`, produced coordinatewise by
`hasDerivAt_continuousMildImage_coord` once its weighted-source premises are
discharged) and the obligation-1 envelope (`henv`, assembled by
`exists_integrable_envelope_mildImage_deriv` from the heat and strict-past
pieces closed here and the residual recent-tail pieces), the physical velocity
is pointwise differentiable with the Navier–Stokes right-hand side as its
derivative.  This is exactly the conclusion shape recorded by the previous
swarm lane for obligation 1; the only premise not produced by this module is
`henv`, whose missing half is named in the module header. -/
theorem hasDerivAt_physicalVelocity_continuousMildImage
    (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace) (v : ℝ → ES → ComplexSpace)
    (i : Fin 3) (x : Navier.Space) (t₀ : ℝ) (_ht₀ : 0 < t₀) (u : Set ℝ)
    (hu : u ∈ 𝓝 t₀)
    (hw_meas : ∀ᶠ s in 𝓝 t₀,
      AEStronglyMeasurable (fun ξ : ES => continuousMildImage ν hν a v s ξ i))
    (hw_int : Integrable (fun ξ : ES => continuousMildImage ν hν a v t₀ ξ i))
    (hdv_meas : AEStronglyMeasurable (fun ξ : ES =>
        -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v t₀ ξ i
          + continuousNavierSource v v t₀ ξ i))
    (hdv_diff : ∀ᵐ ξ ∂volume, ∀ s ∈ u,
        HasDerivAt (fun r : ℝ => continuousMildImage ν hν a v r ξ i)
          (-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v s ξ i
            + continuousNavierSource v v s ξ i) s)
    (henv : ∃ g : ES → ℝ, Integrable g ∧ ∀ᵐ ξ ∂volume, ∀ s ∈ u,
        ‖-((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v s ξ i
          + continuousNavierSource v v s ξ i‖ ≤ g ξ) :
    HasDerivAt (fun s : ℝ =>
        physicalVelocity (continuousMildImage ν hν a v) s x i)
      (realPhysicalCoord (fun ξ : ES =>
          -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v t₀ ξ
            + continuousNavierSource v v t₀ ξ) i (euclidPoint x)) t₀ := by
  set dv : ℝ → ES → ComplexSpace := fun s ξ =>
    fun j => -((ν * ‖ξ‖ ^ 2 : ℝ) : ℂ) • continuousMildImage ν hν a v s ξ j
      + continuousNavierSource v v s ξ j
  refine hasDerivAt_physicalVelocity_of_dominated (continuousMildImage ν hν a v)
    dv i x t₀ u hu hw_meas hw_int ?_ ?_ ?_
  · exact hdv_meas
  · exact henv
  · exact hdv_diff
