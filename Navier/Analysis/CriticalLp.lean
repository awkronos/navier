import Navier.Analysis.CriticalL3Integrable

/-!
# Faithful Mathlib `L^3` critical-space transport

This module replaces scalar-integral-only interfaces with Mathlib's genuine
`MemLp` predicate and `eLpNorm`.  Membership records almost-everywhere strong
measurability as well as finiteness of the extended `L^3` norm, so neither a
nonmeasurable field nor Mathlib's zero integral for a nonintegrable density can
inhabit the critical-space contract.

The bridge to the integrable cubic-density interface is exact once vector
almost-everywhere strong measurability is supplied.  Positive spatial critical
scaling preserves and reflects measurability, cubic-density integrability, and
`MemLp`; on genuine members its `eLpNorm` and real `lpNorm` are exactly
invariant.  These leaves compose into an exact parabolic-scaling equivalence
for finite uniform `L^3`-norm bounds on arbitrary time sets and on `[0,T)`.

No theorem here constructs a bound for a Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Navier.Analysis.CriticalLp

open Navier
open Navier.Analysis.Covariance
open Navier.Analysis.CriticalL3
open Navier.Analysis.CriticalL3Integrable
open Navier.EnergyObstruction

/-- The spatial part of critical Navier--Stokes scaling:
`f(x) ↦ lambda * f(lambda*x)`. -/
def criticalL3SpatialScale
    (lambda : ℝ) (f : Space → Space) : Space → Space :=
  fun x => lambda • f (lambda • x)

/-- In the exact vector-valued setting used by the project, genuine `L^3`
membership is equivalent to integrability of the cubic norm density once
almost-everywhere strong measurability of the vector field is known. -/
theorem memLp_three_iff_integrable_norm_cube
    {f : Space → Space} (hf : AEStronglyMeasurable f volume) :
    MemLp f 3 volume ↔ Integrable (fun x => ‖f x‖ ^ 3) volume := by
  have h :=
    integrable_norm_rpow_iff (p := (3 : ℝ≥0∞)) hf
      (by norm_num) (by norm_num)
  simpa using h.symm

/-- Positive critical spatial scaling preserves and reflects vector
almost-everywhere strong measurability. -/
theorem aestronglyMeasurable_criticalL3SpatialScale_iff
    (lambda : ℝ) (hLambda : 0 < lambda) (f : Space → Space) :
    AEStronglyMeasurable (criticalL3SpatialScale lambda f) volume ↔
      AEStronglyMeasurable f volume := by
  constructor
  · intro hscaled
    have hcomp : AEStronglyMeasurable
        ((criticalL3SpatialScale lambda f) ∘
          fun x : Space => lambda⁻¹ • x) volume :=
      hscaled.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_smul volume
          (inv_ne_zero hLambda.ne'))
    have hres : AEStronglyMeasurable
        (lambda⁻¹ • ((criticalL3SpatialScale lambda f) ∘
          fun x : Space => lambda⁻¹ • x)) volume :=
      hcomp.const_smul lambda⁻¹
    have heq :
        lambda⁻¹ • ((criticalL3SpatialScale lambda f) ∘
          fun x : Space => lambda⁻¹ • x) = f := by
      funext x
      simp [criticalL3SpatialScale, Function.comp_apply, smul_smul,
        hLambda.ne']
    rw [heq] at hres
    exact hres
  · intro hf
    have hcomp : AEStronglyMeasurable
        (f ∘ fun x : Space => lambda • x) volume :=
      hf.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_smul volume hLambda.ne')
    have hres : AEStronglyMeasurable
        (lambda • (f ∘ fun x : Space => lambda • x)) volume :=
      hcomp.const_smul lambda
    have heq :
        lambda • (f ∘ fun x : Space => lambda • x) =
          criticalL3SpatialScale lambda f := by
      rfl
    rw [heq] at hres
    exact hres

/-- Positive critical spatial scaling preserves and reflects integrability of
the cubic norm density. -/
theorem integrable_norm_cube_criticalL3SpatialScale_iff
    (lambda : ℝ) (hLambda : 0 < lambda) (f : Space → Space) :
    Integrable (fun x => ‖criticalL3SpatialScale lambda f x‖ ^ 3) volume ↔
      Integrable (fun x => ‖f x‖ ^ 3) volume := by
  let g : Space → ℝ := fun y => ‖f y‖ ^ 3
  calc
    Integrable (fun x => ‖criticalL3SpatialScale lambda f x‖ ^ 3) volume ↔
        Integrable (fun x : Space => lambda ^ 3 * g (lambda • x)) volume := by
      simp only [criticalL3SpatialScale, norm_smul, Real.norm_eq_abs,
        abs_of_pos hLambda, mul_pow, g]
    _ ↔ Integrable (fun x : Space => g (lambda • x)) volume :=
      integrable_const_mul_iff
        (isUnit_iff_ne_zero.mpr (pow_ne_zero 3 hLambda.ne')) _
    _ ↔ Integrable g volume :=
      integrable_comp_smul_iff volume g hLambda.ne'
    _ ↔ Integrable (fun x => ‖f x‖ ^ 3) volume := by
      rfl

/-- Positive critical spatial scaling preserves and reflects genuine Mathlib
`L^3` membership. -/
theorem memLp_three_criticalL3SpatialScale_iff
    (lambda : ℝ) (hLambda : 0 < lambda) (f : Space → Space) :
    MemLp (criticalL3SpatialScale lambda f) 3 volume ↔
      MemLp f 3 volume := by
  constructor
  · intro hscaled
    have hmeas : AEStronglyMeasurable f volume :=
      (aestronglyMeasurable_criticalL3SpatialScale_iff
        lambda hLambda f).mp hscaled.1
    apply (memLp_three_iff_integrable_norm_cube hmeas).mpr
    exact
      (integrable_norm_cube_criticalL3SpatialScale_iff
        lambda hLambda f).mp (hscaled.integrable_norm_pow (by norm_num))
  · intro hf
    have hmeas :
        AEStronglyMeasurable (criticalL3SpatialScale lambda f) volume :=
      (aestronglyMeasurable_criticalL3SpatialScale_iff
        lambda hLambda f).mpr hf.1
    apply (memLp_three_iff_integrable_norm_cube hmeas).mpr
    exact
      (integrable_norm_cube_criticalL3SpatialScale_iff
        lambda hLambda f).mpr (hf.integrable_norm_pow (by norm_num))

/-- On a genuine `L^3` member, the extended `L^3` norm is exactly invariant
under positive critical spatial scaling.  Membership is established before
the integral representation is used, so this cannot reduce to a
nonintegrable `0 = 0`. -/
theorem eLpNorm_three_criticalL3SpatialScale
    (lambda : ℝ) (hLambda : 0 < lambda) (f : Space → Space)
    (hf : MemLp f 3 volume) :
    eLpNorm (criticalL3SpatialScale lambda f) 3 volume =
      eLpNorm f 3 volume := by
  have hscaled : MemLp (criticalL3SpatialScale lambda f) 3 volume :=
    (memLp_three_criticalL3SpatialScale_iff lambda hLambda f).mpr hf
  rw [hscaled.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num
  rw [show (fun x => ‖criticalL3SpatialScale lambda f x‖ ^ 3) =
      (fun x => ‖lambda • f (lambda • x)‖ ^ 3) by rfl]
  rw [l3_critical_dilation lambda hLambda f]

/-- The real-valued Mathlib `L^3` norm is likewise exactly invariant on
genuine members. -/
theorem lpNorm_three_criticalL3SpatialScale
    (lambda : ℝ) (hLambda : 0 < lambda) (f : Space → Space)
    (hf : MemLp f 3 volume) :
    lpNorm (criticalL3SpatialScale lambda f) 3 volume =
      lpNorm f 3 volume := by
  have hscaled : MemLp (criticalL3SpatialScale lambda f) 3 volume :=
    (memLp_three_criticalL3SpatialScale_iff lambda hLambda f).mpr hf
  rw [← toReal_eLpNorm hscaled.1, ← toReal_eLpNorm hf.1]
  rw [eLpNorm_three_criticalL3SpatialScale lambda hLambda f hf]

/-- Slice-level bridge from genuine `L^3` membership to the earlier
integrable-density predicate.  The reverse direction needs the displayed
vector measurability hypothesis, which the scalar-density predicate alone does
not contain. -/
theorem memLp_three_iff_l3SliceIntegrable
    (u : VelocityEvolution) (t : ℝ)
    (hu : AEStronglyMeasurable (u t) volume) :
    MemLp (u t) 3 volume ↔ L3SliceIntegrable u t := by
  simpa only [L3SliceIntegrable] using
    (memLp_three_iff_integrable_norm_cube hu)

/-- Genuine spatial `L^3` membership of corresponding time slices is exactly
preserved by positive parabolic velocity scaling. -/
theorem memLp_three_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (t : ℝ) :
    MemLp ((parabolicScaledVelocity lambda u) t) 3 volume ↔
      MemLp (u (lambda ^ 2 * t)) 3 volume := by
  change MemLp
      (criticalL3SpatialScale lambda (u (lambda ^ 2 * t))) 3 volume ↔ _
  exact memLp_three_criticalL3SpatialScale_iff
    lambda hLambda (u (lambda ^ 2 * t))

/-- The extended `L^3` norm of corresponding parabolic time slices is exactly
invariant, assuming genuine membership of the original slice. -/
theorem eLpNorm_three_parabolicScaled
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (t : ℝ)
    (hu : MemLp (u (lambda ^ 2 * t)) 3 volume) :
    eLpNorm ((parabolicScaledVelocity lambda u) t) 3 volume =
      eLpNorm (u (lambda ^ 2 * t)) 3 volume := by
  change eLpNorm
      (criticalL3SpatialScale lambda (u (lambda ^ 2 * t))) 3 volume = _
  exact eLpNorm_three_criticalL3SpatialScale
    lambda hLambda (u (lambda ^ 2 * t)) hu

/-- The corresponding real-valued `L^3` norms are exactly invariant on
genuine members. -/
theorem lpNorm_three_parabolicScaled
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (t : ℝ)
    (hu : MemLp (u (lambda ^ 2 * t)) 3 volume) :
    lpNorm ((parabolicScaledVelocity lambda u) t) 3 volume =
      lpNorm (u (lambda ^ 2 * t)) 3 volume := by
  change lpNorm
      (criticalL3SpatialScale lambda (u (lambda ^ 2 * t))) 3 volume = _
  exact lpNorm_three_criticalL3SpatialScale
    lambda hLambda (u (lambda ^ 2 * t)) hu

/-- A faithful uniform critical-space contract: the bound is a finite
extended real, every selected slice is a genuine `L^3` member, and its actual
Mathlib `eLpNorm` is bounded. -/
def CriticalL3MemLpBoundOn
    (u : VelocityEvolution) (times : Set ℝ) (B : ℝ≥0∞) : Prop :=
  B < ∞ ∧
    ∀ t ∈ times,
      MemLp (u t) 3 volume ∧ eLpNorm (u t) 3 volume ≤ B

/-- The faithful uniform `MemLp`/`eLpNorm` contract is exactly covariant when
the time set is transported by positive parabolic dilation. -/
theorem criticalL3MemLpBoundOn_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (times : Set ℝ) (B : ℝ≥0∞) :
    CriticalL3MemLpBoundOn
        (parabolicScaledVelocity lambda u) times B ↔
      CriticalL3MemLpBoundOn u
        ((fun t : ℝ => lambda ^ 2 * t) '' times) B := by
  constructor
  · rintro ⟨hB, h⟩
    refine ⟨hB, ?_⟩
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    have hAt := h t ht
    have hmem : MemLp (u (lambda ^ 2 * t)) 3 volume :=
      (memLp_three_parabolicScaled_iff lambda hLambda u t).mp hAt.1
    refine ⟨hmem, ?_⟩
    rw [← eLpNorm_three_parabolicScaled lambda hLambda u t hmem]
    exact hAt.2
  · rintro ⟨hB, h⟩
    refine ⟨hB, ?_⟩
    intro t ht
    have hAt := h (lambda ^ 2 * t) ⟨t, ht, rfl⟩
    have hmem : MemLp ((parabolicScaledVelocity lambda u) t) 3 volume :=
      (memLp_three_parabolicScaled_iff lambda hLambda u t).mpr hAt.1
    refine ⟨hmem, ?_⟩
    rw [eLpNorm_three_parabolicScaled lambda hLambda u t hAt.1]
    exact hAt.2

/-- Faithful uniform critical `L^3` control before a finite time is invariant
under positive parabolic scaling, with the time endpoint scaled by
`lambda^2`. -/
theorem criticalL3MemLpBoundBefore_parabolicScaled_iff
    (lambda : ℝ) (hLambda : 0 < lambda)
    (u : VelocityEvolution) (T : ℝ) (B : ℝ≥0∞) :
    CriticalL3MemLpBoundOn
        (parabolicScaledVelocity lambda u) (Set.Ico 0 T) B ↔
      CriticalL3MemLpBoundOn
        u (Set.Ico 0 (lambda ^ 2 * T)) B := by
  rw [criticalL3MemLpBoundOn_parabolicScaled_iff lambda hLambda]
  rw [time_dilation_image_Ico lambda T hLambda]

end Navier.Analysis.CriticalLp
