import Navier.Analysis.ContinuousLeiLinSpace
import Navier.Analysis.ContinuousLeiLinTimeDuhamel
import Navier.Analysis.ContinuousLeiLinDissipation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous Lei--Lin mild self-map budgets on `R^3`

The lattice driver `CriticalMildSmallDataGlobal.smallDataGlobalMild` closes its
fixed point on two budget facts evaluated on the spacetime ball
`sup_t ‖v t‖ <= 2 * ‖a‖`:

1. the image `X⁻¹` bound `‖mild image t‖ <= ‖a‖ + (3 * ν⁻¹) * (2 * ‖a‖)²`
   (lattice `norm_criticalMildImage_gap_le`);
2. the same bound for the time-integrated dissipation of the image, so the
   complete spacetime ball is preserved.

This module supplies the exact continuous analogues on the literal Fourier
carrier: the mild self-map `continuousMildImage` (free heat term plus the
quadratic Duhamel term of `ContinuousLeiLinTimeDuhamel`) obeys

* `coordinateXm1Mass` budget: the image's coordinate `X⁻¹` mass at every
  time is bounded by `coordinateXm1Mass a` plus `3` times the time integral
  of the interpolated mass product `coordinateXm1Mass * coordinateX1Mass`
  (`continuousMildImage_coordinateXm1Mass_le`);
* `coordinateX1Mass` budget: the image's time-integrated `X¹` mass on a
  horizon `[0, T]` is bounded by `ν⁻¹` times the same shape
  (`integral_coordinateX1Mass_continuousMildImage_le`).

Combined with the ball hypotheses `coordinateXm1Mass (u s) <= 2 * R` and
`∫₀ᵀ coordinateX1Mass (u s) ds <= 2 * ν⁻¹ * R` for `R := coordinateXm1Mass a`,
the two budgets close self-map-wise: the image `X⁻¹` budget is
`R + 12 * ν⁻¹ * R²` and the image dissipation budget `ν⁻¹ * (R + 12 * ν⁻¹ * R²)`,
so `R <= ν / 16` (the lattice threshold) gives `(7/4) * R` and
`(7/4) * ν⁻¹ * R` — strictly inside `(2 * R, 2 * ν⁻¹ * R)`.  This is the
weight-compatible transport of the `ε = ν / 16` small-data threshold from the
Fourier lattice onto the whole-space carrier, with the attained constant
reported honestly (lattice-matching `ν / 16`; the raw budget closes already at
`ν / 12`).  The remaining fixed-point obligations — contraction of the image
on the spacetime metric and completeness of the ball — are the named residual
of this module.

Reference: T. Kato, Math. Z. 187 (1984), "Strong `L^p`-solutions of the
Navier--Stokes equation in `R^m`"; Z. Lei and F. Lin, Comm. Pure Appl. Math.
64 (2011), Sec. 2--3 for the critical-space self-map scheme whose continuous
analogue is assembled here.
Mathlib inputs: `integral_mono`, `integral_add`, `integral_undef`,
`Measurable.pow_const`, `HasFiniteIntegral.mono`, `Integrable.mono`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set Filter Topology BigOperators
open scoped NNReal ENNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinDissipation

namespace Navier.Analysis.ContinuousLeiLinSelfMap

/-!
## Subadditivity of the coordinate masses

In the current Bochner convention the integral of a non-integrable function is
`0`, so subadditivity needs no measurability bookkeeping: a non-integrable sum
only strengthens the inequality.
-/

/-- The homogeneous `X⁻¹` mass is subadditive. -/
theorem normXm1_add_le (f g : ES -> ℂ)
    (hf : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖))
    (hg : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖g ξ‖)) :
    normXm1 (fun ξ : ES => f ξ + g ξ) ≤ normXm1 f + normXm1 g := by
  unfold normXm1
  have hw (ξ : ES) : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ξ)
  have hsum : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖f ξ‖ + ‖ξ‖⁻¹ * ‖g ξ‖) :=
    hf.add hg
  by_cases hL : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖(fun x : ES => f x + g x) ξ‖)
  · refine le_trans (integral_mono hL hsum ?_) ((integral_add hf hg).le)
    intro ξ
    calc
      ‖ξ‖⁻¹ * ‖(fun x : ES => f x + g x) ξ‖
          ≤ ‖ξ‖⁻¹ * (‖f ξ‖ + ‖g ξ‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le (f ξ) (g ξ)) (hw ξ)
      _ = ‖ξ‖⁻¹ * ‖f ξ‖ + ‖ξ‖⁻¹ * ‖g ξ‖ := by rw [mul_add]
  · rw [integral_undef hL]
    refine add_nonneg ?_ ?_
    · exact integral_nonneg fun ξ => mul_nonneg (hw ξ) (norm_nonneg _)
    · exact integral_nonneg fun ξ => mul_nonneg (hw ξ) (norm_nonneg _)

/-- The homogeneous `X¹` mass is subadditive. -/
theorem normX1_add_le (f g : ES -> ℂ)
    (hf : Integrable (fun ξ : ES => ‖ξ‖ * ‖f ξ‖))
    (hg : Integrable (fun ξ : ES => ‖ξ‖ * ‖g ξ‖)) :
    normX1 (fun ξ : ES => f ξ + g ξ) ≤ normX1 f + normX1 g := by
  unfold normX1
  have hw (ξ : ES) : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hsum : Integrable (fun ξ : ES => ‖ξ‖ * ‖f ξ‖ + ‖ξ‖ * ‖g ξ‖) :=
    hf.add hg
  by_cases hL : Integrable (fun ξ : ES => ‖ξ‖ * ‖(fun x : ES => f x + g x) ξ‖)
  · refine le_trans (integral_mono hL hsum ?_) ((integral_add hf hg).le)
    intro ξ
    calc
      ‖ξ‖ * ‖(fun x : ES => f x + g x) ξ‖
          ≤ ‖ξ‖ * (‖f ξ‖ + ‖g ξ‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le (f ξ) (g ξ)) (hw ξ)
      _ = ‖ξ‖ * ‖f ξ‖ + ‖ξ‖ * ‖g ξ‖ := by rw [mul_add]
  · rw [integral_undef hL]
    refine add_nonneg ?_ ?_
    · exact integral_nonneg fun ξ => mul_nonneg (hw ξ) (norm_nonneg _)
    · exact integral_nonneg fun ξ => mul_nonneg (hw ξ) (norm_nonneg _)

/-- Coordinate aggregation of `X⁻¹` subadditivity. -/
theorem coordinateXm1Mass_add_le (u v : ES -> ComplexSpace)
    (hu : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖u ξ i‖))
    (hv : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖v ξ i‖)) :
    coordinateXm1Mass (fun ξ : ES => u ξ + v ξ) ≤
      coordinateXm1Mass u + coordinateXm1Mass v := by
  unfold coordinateXm1Mass
  refine (Finset.sum_le_sum
    (f := fun i : Fin 3 => normXm1 (fun ξ : ES => u ξ i + v ξ i))
    (g := fun i : Fin 3 =>
      normXm1 (fun ξ : ES => u ξ i) + normXm1 (fun ξ : ES => v ξ i)) ?_).trans ?_
  · intro i _
    exact normXm1_add_le (fun ξ : ES => u ξ i) (fun ξ : ES => v ξ i) (hu i) (hv i)
  · rw [Finset.sum_add_distrib]

/-- Coordinate aggregation of `X¹` subadditivity. -/
theorem coordinateX1Mass_add_le (u v : ES -> ComplexSpace)
    (hu : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖))
    (hv : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖v ξ i‖)) :
    coordinateX1Mass (fun ξ : ES => u ξ + v ξ) ≤
      coordinateX1Mass u + coordinateX1Mass v := by
  unfold coordinateX1Mass
  refine (Finset.sum_le_sum
    (f := fun i : Fin 3 => normX1 (fun ξ : ES => u ξ i + v ξ i))
    (g := fun i : Fin 3 =>
      normX1 (fun ξ : ES => u ξ i) + normX1 (fun ξ : ES => v ξ i)) ?_).trans ?_
  · intro i _
    exact normX1_add_le (fun ξ : ES => u ξ i) (fun ξ : ES => v ξ i) (hu i) (hv i)
  · rw [Finset.sum_add_distrib]

/-!
## The mild self-map
-/

/-- The whole-space mild image at time `t`: the free heat term plus the
quadratic Duhamel term driven by the trajectory itself. -/
def continuousMildImage (ν : ℝ) (_hν : 0 < ν) (a : ES -> ComplexSpace)
    (u : ℝ -> ES -> ComplexSpace) (t : ℝ) (ξ : ES) : ComplexSpace :=
  heatVec ν t a ξ + continuousDuhamel ν u u t ξ

theorem continuousMildImage_coord_apply (ν : ℝ) (hν : 0 < ν)
    (a : ES -> ComplexSpace) (u : ℝ -> ES -> ComplexSpace)
    (t : ℝ) (ξ : ES) (i : Fin 3) :
    continuousMildImage ν hν a u t ξ i =
      heatVec ν t a ξ i + continuousDuhamel ν u u t ξ i := rfl

/-- The coordinate `X⁻¹` weight of the free heat term is integrable whenever
the datum's is: the heat multiplier is bounded by `1` for `t >= 0`. -/
private theorem heatVecXm1Integrable (a : ES -> ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖heatVec ν t a ξ i‖) := by
  have hw (ξ : ES) : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ξ)
  have hexpm : Measurable (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) := by
    refine Real.measurable_exp.comp ?_
    refine Measurable.neg ?_
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact measurable_const
    · exact continuous_norm.measurable.pow_const 2
    · exact measurable_const
  have hexp_aesm :
      AEStronglyMeasurable (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) :=
    hexpm.aestronglyMeasurable
  have hexp_pos : ∀ ξ : ES, 0 < Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) :=
    fun ξ => Real.exp_pos _
  have hexp_le : ∀ ξ : ES, Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) ≤ 1 := by
    intro ξ
    refine Real.exp_le_one_iff.mpr ?_
    have h1 : 0 ≤ ν * ‖ξ‖ ^ 2 * t := by positivity
    nlinarith
  have hpe (ξ : ES) : ‖ξ‖⁻¹ * ‖heatVec ν t a ξ i‖ =
      Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖a ξ i‖) := by
    show ‖ξ‖⁻¹ * ‖heatMode ν t (fun ζ : ES => a ζ i) ξ‖ = _
    have h1 : ‖heatMode ν t (fun ζ : ES => a ζ i) ξ‖ =
        Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖a ξ i‖ := by
      rw [heatMode]
      show ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * (fun ζ : ES => a ζ i) ξ‖ = _
      rw [Complex.norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hexp_pos ξ).le]
    rw [h1]
    ring
  have hR : Integrable (fun ξ : ES =>
      Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖⁻¹ * ‖a ξ i‖)) := by
    refine ⟨hexp_aesm.mul (ha i).aestronglyMeasurable,
      HasFiniteIntegral.mono (ha i).hasFiniteIntegral
        (Eventually.of_forall fun ξ => ?_)⟩
    have hn : 0 ≤ ‖ξ‖⁻¹ * ‖a ξ i‖ := mul_nonneg (hw ξ) (norm_nonneg _)
    have hn2 : 0 ≤ Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) := (hexp_pos ξ).le
    rw [Real.norm_of_nonneg (mul_nonneg hn2 hn), Real.norm_of_nonneg hn]
    nlinarith [hexp_le ξ]
  exact hR.congr (Eventually.of_forall fun ξ => (hpe ξ).symm)


/-!
## The `X⁻¹` self-map budget
-/

/-- Coordinate aggregation of the chunk-4 per-coordinate mild feed: the
coordinate `X⁻¹` mass of the quadratic Duhamel term at time `t` is bounded by
`3` times the time integral of the interpolated mass product, the exact
continuous analogue of the lattice fixed-point input
`(3 * ν⁻¹) * (2 * ‖a‖)²` after the gap budget is applied. -/
theorem coordinateXm1Mass_continuousDuhamel_self_le_integral_product
    (u : ℝ → ES → ComplexSpace) (ν t : ℝ) (hν : 0 < ν)
    (hb : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) •
          heatMode ν (t - p.2) (fun ζ : ES => continuousNavierSource u u p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u u s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource u u s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) t,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
          complexEuclideanNorm (continuousNavierSource u u s ξ)))
    (hi : Integrable (fun s : ℝ =>
        ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierSource u u s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hu : ∀ r j, AEStronglyMeasurable (fun η : ES => u r η j))
    (hu0 : ∀ r j, Integrable (fun η : ES => ‖u r η j‖))
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (h0sq : IntegrableOn (fun r => coordinateX0Mass (u r) ^ 2) (Icc (0 : ℝ) t))
    (hmixed : IntegrableOn (fun r =>
        coordinateXm1Mass (u r) * coordinateX1Mass (u r)) (Icc (0 : ℝ) t)) :
    coordinateXm1Mass (continuousDuhamel ν u u t) ≤
      3 * ∫ s in Icc (0 : ℝ) t,
        coordinateXm1Mass (u s) * coordinateX1Mass (u s) := by
  unfold coordinateXm1Mass
  refine (Finset.sum_le_sum
    (f := fun i : Fin 3 => normXm1 (fun ξ : ES => continuousDuhamel ν u u t ξ i))
    (g := fun _ : Fin 3 =>
      ∫ s in Icc (0 : ℝ) t, coordinateXm1Mass (u s) * coordinateX1Mass (u s)) ?_).trans_eq ?_
  · intro i _
    exact normXm1_continuousDuhamel_self_le_coordinateXm1X1 u ν t i hν (hb i) (hf i) (hg i)
      (fun s hs => hb0 s hs i) hs1 hi hu hu0 hum1 hu1 h0sq hmixed
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (↑(3 : ℕ) : ℝ) = 3 from rfl]
    delta coordinateXm1Mass
    rfl

/-- The mild self-map `X⁻¹` budget: at every forward time the coordinate
`X⁻¹` mass of `continuousMildImage` is bounded by the datum mass plus `3`
times the time-integrated interpolated mass product — the continuous analogue
of `norm_criticalMildImage_gap_le`. -/
theorem continuousMildImage_coordinateXm1Mass_le
    (ν : ℝ) (hν : 0 < ν) (a : ES -> ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (u : ℝ → ES → ComplexSpace) (t : ℝ) (ht : 0 ≤ t)
    (hd : ∀ i : Fin 3, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousDuhamel ν u u t ξ i‖))
    (hb : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) •
          heatMode ν (t - p.2) (fun ζ : ES => continuousNavierSource u u p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u u s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource u u s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) t,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
          complexEuclideanNorm (continuousNavierSource u u s ξ)))
    (hi : Integrable (fun s : ℝ =>
        ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierSource u u s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hu : ∀ r j, AEStronglyMeasurable (fun η : ES => u r η j))
    (hu0 : ∀ r j, Integrable (fun η : ES => ‖u r η j‖))
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (h0sq : IntegrableOn (fun r => coordinateX0Mass (u r) ^ 2) (Icc (0 : ℝ) t))
    (hmixed : IntegrableOn (fun r =>
        coordinateXm1Mass (u r) * coordinateX1Mass (u r)) (Icc (0 : ℝ) t)) :
    coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
      coordinateXm1Mass a +
        3 * ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) := by
  calc coordinateXm1Mass (continuousMildImage ν hν a u t)
      = coordinateXm1Mass (fun ξ : ES =>
          heatVec ν t a ξ + continuousDuhamel ν u u t ξ) := rfl
    _ ≤ coordinateXm1Mass (heatVec ν t a) +
          coordinateXm1Mass (continuousDuhamel ν u u t) :=
        coordinateXm1Mass_add_le (heatVec ν t a) (continuousDuhamel ν u u t)
          (fun i => heatVecXm1Integrable a ha ν t hν ht i) hd
    _ ≤ coordinateXm1Mass a +
          3 * ∫ s in Icc (0 : ℝ) t,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s) :=
        add_le_add (coordinateXm1Mass_heatVec_le a ha ν t hν ht)
          (coordinateXm1Mass_continuousDuhamel_self_le_integral_product
            u ν t hν hb hf hg hb0 hs1 hi hu hu0 hum1 hu1 h0sq hmixed)

/-!
## Spacetime `X¹` budget for the Duhamel term

The continuous substitute for the lattice gap is the output-time heat budget
`integral_normX1_heatMode_le`: integrating the `X¹` mass of the heat mode over
the OUTPUT time costs exactly `ν⁻¹` in the input `X⁻¹` mass.  The Duhamel
term integrates the heat mode in its SOURCE time, so the output-time budget is
transported by a Tonelli swap over the spacetime square: the joint kernel
`kernelFun` below carries the source `X⁻¹`-weight as a `t`-constant factor and
kills the `s > t` half-space by an `ite`, making the swap integrability-free.
-/

private theorem exp_pos_heat (a : ℝ) : 0 < Real.exp (-a) := by
  rw [Real.exp_neg]
  exact inv_pos.mpr (Real.exp_pos _)

private theorem integral_exp_neg_Icc (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t) :
    (∫ s in Icc (0 : ℝ) t, Real.exp (-(c * s))) =
      c⁻¹ * (1 - Real.exp (-(c * t))) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  rw [show (fun s : ℝ => Real.exp (-(c * s))) = fun s => Real.exp ((-c) * s) by
    ext s; rw [neg_mul]]
  rw [intervalIntegral.integral_comp_mul_left (hc := neg_ne_zero.mpr hc.ne')]
  rw [integral_exp]
  simp only [neg_mul, mul_zero, smul_eq_mul, Real.exp_zero, inv_neg]
  ring

private theorem heat_budget_pointwise (ν r q t : ℝ) (hν : 0 < ν) (_ht : 0 ≤ t)
    (hr : 0 < r) (hq : 0 ≤ q) :
    r * q * ((ν * r ^ 2)⁻¹ * (1 - Real.exp (-(ν * r ^ 2 * t)))) ≤ ν⁻¹ * (r⁻¹ * q) := by
  have e1 : 1 - Real.exp (-(ν * r ^ 2 * t)) ≤ 1 := by
    nlinarith [exp_pos_heat (ν * r ^ 2 * t)]
  have hc : 0 < ν * r ^ 2 := mul_pos hν (pow_pos hr 2)
  have hA : 0 ≤ r * q := mul_nonneg hr.le hq
  calc r * q * ((ν * r ^ 2)⁻¹ * (1 - Real.exp (-(ν * r ^ 2 * t))))
      ≤ r * q * ((ν * r ^ 2)⁻¹ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e1 (inv_nonneg.mpr hc.le)) hA
    _ = r * q * (ν * r ^ 2)⁻¹ := by ring
    _ = ν⁻¹ * (r⁻¹ * q) := by field_simp [hν.ne', hr.ne']

/-- The heat multiplier evaluated pointwise on the complex carrier. -/
private theorem norm_heatMode (ν t : ℝ) (f : ES -> ℂ) (ξ : ES) :
    ‖heatMode ν t f ξ‖ = Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖f ξ‖ := by
  show ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * f ξ‖ = _
  rw [Complex.norm_mul, Complex.norm_real]
  exact congrArg (fun e : ℝ => e * ‖f ξ‖) (Real.norm_of_nonneg (exp_pos_heat _).le)

/-- The `ofReal`-bridge of a real integral to its `lintegral`, valid without
any integrability hypothesis: the non-integrable case collapses both sides. -/
private theorem ofReal_integral_le_lintegral_ofReal {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α -> ℝ) (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hfi : Integrable f μ
  · exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hf).le
  · rw [integral_undef hfi, ENNReal.ofReal_zero]
    positivity

/-- The output-time bracket of the heat kernel: integrating `‖ξ‖ * exp`
over the output horizon `[s, T]` costs `ν⁻¹ ‖ξ‖⁻¹`, uniformly in `s`, `T`. -/
private theorem kernel_budget (ξ : ES) (s T ν : ℝ) (hν : 0 < ν) :
    (∫ t in Icc s T, ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) ≤ ν⁻¹ * ‖ξ‖⁻¹ := by
  by_cases hr : ‖ξ‖ = 0
  · rw [hr]
    simp
  · have hw : 0 < ‖ξ‖ := lt_of_le_of_ne (norm_nonneg ξ) (Ne.symm hr)
    have hc : 0 < ν * ‖ξ‖ ^ 2 := mul_pos hν (pow_pos hw 2)
    by_cases hst : s ≤ T
    · have hts : 0 ≤ T - s := by linarith
      have hstep : (∫ t in Icc s T, ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) =
          ‖ξ‖ * ∫ x in Icc (0 : ℝ) (T - s), Real.exp (-(ν * ‖ξ‖ ^ 2 * x)) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hst,
          intervalIntegral.integral_comp_sub_right
            (fun x : ℝ => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * x))) s,
          sub_self,
          show (fun x : ℝ => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * x))) =
              (fun x : ℝ => ‖ξ‖ • Real.exp (-(ν * ‖ξ‖ ^ 2 * x))) by
            ext x; rw [smul_eq_mul],
          intervalIntegral.integral_smul ‖ξ‖, smul_eq_mul,
          intervalIntegral.integral_of_le hts, ← integral_Icc_eq_integral_Ioc]
      rw [hstep, integral_exp_neg_Icc (ν * ‖ξ‖ ^ 2) (T - s) hc hts]
      have hz := heat_budget_pointwise ν ‖ξ‖ 1 (T - s) hν hts hw zero_le_one
      rw [mul_one, mul_one] at hz
      exact hz
    · have hset : Icc s T = ∅ := Icc_eq_empty hst
      have hz : (∫ t in Icc s T, ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) = 0 := by
        rw [hset]
        simp
      rw [hz]
      positivity

/-- The coordinate `X¹` weight of the free heat term is integrable whenever
the datum's is: the heat multiplier is bounded by `1` for `t >= 0`. -/
private theorem heatVecX1Integrable (a : ES -> ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (ν t : ℝ) (hν : 0 < ν) (ht : 0 ≤ t) (i : Fin 3) :
    Integrable (fun ξ : ES => ‖ξ‖ * ‖heatVec ν t a ξ i‖) := by
  have hw (ξ : ES) : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hexpm : Measurable (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) := by
    refine Real.measurable_exp.comp ?_
    refine Measurable.neg ?_
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact measurable_const
    · exact continuous_norm.measurable.pow_const 2
    · exact measurable_const
  have hexp_aesm :
      AEStronglyMeasurable (fun ξ : ES => Real.exp (-(ν * ‖ξ‖ ^ 2 * t))) :=
    hexpm.aestronglyMeasurable
  have hexp_pos : ∀ ξ : ES, 0 < Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) :=
    fun ξ => Real.exp_pos _
  have hexp_le : ∀ ξ : ES, Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) ≤ 1 := by
    intro ξ
    refine Real.exp_le_one_iff.mpr ?_
    have h1 : 0 ≤ ν * ‖ξ‖ ^ 2 * t := by positivity
    nlinarith
  have hpe (ξ : ES) : ‖ξ‖ * ‖heatVec ν t a ξ i‖ =
      Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖ * ‖a ξ i‖) := by
    show ‖ξ‖ * ‖heatMode ν t (fun ζ : ES => a ζ i) ξ‖ = _
    have h1 : ‖heatMode ν t (fun ζ : ES => a ζ i) ξ‖ =
        Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * ‖a ξ i‖ := by
      rw [heatMode]
      show ‖((Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * (fun ζ : ES => a ζ i) ξ‖ = _
      rw [Complex.norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hexp_pos ξ).le]
    rw [h1]
    ring
  have hR : Integrable (fun ξ : ES =>
      Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) * (‖ξ‖ * ‖a ξ i‖)) := by
    refine ⟨hexp_aesm.mul (ha i).aestronglyMeasurable,
      HasFiniteIntegral.mono (ha i).hasFiniteIntegral
        (Eventually.of_forall fun ξ => ?_)⟩
    have hn : 0 ≤ ‖ξ‖ * ‖a ξ i‖ := mul_nonneg (hw ξ) (norm_nonneg _)
    have hn2 : 0 ≤ Real.exp (-(ν * ‖ξ‖ ^ 2 * t)) := (hexp_pos ξ).le
    rw [Real.norm_of_nonneg (mul_nonneg hn2 hn), Real.norm_of_nonneg hn]
    nlinarith [hexp_le ξ]
  exact hR.congr (Eventually.of_forall fun ξ => (hpe ξ).symm)

/-- The Tonelli kernel of the Duhamel `X¹` budget: the source `X⁻¹` weight
as a `t`-constant factor, the heat weight killed off the causal half-space. -/
private def kernelFun (u : ℝ -> ES -> ComplexSpace) (i : Fin 3) (ν : ℝ)
    (ξ : ES) (t s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖continuousNavierSource u u s ξ i‖ *
    (if s ≤ t then
      ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0)

/-- The spacetime `X¹` budget of the quadratic Duhamel term: the
OUTPUT-time integral of the coordinate `X¹` mass is bounded by `ν⁻¹` times
the source-time integral of the coordinate `X⁻¹` mass — the exact continuous
analogue of the lattice budget `(ν⁻¹) * (3 * (2 * ‖a‖))` half, with no
spectral gap.  The `AEMeasurable` bundles are carried explicitly, matching the
convention of `normXm1_continuousDuhamel_self_le_coordinateXm1X1`. -/
theorem integral_normX1_continuousDuhamel_self_le_source
    (u : ℝ → ES → ComplexSpace) (ν T : ℝ) (i : Fin 3) (hν : 0 < ν)
    (hD0 : Integrable (fun t : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖))
    (hW1 : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable
        (fun p : ES × ℝ => kernelFun u i ν p.1 t p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW : AEMeasurable
        (fun z : ℝ × (ES × ℝ) => kernelFun u i ν z.2.1 z.1 z.2.2)
        ((volume.restrict (Icc (0 : ℝ) T)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) T)))))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖))
    (hg : Integrable (fun s : ℝ =>
        normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hJ : AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T)))) :
    ∫ t in Icc (0 : ℝ) T, normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i) ≤
      ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
        normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i) := by
  set μ := volume.restrict (Icc (0 : ℝ) T) with hμdef
  have hmT : MeasurableSet (Icc (0 : ℝ) T) := isClosed_Icc.measurableSet
  have hw0 (ξ : ES) : 0 ≤ ‖ξ‖ := norm_nonneg ξ
  have hw1 (ξ : ES) : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ξ)
  -- bracket: the output-time integral of the causal kernel costs ν⁻¹ ‖ξ‖⁻¹
  have hbr (ξ : ES) (s : ℝ) :
      ∫⁻ t, kernelFun u i ν ξ t s ∂μ ≤
        ENNReal.ofReal ‖continuousNavierSource u u s ξ i‖ *
          ENNReal.ofReal (ν⁻¹ * ‖ξ‖⁻¹) := by
    have hc : AEMeasurable (fun t : ℝ => if s ≤ t then
        ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) μ :=
      (Measurable.ite (isClosed_Ici.measurableSet)
        ((ENNReal.continuous_ofReal.comp
            (continuous_const.mul (Real.continuous_exp.comp
              (Continuous.neg (continuous_const.mul
                (continuous_id.sub continuous_const)))))).measurable)
        measurable_const).aemeasurable
    have hite : (fun t : ℝ => if s ≤ t then
        ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) =
        (Ici s).indicator (fun t : ℝ =>
          ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))))) := by
      funext t
      by_cases h : s ≤ t <;> simp [h, Set.mem_Ici]
    set g : ℝ -> ℝ := fun t => ‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s))) with hgdef
    have hg : Continuous (fun t : ℝ => ‖ξ‖ *
        Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) :=
      continuous_const.mul (Real.continuous_exp.comp
        (Continuous.neg (continuous_const.mul
          (continuous_id.sub continuous_const))))
    have hig : Integrable g (volume.restrict (Icc s T)) :=
      hg.continuousOn.integrableOn_Icc
    have hL : ∫⁻ t, (fun t : ℝ => if s ≤ t then
          ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) t ∂μ
        = ∫⁻ t in Ici s, ENNReal.ofReal (‖ξ‖ *
            Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) ∂μ := by
      rw [hite, MeasureTheory.lintegral_indicator isClosed_Ici.measurableSet]
    have hE : ∫⁻ t in Ici s, ENNReal.ofReal (‖ξ‖ *
          Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) ∂μ
        = ∫⁻ t, (fun x : ℝ => ENNReal.ofReal (‖ξ‖ *
            Real.exp (-(ν * ‖ξ‖ ^ 2 * (x - s))))) t
            ∂(volume.restrict (Ici s ∩ Icc (0 : ℝ) T)) := by
      rw [hμdef, Measure.restrict_restrict isClosed_Ici.measurableSet]
    have hcalc : ∫⁻ t, (fun t : ℝ => if s ≤ t then
          ENNReal.ofReal (‖ξ‖ * Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) else 0) t ∂μ ≤
        ENNReal.ofReal (∫ t in Icc s T, ‖ξ‖ *
          Real.exp (-(ν * ‖ξ‖ ^ 2 * (t - s)))) := by
      refine ((le_of_eq hL).trans (le_of_eq hE)).trans
        ((MeasureTheory.lintegral_mono'
            (Measure.restrict_mono_set volume
              (show Ici s ∩ Icc (0 : ℝ) T ⊆ Icc s T
                from fun x hx => ⟨hx.1, hx.2.2⟩)) le_rfl).trans
          ((MeasureTheory.ofReal_integral_eq_lintegral_ofReal hig
              (ae_of_all _ fun t =>
                mul_nonneg (hw0 ξ) (exp_pos_heat _).le)).symm.le.trans
            (le_of_eq rfl)))
    simp only [kernelFun]
    rw [MeasureTheory.lintegral_const_mul''
      (ENNReal.ofReal ‖continuousNavierSource u u s ξ i‖) hc]
    exact mul_le_mul_of_nonneg_left
      (le_trans hcalc
        (ENNReal.ofReal_le_ofReal (kernel_budget ξ s T ν hν))) (by positivity)
  -- pointwise (t): the Duhamel X¹ mass passes through the kernel
  have h1t (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ENNReal.ofReal (normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i)) ≤
        ∫⁻ p : ES × ℝ, kernelFun u i ν p.1 t p.2 ∂(volume.prod μ) := by
    have hbx : ENNReal.ofReal (normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i)) =
        ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hDξ t ht)
        (ae_of_all volume fun ξ => mul_nonneg (hw0 ξ) (norm_nonneg _))
    have hp (ξ : ES) : ENNReal.ofReal (‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖) ≤
        ∫⁻ s, kernelFun u i ν ξ t s ∂μ := by
      set f' : ℝ -> ℂ := fun s => heatMode ν (t - s)
          (fun ζ : ES => continuousNavierSource u u s ζ i) ξ with hf'def
      have hD' : continuousDuhamel ν u u t ξ i = ∫ s in Icc (0 : ℝ) t, f' s := rfl
      have h1 : ‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖ ≤
          ∫ s in Icc (0 : ℝ) t, ‖ξ‖ * ‖f' s‖ := by
        rw [hD']
        refine le_trans (mul_le_mul_of_nonneg_left
            (norm_integral_le_integral_norm f') (norm_nonneg ξ)) ?_
        exact (MeasureTheory.integral_smul ‖ξ‖ (fun s : ℝ => ‖f' s‖)).symm.le
      have h2 : ENNReal.ofReal (∫ s in Icc (0 : ℝ) t, ‖ξ‖ * ‖f' s‖) ≤
          ∫⁻ s, ENNReal.ofReal (‖ξ‖ * ‖f' s‖) ∂(volume.restrict (Icc (0 : ℝ) t)) :=
        ofReal_integral_le_lintegral_ofReal (volume.restrict (Icc (0 : ℝ) t))
          (fun s : ℝ => ‖ξ‖ * ‖f' s‖)
          (ae_of_all _ fun s => mul_nonneg (hw0 ξ) (norm_nonneg _))
      have h3 : (∫⁻ s, ENNReal.ofReal (‖ξ‖ * ‖f' s‖)
            ∂(volume.restrict (Icc (0 : ℝ) t))) =
          ∫⁻ s, kernelFun u i ν ξ t s ∂(volume.restrict (Icc (0 : ℝ) t)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem (isClosed_Icc.measurableSet)] with s hs
        rw [Set.mem_Icc] at hs
        rw [hf'def, norm_heatMode, kernelFun, if_pos hs.2,
          ← ENNReal.ofReal_mul (norm_nonneg _)]
        exact congrArg ENNReal.ofReal (by ring)
      calc ENNReal.ofReal (‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖)
          ≤ ENNReal.ofReal (∫ s in Icc (0 : ℝ) t, ‖ξ‖ * ‖f' s‖) :=
            ENNReal.ofReal_le_ofReal h1
        _ ≤ ∫⁻ s, ENNReal.ofReal (‖ξ‖ * ‖f' s‖)
              ∂(volume.restrict (Icc (0 : ℝ) t)) := h2
        _ = ∫⁻ s, kernelFun u i ν ξ t s
              ∂(volume.restrict (Icc (0 : ℝ) t)) := h3
        _ ≤ ∫⁻ s, kernelFun u i ν ξ t s ∂μ :=
            MeasureTheory.lintegral_mono' (Measure.restrict_mono
              (Icc_subset_Icc le_rfl ht.2) (le_refl _)) le_rfl
    rw [hbx]
    refine (lintegral_mono_ae (ae_of_all volume hp)).trans ?_
    rw [← MeasureTheory.lintegral_lintegral
      (f := fun ξ : ES => fun s : ℝ => kernelFun u i ν ξ t s) (hf := hW1 t ht)]
  have hkey :
      ∫⁻ t, ENNReal.ofReal (normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i)) ∂μ ≤
        ENNReal.ofReal (ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
          normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) := by
    calc ∫⁻ t, ENNReal.ofReal (normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i)) ∂μ
        ≤ ∫⁻ t, ∫⁻ p : ES × ℝ, kernelFun u i ν p.1 t p.2 ∂(volume.prod μ) ∂μ :=
            (lintegral_mono_ae (by
              filter_upwards [ae_restrict_mem hmT] with t ht
              exact h1t t ht))
      _ = ∫⁻ z : ℝ × (ES × ℝ),
            kernelFun u i ν z.2.1 z.1 z.2.2 ∂(μ.prod (volume.prod μ)) := by
            rw [← MeasureTheory.lintegral_lintegral
              (f := fun t : ℝ => fun p : ES × ℝ => kernelFun u i ν p.1 t p.2)
              (hf := hW)]
      _ = ∫⁻ p : ES × ℝ, ∫⁻ t : ℝ, kernelFun u i ν p.1 t p.2 ∂μ ∂(volume.prod μ) := by
            refine MeasureTheory.lintegral_prod_symm
              (f := fun z : ℝ × (ES × ℝ) => kernelFun u i ν z.2.1 z.1 z.2.2)
              (hf := hW)
      _ ≤ ∫⁻ p : ES × ℝ, ENNReal.ofReal ‖continuousNavierSource u u p.2 p.1 i‖ *
            ENNReal.ofReal (ν⁻¹ * ‖p.1‖⁻¹) ∂(volume.prod μ) :=
            lintegral_mono_ae (ae_of_all (volume.prod μ) fun p => hbr p.1 p.2)
      _ = ENNReal.ofReal ν⁻¹ *
            ∫⁻ p : ES × ℝ,
              ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖)
                ∂(volume.prod μ) := by
            refine Eq.trans (lintegral_congr (fun p => ?_))
              (MeasureTheory.lintegral_const_mul'' (ENNReal.ofReal ν⁻¹) hJ)
            rw [ENNReal.ofReal_mul (inv_nonneg.mpr hν.le),
              ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
            ring
      _ = ENNReal.ofReal ν⁻¹ *
            ∫⁻ s, ENNReal.ofReal
              (normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) ∂μ := by
            rw [MeasureTheory.lintegral_prod_symm
              (f := fun p : ES × ℝ =>
                ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖))
              (hf := hJ)]
            refine congrArg (ENNReal.ofReal ν⁻¹ * ·) (lintegral_congr_ae ?_)
            filter_upwards [ae_restrict_mem hmT] with s hs
            exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hb0 s hs)
                (ae_of_all volume fun ξ =>
                  mul_nonneg (hw1 ξ) (norm_nonneg _))).symm.trans
              (congrArg ENNReal.ofReal rfl)
      _ = ENNReal.ofReal ν⁻¹ * ENNReal.ofReal
            (∫ s in Icc (0 : ℝ) T,
              normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) := by
          refine congrArg (ENNReal.ofReal ν⁻¹ * ·) ?_
          exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg
            (ae_of_all μ fun _ =>
              integral_nonneg fun ξ => mul_nonneg (hw1 ξ) (norm_nonneg _))).symm
      _ = ENNReal.ofReal (ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) :=
          (ENNReal.ofReal_mul (inv_nonneg.mpr hν.le)).symm
  have hne : 0 ≤
      ν⁻¹ * ∫ s in Icc (0 : ℝ) T, normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i) :=
    mul_nonneg (inv_nonneg.mpr hν.le) (integral_nonneg fun s =>
      integral_nonneg fun ξ => mul_nonneg (hw1 ξ) (norm_nonneg _))
  refine (ENNReal.ofReal_le_ofReal_iff hne).mp ?_
  exact ((MeasureTheory.ofReal_integral_eq_lintegral_ofReal hD0
    (ae_of_all μ fun _ => integral_nonneg fun ξ =>
      mul_nonneg (hw0 ξ) (norm_nonneg _)))).le.trans hkey

/-- A single complex coordinate is bounded by the Hermitian Euclidean norm. -/
private theorem norm_coord_le_complexEuclideanNorm (z : ComplexSpace) (i : Fin 3) :
    ‖z i‖ ≤ complexEuclideanNorm z := by
  calc ‖z i‖ = ‖complexEuclideanPoint z i‖ :=
      congrArg (fun w : ℂ => ‖w‖) (complexEuclideanPoint_apply z i).symm
    _ ≤ ‖complexEuclideanPoint z‖ := PiLp.norm_apply_le (complexEuclideanPoint z) i

/-- The coordinate-aggregated spacetime `X¹` budget of the quadratic Duhamel
term: the `OUTPUT`-time integral of the `X¹` mass of `continuousDuhamel ν u u`
is bounded by `3 * ν⁻¹` times the time integral of the interpolated mass
product — the exact continuous analogue of the lattice spacetime half of the
fixed-point budget.  The scalar `ν⁻¹` is the gap substitute
`integral_normX1_heatMode_le`; the factor `3` and the interpolation come from
summing the coordinate budgets and the diagonal estimate. -/
theorem integral_coordinateX1Mass_continuousDuhamel_self_le_integral_product
    (u : ℝ → ES → ComplexSpace) (ν T : ℝ) (hν : 0 < ν)
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖))
    (hW1 : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable
        (fun p : ES × ℝ => kernelFun u i ν p.1 t p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW : ∀ i : Fin 3, AEMeasurable
        (fun z : ℝ × (ES × ℝ) => kernelFun u i ν z.2.1 z.1 z.2.2)
        ((volume.restrict (Icc (0 : ℝ) T)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) T)))))
    (hb0 : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hJ : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource u u s ξ)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource u u s ξ))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hu : ∀ r j, AEStronglyMeasurable (fun η : ES => u r η j))
    (hu0 : ∀ r j, Integrable (fun η : ES => ‖u r η j‖))
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (h0sq : IntegrableOn (fun r => coordinateX0Mass (u r) ^ 2) (Icc (0 : ℝ) T))
    (hmixed : IntegrableOn (fun r =>
        coordinateXm1Mass (u r) * coordinateX1Mass (u r)) (Icc (0 : ℝ) T)) :
    ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel ν u u t) ≤
      (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
        coordinateXm1Mass (u s) * coordinateX1Mass (u s) := by
  have hmT : MeasurableSet (Icc (0 : ℝ) T) := isClosed_Icc.measurableSet
  have hw1 (ξ : ES) : 0 ≤ ‖ξ‖⁻¹ := inv_nonneg.mpr (norm_nonneg ξ)
  -- per-coordinate source budget against the ℓ²-majorant of the full source
  have hsrc (i : Fin 3) :
      (∫ s in Icc (0 : ℝ) T, normXm1 (fun ξ : ES =>
          continuousNavierSource u u s ξ i)) ≤
        ∫ s in Icc (0 : ℝ) T, ∫ ξ : ES, ‖ξ‖⁻¹ *
          complexEuclideanNorm (continuousNavierSource u u s ξ) := by
    refine setIntegral_mono_on (hf := hg i) (hg := hi) hmT fun s hs => ?_
    show (∫ ξ : ES, ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖) ≤
      ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierSource u u s ξ)
    exact MeasureTheory.integral_mono (hb0 i s hs) (hs1 s hs) fun ξ =>
      mul_le_mul_of_nonneg_left
        (norm_coord_le_complexEuclideanNorm (continuousNavierSource u u s ξ) i) (hw1 ξ)
  -- sum the coordinate spacetime budgets
  have hL : ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousDuhamel ν u u t)
      = ∑ i : Fin 3, ∫ t in Icc (0 : ℝ) T,
          normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i) := by
    unfold coordinateX1Mass
    exact integral_finset_sum (f := fun i (t : ℝ) => normX1 (fun ξ : ES =>
      continuousDuhamel ν u u t ξ i)) Finset.univ (fun i _ => hD0 i)
  rw [hL]
  refine (Finset.sum_le_sum
    (f := fun i : Fin 3 => ∫ t in Icc (0 : ℝ) T,
        normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i))
    (g := fun i : Fin 3 => ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
        normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i)) ?_).trans ?_
  · intro i _
    exact integral_normX1_continuousDuhamel_self_le_source u ν T i hν (hD0 i) (hDξ i)
      (hW1 i) (hW i) (hb0 i) (hg i) (hJ i)
  · rw [← Finset.mul_sum]
    have hstep : (∑ i : Fin 3, ∫ s in Icc (0 : ℝ) T, normXm1 (fun ξ : ES =>
          continuousNavierSource u u s ξ i)) ≤
        (3 : ℝ) * ∫ s in Icc (0 : ℝ) T,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) := by
      refine le_trans (Finset.sum_le_sum
        (f := fun i : Fin 3 => ∫ s in Icc (0 : ℝ) T, normXm1 (fun ξ : ES =>
            continuousNavierSource u u s ξ i))
        (g := fun _ : Fin 3 => ∫ s in Icc (0 : ℝ) T, ∫ ξ : ES, ‖ξ‖⁻¹ *
            complexEuclideanNorm (continuousNavierSource u u s ξ)) (fun i _ => hsrc i)) ?_
      have hsum3 : (∑ i : Fin 3, ∫ s in Icc (0 : ℝ) T, ∫ ξ : ES, ‖ξ‖⁻¹ *
            complexEuclideanNorm (continuousNavierSource u u s ξ))
          = (3 : ℝ) * ∫ s in Icc (0 : ℝ) T, ∫ ξ : ES, ‖ξ‖⁻¹ *
            complexEuclideanNorm (continuousNavierSource u u s ξ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          show (↑(3 : ℕ) : ℝ) = (3 : ℝ) from rfl]
      rw [hsum3]
      exact mul_le_mul_of_nonneg_left
        (integral_normXm1_continuousNavierSource_self_le_coordinateXm1X1 u
          (Icc (0 : ℝ) T) hu hu0 hum1 hu1 hmT hi h0sq hmixed)
        (by norm_num : (0 : ℝ) ≤ (3 : ℝ))
    refine le_trans (mul_le_mul_of_nonneg_left hstep (inv_nonneg.mpr hν.le)) ?_
    exact le_of_eq (by ring)

/-- Monotonicity of the nonnegative `Icc` set integral in the horizon:
`∫₀ᵗ f ≤ ∫₀ᵀ f` whenever `t ≤ T` and `f ≥ 0` pointwise, both integrable. -/
private theorem setIntegral_Icc_mono {t T : ℝ} (htT : t ≤ T) (f : ℝ → ℝ)
    (hfm : ∀ x, 0 ≤ f x)
    (hft : Integrable f (volume.restrict (Icc (0 : ℝ) t)))
    (hfT : Integrable f (volume.restrict (Icc (0 : ℝ) T))) :
    ∫ s in Icc (0 : ℝ) t, f s ≤ ∫ s in Icc (0 : ℝ) T, f s := by
  have h1 : ENNReal.ofReal (∫ s in Icc (0 : ℝ) t, f s) =
      ∫⁻ s, ENNReal.ofReal (f s) ∂(volume.restrict (Icc (0 : ℝ) t)) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hft
      (ae_of_all (volume.restrict (Icc (0 : ℝ) t)) hfm)
  have h2 : ENNReal.ofReal (∫ s in Icc (0 : ℝ) T, f s) =
      ∫⁻ s, ENNReal.ofReal (f s) ∂(volume.restrict (Icc (0 : ℝ) T)) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfT
      (ae_of_all (volume.restrict (Icc (0 : ℝ) T)) hfm)
  have hle : ∫⁻ s, ENNReal.ofReal (f s) ∂(volume.restrict (Icc (0 : ℝ) t)) ≤
      ∫⁻ s, ENNReal.ofReal (f s) ∂(volume.restrict (Icc (0 : ℝ) T)) :=
    MeasureTheory.lintegral_mono'
      (Measure.restrict_mono_set volume
        (Icc_subset_Icc (le_refl (0 : ℝ)) htT)) le_rfl
  refine (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hfm)).mp ?_
  calc ENNReal.ofReal (∫ s in Icc (0 : ℝ) t, f s)
      = ∫⁻ s, ENNReal.ofReal (f s) ∂(volume.restrict (Icc (0 : ℝ) t)) := h1
    _ ≤ ∫⁻ s, ENNReal.ofReal (f s) ∂(volume.restrict (Icc (0 : ℝ) T)) := hle
    _ = ENNReal.ofReal (∫ s in Icc (0 : ℝ) T, f s) := h2.symm

/-- The spacetime `X¹` budget of the mild image: the heat half costs
`ν⁻¹ * coordinateXm1Mass a` (dissipation gap substitute), the Duhamel half
costs `3 * ν⁻¹` times the interpolated mass-product integral. -/
theorem integral_coordinateX1Mass_continuousMildImage_le
    (ν : ℝ) (hν : 0 < ν) (a : ES -> ComplexSpace)
    (ha : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ i‖))
    (ha1 : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖a ξ i‖))
    (u : ℝ → ES → ComplexSpace) (T : ℝ) (hT : 0 ≤ T)
    (hIt : Integrable (fun t : ℝ =>
        coordinateX1Mass (continuousMildImage ν hν a u t))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hHt : Integrable (fun t : ℝ => coordinateX1Mass (heatVec ν t a))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hD0 : ∀ i : Fin 3, Integrable (fun t : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν u u t ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hDξ : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν u u t ξ i‖))
    (hW1 : ∀ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable
        (fun p : ES × ℝ => kernelFun u i ν p.1 t p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hW : ∀ i : Fin 3, AEMeasurable
        (fun z : ℝ × (ES × ℝ) => kernelFun u i ν z.2.1 z.1 z.2.2)
        ((volume.restrict (Icc (0 : ℝ) T)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) T)))))
    (hb0 : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource u u s ξ i‖))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ξ : ES => continuousNavierSource u u s ξ i))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hJ : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource u u p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) T))))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) T, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource u u s ξ)))
    (hi : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource u u s ξ))
        (volume.restrict (Icc (0 : ℝ) T)))
    (hu : ∀ r j, AEStronglyMeasurable (fun η : ES => u r η j))
    (hu0 : ∀ r j, Integrable (fun η : ES => ‖u r η j‖))
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (h0sq : IntegrableOn (fun r => coordinateX0Mass (u r) ^ 2) (Icc (0 : ℝ) T))
    (hmixed : IntegrableOn (fun r =>
        coordinateXm1Mass (u r) * coordinateX1Mass (u r)) (Icc (0 : ℝ) T)) :
    ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousMildImage ν hν a u t) ≤
      ν⁻¹ * coordinateXm1Mass a +
        (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) := by
  have hmT : MeasurableSet (Icc (0 : ℝ) T) := isClosed_Icc.measurableSet
  have hDt : Integrable (fun t : ℝ => coordinateX1Mass (continuousDuhamel ν u u t))
      (volume.restrict (Icc (0 : ℝ) T)) :=
    integrable_finsetSum (f := fun i (t : ℝ) => normX1 (fun ξ : ES =>
      continuousDuhamel ν u u t ξ i)) Finset.univ (fun i _ => hD0 i)
  refine le_trans (integral_mono_ae hIt (hHt.add hDt) (by
      filter_upwards [ae_restrict_mem hmT] with t ht
      exact coordinateX1Mass_add_le (heatVec ν t a) (continuousDuhamel ν u u t)
        (fun i => heatVecX1Integrable a ha1 ν t hν ht.1 i) (fun i => hDξ i t ht))) ?_
  refine (le_of_eq (integral_add hHt hDt)).trans ?_
  exact add_le_add (integral_coordinateX1Mass_heatVec_le a ha ν T hν hT)
    (integral_coordinateX1Mass_continuousDuhamel_self_le_integral_product
      u ν T hν hD0 hDξ hW1 hW hb0 hg hJ hs1 hi hu hu0 hum1 hu1 h0sq hmixed)

/-- Ball-closure arithmetic at `R ≤ ν/16`: given the per-time `Xm1` budget
(`B2`) and the spacetime `X¹` budget (`D3`) for the mild image, and ball
membership of the trial trajectory `u`, the image lands in the `(7/4)R`
`Xm1`-ball and the `(7/4)ν⁻¹R` spacetime-`X¹`-ball. The threshold `ν/16`
enters only through `ν⁻¹ * R ≤ 1/16`, and the attained constants are exactly
`7/4` times the radius in each norm. -/
theorem continuousMildImage_self_map_ball
    (ν R T : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) (hT : 0 ≤ T) (hRν : R ≤ ν / 16)
    (a : ES -> ComplexSpace) (u : ℝ -> ES -> ComplexSpace)
    (haR : coordinateXm1Mass a ≤ R)
    (hballXm1 : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ (2 : ℝ) * R)
    (hballX1 : ∫ s in Icc (0 : ℝ) T, coordinateX1Mass (u s) ≤ (2 : ℝ) * ν⁻¹ * R)
    (hX1i : ∀ t ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun s : ℝ => coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume)
    (hprod : ∀ t ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun s : ℝ =>
          coordinateXm1Mass (u s) * coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume)
    (hB1 : ∀ t ∈ Icc (0 : ℝ) T,
        coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
          coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s))
    (hD3 : ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousMildImage ν hν a u t) ≤
        ν⁻¹ * coordinateXm1Mass a +
          (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s)) :
    (∀ t ∈ Icc (0 : ℝ) T,
        coordinateXm1Mass (continuousMildImage ν hν a u t) ≤ (7 / 4 : ℝ) * R) ∧
      ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousMildImage ν hν a u t) ≤
        (7 / 4 : ℝ) * ν⁻¹ * R := by
  have hy : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have hsl : ν⁻¹ * R ≤ (1 / 16 : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_left hRν hy) ?_
    field_simp [hν.ne']
    exact le_rfl
  have hx1n (v : ES -> ComplexSpace) : 0 ≤ coordinateX1Mass v :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun ξ =>
      mul_nonneg (norm_nonneg ξ) (norm_nonneg _)
  have hballX1' (t) (ht : t ∈ Icc (0 : ℝ) T) :
      ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) ≤ (2 : ℝ) * ν⁻¹ * R :=
    le_trans (setIntegral_Icc_mono ht.2 (fun s => coordinateX1Mass (u s))
      (fun s => hx1n (u s)) (hX1i t ht) (hX1i T ⟨hT, le_rfl⟩)) hballX1
  have hI1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
        (4 : ℝ) * ν⁻¹ * R * R := by
    have hmt : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
    refine le_trans (setIntegral_mono_on (μ := volume)
        (f := fun s => coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (g := fun s => (2 * R) • coordinateX1Mass (u s))
        (hf := hprod t ht) (hg := (hX1i t ht).smul (2 * R)) hmt ?_) ?_
    · intro s hs
      show coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
        (2 * R) • coordinateX1Mass (u s)
      rw [smul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (hballXm1 s ⟨hs.1, le_trans hs.2 ht.2⟩) (hx1n (u s))
    · rw [MeasureTheory.integral_smul (2 * R) (fun s : ℝ => coordinateX1Mass (u s)),
        smul_eq_mul]
      refine le_trans (mul_le_mul_of_nonneg_left (hballX1' t ht)
        (by nlinarith : (0 : ℝ) ≤ (2 : ℝ) * R)) (le_of_eq (by ring))
  refine ⟨fun t ht => ?_, ?_⟩
  · refine le_trans (hB1 t ht) ?_
    have h3 : (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
        (3 : ℝ) * (4 * ν⁻¹ * R * R) :=
      mul_le_mul_of_nonneg_left (hI1 t ht) (by norm_num : (0 : ℝ) ≤ (3 : ℝ))
    have h12 : (12 : ℝ) * R * (ν⁻¹ * R) ≤ (12 : ℝ) * R * (1 / 16) :=
      mul_le_mul_of_nonneg_left hsl (by nlinarith : (0 : ℝ) ≤ (12 : ℝ) * R)
    nlinarith
  · refine le_trans hD3 ?_
    have hI1T : ∫ s in Icc (0 : ℝ) T,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
        (4 : ℝ) * ν⁻¹ * R * R := hI1 T ⟨hT, le_rfl⟩
    have h1T : ν⁻¹ * coordinateXm1Mass a ≤ ν⁻¹ * R :=
      mul_le_mul_of_nonneg_left haR hy
    have h3T : (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
          coordinateXm1Mass (u s) * coordinateX1Mass (u s) ≤
        (3 : ℝ) * ν⁻¹ * (4 * ν⁻¹ * R * R) :=
      mul_le_mul_of_nonneg_left hI1T (by nlinarith : (0 : ℝ) ≤ (3 : ℝ) * ν⁻¹)
    have hsq : (12 : ℝ) * (ν⁻¹ * R) * (ν⁻¹ * R) ≤
        (12 : ℝ) * (ν⁻¹ * R) * (1 / 16) :=
      mul_le_mul_of_nonneg_left hsl (by nlinarith : (0 : ℝ) ≤ (12 : ℝ) * (ν⁻¹ * R))
    nlinarith

/-- The fixed-point-set form: the `(7/4)`-ball sits inside the radius-`2` ball,
so the mild solution map sends the closed `2R` / `2ν⁻¹R` ball to itself. -/
theorem continuousMildImage_self_map_ball_twoR
    (ν R T : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) (hT : 0 ≤ T) (hRν : R ≤ ν / 16)
    (a : ES -> ComplexSpace) (u : ℝ -> ES -> ComplexSpace)
    (haR : coordinateXm1Mass a ≤ R)
    (hballXm1 : ∀ t ∈ Icc (0 : ℝ) T, coordinateXm1Mass (u t) ≤ (2 : ℝ) * R)
    (hballX1 : ∫ s in Icc (0 : ℝ) T, coordinateX1Mass (u s) ≤ (2 : ℝ) * ν⁻¹ * R)
    (hX1i : ∀ t ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun s : ℝ => coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume)
    (hprod : ∀ t ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun s : ℝ =>
          coordinateXm1Mass (u s) * coordinateX1Mass (u s)) (Icc (0 : ℝ) t) volume)
    (hB1 : ∀ t ∈ Icc (0 : ℝ) T,
        coordinateXm1Mass (continuousMildImage ν hν a u t) ≤
          coordinateXm1Mass a + (3 : ℝ) * ∫ s in Icc (0 : ℝ) t,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s))
    (hD3 : ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousMildImage ν hν a u t) ≤
        ν⁻¹ * coordinateXm1Mass a +
          (3 : ℝ) * ν⁻¹ * ∫ s in Icc (0 : ℝ) T,
            coordinateXm1Mass (u s) * coordinateX1Mass (u s)) :
    (∀ t ∈ Icc (0 : ℝ) T,
        coordinateXm1Mass (continuousMildImage ν hν a u t) ≤ (2 : ℝ) * R) ∧
      ∫ t in Icc (0 : ℝ) T, coordinateX1Mass (continuousMildImage ν hν a u t) ≤
        (2 : ℝ) * ν⁻¹ * R := by
  obtain ⟨h1, h2⟩ := continuousMildImage_self_map_ball ν R T hν hR hT hRν a u
    haR hballXm1 hballX1 hX1i hprod hB1 hD3
  have hy : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  exact ⟨fun t ht => le_trans (h1 t ht) (by nlinarith : (7 / 4 : ℝ) * R ≤ (2 : ℝ) * R),
    le_trans h2 (by nlinarith : (7 / 4 : ℝ) * ν⁻¹ * R ≤ (2 : ℝ) * ν⁻¹ * R)⟩

/-!
## Chunk G: polarization and the difference Duhamel budget

The fixed-point difference `mild u − mild v` cancels the shared free heat term
and reduces to the Duhamel difference.  The Navier source polarizes bilinearly,
`src u u − src v v = src (u−v) u + src v (u−v)`, under explicit pointwise
convolution integrability, the Duhamel integral is linear in the source, and
the mixed-slot `X⁻¹` budget then applies to each polarization half with the
general `X⁰`-product feed.
-/

open scoped Convolution in
/-- Bilinear polarization of the scalar volume convolution against the
complex product: `u ⋆ v − u' ⋆ v' = (u − u') ⋆ v + u' ⋆ (v − v')`, valid
pointwise at every frequency where the four convolution integrals are
integrable (the stated hypotheses). -/
private theorem convolution_pol (u u' v v' : ES → ℂ)
    (huu : ∀ ξ : ES, Integrable (fun η => u η * v (ξ - η)))
    (hu'v' : ∀ ξ : ES, Integrable (fun η => u' η * v' (ξ - η)))
    (hdv : ∀ ξ : ES, Integrable (fun η => (u - u') η * v (ξ - η)))
    (hu'd : ∀ ξ : ES, Integrable (fun η => u' η * (v - v') (ξ - η))) :
    u ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] v -
        u' ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] v' =
      (u - u') ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] v +
        u' ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (v - v') := by
  refine funext (fun ξ => ?_)
  have h1 : (u ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] v) ξ =
      ∫ η, u η * v (ξ - η) := rfl
  have h2 : (u' ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] v') ξ =
      ∫ η, u' η * v' (ξ - η) := rfl
  have h3 : ((u - u') ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] v) ξ =
      ∫ η, (u - u') η * v (ξ - η) := rfl
  have h4 : (u' ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (v - v')) ξ =
      ∫ η, u' η * (v - v') (ξ - η) := rfl
  rw [Pi.sub_apply, Pi.add_apply, h1, h2, h3, h4]
  rw [← integral_sub (huu ξ) (hu'v' ξ),
      ← integral_add (hdv ξ) (hu'd ξ)]
  refine integral_congr_ae (ae_of_all volume (fun η => ?_))
  simp only [Pi.sub_apply]
  ring

/-- Bilinear polarization of the Navier source: the difference of diagonal
sources splits as `src (u−v) u + src v (u−v)`.  The Leray projector is a
complex-linear map and the raw convection is coordinatewise a frequency
convolution against `Complex.I •`, so the scalar convolution polarization
`convolution_pol` transports through both layers. -/
theorem continuousNavierSource_self_sub_self
    (u v : ℝ -> ES -> ComplexSpace) (t : ℝ)
    (h1 : ∀ j i : Fin 3, ∀ ξ : ES,
        Integrable (fun η : ES => u t η j * u t (ξ - η) i))
    (h2 : ∀ j i : Fin 3, ∀ ξ : ES,
        Integrable (fun η : ES => v t η j * v t (ξ - η) i))
    (h3 : ∀ j i : Fin 3, ∀ ξ : ES,
        Integrable (fun η : ES => (u - v) t η j * u t (ξ - η) i))
    (h4 : ∀ j i : Fin 3, ∀ ξ : ES,
        Integrable (fun η : ES => v t η j * (u - v) t (ξ - η) i)) :
    continuousNavierSource u u t - continuousNavierSource v v t =
      continuousNavierSource (u - v) u t + continuousNavierSource v (u - v) t := by
  refine funext (fun ξ => ?_)
  have h1' : (continuousNavierSource u u t) ξ =
      continuousLeray ξ (Complex.I • rawNavierConvection (u t) (u t) ξ) := rfl
  have h2' : (continuousNavierSource v v t) ξ =
      continuousLeray ξ (Complex.I • rawNavierConvection (v t) (v t) ξ) := rfl
  have h3' : (continuousNavierSource (u - v) u t) ξ =
      continuousLeray ξ (Complex.I • rawNavierConvection ((u - v) t) (u t) ξ) := rfl
  have h4' : (continuousNavierSource v (u - v) t) ξ =
      continuousLeray ξ (Complex.I • rawNavierConvection (v t) ((u - v) t) ξ) := rfl
  rw [Pi.sub_apply, Pi.add_apply, h1', h2', h3', h4']
  have rawpol : rawNavierConvection (u t) (u t) ξ -
      rawNavierConvection (v t) (v t) ξ =
      rawNavierConvection ((u - v) t) (u t) ξ +
        rawNavierConvection (v t) ((u - v) t) ξ := by
    refine funext (fun i => ?_)
    rw [Pi.sub_apply, Pi.add_apply]
    rw [rawNavierConvection, rawNavierConvection, rawNavierConvection,
      rawNavierConvection]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← mul_sub, ← mul_add]
    refine congrArg (fun w : ℂ => (ξ j : ℂ) * w) ?_
    have eqf := congrFun (convolution_pol (fun η : ES => u t η j)
        (fun η : ES => v t η j) (fun η : ES => u t η i) (fun η : ES => v t η i)
        (h1 j i) (h2 j i) (h3 j i) (h4 j i)) ξ
    exact eqf
  calc continuousLeray ξ (Complex.I • rawNavierConvection (u t) (u t) ξ) -
        continuousLeray ξ (Complex.I • rawNavierConvection (v t) (v t) ξ)
      = continuousLeray ξ (Complex.I • rawNavierConvection (u t) (u t) ξ -
          Complex.I • rawNavierConvection (v t) (v t) ξ) :=
        ((Navier.Analysis.ComplexLerayProjection.complexLeray (Navier.Analysis.FourierMajorant.spaceProj ξ)).map_sub _ _).symm
    _ = continuousLeray ξ (Complex.I •
          (rawNavierConvection (u t) (u t) ξ -
            rawNavierConvection (v t) (v t) ξ)) :=
        congrArg (continuousLeray ξ) (smul_sub _ _ _).symm
    _ = continuousLeray ξ (Complex.I •
          (rawNavierConvection ((u - v) t) (u t) ξ +
            rawNavierConvection (v t) ((u - v) t) ξ)) :=
        congrArg (fun z : ComplexSpace => continuousLeray ξ (Complex.I • z)) rawpol
    _ = continuousLeray ξ (Complex.I • rawNavierConvection ((u - v) t) (u t) ξ) +
        continuousLeray ξ (Complex.I • rawNavierConvection (v t) ((u - v) t) ξ) := by
      show Navier.Analysis.ComplexLerayProjection.complexLeray
          (Navier.Analysis.FourierMajorant.spaceProj ξ)
          (Complex.I • (rawNavierConvection ((u - v) t) (u t) ξ +
            rawNavierConvection (v t) ((u - v) t) ξ)) =
        Navier.Analysis.ComplexLerayProjection.complexLeray
            (Navier.Analysis.FourierMajorant.spaceProj ξ)
            (Complex.I • rawNavierConvection ((u - v) t) (u t) ξ) +
          Navier.Analysis.ComplexLerayProjection.complexLeray
            (Navier.Analysis.FourierMajorant.spaceProj ξ)
            (Complex.I • rawNavierConvection (v t) ((u - v) t) ξ)
      rw [smul_add]
      exact (Navier.Analysis.ComplexLerayProjection.complexLeray
        (Navier.Analysis.FourierMajorant.spaceProj ξ)).map_add _ _

/-- The Duhamel difference splits into the two polarization halves: the
`[0,t]` integral is linear in the source, and the heat multiplier distributes. -/
theorem continuousDuhamel_self_sub_self
    (ν : ℝ) (u v : ℝ -> ES -> ComplexSpace) (t : ℝ) (ξ : ES) (i : Fin 3)
    (hpol : ∀ s ∈ Icc (0 : ℝ) t,
        continuousNavierSource u u s ξ i - continuousNavierSource v v s ξ i =
          continuousNavierSource (u - v) u s ξ i +
            continuousNavierSource v (u - v) s ξ i)
    (huv : Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u u s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvv : Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource v v s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hwu : Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource (u - v) u s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvw : Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource v (u - v) s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t))) :
    continuousDuhamel ν u u t ξ i - continuousDuhamel ν v v t ξ i =
      continuousDuhamel ν (u - v) u t ξ i +
        continuousDuhamel ν v (u - v) t ξ i := by
  have hmT : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
  show (∫ s in Icc (0 : ℝ) t,
          heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u u s ζ i) ξ) -
      (∫ s in Icc (0 : ℝ) t,
          heatMode ν (t - s) (fun ζ : ES => continuousNavierSource v v s ζ i) ξ) =
      (∫ s in Icc (0 : ℝ) t,
          heatMode ν (t - s) (fun ζ : ES => continuousNavierSource (u - v) u s ζ i) ξ) +
      (∫ s in Icc (0 : ℝ) t,
          heatMode ν (t - s) (fun ζ : ES => continuousNavierSource v (u - v) s ζ i) ξ)
  rw [← integral_sub huv hvv, ← integral_add hwu hvw]
  refine integral_congr_ae (by
      filter_upwards [ae_restrict_mem hmT] with s hs
      simp only [heatMode]
      rw [← mul_sub, ← mul_add, hpol s hs])

/-- Mixed-slot Duhamel `X⁻¹` budget: for two (not necessarily equal) feed
slots `a`, `b`, the coordinate `X⁻¹` mass of the Duhamel integral is bounded
by `3` times the time-integrated product of the two coordinate `X⁰` masses.
This is the polarization-side companion of
`coordinateXm1Mass_continuousDuhamel_self_le_integral_product`: the heat-Fubini
stage `normXm1_continuousDuhamel_le` feeds the coordinate/Euclidean comparison,
and the genuine mixed bilinear feed
`integral_normXm1_continuousNavierSource_le` closes with the `X⁰ × X⁰` product. -/
theorem coordinateXm1Mass_continuousDuhamel_le_integral_X0_product
    (a b : ℝ → ES → ComplexSpace) (ν t : ℝ) (hν : 0 < ν)
    (hb : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) •
          heatMode ν (t - p.2) (fun ζ : ES => continuousNavierSource a b p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s) (fun ζ : ES => continuousNavierSource a b s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource a b s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousNavierSource a b s ξ i‖))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) t,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
          complexEuclideanNorm (continuousNavierSource a b s ξ)))
    (hi : Integrable (fun s : ℝ =>
        ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierSource a b s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (ha : ∀ r j, AEStronglyMeasurable (fun η : ES => a r η j))
    (hbs : ∀ r i, AEStronglyMeasurable (fun η : ES => b r η i))
    (ha0 : ∀ r j, Integrable (fun η : ES => ‖a r η j‖))
    (hb00 : ∀ r i, Integrable (fun η : ES => ‖b r η i‖))
    (hprod : IntegrableOn (fun r =>
        coordinateX0Mass (a r) * coordinateX0Mass (b r)) (Icc (0 : ℝ) t)) :
    coordinateXm1Mass (continuousDuhamel ν a b t) ≤
      3 * ∫ s in Icc (0 : ℝ) t,
        coordinateX0Mass (a s) * coordinateX0Mass (b s) := by
  have hmT : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
  unfold coordinateXm1Mass
  refine (Finset.sum_le_sum
    (f := fun i : Fin 3 => normXm1 (fun ξ : ES => continuousDuhamel ν a b t ξ i))
    (g := fun _ : Fin 3 =>
      ∫ s in Icc (0 : ℝ) t, coordinateX0Mass (a s) * coordinateX0Mass (b s)) ?_).trans_eq ?_
  · intro i _
    refine le_trans (normXm1_continuousDuhamel_le a b ν t i hν (hb i) (hf i) (hg i)
      (fun s hs => hb0 s hs i)) ?_
    refine le_trans (integral_mono_ae (hg i) hi ?_) ?_
    · filter_upwards [ae_restrict_mem hmT] with s hs
      refine le_of_eq (rfl : normXm1 (fun ξ : ES =>
          continuousNavierSource a b s ξ i) =
          ∫ ξ : ES, ‖ξ‖⁻¹ * ‖continuousNavierSource a b s ξ i‖) |>.trans ?_
      refine integral_mono (hb0 s hs i) (hs1 s hs) (fun ξ =>
        mul_le_mul_of_nonneg_left
          (norm_coord_le_complexEuclideanNorm (continuousNavierSource a b s ξ) i)
          (inv_nonneg.mpr (norm_nonneg ξ)))
    · exact integral_normXm1_continuousNavierSource_le a b (Icc (0 : ℝ) t)
        ha hbs ha0 hb00 hmT hi hprod
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (↑(3 : ℕ) : ℝ) = 3 from rfl]

/-- `normXm1` is subadditive for pointwise sums, using explicit weighted
integrability of both summands. -/
private theorem normXm1_scalar_add_le (a b : ES → ℂ)
    (ha : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ‖))
    (hb : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖b ξ‖)) :
    normXm1 (fun ξ : ES => a ξ + b ξ) ≤ normXm1 a + normXm1 b := by
  have hnonneg : 0 ≤ᵐ[volume] fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ + b ξ‖ :=
    ae_of_all volume (fun ξ =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _))
  have hkey : (fun ξ : ES => ‖ξ‖⁻¹ * ‖a ξ + b ξ‖) ≤ᵐ[volume]
      fun ξ : ES => ‖ξ‖⁻¹ * (‖a ξ‖ + ‖b ξ‖) :=
    ae_of_all volume (fun ξ =>
      mul_le_mul_of_nonneg_left (norm_add_le (a ξ) (b ξ))
        (inv_nonneg.mpr (norm_nonneg ξ)))
  have hg : Integrable (fun ξ : ES => ‖ξ‖⁻¹ * (‖a ξ‖ + ‖b ξ‖)) :=
    Integrable.congr (ha.add hb)
      (ae_of_all volume (fun ξ : ES => (mul_add _ _ _).symm))
  have h1 : (∫ ξ : ES, ‖ξ‖⁻¹ * ‖a ξ + b ξ‖) ≤
      ∫ ξ : ES, ‖ξ‖⁻¹ * (‖a ξ‖ + ‖b ξ‖) :=
    integral_mono_of_nonneg (μ := volume) hnonneg hg hkey
  have h2 : ∫ ξ : ES, ‖ξ‖⁻¹ * (‖a ξ‖ + ‖b ξ‖) ≤ normXm1 a + normXm1 b := by
    refine le_of_eq ?_
    show (∫ ξ : ES, ‖ξ‖⁻¹ * (‖a ξ‖ + ‖b ξ‖)) =
      (∫ ξ : ES, ‖ξ‖⁻¹ * ‖a ξ‖) + ∫ ξ : ES, ‖ξ‖⁻¹ * ‖b ξ‖
    rw [integral_congr_ae (μ := volume)
      (ae_of_all volume (fun ξ : ES => mul_add _ _ _))]
    exact integral_add ha hb
  exact le_trans (le_of_eq (rfl : normXm1 (fun ξ : ES => a ξ + b ξ) =
      ∫ ξ : ES, ‖ξ‖⁻¹ * ‖a ξ + b ξ‖) |>.trans h1) h2

/-- The mild-image difference budget: the shared free heat evolution cancels,
and the Duhamel difference splits by polarization into the two mixed slots.
`coordinateXm1Mass (mild u t − mild v t)` is bounded by the sum of the two
mixed Duhamel `X⁻¹` masses; the numerical budget
`coordinateXm1Mass_continuousDuhamel_le_integral_X0_product` closes each side
with the `X⁰ × X⁰` product feed. -/
theorem continuousMildImage_sub_coordinateXm1Mass_le
    (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace)
    (u v : ℝ → ES → ComplexSpace) (t : ℝ)
    (hpol : ∀ i : Fin 3, ∀ ξ : ES, ∀ s ∈ Icc (0 : ℝ) t,
        continuousNavierSource u u s ξ i - continuousNavierSource v v s ξ i =
          continuousNavierSource (u - v) u s ξ i +
            continuousNavierSource v (u - v) s ξ i)
    (huv : ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u u s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvv : ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource v v s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hwu : ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource (u - v) u s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvw : ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource v (u - v) s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hDwu : ∀ i : Fin 3, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousDuhamel ν (u - v) u t ξ i‖))
    (hDvw : ∀ i : Fin 3, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousDuhamel ν v (u - v) t ξ i‖)) :
    coordinateXm1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u t ξ - continuousMildImage ν hν a v t ξ) ≤
      coordinateXm1Mass (continuousDuhamel ν (u - v) u t) +
        coordinateXm1Mass (continuousDuhamel ν v (u - v) t) := by
  have hfe (i : Fin 3) (ξ : ES) :
      (fun ξ : ES => continuousMildImage ν hν a u t ξ i -
        continuousMildImage ν hν a v t ξ i) ξ =
      (fun ξ : ES => continuousDuhamel ν (u - v) u t ξ i +
        continuousDuhamel ν v (u - v) t ξ i) ξ := by
    show continuousMildImage ν hν a u t ξ i - continuousMildImage ν hν a v t ξ i = _
    rw [continuousMildImage_coord_apply, continuousMildImage_coord_apply]
    rw [add_sub_add_left_eq_sub]
    exact continuousDuhamel_self_sub_self ν u v t ξ i (fun s hs => hpol i ξ s hs)
      (huv i ξ) (hvv i ξ) (hwu i ξ) (hvw i ξ)
  unfold coordinateXm1Mass
  refine (Finset.sum_le_sum
    (f := fun i : Fin 3 => normXm1 (fun ξ : ES =>
        continuousMildImage ν hν a u t ξ i - continuousMildImage ν hν a v t ξ i))
    (g := fun i : Fin 3 => normXm1 (fun ξ : ES =>
        continuousDuhamel ν (u - v) u t ξ i) + normXm1 (fun ξ : ES =>
        continuousDuhamel ν v (u - v) t ξ i)) ?_).trans ?_
  · intro i _
    refine (le_of_eq (congrArg normXm1 (funext (hfe i)))).trans ?_
    exact normXm1_scalar_add_le (fun ξ : ES => continuousDuhamel ν (u - v) u t ξ i)
      (fun ξ : ES => continuousDuhamel ν v (u - v) t ξ i) (hDwu i) (hDvw i)
  · rw [Finset.sum_add_distrib]

/-!
## Chunk H: the square-root (Cauchy--Schwarz) ball modulus

The difference feed `∫ X⁰(w) X⁰(u)` closes by real Cauchy--Schwarz in the
square-root form `sqrt(∫ X⁰(w)²) sqrt(∫ X⁰(u)²)`; the fixed-time CS bridge
`X⁰² ≤ X⁻¹ · X¹` then promotes both factors to `sqrt(∫ Xm1 · X1)`, and the
ball budgets at `R ≤ ν/16` give `sqrt(∫ Xm1(u) X1(u)) ≤ 2 sqrt(ν⁻¹) R`.
The mild image difference therefore obeys a modulus that vanishes with the
distance quantity — the attained form of the contraction obligation, which is
quadratic (Hölder one-half), not linear.
-/

/-- Real Cauchy--Schwarz in square-root form for pointwise products of
nonnegative functions: from `0 <= (sqrt(B) f - sqrt(A) g)^2` at the optimal
scale; the zero-mass cases use `integral_eq_zero_of_ae`. -/
private theorem integral_mul_le_sqrt_mul_sqrt (μ : Measure ℝ) (f g : ℝ → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    ∫ x, f x * g x ∂μ ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  set A := ∫ x, f x ^ 2 ∂μ with hAd
  set B := ∫ x, g x ^ 2 ∂μ with hBd
  have hA : 0 ≤ A := integral_nonneg (fun x => sq_nonneg _)
  have hB : 0 ≤ B := integral_nonneg (fun x => sq_nonneg _)
  by_cases hA0 : A = 0
  · have hsqae : (fun x : ℝ => f x ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) :=
      (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all μ fun x => sq_nonneg _) hf2).mp hA0
    have hL : ∫ x, f x * g x ∂μ = 0 :=
      integral_eq_zero_of_ae (μ := μ) (by
        filter_upwards [hsqae] with x hx
        have hx' : f x = 0 := by nlinarith
        rw [hx']
        simp)
    rw [hL]
    positivity
  by_cases hB0 : B = 0
  · have hsqae : (fun x : ℝ => g x ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) :=
      (integral_eq_zero_iff_of_nonneg_ae
        (ae_of_all μ fun x => sq_nonneg _) hg2).mp hB0
    have hL : ∫ x, f x * g x ∂μ = 0 :=
      integral_eq_zero_of_ae (μ := μ) (by
        filter_upwards [hsqae] with x hx
        have hx' : g x = 0 := by nlinarith
        rw [hx']
        simp)
    rw [hL]
    positivity
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    set s := Real.sqrt (Real.sqrt (B / A)) with hs
    have hs0 : 0 < s :=
      Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos hBpos hApos))
    have hI : Integrable (fun x : ℝ =>
        (s ^ 2 / 2) • f x ^ 2 + (1 / (2 * s ^ 2)) • g x ^ 2) μ :=
      (Integrable.smul (s ^ 2 / 2) hf2).add (Integrable.smul (1 / (2 * s ^ 2)) hg2)
    have hpoint (x : ℝ) : f x * g x ≤ (s ^ 2 / 2) • f x ^ 2 + (1 / (2 * s ^ 2)) • g x ^ 2 := by
      have hs2 : s ≠ 0 := hs0.ne'
      have key : (s * f x - g x / s) ^ 2 =
          s ^ 2 * f x ^ 2 - 2 * (f x * g x) + g x ^ 2 / s ^ 2 := by
        field_simp [hs2]
        ring
      have hsq : 0 ≤ s ^ 2 * f x ^ 2 - 2 * (f x * g x) + g x ^ 2 / s ^ 2 := by
        rw [← key]; exact sq_nonneg _
      have hlt : f x * g x ≤ (s ^ 2 / 2) * f x ^ 2 + (1 / (2 * s ^ 2)) * g x ^ 2 := by
        have hdiv : g x ^ 2 / s ^ 2 = (1 / s ^ 2) * g x ^ 2 := by
          field_simp [hs2]
        have h2 : 2 * (f x * g x) ≤ s ^ 2 * f x ^ 2 + (1 / s ^ 2) * g x ^ 2 := by
          linarith
        have hhalf : f x * g x ≤ (s ^ 2 / 2) * f x ^ 2 +
            (1 / s ^ 2) * g x ^ 2 / 2 := by linarith
        have hfinv : (1 / s ^ 2) * g x ^ 2 / 2 = (1 / (2 * s ^ 2)) * g x ^ 2 := by
          field_simp [hs2]
        linarith
      simp only [smul_eq_mul]
      exact hlt
    have hstep : ∫ x, f x * g x ∂μ ≤
        (s ^ 2 / 2) • ∫ x, f x ^ 2 ∂μ + (1 / (2 * s ^ 2)) • ∫ x, g x ^ 2 ∂μ := by
      refine le_trans (integral_mono_of_nonneg ?_ hI ?_) ?_
      · filter_upwards with x
        exact mul_nonneg (hf0 x) (hg0 x)
      · filter_upwards with x
        exact hpoint x
      · refine le_of_eq ((integral_add (Integrable.smul (s ^ 2 / 2) hf2)
              (Integrable.smul (1 / (2 * s ^ 2)) hg2)).trans ?_)
        exact congrArg₂ HAdd.hAdd
          (integral_smul (μ := μ) (c := s ^ 2 / 2) (f := fun x : ℝ => f x ^ 2))
          (integral_smul (μ := μ) (c := 1 / (2 * s ^ 2)) (f := fun x : ℝ => g x ^ 2))
    have hs2e : s ^ 2 = Real.sqrt (B / A) := by
      rw [hs, Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mpr (div_pos hBpos hApos)))]
    have halg : (s ^ 2 / 2) • A + (1 / (2 * s ^ 2)) • B =
        Real.sqrt A * Real.sqrt B := by
      simp only [smul_eq_mul]
      rw [hs2e]
      have hne : 2 * Real.sqrt A * Real.sqrt B ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero (Real.sqrt_pos.mpr hApos).ne')
          (Real.sqrt_pos.mpr hBpos).ne'
      rw [Real.sqrt_div hBpos.le A]
      refine ((mul_left_inj' hne).mp ?_)
      ring_nf
      field_simp [hApos.ne', hBpos.ne', (Real.sqrt_pos.mpr hApos).ne',
        (Real.sqrt_pos.mpr hBpos).ne']
      rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
      ring
    exact le_trans hstep (le_of_eq halg)

/-- The `X⁰` mass is pointwise nonnegative. -/
private theorem coordinateX0Mass_nonneg (u : ES -> ComplexSpace) :
    0 <= coordinateX0Mass u :=
  Finset.sum_nonneg fun i _ => integral_nonneg fun ξ => norm_nonneg _

/-- The `X⁻¹` mass is pointwise nonnegative. -/
private theorem coordinateXm1Mass_nonneg (u : ES -> ComplexSpace) :
    0 <= coordinateXm1Mass u :=
  Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ξ =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _)

/-- The `X¹` mass is pointwise nonnegative. -/
private theorem coordinateX1Mass_nonneg (u : ES -> ComplexSpace) :
    0 <= coordinateX1Mass u :=
  Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- Chunk H, step 2: the mixed-slot `X⁻¹` budget transported through true
square-integrability of the `X⁰` feeds.  Chaining the proved `L¹` feed bound
with the Cauchy--Schwarz ball modulus `integral_mul_le_sqrt_mul_sqrt` at
`μ = volume.restrict (Icc 0 t)` replaces the product of `X⁰` masses by the
product of their `L²` norms, with the factor `3` preserved. -/
theorem coordinateXm1Mass_continuousDuhamel_le_sqrt_product_X0_sq
    (a b : ℝ -> ES -> ComplexSpace) (ν t : ℝ) (hν : 0 < ν)
    (hb : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) •
          heatMode ν (t - p.2) (fun ζ : ES => continuousNavierSource a b p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hf : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s) (fun ζ : ES => continuousNavierSource a b s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hg : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource a b s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0 : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ * ‖continuousNavierSource a b s ξ i‖))
    (hs1 : ∀ s ∈ Icc (0 : ℝ) t,
        Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
          complexEuclideanNorm (continuousNavierSource a b s ξ)))
    (hi : Integrable (fun s : ℝ =>
        ∫ ξ : ES, ‖ξ‖⁻¹ * complexEuclideanNorm (continuousNavierSource a b s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (ha : ∀ r j, AEStronglyMeasurable (fun η : ES => a r η j))
    (hbs : ∀ r i, AEStronglyMeasurable (fun η : ES => b r η i))
    (ha0 : ∀ r j, Integrable (fun η : ES => ‖a r η j‖))
    (hb00 : ∀ r i, Integrable (fun η : ES => ‖b r η i‖))
    (hprod : IntegrableOn (fun r =>
        coordinateX0Mass (a r) * coordinateX0Mass (b r)) (Icc (0 : ℝ) t))
    (ha2 : Integrable (fun s : ℝ => coordinateX0Mass (a s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb2 : Integrable (fun s : ℝ => coordinateX0Mass (b s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t))) :
    coordinateXm1Mass (continuousDuhamel ν a b t) <=
      3 * (Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (a s) ^ 2) *
        Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (b s) ^ 2)) := by
  refine le_trans
      (coordinateXm1Mass_continuousDuhamel_le_integral_X0_product a b ν t hν
        hb hf hg hb0 hs1 hi ha hbs ha0 hb00 hprod) ?_
  refine mul_le_mul_of_nonneg_left
      (integral_mul_le_sqrt_mul_sqrt (volume.restrict (Icc (0 : ℝ) t))
        (fun s => coordinateX0Mass (a s)) (fun s => coordinateX0Mass (b s))
        (fun s => coordinateX0Mass_nonneg (a s)) (fun s => coordinateX0Mass_nonneg (b s))
        ha2 hb2) (by norm_num : (0 : ℝ) <= 3)

/-- Chunk H, step 3: the per-slot weighted interpolation inside the time
square root: `sqrt (∫ X⁰(u)²) <= sqrt (∫ X⁻¹(u) * X¹(u))`, from the pointwise
`X⁰` interpolation inequality of `ContinuousLeiLinTimeDuhamel` fed through
`integral_mono_of_nonneg`. -/
theorem sqrt_X0_sq_le_sqrt_Xm1_mul_X1
    (u : ℝ -> ES -> ComplexSpace) (T : ℝ)
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (hmixed : Integrable (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) T))) :
    Real.sqrt (∫ s in Icc (0 : ℝ) T, coordinateX0Mass (u s) ^ 2) <=
      Real.sqrt (∫ s in Icc (0 : ℝ) T,
        coordinateXm1Mass (u s) * coordinateX1Mass (u s)) := by
  refine Real.sqrt_le_sqrt
      (integral_mono_of_nonneg (μ := volume.restrict (Icc (0 : ℝ) T))
        ?_ hmixed ?_)
  · filter_upwards with s
    exact pow_two_nonneg _
  · filter_upwards with s
    exact coordinateX0Mass_sq_le_coordinateXm1Mass_mul_coordinateX1Mass (u s)
      (fun i => hum1 s i) (fun i => hu1 s i)

/-- Chunk H, step 3b: a slot whose pointwise `X⁻¹` mass is at most `2 R` on
the interval and whose total `X¹` mass is at most `2 ν⁻¹ R` has time
`L²`-`X⁰` square root at most `2 R sqrt ν⁻¹`.  This is the square-root form
of the ball budget used by the lift. -/
private theorem sqrt_integral_X0_sq_le_two_R_mul_sqrt_invNu
    (u : ℝ -> ES -> ComplexSpace) (ν t R : ℝ) (hν : 0 < ν) (hR : 0 <= R)
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (hmixed : Integrable (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (u s) <= 2 * R)
    (hX1int : Integrable (fun s : ℝ => coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) <= 2 * ν⁻¹ * R) :
    Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (u s) ^ 2) <=
      2 * R * Real.sqrt ν⁻¹ := by
  refine (sqrt_X0_sq_le_sqrt_Xm1_mul_X1 u t hum1 hu1 hmixed).trans ?_
  refine ((Real.sqrt_le_sqrt ?_).trans_eq
    (Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) <= 2) hR)
      (Real.sqrt_nonneg _))))
  calc ∫ s in Icc (0 : ℝ) t, coordinateXm1Mass (u s) * coordinateX1Mass (u s)
      <= ∫ s in Icc (0 : ℝ) t, (2 * R) * coordinateX1Mass (u s) := by
        refine integral_mono_of_nonneg (μ := volume.restrict (Icc (0 : ℝ) t))
          ?_ (Integrable.smul (2 * R) hX1int) ?_
        · filter_upwards with s
          exact mul_nonneg (coordinateXm1Mass_nonneg (u s))
            (coordinateX1Mass_nonneg (u s))
        · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
          exact mul_le_mul_of_nonneg_right (hXm1 s hs)
            (coordinateX1Mass_nonneg (u s))
    _ = (2 * R) * ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) := by
        exact integral_smul (μ := volume.restrict (Icc (0 : ℝ) t))
          (c := 2 * R) (f := fun s => coordinateX1Mass (u s))
    _ <= (2 * R) * (2 * ν⁻¹ * R) :=
        mul_le_mul_of_nonneg_left hX1
          (mul_nonneg (by norm_num : (0 : ℝ) <= 2) hR)
    _ = 4 * ν⁻¹ * R ^ 2 := by ring
    _ = (2 * R * Real.sqrt ν⁻¹) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (inv_nonneg.mpr hν.le)]
        ring

/-- Chunk H, step 4: the square-root (Hölder-½) modulus of continuity of the
mild image on the whole-space ball.  Combining the difference decomposition
`continuousMildImage_sub_coordinateXm1Mass_le`, the transported Cauchy--Schwarz
slot budget `coordinateXm1Mass_continuousDuhamel_le_sqrt_product_X0_sq`, and
the ball budgets `<= 2 R` (pointwise `X⁻¹`) and `<= 2 ν⁻¹ R` (total `X¹`), the
`X⁻¹` distance of two mild images is bounded by

`12 * sqrt ν⁻¹ * R * sqrt (∫₀ᵗ X⁻¹(u − v) · X¹(u − v))`.

Honest status: this is a quadratic/Hölder-½ modulus with a ball-radius factor,
NOT a linear Banach contraction constant; the linear-constant residual of the
module header remains OPEN, as does completeness of the ball subtype.  The
attained constant is `12 sqrt ν⁻¹ R` against the mixed `X⁻¹·X¹` feed of the
difference slot. -/
theorem continuousMildImage_sub_coordinateXm1Mass_le_ball_modulus
    (ν : ℝ) (hν : 0 < ν) (a : ES -> ComplexSpace)
    (u v : ℝ -> ES -> ComplexSpace) (R t : ℝ) (hR : 0 <= R)
    (hpol : ∀ i : Fin 3, ∀ ξ : ES, ∀ s ∈ Icc (0 : ℝ) t,
        continuousNavierSource u u s ξ i - continuousNavierSource v v s ξ i =
          continuousNavierSource (u - v) u s ξ i +
            continuousNavierSource v (u - v) s ξ i)
    (huv : ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource u u s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvv : ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES => continuousNavierSource v v s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hwu : ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES =>
          continuousNavierSource (u - v) u s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvw : ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun s : ℝ =>
        heatMode ν (t - s) (fun ζ : ES =>
          continuousNavierSource v (u - v) s ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hDwu : ∀ i : Fin 3, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousDuhamel ν (u - v) u t ξ i‖))
    (hDvw : ∀ i : Fin 3, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousDuhamel ν v (u - v) t ξ i‖))
    (hmw : ∀ r j, AEStronglyMeasurable (fun η : ES => (u - v) r η j))
    (hmw0 : ∀ r j, Integrable (fun η : ES => ‖(u - v) r η j‖))
    (hmu : ∀ r j, AEStronglyMeasurable (fun η : ES => u r η j))
    (hmu0 : ∀ r j, Integrable (fun η : ES => ‖u r η j‖))
    (hmv : ∀ r j, AEStronglyMeasurable (fun η : ES => v r η j))
    (hmv0 : ∀ r j, Integrable (fun η : ES => ‖v r η j‖))
    (hw2 : Integrable (fun s : ℝ => coordinateX0Mass ((u - v) s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hu2 : Integrable (fun s : ℝ => coordinateX0Mass (u s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hv2 : Integrable (fun s : ℝ => coordinateX0Mass (v s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hbWU : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) • heatMode ν (t - p.2)
          (fun ζ : ES => continuousNavierSource (u - v) u p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hfWU : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s)
          (fun ζ : ES => continuousNavierSource (u - v) u s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hgWU : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource (u - v) u s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0WU : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
        Integrable (fun ξ : ES =>
          ‖ξ‖⁻¹ * ‖continuousNavierSource (u - v) u s ξ i‖))
    (hs1WU : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource (u - v) u s ξ)))
    (hiWU : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource (u - v) u s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hprodWU : IntegrableOn (fun r =>
        coordinateX0Mass ((u - v) r) * coordinateX0Mass (u r)) (Icc (0 : ℝ) t))
    (hbVW : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) • heatMode ν (t - p.2)
          (fun ζ : ES => continuousNavierSource v (u - v) p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hfVW : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s)
          (fun ζ : ES => continuousNavierSource v (u - v) s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hgVW : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ζ : ES => continuousNavierSource v (u - v) s ζ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0VW : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3,
        Integrable (fun ξ : ES =>
          ‖ξ‖⁻¹ * ‖continuousNavierSource v (u - v) s ξ i‖))
    (hs1VW : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource v (u - v) s ξ)))
    (hiVW : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource v (u - v) s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hprodVW : IntegrableOn (fun r =>
        coordinateX0Mass (v r) * coordinateX0Mass ((u - v) r)) (Icc (0 : ℝ) t))
    (wXm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖(u - v) r η j‖))
    (wX1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖(u - v) r η j‖))
    (hmixedW : Integrable (fun s : ℝ =>
        coordinateXm1Mass ((u - v) s) * coordinateX1Mass ((u - v) s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (uXm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (uX1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (hmixedU : Integrable (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (vXm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖v r η j‖))
    (vX1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖v r η j‖))
    (hmixedV : Integrable (fun s : ℝ =>
        coordinateXm1Mass (v s) * coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (u s) <= 2 * R)
    (huX1int : Integrable (fun s : ℝ => coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) <= 2 * ν⁻¹ * R)
    (hvXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (v s) <= 2 * R)
    (hvX1int : Integrable (fun s : ℝ => coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (v s) <= 2 * ν⁻¹ * R) :
    coordinateXm1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u t ξ - continuousMildImage ν hν a v t ξ) <=
      12 * Real.sqrt ν⁻¹ * R *
        Real.sqrt (∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass ((u - v) s) * coordinateX1Mass ((u - v) s)) := by
  have hG4 := continuousMildImage_sub_coordinateXm1Mass_le ν hν a u v t
    hpol huv hvv hwu hvw hDwu hDvw
  set A := Real.sqrt (∫ s in Icc (0 : ℝ) t,
      coordinateXm1Mass ((u - v) s) * coordinateX1Mass ((u - v) s)) with hAd
  set C := 2 * R * Real.sqrt ν⁻¹ with hCd
  have hw_sqrt :
      Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass ((u - v) s) ^ 2) <= A := by
    rw [hAd]
    exact sqrt_X0_sq_le_sqrt_Xm1_mul_X1 (u - v) t wXm1 wX1 hmixedW
  have hu_sqrt : Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (u s) ^ 2) <= C := by
    rw [hCd]
    exact sqrt_integral_X0_sq_le_two_R_mul_sqrt_invNu u ν t R hν hR uXm1 uX1
      hmixedU huXm1 huX1int huX1
  have hv_sqrt : Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (v s) ^ 2) <= C := by
    rw [hCd]
    exact sqrt_integral_X0_sq_le_two_R_mul_sqrt_invNu v ν t R hν hR vXm1 vX1
      hmixedV hvXm1 hvX1int hvX1
  have hDwu := coordinateXm1Mass_continuousDuhamel_le_sqrt_product_X0_sq
    (u - v) u ν t hν hbWU hfWU hgWU hb0WU hs1WU hiWU hmw hmu hmw0 hmu0 hprodWU hw2 hu2
  have hDvw := coordinateXm1Mass_continuousDuhamel_le_sqrt_product_X0_sq
    v (u - v) ν t hν hbVW hfVW hgVW hb0VW hs1VW hiVW hmv hmw hmv0 hmw0 hprodVW hv2 hw2
  have b1 : coordinateXm1Mass (continuousDuhamel ν (u - v) u t) <= 3 * (A * C) := by
    refine hDwu.trans (mul_le_mul_of_nonneg_left ?_
      (by norm_num : (0 : ℝ) <= 3))
    gcongr
  have b2 : coordinateXm1Mass (continuousDuhamel ν v (u - v) t) <= 3 * (C * A) := by
    refine hDvw.trans (mul_le_mul_of_nonneg_left ?_
      (by norm_num : (0 : ℝ) <= 3))
    gcongr
  have hsum : (3 : ℝ) * (A * C) + 3 * (C * A) = 12 * Real.sqrt ν⁻¹ * R * A := by
    rw [hAd, hCd]
    ring
  refine (hG4.trans (add_le_add b1 b2)).trans hsum.le

-- Axiom audit for the public API of this module.
#print axioms normXm1_add_le
#print axioms normX1_add_le
#print axioms coordinateXm1Mass_add_le
#print axioms coordinateX1Mass_add_le
#print axioms continuousMildImage_coord_apply
#print axioms coordinateXm1Mass_continuousDuhamel_self_le_integral_product
#print axioms continuousMildImage_coordinateXm1Mass_le
#print axioms integral_normX1_continuousDuhamel_self_le_source
#print axioms integral_coordinateX1Mass_continuousDuhamel_self_le_integral_product
#print axioms integral_coordinateX1Mass_continuousMildImage_le
#print axioms continuousMildImage_self_map_ball
#print axioms continuousMildImage_self_map_ball_twoR
#print axioms continuousNavierSource_self_sub_self
#print axioms continuousDuhamel_self_sub_self
#print axioms coordinateXm1Mass_continuousDuhamel_le_integral_X0_product
#print axioms continuousMildImage_sub_coordinateXm1Mass_le
#print axioms coordinateXm1Mass_continuousDuhamel_le_sqrt_product_X0_sq
#print axioms sqrt_X0_sq_le_sqrt_Xm1_mul_X1
#print axioms continuousMildImage_sub_coordinateXm1Mass_le_ball_modulus
