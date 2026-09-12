import Navier.Analysis.ContinuousLeiLinSelfMap

/-!
# The contraction modulus of the whole-space mild map in the ball distance

The self-map budgets in `ContinuousLeiLinSelfMap` close the `(7/4)R` ball
at `R <= ν/16` (obligation [PDE self-map]), and Chunk H supplies the
Hölder-½ modulus of the mild image against the mixed `X⁻¹·X¹` feed of the
difference slot.  This module completes that transport by pushing the
difference feed through the BALL DISTANCE itself: with
`d = sup(s in [0,t]) X⁻¹((u - v) s)` and `ν⁻¹R ≤ 1/16`, the attained
modulus is

  `X⁻¹(mild u t - mild v t) ≤ (3/2) * sqrt (R * d)`.

Honest status (recorded per `research-mathematics.md` §2): this is a
quadratic/Hölder-½ modulus, NOT a linear Banach contraction constant, and no
linear constant is available FOR THIS METRIC — the plain sup-`X⁻¹` ball
metric.  The boundary is metric-specific, not a property of the lift: in
`ContinuousLeiLinAdmissibleContraction` the SAME Chunk-H modulus is shown to
be linear in the admissible norm `A + ν·B` (sup-`X⁻¹` bound `A` plus `ν`
times the spacetime `X¹` bound `B`), with the strict contraction factor
`3/8` at the same threshold `R ≤ ν/16`
(`continuousMildImage_sub_coordinateXm1Mass_le_linear_admissible`).  The
reason the sup-`X⁻¹` metric alone cannot carry a linear constant is below.
The fixed-time symbol carrier
(`ContinuousLeiLinSpace.inv_mul_derivative_le`) cancels the output `X⁻¹`
weight against the output-frequency derivative exactly, leaving the
UNWEIGHTED convolution mass of both inputs: every bilinear feed here ends
in `X⁰(w) * X⁰(z)`
(`coordinateXm1Mass_continuousDuhamel_le_integral_X0_product`).  The
quantity `X⁰(w)` is not linearly bounded by `sup X⁻¹(w)` on this carrier
(a frequency bump at scale Λ has `X⁰` mass fixed while `X⁻¹` mass decays
like `Λ⁻¹`), and negative weights do not split across convolution
(`‖η + ζ‖⁻¹ ≤ ‖η‖⁻¹ + ‖ζ‖⁻¹` fails).  A linear contraction therefore needs
the difference measured in a spacetime admissible norm carrying its own
dissipation feed (the Kato / Furioli--Lemarié-Rieusset scheme) — that is
exactly what `ContinuousLeiLinAdmissibleContraction` now supplies for the
`X⁻¹` output slot.  On the plain sup-`X⁻¹` metric the `(3/2)·sqrt(R·d)`
bound obtained here is the attained contraction obligation for the lift,
matching the BUILD THE LIFT directive's instruction to report the attained
constant honestly.
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
open Navier.Analysis.ContinuousLeiLinSelfMap

namespace Navier.Analysis.ContinuousLeiLinContraction

/-- The coordinate `X⁻¹` mass is nonnegative. -/
private theorem xm1_nonneg (u : ES -> ComplexSpace) :
    0 <= coordinateXm1Mass u :=
  Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ξ =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _)

/-- The coordinate `X¹` mass is nonnegative. -/
private theorem x1_nonneg (u : ES -> ComplexSpace) :
    0 <= coordinateX1Mass u :=
  Finset.sum_nonneg fun i _ =>
    integral_nonneg fun ξ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The coordinate `X¹` mass is subadditive under differences. -/
theorem coordinateX1Mass_sub_le (u v : ES -> ComplexSpace)
    (hu : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖u ξ i‖))
    (hv : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖v ξ i‖)) :
    coordinateX1Mass (u - v) ≤ coordinateX1Mass u + coordinateX1Mass v := by
  have hng : ∀ i : Fin 3, Integrable (fun ξ : ES => ‖ξ‖ * ‖(-v) ξ i‖) := by
    intro i
    have hfun : (fun ξ : ES => ‖ξ‖ * ‖(-v) ξ i‖) =
        fun ξ : ES => ‖ξ‖ * ‖v ξ i‖ := by
      funext ξ
      simp
    rw [hfun]
    exact hv i
  have hn1 : ∀ f : ES -> ℂ, normX1 (fun ξ : ES => -f ξ) = normX1 f := by
    intro f
    show (∫ ξ : ES, ‖ξ‖ * ‖-f ξ‖) = ∫ ξ : ES, ‖ξ‖ * ‖f ξ‖
    refine integral_congr_ae ?_
    filter_upwards with ξ
    rw [norm_neg]
  have hneg : coordinateX1Mass (-v) = coordinateX1Mass v := by
    unfold coordinateX1Mass
    refine Finset.sum_congr rfl fun i _ => ?_
    refine congrArg normX1 (by funext ξ; rfl) |>.trans (hn1 (fun ξ : ES => v ξ i))
  rw [sub_eq_add_neg]
  refine (coordinateX1Mass_add_le u (-v) hu hng).trans ?_
  exact add_le_add (le_refl _) hneg.le

/-- Chunk J, step 1: the difference-slot mixed feed is bounded by the ball
data alone: if the pointwise `X⁻¹` mass of the difference is at most `d`
and its `X¹` mass is pointwise dominated by the two slots' `X¹` masses, the
time-integrated product `∫ X⁻¹(w) · X¹(w)` is at most `4 ν⁻¹ R d`. -/
theorem integral_Xm1_mul_X1_le_four_invNu_R_d
    (ν R d t : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) (hd0 : 0 ≤ d)
    (w u v : ℝ -> ES -> ComplexSpace)
    (hwprod : Integrable (fun s : ℝ =>
        coordinateXm1Mass (w s) * coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (w s) ≤ d)
    (hsub : ∀ s ∈ Icc (0 : ℝ) t,
        coordinateX1Mass (w s) ≤ coordinateX1Mass (u s) + coordinateX1Mass (v s))
    (huX1int : Integrable (fun s : ℝ => coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvX1int : Integrable (fun s : ℝ => coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) ≤ 2 * ν⁻¹ * R)
    (hvX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (v s) ≤ 2 * ν⁻¹ * R) :
    ∫ s in Icc (0 : ℝ) t, coordinateXm1Mass (w s) * coordinateX1Mass (w s) ≤
      4 * ν⁻¹ * R * d := by
  have hmn : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) t)]
      fun s : ℝ => coordinateXm1Mass (w s) * coordinateX1Mass (w s) := by
    filter_upwards with s
    exact mul_nonneg (xm1_nonneg (w s)) (x1_nonneg (w s))
  have hmaj : Integrable (fun s : ℝ =>
      d • (coordinateX1Mass (u s) + coordinateX1Mass (v s)))
      (volume.restrict (Icc (0 : ℝ) t)) :=
    (huX1int.add hvX1int).smul d
  have hfg : (fun s : ℝ => coordinateXm1Mass (w s) * coordinateX1Mass (w s)) ≤ᵐ[volume.restrict (Icc (0 : ℝ) t)]
      fun s : ℝ => d • (coordinateX1Mass (u s) + coordinateX1Mass (v s)) := by
    filter_upwards [ae_restrict_mem hmn] with s hs
    have key : coordinateXm1Mass (w s) * coordinateX1Mass (w s) ≤
        d * (coordinateX1Mass (u s) + coordinateX1Mass (v s)) := by
      refine le_trans (mul_le_mul_of_nonneg_right (hdist s hs) (x1_nonneg (w s))) ?_
      exact mul_le_mul_of_nonneg_left (hsub s hs) hd0
    simpa only [smul_eq_mul] using key
  refine le_trans (integral_mono_of_nonneg hnonneg hmaj hfg) ?_
  rw [integral_smul, integral_add huX1int hvX1int, smul_eq_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (add_le_add huX1 hvX1) hd0) ?_
  ring_nf
  exact le_rfl

/-- Chunk J, step 2: the reduction of the ball modulus to the ball distance.
Any `M` controlled by the Chunk H modulus `12 sqrt ν⁻¹ R sqrt(∫ X⁻¹(w)·X¹(w))`
is controlled by `(3/2) * sqrt (R * d)` once `w` obeys the pointwise distance
bound `d` and the ball dissipation budgets, at `R ≤ ν/16`. -/
theorem modulus_to_distance_reduction
    (ν R d t : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) (hd0 : 0 ≤ d) (hRν : R ≤ ν / 16)
    (w u v : ℝ -> ES -> ComplexSpace)
    (hwprod : Integrable (fun s : ℝ =>
        coordinateXm1Mass (w s) * coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (w s) ≤ d)
    (hsub : ∀ s ∈ Icc (0 : ℝ) t,
        coordinateX1Mass (w s) ≤ coordinateX1Mass (u s) + coordinateX1Mass (v s))
    (huX1int : Integrable (fun s : ℝ => coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvX1int : Integrable (fun s : ℝ => coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) ≤ 2 * ν⁻¹ * R)
    (hvX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (v s) ≤ 2 * ν⁻¹ * R)
    (M : ℝ)
    (hmod : M ≤ 12 * Real.sqrt ν⁻¹ * R *
        Real.sqrt (∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (w s) * coordinateX1Mass (w s))) :
    M ≤ (3 / 2 : ℝ) * Real.sqrt (R * d) := by
  have hn0 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have hinvR : ν⁻¹ * R ≤ 1 / 16 := by
    refine le_trans (mul_le_mul_of_nonneg_left hRν hn0) ?_
    field_simp [hν.ne']
    exact le_rfl
  have hle : (∫ s in Icc (0 : ℝ) t,
      coordinateXm1Mass (w s) * coordinateX1Mass (w s)) ≤ 4 * ν⁻¹ * R * d :=
    integral_Xm1_mul_X1_le_four_invNu_R_d ν R d t hν hR hd0 w u v hwprod hdist
      hsub huX1int hvX1int huX1 hvX1
  have hsqrt : Real.sqrt (∫ s in Icc (0 : ℝ) t,
      coordinateXm1Mass (w s) * coordinateX1Mass (w s)) ≤
      2 * Real.sqrt (ν⁻¹ * R * d) := by
    have key : (2 * Real.sqrt (ν⁻¹ * R * d)) ^ 2 = 4 * ν⁻¹ * R * d := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg (mul_nonneg hn0 hR) hd0)]
      ring
    refine (Real.sqrt_le_sqrt (hle.trans key.symm.le)).trans_eq ?_
    exact Real.sqrt_sq (mul_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
      (Real.sqrt_nonneg _))
  have hcoeff : 0 ≤ (12 : ℝ) * Real.sqrt ν⁻¹ * R :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (Real.sqrt_nonneg _)) hR
  have ha : Real.sqrt ν⁻¹ * Real.sqrt (ν⁻¹ * (R * d)) =
      ν⁻¹ * Real.sqrt (R * d) :=
    calc Real.sqrt ν⁻¹ * Real.sqrt (ν⁻¹ * (R * d))
        = Real.sqrt (ν⁻¹ * (ν⁻¹ * (R * d))) :=
          (Real.sqrt_mul hn0 (ν⁻¹ * (R * d))).symm
      _ = Real.sqrt (ν⁻¹ ^ 2 * (R * d)) := by congr 1; ring
      _ = Real.sqrt (ν⁻¹ ^ 2) * Real.sqrt (R * d) :=
          Real.sqrt_mul (pow_two_nonneg _) (R * d)
      _ = ν⁻¹ * Real.sqrt (R * d) := by rw [Real.sqrt_sq hn0]
  have e1 : (12 : ℝ) * Real.sqrt ν⁻¹ * R * (2 * Real.sqrt (ν⁻¹ * R * d)) =
      24 * (ν⁻¹ * R) * Real.sqrt (R * d) := by
    have h2 : (12 : ℝ) * Real.sqrt ν⁻¹ * R * (2 * Real.sqrt (ν⁻¹ * R * d)) =
        (24 : ℝ) * (Real.sqrt ν⁻¹ * Real.sqrt (ν⁻¹ * (R * d))) * R := by
      rw [mul_assoc ν⁻¹ R d]
      ring
    rw [h2, ha]
    ring
  have hbnd : (24 : ℝ) * (ν⁻¹ * R) * Real.sqrt (R * d) ≤
      (3 / 2 : ℝ) * Real.sqrt (R * d) := by
    calc (24 : ℝ) * (ν⁻¹ * R) * Real.sqrt (R * d)
        = (24 * Real.sqrt (R * d)) * (ν⁻¹ * R) := by ring
      _ ≤ (24 * Real.sqrt (R * d)) * (1 / 16) :=
          mul_le_mul_of_nonneg_left hinvR
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ (24 : ℝ)) (Real.sqrt_nonneg _))
      _ = (3 / 2 : ℝ) * Real.sqrt (R * d) := by ring
  refine hmod.trans ?_
  exact ((mul_le_mul_of_nonneg_left hsqrt hcoeff).trans (le_of_eq e1)).trans hbnd

/-- **The contraction obligation, attained form.**  For two trial
trajectories whose images obey the Chunk H hypotheses, whose difference obeys
the pointwise `X⁻¹` distance bound `d` on `[0, t]`, and whose `X¹` dissipation
budgets are the ball budgets `2 ν⁻¹ R`, the mild image difference at time `t`
is bounded by `(3/2) * sqrt (R * d)` at `R ≤ ν/16`.  As recorded in the module
header, this Hölder-½ form is the ATTAINED contraction constant of the whole-
space lift on the sup-`X⁻¹` ball metric.  The linear Banach form is
unavailable on THAT metric; it is available on the admissible spacetime norm
and is proved in
`ContinuousLeiLinAdmissibleContraction.continuousMildImage_sub_coordinateXm1Mass_le_linear_admissible`
with factor `3/8`. -/
theorem continuousMildImage_sub_coordinateXm1Mass_le_ball_modulus_sqrt_ball_distance

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
    (hvX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (v s) <= 2 * ν⁻¹ * R)
    (hRν : R ≤ ν / 16) (d : ℝ) (hd0 : 0 ≤ d)
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass ((u - v) s) ≤ d) :
    coordinateXm1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u t ξ - continuousMildImage ν hν a v t ξ) ≤
      (3 / 2 : ℝ) * Real.sqrt (R * d) := by
  refine modulus_to_distance_reduction ν R d t hν hR hd0 hRν (u - v) u v hmixedW
    hdist
    (fun s hs => coordinateX1Mass_sub_le (u s) (v s) (fun i => uX1 s i)
      (fun i => vX1 s i))
    huX1int hvX1int huX1 hvX1 _ ?_
  · exact continuousMildImage_sub_coordinateXm1Mass_le_ball_modulus ν hν a u v R t hR hpol huv hvv hwu hvw hDwu hDvw hmw hmw0 hmu hmu0 hmv hmv0 hw2 hu2 hv2 hbWU hfWU hgWU hb0WU hs1WU hiWU hprodWU hbVW hfVW hgVW hb0VW hs1VW hiVW hprodVW wXm1 wX1 hmixedW uXm1 uX1 hmixedU vXm1 vX1 hmixedV huXm1 huX1int huX1 hvXm1 hvX1int hvX1

end Navier.Analysis.ContinuousLeiLinContraction

#print axioms Navier.Analysis.ContinuousLeiLinContraction.coordinateX1Mass_sub_le
#print axioms Navier.Analysis.ContinuousLeiLinContraction.integral_Xm1_mul_X1_le_four_invNu_R_d
#print axioms Navier.Analysis.ContinuousLeiLinContraction.modulus_to_distance_reduction
#print axioms Navier.Analysis.ContinuousLeiLinContraction.continuousMildImage_sub_coordinateXm1Mass_le_ball_modulus_sqrt_ball_distance
