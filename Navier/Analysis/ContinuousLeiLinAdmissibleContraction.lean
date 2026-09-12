import Navier.Analysis.ContinuousLeiLinContraction

/-!
# The LINEAR Banach contraction of the whole-space mild map

`ContinuousLeiLinContraction` closes the contraction obligation in the
attained Hölder-½ form

  `X⁻¹(mild u t − mild v t) ≤ (3/2) · sqrt (R · d)`,   `d = sup X⁻¹(u − v)`,

and its module header records that a LINEAR contraction constant is
unavailable **on the sup-`X⁻¹` metric**.  That boundary is real but it is a
statement about one metric, not about the lift: the admissible norm of the
Kato / Lei–Lin scheme carries its own dissipation feed,

  `‖w‖_ν,t = A + ν · B`,   `A ≥ sup_{s∈[0,t]} X⁻¹(w s)`,
  `B ≥ ∫₀ᵗ X¹(w s) ds`,

and on that norm the SAME Chunk-H modulus is linear.  Concretely, the mixed
feed obeys `∫₀ᵗ X⁻¹(w s)·X¹(w s) ds ≤ A · B`
(`integral_Xm1_mul_X1_le_admissible_bounds`), so its square root obeys the
AM–GM bound `sqrt(A·B) ≤ (A + ν·B) / (2·sqrt ν)`
(`sqrt_mul_le_admissible_norm`), and the attained Chunk-H coefficient
`12·sqrt ν⁻¹·R` collapses to `6·ν⁻¹·R ≤ 3/8` at the ball threshold
`R ≤ ν/16`:

  `X⁻¹(mild u t − mild v t) ≤ (3/8) · (A + ν · B)`.

This is a strict linear contraction factor `3/8 < 1` in the `X⁻¹` output
slot of the admissible norm, at the same `ν/16` threshold carried by the
self-map (`continuousMildImage_self_map_ball`).  It closes the module
header's "linear constant" obligation for that slot.

Remaining obligation, named exactly (`research-mathematics.md` §2): the
matching LINEAR estimate for the second slot of the admissible norm, i.e.
`ν · ∫₀ᵗ X¹(mild u s − mild v s) ds ≤ κ · (A + ν · B)` with `κ < 1`.  The
whole-space `X¹` spacetime budget is currently proved only for the DIAGONAL
Duhamel feed (`integral_coordinateX1Mass_continuousDuhamel_self_le_integral_product`,
whose Tonelli kernel `kernelFun` is hard-wired to `continuousNavierSource u u`);
the missing primitive is the mixed-slot generalization of that kernel to
`continuousNavierSource a b`.  Once it lands, the two slots together give the
complete Banach contraction of the whole-space mild map on the admissible
ball, which is the fixed-point input of the NS4 whole-space carrier.
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
open Navier.Analysis.ContinuousLeiLinContraction

namespace Navier.Analysis.ContinuousLeiLinAdmissibleContraction

/-- The admissible (Kato / Lei–Lin) spacetime norm bound of the trial class:
the sup bound `A` of the homogeneous `X⁻¹` mass plus `ν` times the bound `B`
of the spacetime `X¹` dissipation integral.  Both slots are needed: the
`X⁻¹` slot alone does not control the bilinear feed linearly. -/
def admissibleNorm (ν A B : ℝ) : ℝ := A + ν * B

/-- The coordinate `X¹` mass is nonnegative. -/
private theorem x1_nonneg' (u : ES -> ComplexSpace) :
    0 <= coordinateX1Mass u :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **The mixed feed against the admissible bounds.**  If the difference slot
obeys the pointwise `X⁻¹` bound `A` on `[0, t]` and the spacetime `X¹` bound
`B`, then its mixed feed is at most the product `A · B`.  Unlike
`integral_Xm1_mul_X1_le_four_invNu_R_d`, no ball data of the two trial
trajectories is used: the bound is exactly bilinear in the two slots of the
admissible norm of the difference. -/
theorem integral_Xm1_mul_X1_le_admissible_bounds
    (A B t : ℝ) (hA : 0 ≤ A) (w : ℝ -> ES -> ComplexSpace)
    (hmixed : Integrable (fun s : ℝ =>
        coordinateXm1Mass (w s) * coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (w s) ≤ A)
    (hX1int : Integrable (fun s : ℝ => coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (w s) ≤ B) :
    (∫ s in Icc (0 : ℝ) t,
        coordinateXm1Mass (w s) * coordinateX1Mass (w s)) ≤ A * B := by
  have hmT : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
  have hstep : (∫ s in Icc (0 : ℝ) t,
      coordinateXm1Mass (w s) * coordinateX1Mass (w s)) ≤
      ∫ s in Icc (0 : ℝ) t, A * coordinateX1Mass (w s) := by
    refine integral_mono_ae hmixed (hX1int.const_mul A) ?_
    filter_upwards [ae_restrict_mem hmT] with s hs
    exact mul_le_mul_of_nonneg_right (hdist s hs) (x1_nonneg' (w s))
  refine hstep.trans ?_
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hX1 hA

/-- **AM–GM against the admissible norm.**  The geometric mean of the two
admissible slots is controlled linearly by the norm itself:
`sqrt (A · B) ≤ (A + ν · B) / (2 · sqrt ν)`.  This is the exact step that
turns the Hölder-½ Chunk-H modulus into a linear contraction: the square root
is sublinear in the PAIR, not in either slot separately. -/
theorem sqrt_mul_le_admissible_norm (ν A B : ℝ) (hν : 0 < ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Real.sqrt (A * B) ≤ admissibleNorm ν A B / (2 * Real.sqrt ν) := by
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hνB : 0 ≤ ν * B := mul_nonneg hν.le hB
  have hag : Real.sqrt (A * (ν * B)) ≤ (A + ν * B) / 2 := by
    have hsq : A * (ν * B) ≤ ((A + ν * B) / 2) ^ 2 := by
      nlinarith [sq_nonneg (A - ν * B)]
    calc Real.sqrt (A * (ν * B)) ≤ Real.sqrt (((A + ν * B) / 2) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = (A + ν * B) / 2 := Real.sqrt_sq (by positivity)
  have hfac : Real.sqrt (A * (ν * B)) = Real.sqrt ν * Real.sqrt (A * B) := by
    have : A * (ν * B) = ν * (A * B) := by ring
    rw [this, Real.sqrt_mul hν.le]
  have hkey : Real.sqrt ν * Real.sqrt (A * B) ≤ (A + ν * B) / 2 := by
    rw [← hfac]; exact hag
  rw [admissibleNorm, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt ν)]
  calc Real.sqrt (A * B) * (2 * Real.sqrt ν)
      = 2 * (Real.sqrt ν * Real.sqrt (A * B)) := by ring
    _ ≤ 2 * ((A + ν * B) / 2) := by linarith
    _ = A + ν * B := by ring

/-- **The linear contraction reduction.**  Any quantity `M` controlled by the
Chunk-H modulus `12·sqrt ν⁻¹·R·sqrt(∫ X⁻¹(w)·X¹(w))` is controlled by
`(3/8)·(A + ν·B)` once `w` obeys the admissible bounds `A`, `B` and
`R ≤ ν/16`.  The coefficient chain is exactly
`12·sqrt ν⁻¹ · R · (A + νB)/(2 sqrt ν) = 6·ν⁻¹R·(A + νB) ≤ (3/8)(A + νB)`.

This is the LINEAR companion of
`ContinuousLeiLinContraction.modulus_to_distance_reduction`, which reduces the
same modulus to the Hölder-½ form `(3/2)·sqrt(R·d)` on the sup-`X⁻¹` metric. -/
theorem modulus_to_admissible_norm_reduction
    (ν R A B t : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRν : R ≤ ν / 16) (w : ℝ -> ES -> ComplexSpace)
    (hmixed : Integrable (fun s : ℝ =>
        coordinateXm1Mass (w s) * coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (w s) ≤ A)
    (hX1int : Integrable (fun s : ℝ => coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (w s) ≤ B)
    (M : ℝ)
    (hmod : M ≤ 12 * Real.sqrt ν⁻¹ * R *
        Real.sqrt (∫ s in Icc (0 : ℝ) t,
          coordinateXm1Mass (w s) * coordinateX1Mass (w s))) :
    M ≤ (3 / 8 : ℝ) * admissibleNorm ν A B := by
  have hn0 : (0 : ℝ) ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hNn : 0 ≤ admissibleNorm ν A B := by
    rw [admissibleNorm]; positivity
  have hinvR : ν⁻¹ * R ≤ 1 / 16 := by
    refine le_trans (mul_le_mul_of_nonneg_left hRν hn0) ?_
    field_simp [hν.ne']
    exact le_rfl
  have hfeed := integral_Xm1_mul_X1_le_admissible_bounds A B t hA w hmixed hdist
    hX1int hX1
  have hsqrt : Real.sqrt (∫ s in Icc (0 : ℝ) t,
      coordinateXm1Mass (w s) * coordinateX1Mass (w s)) ≤
      admissibleNorm ν A B / (2 * Real.sqrt ν) :=
    (Real.sqrt_le_sqrt hfeed).trans (sqrt_mul_le_admissible_norm ν A B hν hA hB)
  have hcoeff : 0 ≤ (12 : ℝ) * Real.sqrt ν⁻¹ * R :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (Real.sqrt_nonneg _)) hR
  have hsinv : Real.sqrt ν⁻¹ = (Real.sqrt ν)⁻¹ := by
    rw [← Real.sqrt_inv]
  have hss : Real.sqrt ν * Real.sqrt ν = ν := Real.mul_self_sqrt hν.le
  have hinv2 : (Real.sqrt ν)⁻¹ * (Real.sqrt ν)⁻¹ = ν⁻¹ := by
    rw [← mul_inv, hss]
  have hprod : (12 : ℝ) * Real.sqrt ν⁻¹ * R *
      (admissibleNorm ν A B / (2 * Real.sqrt ν)) =
      6 * (ν⁻¹ * R) * admissibleNorm ν A B := by
    have h1 : (12 : ℝ) * Real.sqrt ν⁻¹ * R *
        (admissibleNorm ν A B / (2 * Real.sqrt ν)) =
        6 * ((Real.sqrt ν)⁻¹ * (Real.sqrt ν)⁻¹ * R) * admissibleNorm ν A B := by
      rw [hsinv, div_eq_mul_inv, mul_inv]
      ring
    rw [h1, hinv2]
  have hfinal : 6 * (ν⁻¹ * R) * admissibleNorm ν A B ≤
      (3 / 8 : ℝ) * admissibleNorm ν A B := by
    have h6 : 6 * (ν⁻¹ * R) ≤ (3 / 8 : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_right h6 hNn
  refine hmod.trans ?_
  refine le_trans (mul_le_mul_of_nonneg_left hsqrt hcoeff) ?_
  exact hprod.le.trans hfinal

/-- **The whole-space mild map is a LINEAR contraction in the admissible
norm.**  Same hypothesis bundle as
`ContinuousLeiLinSelfMap.continuousMildImage_sub_coordinateXm1Mass_le_ball_modulus`
(polarization, Fubini/Bochner integrability of both mixed slots, and the ball
budgets `X⁻¹(u s), X⁻¹(v s) ≤ 2R`, `∫ X¹(u), ∫ X¹(v) ≤ 2ν⁻¹R`), with the
difference slot measured in the admissible norm: `A` bounds its pointwise
`X⁻¹` mass on `[0, t]` and `B` bounds its spacetime `X¹` integral.  At
`R ≤ ν/16` the mild image difference obeys

  `X⁻¹(mild u t − mild v t) ≤ (3/8) · (A + ν · B)`.

The factor `3/8 < 1` is a strict LINEAR contraction constant, superseding the
sup-`X⁻¹` Hölder-½ form
`continuousMildImage_sub_coordinateXm1Mass_le_ball_modulus_sqrt_ball_distance`
for the `X⁻¹` output slot.  The remaining named obligation is the matching
`X¹` output slot, which needs the mixed-slot generalization of `kernelFun`
(see the module header). -/
theorem continuousMildImage_sub_coordinateXm1Mass_le_linear_admissible
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
    (hRν : R ≤ ν / 16) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass ((u - v) s) ≤ A)
    (hwX1int : Integrable (fun s : ℝ => coordinateX1Mass ((u - v) s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hwX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass ((u - v) s) ≤ B) :
    coordinateXm1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u t ξ - continuousMildImage ν hν a v t ξ) ≤
      (3 / 8 : ℝ) * admissibleNorm ν A B := by
  refine modulus_to_admissible_norm_reduction ν R A B t hν hR hA hB hRν (u - v)
    hmixedW hdist hwX1int hwX1 _ ?_
  exact continuousMildImage_sub_coordinateXm1Mass_le_ball_modulus ν hν a u v R t hR hpol huv hvv hwu hvw hDwu hDvw hmw hmw0 hmu hmu0 hmv hmv0 hw2 hu2 hv2 hbWU hfWU hgWU hb0WU hs1WU hiWU hprodWU hbVW hfVW hgVW hb0VW hs1VW hiVW hprodVW wXm1 wX1 hmixedW uXm1 uX1 hmixedU vXm1 vX1 hmixedV huXm1 huX1int huX1 hvXm1 hvX1int hvX1

/-- The contraction factor is strictly less than one: the admissible-norm
contraction of the whole-space mild map is a genuine Banach contraction
constant in its `X⁻¹` slot, not a modulus of continuity. -/
theorem contraction_factor_lt_one : (3 / 8 : ℝ) < 1 := by norm_num

end Navier.Analysis.ContinuousLeiLinAdmissibleContraction

#print axioms Navier.Analysis.ContinuousLeiLinAdmissibleContraction.integral_Xm1_mul_X1_le_admissible_bounds
#print axioms Navier.Analysis.ContinuousLeiLinAdmissibleContraction.sqrt_mul_le_admissible_norm
#print axioms Navier.Analysis.ContinuousLeiLinAdmissibleContraction.modulus_to_admissible_norm_reduction
#print axioms Navier.Analysis.ContinuousLeiLinAdmissibleContraction.continuousMildImage_sub_coordinateXm1Mass_le_linear_admissible
