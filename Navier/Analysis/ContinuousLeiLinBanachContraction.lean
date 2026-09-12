import Navier.Analysis.ContinuousLeiLinMixedX1

/-!
# The `X¹` slot of the admissible Banach contraction

`ContinuousLeiLinAdmissibleContraction` closes the `X⁻¹` slot of the
admissible-norm contraction with factor `3/8` at `R ≤ ν/16`.  This module
closes the second slot: the spacetime `X¹` half of the same norm, using the
mixed-slot budget of `ContinuousLeiLinMixedX1`.

The chain is
* `integral_X0_product_le_ball_admissible` — time Cauchy–Schwarz on the
  `X⁰` feed, the fixed-time interpolation `X⁰² ≤ X⁻¹·X¹`, the admissible
  AM–GM bound on the difference slot and the ball budget `2R·sqrt ν⁻¹` on the
  trial slot give `∫₀ᵗ X⁰(w)·X⁰(z) ≤ ν⁻¹·R·(A + ν·B)`;
* `coordinateX1Mass_continuousMildImage_sub_le` — the shared free heat term
  cancels, so the `X¹` mass of the image difference splits into the two
  polarization Duhamel slots (the `X¹` analogue of
  `continuousMildImage_sub_coordinateXm1Mass_le`);
* `X1_slot_admissible_reduction` — the mixed `X¹` budget `3·ν⁻¹` times the
  two feeds, at `ν⁻¹R ≤ 1/16`, gives
  `ν · ∫₀ᵗ X¹(mild u s − mild v s) ds ≤ (3/8)·(A + ν·B)`.

Together with the `X⁻¹` slot the whole-space mild map is a LINEAR Banach
contraction of the admissible norm with factor `3/4 < 1` at `R ≤ ν/16`
(`admissibleNorm_slot_sum`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter Topology BigOperators
open scoped NNReal ENNReal
open Navier.Analysis.ContinuousLeiLinSpace
open Navier.Analysis.ContinuousLeiLinTimeDuhamel
open Navier.Analysis.ComplexLerayNorm
open Navier.Analysis.ContinuousLeiLinDissipation
open Navier.Analysis.ContinuousLeiLinSelfMap
open Navier.Analysis.ContinuousLeiLinAdmissibleContraction
open Navier.Analysis.ContinuousLeiLinMixedX1

namespace Navier.Analysis.ContinuousLeiLinBanachContraction

/-- The `X⁰` mass is pointwise nonnegative. -/
private theorem x0_nonneg (u : ES -> ComplexSpace) :
    0 <= coordinateX0Mass u :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

/-- The `X⁻¹` mass is pointwise nonnegative. -/
private theorem xm1_nonneg (u : ES -> ComplexSpace) :
    0 <= coordinateXm1Mass u :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun ξ =>
      mul_nonneg (inv_nonneg.mpr (norm_nonneg ξ)) (norm_nonneg _)

/-- The `X¹` mass is pointwise nonnegative. -/
private theorem x1_nonneg (u : ES -> ComplexSpace) :
    0 <= coordinateX1Mass u :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)

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

/-- A slot whose pointwise `X⁻¹` mass is at most `2 R` on `[0, t]` and whose
total `X¹` mass is at most `2 ν⁻¹ R` has time `L²`-`X⁰` square root at most
`2 R sqrt ν⁻¹` (the ball form; companion of the admissible form below). -/
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
      <= (2 * R) * (2 * ν⁻¹ * R) :=
        integral_Xm1_mul_X1_le_admissible_bounds (2 * R) (2 * ν⁻¹ * R) t
          (by positivity) u hmixed hXm1 hX1int hX1
    _ = 4 * ν⁻¹ * R ^ 2 := by ring
    _ = (2 * R * Real.sqrt ν⁻¹) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (inv_nonneg.mpr hν.le)]
        ring

/-- The admissible form of the same square root: a slot obeying the
admissible bounds `A` (pointwise `X⁻¹`) and `B` (spacetime `X¹`) has time
`L²`-`X⁰` square root at most `(A + ν·B) / (2·sqrt ν)`. -/
theorem sqrt_integral_X0_sq_le_admissible
    (w : ℝ -> ES -> ComplexSpace) (ν t A B : ℝ) (hν : 0 < ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hwm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖w r η j‖))
    (hw1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖w r η j‖))
    (hmixed : Integrable (fun s : ℝ =>
        coordinateXm1Mass (w s) * coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (w s) ≤ A)
    (hX1int : Integrable (fun s : ℝ => coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (w s) ≤ B) :
    Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (w s) ^ 2) ≤
      admissibleNorm ν A B / (2 * Real.sqrt ν) := by
  refine (sqrt_X0_sq_le_sqrt_Xm1_mul_X1 w t hwm1 hw1 hmixed).trans ?_
  refine (Real.sqrt_le_sqrt (integral_Xm1_mul_X1_le_admissible_bounds A B t hA w
    hmixed hdist hX1int hX1)).trans ?_
  exact sqrt_mul_le_admissible_norm ν A B hν hA hB

/-- **The bilinear `X⁰` feed against one admissible slot and one ball slot.**
Time Cauchy–Schwarz plus the two square-root bounds give

  `∫₀ᵗ X⁰(w s)·X⁰(z s) ds ≤ ν⁻¹ · R · (A + ν·B)`,

linear in the admissible norm of `w` and proportional to the ball radius of
`z`.  This is the estimate that makes BOTH slots of the mild map contract. -/
theorem integral_X0_product_le_ball_admissible
    (w z : ℝ -> ES -> ComplexSpace) (ν t R A B : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hwm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖w r η j‖))
    (hw1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖w r η j‖))
    (hmixedW : Integrable (fun s : ℝ =>
        coordinateXm1Mass (w s) * coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (w s) ≤ A)
    (hwX1int : Integrable (fun s : ℝ => coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hwX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (w s) ≤ B)
    (hzm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖z r η j‖))
    (hz1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖z r η j‖))
    (hmixedZ : Integrable (fun s : ℝ =>
        coordinateXm1Mass (z s) * coordinateX1Mass (z s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hzXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (z s) ≤ 2 * R)
    (hzX1int : Integrable (fun s : ℝ => coordinateX1Mass (z s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hzX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (z s) ≤ 2 * ν⁻¹ * R)
    (hw2 : Integrable (fun s : ℝ => coordinateX0Mass (w s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hz2 : Integrable (fun s : ℝ => coordinateX0Mass (z s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t))) :
    (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (w s) * coordinateX0Mass (z s)) ≤
      ν⁻¹ * R * admissibleNorm ν A B := by
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.mpr hν
  have hNn : 0 ≤ admissibleNorm ν A B := by rw [admissibleNorm]; positivity
  have hcs := integral_mul_le_sqrt_mul_sqrt (volume.restrict (Icc (0 : ℝ) t))
    (fun s => coordinateX0Mass (w s)) (fun s => coordinateX0Mass (z s))
    (fun s => x0_nonneg (w s)) (fun s => x0_nonneg (z s)) hw2 hz2
  have hWb := sqrt_integral_X0_sq_le_admissible w ν t A B hν hA hB hwm1 hw1
    hmixedW hdist hwX1int hwX1
  have hZb := sqrt_integral_X0_sq_le_two_R_mul_sqrt_invNu z ν t R hν hR hzm1 hz1
    hmixedZ hzXm1 hzX1int hzX1
  have hZ0 : 0 ≤ Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (z s) ^ 2) :=
    Real.sqrt_nonneg _
  have hprod : (admissibleNorm ν A B / (2 * Real.sqrt ν)) *
      (2 * R * Real.sqrt ν⁻¹) = ν⁻¹ * R * admissibleNorm ν A B := by
    have hsinv : Real.sqrt ν⁻¹ = (Real.sqrt ν)⁻¹ := by rw [← Real.sqrt_inv]
    have hss : Real.sqrt ν * Real.sqrt ν = ν := Real.mul_self_sqrt hν.le
    have hinv2 : (Real.sqrt ν)⁻¹ * (Real.sqrt ν)⁻¹ = ν⁻¹ := by
      rw [← mul_inv, hss]
    have h1 : (admissibleNorm ν A B / (2 * Real.sqrt ν)) *
        (2 * R * Real.sqrt ν⁻¹) =
        ((Real.sqrt ν)⁻¹ * (Real.sqrt ν)⁻¹) * R * admissibleNorm ν A B := by
      rw [hsinv, div_eq_mul_inv, mul_inv]
      ring
    rw [h1, hinv2]
  refine hcs.trans ?_
  calc Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (w s) ^ 2) *
        Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (z s) ^ 2)
      ≤ (admissibleNorm ν A B / (2 * Real.sqrt ν)) *
          Real.sqrt (∫ s in Icc (0 : ℝ) t, coordinateX0Mass (z s) ^ 2) :=
        mul_le_mul_of_nonneg_right hWb hZ0
    _ ≤ (admissibleNorm ν A B / (2 * Real.sqrt ν)) * (2 * R * Real.sqrt ν⁻¹) :=
        mul_le_mul_of_nonneg_left hZb (by positivity)
    _ = ν⁻¹ * R * admissibleNorm ν A B := hprod

/-- **The `X¹`-slot contraction, reduction form.**  Any quantity `M`
controlled by the mixed `X¹` budget `3·ν⁻¹` times the two polarization `X⁰`
feeds is controlled by `(3/8)·ν⁻¹·(A + ν·B)` at `R ≤ ν/16`; equivalently
`ν·M ≤ (3/8)·(A + ν·B)`.  The caller instantiates `M` with
`∫₀ᵗ X¹(mild u s − mild v s) ds`, using
`coordinateX1Mass_continuousMildImage_sub_le` for the split and
`ContinuousLeiLinMixedX1.integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product`
for each slot budget. -/
theorem X1_slot_admissible_reduction
    (w u v : ℝ -> ES -> ComplexSpace) (ν t R A B : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hRν : R ≤ ν / 16)
    (hwm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖w r η j‖))
    (hw1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖w r η j‖))
    (hmixedW : Integrable (fun s : ℝ =>
        coordinateXm1Mass (w s) * coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (w s) ≤ A)
    (hwX1int : Integrable (fun s : ℝ => coordinateX1Mass (w s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hwX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (w s) ≤ B)
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (hmixedU : Integrable (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (u s) ≤ 2 * R)
    (huX1int : Integrable (fun s : ℝ => coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) ≤ 2 * ν⁻¹ * R)
    (hvm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖v r η j‖))
    (hv1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖v r η j‖))
    (hmixedV : Integrable (fun s : ℝ =>
        coordinateXm1Mass (v s) * coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (v s) ≤ 2 * R)
    (hvX1int : Integrable (fun s : ℝ => coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (v s) ≤ 2 * ν⁻¹ * R)
    (hw2 : Integrable (fun s : ℝ => coordinateX0Mass (w s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hu2 : Integrable (fun s : ℝ => coordinateX0Mass (u s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hv2 : Integrable (fun s : ℝ => coordinateX0Mass (v s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (M : ℝ)
    (hM : M ≤ 3 * ν⁻¹ * (∫ s in Icc (0 : ℝ) t,
            coordinateX0Mass (w s) * coordinateX0Mass (u s)) +
          3 * ν⁻¹ * (∫ s in Icc (0 : ℝ) t,
            coordinateX0Mass (v s) * coordinateX0Mass (w s))) :
    ν * M ≤ (3 / 8 : ℝ) * admissibleNorm ν A B := by
  have hn0 : (0 : ℝ) ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have hNn : 0 ≤ admissibleNorm ν A B := by rw [admissibleNorm]; positivity
  have hinvR : ν⁻¹ * R ≤ 1 / 16 := by
    refine le_trans (mul_le_mul_of_nonneg_left hRν hn0) ?_
    field_simp [hν.ne']
    exact le_rfl
  have hWU := integral_X0_product_le_ball_admissible w u ν t R A B hν hR hA hB
    hwm1 hw1 hmixedW hdist hwX1int hwX1 hum1 hu1 hmixedU huXm1 huX1int huX1 hw2 hu2
  have hVW : (∫ s in Icc (0 : ℝ) t,
      coordinateX0Mass (v s) * coordinateX0Mass (w s)) ≤
      ν⁻¹ * R * admissibleNorm ν A B := by
    have hswap : (∫ s in Icc (0 : ℝ) t,
        coordinateX0Mass (v s) * coordinateX0Mass (w s)) =
        ∫ s in Icc (0 : ℝ) t,
          coordinateX0Mass (w s) * coordinateX0Mass (v s) := by
      refine integral_congr_ae ?_
      filter_upwards with s
      exact mul_comm _ _
    rw [hswap]
    exact integral_X0_product_le_ball_admissible w v ν t R A B hν hR hA hB
      hwm1 hw1 hmixedW hdist hwX1int hwX1 hvm1 hv1 hmixedV hvXm1 hvX1int hvX1 hw2 hv2
  have hsum : M ≤ 6 * ν⁻¹ * (ν⁻¹ * R) * admissibleNorm ν A B := by
    refine hM.trans ?_
    have h1 := mul_le_mul_of_nonneg_left hWU
      (by positivity : (0 : ℝ) ≤ 3 * ν⁻¹)
    have h2 := mul_le_mul_of_nonneg_left hVW
      (by positivity : (0 : ℝ) ≤ 3 * ν⁻¹)
    nlinarith [h1, h2]
  have hkey : ν * M ≤ ν * (6 * ν⁻¹ * (ν⁻¹ * R) * admissibleNorm ν A B) :=
    mul_le_mul_of_nonneg_left hsum hν.le
  refine hkey.trans ?_
  have hcollapse : ν * (6 * ν⁻¹ * (ν⁻¹ * R) * admissibleNorm ν A B) =
      6 * (ν⁻¹ * R) * admissibleNorm ν A B := by
    field_simp
  rw [hcollapse]
  have h6 : 6 * (ν⁻¹ * R) ≤ (3 / 8 : ℝ) := by linarith
  exact mul_le_mul_of_nonneg_right h6 hNn

/-- **The `X¹` split of the mild-image difference.**  The shared free heat
evolution cancels, so the `X¹` mass of the image difference is bounded by the
sum of the two polarization Duhamel `X¹` masses.  `X¹` analogue of
`ContinuousLeiLinSelfMap.continuousMildImage_sub_coordinateXm1Mass_le`. -/
theorem coordinateX1Mass_continuousMildImage_sub_le
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
        ‖ξ‖ * ‖continuousDuhamel ν (u - v) u t ξ i‖))
    (hDvw : ∀ i : Fin 3, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν v (u - v) t ξ i‖)) :
    coordinateX1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u t ξ - continuousMildImage ν hν a v t ξ) ≤
      coordinateX1Mass (continuousDuhamel ν (u - v) u t) +
        coordinateX1Mass (continuousDuhamel ν v (u - v) t) := by
  have hfe : (fun ξ : ES =>
      continuousMildImage ν hν a u t ξ - continuousMildImage ν hν a v t ξ) =
      (continuousDuhamel ν (u - v) u t + continuousDuhamel ν v (u - v) t) := by
    funext ξ
    funext i
    show continuousMildImage ν hν a u t ξ i - continuousMildImage ν hν a v t ξ i =
      continuousDuhamel ν (u - v) u t ξ i + continuousDuhamel ν v (u - v) t ξ i
    rw [continuousMildImage_coord_apply, continuousMildImage_coord_apply,
      add_sub_add_left_eq_sub]
    exact continuousDuhamel_self_sub_self ν u v t ξ i (fun s hs => hpol i ξ s hs)
      (huv i ξ) (hvv i ξ) (hwu i ξ) (hvw i ξ)
  rw [hfe]
  exact coordinateX1Mass_add_le (continuousDuhamel ν (u - v) u t)
    (continuousDuhamel ν v (u - v) t) hDwu hDvw

/-- **The two admissible slots compose to the Banach factor `3/4`.**  Adding
the `X⁻¹` slot bound (`ContinuousLeiLinAdmissibleContraction`,
`continuousMildImage_sub_coordinateXm1Mass_le_linear_admissible`) and the
`X¹` slot bound (`X1_slot_admissible_reduction`) gives the admissible norm of
the mild-image difference bounded by `(3/4)·(A + ν·B)`; the factor
`3/4 < 1` is a strict LINEAR Banach contraction constant at `R ≤ ν/16`. -/
theorem admissibleNorm_slot_sum (ν A B X Y : ℝ)
    (hX : X ≤ (3 / 8 : ℝ) * admissibleNorm ν A B)
    (hY : Y ≤ (3 / 8 : ℝ) * admissibleNorm ν A B) :
    X + Y ≤ (3 / 4 : ℝ) * admissibleNorm ν A B := by linarith

/-- The composed Banach factor is strictly less than one. -/
theorem banach_factor_lt_one : (3 / 4 : ℝ) < 1 := by norm_num

/-- **The `X¹` slot of the admissible contraction, fully instantiated.**  The
single-theorem form of `X1_slot_admissible_reduction`: no `M`, no supplied
modulus.  The split `coordinateX1Mass_continuousMildImage_sub_le` is applied
at every horizon `s ∈ [0, t]`, the mixed-slot spacetime budget
`ContinuousLeiLinMixedX1.integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product`
is applied to each polarization slot, and the bilinear feed
`integral_X0_product_le_ball_admissible` closes both at `R ≤ ν/16`:

  `ν · ∫₀ᵗ X¹(mild u s − mild v s) ds ≤ (3/8) · (A + ν·B)`.

Together with
`ContinuousLeiLinAdmissibleContraction.continuousMildImage_sub_coordinateXm1Mass_le_linear_admissible`
this is the complete linear Banach contraction of the whole-space mild map on
the admissible norm, with factor `3/4` (`admissibleNorm_slot_sum`). -/
theorem integral_coordinateX1Mass_continuousMildImage_sub_le_admissible
    (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace)
    (u v : ℝ → ES → ComplexSpace) (R t A B : ℝ) (hR : 0 ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hRν : R ≤ ν / 16)
    -- polarization of the source, at the outer horizon (restricts to every `s ≤ t`)
    (hpol : ∀ i : Fin 3, ∀ ξ : ES, ∀ r ∈ Icc (0 : ℝ) t,
        continuousNavierSource u u r ξ i - continuousNavierSource v v r ξ i =
          continuousNavierSource (u - v) u r ξ i +
            continuousNavierSource v (u - v) r ξ i)
    -- Bochner integrability of the four heat-transported sources at every horizon
    (hSuv : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun r : ℝ =>
        heatMode ν (s - r) (fun ζ : ES => continuousNavierSource u u r ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) s)))
    (hSvv : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun r : ℝ =>
        heatMode ν (s - r) (fun ζ : ES => continuousNavierSource v v r ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) s)))
    (hSwu : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun r : ℝ =>
        heatMode ν (s - r) (fun ζ : ES => continuousNavierSource (u - v) u r ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) s)))
    (hSvw : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun r : ℝ =>
        heatMode ν (s - r) (fun ζ : ES => continuousNavierSource v (u - v) r ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) s)))
    -- `X¹` integrability of the two Duhamel slots and of the image difference
    (hDWU : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν (u - v) u s ξ i‖))
    (hDVW : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν v (u - v) s ξ i‖))
    (hD0WU : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν (u - v) u s ξ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hD0VW : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν v (u - v) s ξ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hMild : Integrable (fun s : ℝ => coordinateX1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u s ξ - continuousMildImage ν hν a v s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    -- Tonelli measurability of the two mixed kernels
    (hW1WU : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, AEMeasurable
        (fun p : ES × ℝ => mixedKernelFun (u - v) u i ν p.1 s p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hWWU : ∀ i : Fin 3, AEMeasurable
        (fun z : ℝ × (ES × ℝ) => mixedKernelFun (u - v) u i ν z.2.1 z.1 z.2.2)
        ((volume.restrict (Icc (0 : ℝ) t)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) t)))))
    (hW1VW : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, AEMeasurable
        (fun p : ES × ℝ => mixedKernelFun v (u - v) i ν p.1 s p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hWVW : ∀ i : Fin 3, AEMeasurable
        (fun z : ℝ × (ES × ℝ) => mixedKernelFun v (u - v) i ν z.2.1 z.1 z.2.2)
        ((volume.restrict (Icc (0 : ℝ) t)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) t)))))
    -- source `X⁻¹` integrability bundles of the two mixed slots
    (hb0WU : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource (u - v) u s ξ i‖))
    (hgWU : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ξ : ES => continuousNavierSource (u - v) u s ξ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hJWU : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource (u - v) u p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hs1WU : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource (u - v) u s ξ)))
    (hiWU : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource (u - v) u s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0VW : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource v (u - v) s ξ i‖))
    (hgVW : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ξ : ES => continuousNavierSource v (u - v) s ξ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hJVW : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource v (u - v) p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hs1VW : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource v (u - v) s ξ)))
    (hiVW : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource v (u - v) s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    -- slot measurability / first-moment integrability
    (hmw : ∀ r j, AEStronglyMeasurable (fun η : ES => (u - v) r η j))
    (hmw0 : ∀ r j, Integrable (fun η : ES => ‖(u - v) r η j‖))
    (hmu : ∀ r j, AEStronglyMeasurable (fun η : ES => u r η j))
    (hmu0 : ∀ r j, Integrable (fun η : ES => ‖u r η j‖))
    (hmv : ∀ r j, AEStronglyMeasurable (fun η : ES => v r η j))
    (hmv0 : ∀ r j, Integrable (fun η : ES => ‖v r η j‖))
    (hprodWU : IntegrableOn (fun r =>
        coordinateX0Mass ((u - v) r) * coordinateX0Mass (u r)) (Icc (0 : ℝ) t))
    (hprodVW : IntegrableOn (fun r =>
        coordinateX0Mass (v r) * coordinateX0Mass ((u - v) r)) (Icc (0 : ℝ) t))
    -- admissible data of the difference slot and ball data of the two trials
    (hwm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖(u - v) r η j‖))
    (hw1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖(u - v) r η j‖))
    (hmixedW : Integrable (fun s : ℝ =>
        coordinateXm1Mass ((u - v) s) * coordinateX1Mass ((u - v) s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass ((u - v) s) ≤ A)
    (hwX1int : Integrable (fun s : ℝ => coordinateX1Mass ((u - v) s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hwX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass ((u - v) s) ≤ B)
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (hmixedU : Integrable (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (u s) ≤ 2 * R)
    (huX1int : Integrable (fun s : ℝ => coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) ≤ 2 * ν⁻¹ * R)
    (hvm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖v r η j‖))
    (hv1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖v r η j‖))
    (hmixedV : Integrable (fun s : ℝ =>
        coordinateXm1Mass (v s) * coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (v s) ≤ 2 * R)
    (hvX1int : Integrable (fun s : ℝ => coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (v s) ≤ 2 * ν⁻¹ * R)
    (hw2 : Integrable (fun s : ℝ => coordinateX0Mass ((u - v) s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hu2 : Integrable (fun s : ℝ => coordinateX0Mass (u s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hv2 : Integrable (fun s : ℝ => coordinateX0Mass (v s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t))) :
    ν * (∫ s in Icc (0 : ℝ) t, coordinateX1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u s ξ - continuousMildImage ν hν a v s ξ)) ≤
      (3 / 8 : ℝ) * admissibleNorm ν A B := by
  have hmT : MeasurableSet (Icc (0 : ℝ) t) := isClosed_Icc.measurableSet
  have hsumint : Integrable (fun s : ℝ =>
      coordinateX1Mass (continuousDuhamel ν (u - v) u s) +
        coordinateX1Mass (continuousDuhamel ν v (u - v) s))
      (volume.restrict (Icc (0 : ℝ) t)) := by
    refine Integrable.add ?_ ?_
    · exact integrable_finsetSum
        (f := fun i (s : ℝ) => normX1 (fun ξ : ES =>
          continuousDuhamel ν (u - v) u s ξ i)) Finset.univ (fun i _ => hD0WU i)
    · exact integrable_finsetSum
        (f := fun i (s : ℝ) => normX1 (fun ξ : ES =>
          continuousDuhamel ν v (u - v) s ξ i)) Finset.univ (fun i _ => hD0VW i)
  -- Step 1: the pointwise split at every horizon `s ∈ [0, t]`
  have hstep1 : (∫ s in Icc (0 : ℝ) t, coordinateX1Mass (fun ξ : ES =>
      continuousMildImage ν hν a u s ξ - continuousMildImage ν hν a v s ξ)) ≤
      ∫ s in Icc (0 : ℝ) t,
        (coordinateX1Mass (continuousDuhamel ν (u - v) u s) +
          coordinateX1Mass (continuousDuhamel ν v (u - v) s)) := by
    refine integral_mono_ae hMild hsumint ?_
    filter_upwards [ae_restrict_mem hmT] with s hs
    refine coordinateX1Mass_continuousMildImage_sub_le ν hν a u v s ?_
      (fun i ξ => hSuv s hs i ξ) (fun i ξ => hSvv s hs i ξ)
      (fun i ξ => hSwu s hs i ξ) (fun i ξ => hSvw s hs i ξ)
      (fun i => hDWU i s hs) (fun i => hDVW i s hs)
    intro i ξ r hr
    exact hpol i ξ r ⟨hr.1, le_trans hr.2 hs.2⟩
  -- Step 2: the two mixed spacetime budgets
  have hbudWU := integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product
    (u - v) u ν t hν hD0WU (fun i s hs => hDWU i s hs) hW1WU hWWU hb0WU hgWU hJWU
    hs1WU hiWU hmw hmu hmw0 hmu0 hprodWU
  have hbudVW := integral_coordinateX1Mass_continuousDuhamel_le_integral_X0_product
    v (u - v) ν t hν hD0VW (fun i s hs => hDVW i s hs) hW1VW hWVW hb0VW hgVW hJVW
    hs1VW hiVW hmv hmw hmv0 hmw0 hprodVW
  have hsplitint : (∫ s in Icc (0 : ℝ) t,
      (coordinateX1Mass (continuousDuhamel ν (u - v) u s) +
        coordinateX1Mass (continuousDuhamel ν v (u - v) s))) =
      (∫ s in Icc (0 : ℝ) t, coordinateX1Mass (continuousDuhamel ν (u - v) u s)) +
        ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (continuousDuhamel ν v (u - v) s) := by
    refine integral_add ?_ ?_
    · exact integrable_finsetSum
        (f := fun i (s : ℝ) => normX1 (fun ξ : ES =>
          continuousDuhamel ν (u - v) u s ξ i)) Finset.univ (fun i _ => hD0WU i)
    · exact integrable_finsetSum
        (f := fun i (s : ℝ) => normX1 (fun ξ : ES =>
          continuousDuhamel ν v (u - v) s ξ i)) Finset.univ (fun i _ => hD0VW i)
  have hM : (∫ s in Icc (0 : ℝ) t, coordinateX1Mass (fun ξ : ES =>
      continuousMildImage ν hν a u s ξ - continuousMildImage ν hν a v s ξ)) ≤
      3 * ν⁻¹ * (∫ s in Icc (0 : ℝ) t,
          coordinateX0Mass ((u - v) s) * coordinateX0Mass (u s)) +
        3 * ν⁻¹ * (∫ s in Icc (0 : ℝ) t,
          coordinateX0Mass (v s) * coordinateX0Mass ((u - v) s)) := by
    refine hstep1.trans ?_
    rw [hsplitint]
    exact add_le_add hbudWU hbudVW
  exact X1_slot_admissible_reduction (u - v) u v ν t R A B hν hR hA hB hRν
    hwm1 hw1 hmixedW hdist hwX1int hwX1 hum1 hu1 hmixedU huXm1 huX1int huX1
    hvm1 hv1 hmixedV hvXm1 hvX1int hvX1 hw2 hu2 hv2 _ hM

set_option maxHeartbeats 4000000 in
/-- **THE WHOLE-SPACE MILD MAP IS A LINEAR BANACH CONTRACTION.**  Single
statement, both admissible slots, no supplied modulus:

  `X⁻¹(mild u t − mild v t) + ν·∫₀ᵗ X¹(mild u s − mild v s) ds
      ≤ (3/4) · (A + ν·B)`

for two trial trajectories in the `R ≤ ν/16` ball whose difference obeys the
admissible bounds `A` (pointwise `X⁻¹` on `[0,t]`) and `B` (spacetime `X¹`).
The factor `3/4 < 1` (`banach_factor_lt_one`) is a strict LINEAR contraction
constant of the admissible norm at the SAME threshold the self-map uses
(`ContinuousLeiLinSelfMap.continuousMildImage_self_map_ball`), so the pair
(self-map, contraction) is the complete fixed-point input of the whole-space
carrier.

The `X⁻¹` half is
`ContinuousLeiLinAdmissibleContraction.continuousMildImage_sub_coordinateXm1Mass_le_linear_admissible`;
the `X¹` half is `integral_coordinateX1Mass_continuousMildImage_sub_le_admissible`.
Six hypothesis families beyond the `X¹` bundle are needed for the `X⁻¹` half:
the `X⁻¹`-weighted Duhamel integrability at the terminal time and the two
heat-Fubini bundles of the polarization slots. -/
theorem admissibleNorm_continuousMildImage_sub_le_banach
    (ν : ℝ) (hν : 0 < ν) (a : ES → ComplexSpace)
    (u v : ℝ → ES → ComplexSpace) (R t A B : ℝ) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hRν : R ≤ ν / 16)
    (hpol : ∀ i : Fin 3, ∀ ξ : ES, ∀ r ∈ Icc (0 : ℝ) t,
        continuousNavierSource u u r ξ i - continuousNavierSource v v r ξ i =
          continuousNavierSource (u - v) u r ξ i +
            continuousNavierSource v (u - v) r ξ i)
    (hSuv : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun r : ℝ =>
        heatMode ν (s - r) (fun ζ : ES => continuousNavierSource u u r ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) s)))
    (hSvv : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun r : ℝ =>
        heatMode ν (s - r) (fun ζ : ES => continuousNavierSource v v r ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) s)))
    (hSwu : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun r : ℝ =>
        heatMode ν (s - r) (fun ζ : ES => continuousNavierSource (u - v) u r ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) s)))
    (hSvw : ∀ s ∈ Icc (0 : ℝ) t, ∀ i : Fin 3, ∀ ξ : ES, Integrable (fun r : ℝ =>
        heatMode ν (s - r) (fun ζ : ES => continuousNavierSource v (u - v) r ζ i) ξ)
        (volume.restrict (Icc (0 : ℝ) s)))
    (hDWU : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν (u - v) u s ξ i‖))
    (hDVW : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖ * ‖continuousDuhamel ν v (u - v) s ξ i‖))
    (hDwuXm1 : ∀ i : Fin 3, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousDuhamel ν (u - v) u t ξ i‖))
    (hDvwXm1 : ∀ i : Fin 3, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousDuhamel ν v (u - v) t ξ i‖))
    (hD0WU : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν (u - v) u s ξ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hD0VW : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normX1 (fun ξ : ES => continuousDuhamel ν v (u - v) s ξ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hMild : Integrable (fun s : ℝ => coordinateX1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u s ξ - continuousMildImage ν hν a v s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hW1WU : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, AEMeasurable
        (fun p : ES × ℝ => mixedKernelFun (u - v) u i ν p.1 s p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hWWU : ∀ i : Fin 3, AEMeasurable
        (fun z : ℝ × (ES × ℝ) => mixedKernelFun (u - v) u i ν z.2.1 z.1 z.2.2)
        ((volume.restrict (Icc (0 : ℝ) t)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) t)))))
    (hW1VW : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, AEMeasurable
        (fun p : ES × ℝ => mixedKernelFun v (u - v) i ν p.1 s p.2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hWVW : ∀ i : Fin 3, AEMeasurable
        (fun z : ℝ × (ES × ℝ) => mixedKernelFun v (u - v) i ν z.2.1 z.1 z.2.2)
        ((volume.restrict (Icc (0 : ℝ) t)).prod
          (volume.prod (volume.restrict (Icc (0 : ℝ) t)))))
    (hbWU : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) • heatMode ν (t - p.2)
          (fun ζ : ES => continuousNavierSource (u - v) u p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hfWU : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s)
          (fun ζ : ES => continuousNavierSource (u - v) u s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hbVW : ∀ i : Fin 3, Integrable (fun p : ES × ℝ =>
        (‖p.1‖⁻¹ : ℝ) • heatMode ν (t - p.2)
          (fun ζ : ES => continuousNavierSource v (u - v) p.2 ζ i) p.1)
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hfVW : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (heatMode ν (t - s)
          (fun ζ : ES => continuousNavierSource v (u - v) s ζ i)))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0WU : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource (u - v) u s ξ i‖))
    (hgWU : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ξ : ES => continuousNavierSource (u - v) u s ξ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hJWU : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource (u - v) u p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hs1WU : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource (u - v) u s ξ)))
    (hiWU : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource (u - v) u s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hb0VW : ∀ i : Fin 3, ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES =>
        ‖ξ‖⁻¹ * ‖continuousNavierSource v (u - v) s ξ i‖))
    (hgVW : ∀ i : Fin 3, Integrable (fun s : ℝ =>
        normXm1 (fun ξ : ES => continuousNavierSource v (u - v) s ξ i))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hJVW : ∀ i : Fin 3, AEMeasurable (fun p : ES × ℝ =>
        ENNReal.ofReal (‖p.1‖⁻¹ * ‖continuousNavierSource v (u - v) p.2 p.1 i‖))
        (volume.prod (volume.restrict (Icc (0 : ℝ) t))))
    (hs1VW : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ξ : ES => ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource v (u - v) s ξ)))
    (hiVW : Integrable (fun s : ℝ => ∫ ξ : ES, ‖ξ‖⁻¹ *
        complexEuclideanNorm (continuousNavierSource v (u - v) s ξ))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hmw : ∀ r j, AEStronglyMeasurable (fun η : ES => (u - v) r η j))
    (hmw0 : ∀ r j, Integrable (fun η : ES => ‖(u - v) r η j‖))
    (hmu : ∀ r j, AEStronglyMeasurable (fun η : ES => u r η j))
    (hmu0 : ∀ r j, Integrable (fun η : ES => ‖u r η j‖))
    (hmv : ∀ r j, AEStronglyMeasurable (fun η : ES => v r η j))
    (hmv0 : ∀ r j, Integrable (fun η : ES => ‖v r η j‖))
    (hprodWU : IntegrableOn (fun r =>
        coordinateX0Mass ((u - v) r) * coordinateX0Mass (u r)) (Icc (0 : ℝ) t))
    (hprodVW : IntegrableOn (fun r =>
        coordinateX0Mass (v r) * coordinateX0Mass ((u - v) r)) (Icc (0 : ℝ) t))
    (hwm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖(u - v) r η j‖))
    (hw1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖(u - v) r η j‖))
    (hmixedW : Integrable (fun s : ℝ =>
        coordinateXm1Mass ((u - v) s) * coordinateX1Mass ((u - v) s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hdist : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass ((u - v) s) ≤ A)
    (hwX1int : Integrable (fun s : ℝ => coordinateX1Mass ((u - v) s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hwX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass ((u - v) s) ≤ B)
    (hum1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖u r η j‖))
    (hu1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖u r η j‖))
    (hmixedU : Integrable (fun s : ℝ =>
        coordinateXm1Mass (u s) * coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (u s) ≤ 2 * R)
    (huX1int : Integrable (fun s : ℝ => coordinateX1Mass (u s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (huX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (u s) ≤ 2 * ν⁻¹ * R)
    (hvm1 : ∀ r j, Integrable (fun η : ES => ‖η‖⁻¹ * ‖v r η j‖))
    (hv1 : ∀ r j, Integrable (fun η : ES => ‖η‖ * ‖v r η j‖))
    (hmixedV : Integrable (fun s : ℝ =>
        coordinateXm1Mass (v s) * coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvXm1 : ∀ s ∈ Icc (0 : ℝ) t, coordinateXm1Mass (v s) ≤ 2 * R)
    (hvX1int : Integrable (fun s : ℝ => coordinateX1Mass (v s))
        (volume.restrict (Icc (0 : ℝ) t)))
    (hvX1 : ∫ s in Icc (0 : ℝ) t, coordinateX1Mass (v s) ≤ 2 * ν⁻¹ * R)
    (hw2 : Integrable (fun s : ℝ => coordinateX0Mass ((u - v) s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hu2 : Integrable (fun s : ℝ => coordinateX0Mass (u s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t)))
    (hv2 : Integrable (fun s : ℝ => coordinateX0Mass (v s) ^ 2)
        (volume.restrict (Icc (0 : ℝ) t))) :
    coordinateXm1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u t ξ - continuousMildImage ν hν a v t ξ) +
      ν * (∫ s in Icc (0 : ℝ) t, coordinateX1Mass (fun ξ : ES =>
        continuousMildImage ν hν a u s ξ - continuousMildImage ν hν a v s ξ)) ≤
      (3 / 4 : ℝ) * admissibleNorm ν A B := by
  have httm : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hXm1 := continuousMildImage_sub_coordinateXm1Mass_le_linear_admissible
    ν hν a u v R t hR hpol (fun i ξ => hSuv t httm i ξ) (fun i ξ => hSvv t httm i ξ)
    (fun i ξ => hSwu t httm i ξ) (fun i ξ => hSvw t httm i ξ) hDwuXm1 hDvwXm1
    hmw hmw0 hmu hmu0 hmv hmv0 hw2 hu2 hv2
    hbWU hfWU hgWU (fun s hs i => hb0WU i s hs) hs1WU hiWU hprodWU
    hbVW hfVW hgVW (fun s hs i => hb0VW i s hs) hs1VW hiVW hprodVW
    hwm1 hw1 hmixedW hum1 hu1 hmixedU hvm1 hv1 hmixedV
    huXm1 huX1int huX1 hvXm1 hvX1int hvX1 hRν A B hA hB hdist hwX1int hwX1
  have hX1 := integral_coordinateX1Mass_continuousMildImage_sub_le_admissible
    ν hν a u v R t A B hR hA hB hRν hpol hSuv hSvv hSwu hSvw hDWU hDVW
    hD0WU hD0VW hMild hW1WU hWWU hW1VW hWVW
    hb0WU hgWU hJWU hs1WU hiWU hb0VW hgVW hJVW hs1VW hiVW
    hmw hmw0 hmu hmu0 hmv hmv0 hprodWU hprodVW
    hwm1 hw1 hmixedW hdist hwX1int hwX1 hum1 hu1 hmixedU huXm1 huX1int huX1
    hvm1 hv1 hmixedV hvXm1 hvX1int hvX1 hw2 hu2 hv2
  exact admissibleNorm_slot_sum ν A B _ _ hXm1 hX1

/-! ## The uniqueness mechanism bought by the contraction

A contraction factor `< 1` gives uniqueness without any completeness
argument: if the difference of two fixed points has ATTAINED admissible
bounds `A`, `B`, then each slot bound reproduces itself with the factor
`3/8`, and the two together force `A = B = 0`.  The arithmetic core is
isolated below; the analytic input is exactly that the two slot bounds are
attained by the difference (the `X⁻¹` bound as a supremum over `[0, t]`, the
`X¹` bound as the actual spacetime integral). -/

/-- **The admissible self-improvement collapse.**  Nonnegative admissible
bounds that reproduce themselves under the two `3/8` slot contractions are
both zero.  This is the uniqueness engine of the whole-space mild map: the
sum of the two slot inequalities gives `A + ν·B ≤ (3/4)(A + ν·B)`, and
`3/4 < 1` with nonnegativity forces the pair to vanish. -/
theorem admissible_bounds_eq_zero_of_self_contraction (ν A B : ℝ) (hν : 0 < ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hslotXm1 : A ≤ (3 / 8 : ℝ) * admissibleNorm ν A B)
    (hslotX1 : ν * B ≤ (3 / 8 : ℝ) * admissibleNorm ν A B) :
    A = 0 ∧ B = 0 := by
  have hNn : 0 ≤ admissibleNorm ν A B := by rw [admissibleNorm]; positivity
  have hsum : admissibleNorm ν A B ≤ (3 / 4 : ℝ) * admissibleNorm ν A B := by
    have h := admissibleNorm_slot_sum ν A B A (ν * B) hslotXm1 hslotX1
    rw [admissibleNorm] at h ⊢
    linarith
  have hzero : admissibleNorm ν A B = 0 := by
    rw [admissibleNorm] at hNn hsum ⊢
    linarith
  rw [admissibleNorm] at hzero
  have hνB : 0 ≤ ν * B := mul_nonneg hν.le hB
  have hA0 : A = 0 := by linarith
  have hB0 : B = 0 := by
    have : ν * B = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hν.ne'
  exact ⟨hA0, hB0⟩

/-! ### Satisfiability guards for the collapse premise

Both poles of `admissible_bounds_eq_zero_of_self_contraction` are closed at
real points: the premise is satisfiable (the zero pair), and it is NOT an
ambient fact (a nonzero pair violates it).  So the theorem is neither
vacuous nor content-free. -/

/-- The premise is satisfiable: the zero admissible pair obeys both slot
contractions, so the theorem is not vacuously true. -/
theorem collapse_premise_satisfiable (ν : ℝ) :
    (0 : ℝ) ≤ (3 / 8 : ℝ) * admissibleNorm ν 0 0 ∧
      ν * 0 ≤ (3 / 8 : ℝ) * admissibleNorm ν 0 0 := by
  rw [admissibleNorm]
  norm_num

/-- The premise is not an ambient fact: the pair `A = 1`, `B = 0` violates the
`X⁻¹` slot contraction at every viscosity, so the hypothesis carries real
information. -/
theorem collapse_premise_not_ambient (ν : ℝ) :
    ¬ ((1 : ℝ) ≤ (3 / 8 : ℝ) * admissibleNorm ν 1 0) := by
  rw [admissibleNorm]
  norm_num

/-! ## Geometric convergence of the Picard scheme

The contraction factor `3/4` is exactly what makes the Picard iteration
`a_{n+1} = mild a_n` a Cauchy scheme: if `D n` denotes the admissible norm of
the `n`-th successive difference, the contraction gives `D (n+1) ≤ (3/4)·D n`
at every step, hence geometric decay and `D n → 0`.  This is the quantitative
Cauchy input a completeness argument consumes; what remains for the fixed
point itself is a complete carrier in which to take the limit, plus
attainment of the two admissible bounds at every step. -/

/-- Geometric decay of any nonnegative sequence that contracts by `3/4`. -/
theorem admissible_iterate_le_geometric (D : ℕ → ℝ) (C : ℝ)
    (_hD0 : ∀ n, 0 ≤ D n) (hC : D 0 ≤ C)
    (hstep : ∀ n, D (n + 1) ≤ (3 / 4 : ℝ) * D n) :
    ∀ n, D n ≤ (3 / 4 : ℝ) ^ n * C := by
  intro n
  induction n with
  | zero => simpa using hC
  | succ k ih =>
      calc D (k + 1) ≤ (3 / 4 : ℝ) * D k := hstep k
        _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ) ^ k * C) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (3 / 4 : ℝ) ^ (k + 1) * C := by ring

/-- **The Picard scheme is Cauchy.**  A nonnegative sequence of admissible
norms that contracts by the Banach factor `3/4` tends to zero.  With
`D n = admissibleNorm ν (A n) (B n)` and `hstep` supplied by
`admissibleNorm_continuousMildImage_sub_le_banach`, the successive differences
of the Picard iterates vanish in the admissible norm. -/
theorem admissible_iterate_tendsto_zero (D : ℕ → ℝ) (C : ℝ)
    (hD0 : ∀ n, 0 ≤ D n) (hC : D 0 ≤ C)
    (hstep : ∀ n, D (n + 1) ≤ (3 / 4 : ℝ) * D n) :
    Filter.Tendsto D Filter.atTop (nhds 0) := by
  have hC0 : 0 ≤ C := le_trans (hD0 0) hC
  have hgeo : Filter.Tendsto (fun n : ℕ => (3 / 4 : ℝ) ^ n * C)
      Filter.atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    simpa using h.mul_const C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hgeo (fun n => hD0 n) ?_
  exact fun n => admissible_iterate_le_geometric D C hD0 hC hstep n

end Navier.Analysis.ContinuousLeiLinBanachContraction

#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.sqrt_integral_X0_sq_le_admissible
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.integral_X0_product_le_ball_admissible
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.X1_slot_admissible_reduction
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.coordinateX1Mass_continuousMildImage_sub_le
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.integral_coordinateX1Mass_continuousMildImage_sub_le_admissible
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.admissibleNorm_continuousMildImage_sub_le_banach
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.admissibleNorm_slot_sum
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.admissible_bounds_eq_zero_of_self_contraction
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.collapse_premise_satisfiable
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.collapse_premise_not_ambient
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.admissible_iterate_le_geometric
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.admissible_iterate_tendsto_zero
