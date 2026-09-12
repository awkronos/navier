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

end Navier.Analysis.ContinuousLeiLinBanachContraction

#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.sqrt_integral_X0_sq_le_admissible
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.integral_X0_product_le_ball_admissible
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.X1_slot_admissible_reduction
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.coordinateX1Mass_continuousMildImage_sub_le
#print axioms Navier.Analysis.ContinuousLeiLinBanachContraction.admissibleNorm_slot_sum
