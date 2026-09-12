import Navier.Analysis.WholeSpaceHeatThirdDerivative
import Navier.Analysis.WholeSpaceSolenoidalHeatConvectionIntegrability
import Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit
import Navier.Analysis.WholeSpaceSolenoidalHeatViscousIntegrability

/-!
# Spatial dominated convergence for the viscous cutoff transport

This file closes the residual recorded in
`WholeSpaceSolenoidalHeatViscousCutoffLimit`: it supplies one uniform
integrable envelope for the two cutoff-derivative errors of the viscous
second-order product `D²(χ_R · curl B)` paired with a finite-energy
velocity slice, and derives the spatial dominated-convergence limit of the
cutoff viscous transport integral against its cutoff-free counterpart.

The envelope is a sum of Gaussian–velocity pairings
`heatKernel κ σ (x₀ - ·) * ‖u s ·‖`, each integrable by the `L²`–Gaussian
`rpow` pairing, plus the already-established cutoff-free
`D²(curl B) · u` integrand.  The three product-rule errors are bounded by
the scaled-cutoff derivative rates `R⁻¹ M₁ ≤ M₁`, `R⁻² M₂ ≤ M₂`,
`χ_R ≤ 1` against the first-, second-, and third Gaussian moment
estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators Topology ContDiff Matrix
open Filter
open MeasureTheory

namespace Navier.Analysis.WholeSpaceSolenoidalHeatViscousDomination

open Navier
open Navier.Breakdown
open Navier.Analysis
open Navier.Analysis.CriticalControlDecomposition
open Navier.Analysis.CurlIdentities
open Navier.Analysis.HeatSemigroupSmoothing
open Navier.Analysis.ParabolicCaccioppoli
open Navier.Analysis.ScaledCutoff
open Navier.Analysis.Vorticity
open Navier.Analysis.WholeSpaceCriticalEvolution
open Navier.Analysis.WholeSpaceSolenoidalHeatApproximation
open Navier.Analysis.WholeSpaceSolenoidalHeatMixedDomination
open Navier.Analysis.WholeSpaceSolenoidalHeatViscousCutoffLimit

private theorem backwardHeatCurlField_component_zero
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 0) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 1) * a 2 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 2) * a 1 := by
  funext y
  rw [WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

private theorem backwardHeatCurlField_component_one
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 1) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 2) * a 0 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 0) * a 2 := by
  funext y
  rw [WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

private theorem backwardHeatCurlField_component_two
    (κ τ : ℝ) (x₀ a : Space) :
    (fun y : Space => backwardHeatCurlField κ τ x₀ a y 2) =
      fun y : Space =>
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 0) * a 1 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 1) * a 0 := by
  funext y
  rw [WholeSpaceHeatThirdDerivative.backwardHeatCurlField_eq_gradient_cross]
  simp [staticGradient, cross_apply, basisVector]

private theorem directional_constLinearCombination
    {F H : Space → ℝ} (hF : ContDiff ℝ ∞ F) (hH : ContDiff ℝ ∞ H)
    (c d : ℝ) (direction : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space => F y * c - H y * d) x
        (basisVector direction) =
      fderiv ℝ F x (basisVector direction) * c -
        fderiv ℝ H x (basisVector direction) * d := by
  rw [fderiv_fun_sub]
  · change (fderiv ℝ (F * fun _ : Space => c) x -
      fderiv ℝ (H * fun _ : Space => d) x) (basisVector direction) = _
    rw [fderiv_mul
        ((hF.differentiable (by norm_num)).differentiableAt)
        (differentiableAt_const c),
      fderiv_mul
        ((hH.differentiable (by norm_num)).differentiableAt)
        (differentiableAt_const d)]
    simp only [sub_apply, add_apply, smul_apply, fderiv_const_apply,
      zero_apply, mul_zero, smul_eq_mul]
    ring
  · exact ((hF.mul contDiff_const).differentiable
      (by norm_num)).differentiableAt
  · exact ((hH.mul contDiff_const).differentiable
      (by norm_num)).differentiableAt

/-- **Pure product-rule triangle.**  The generic algebraic skeleton of the
envelope estimate: the absolute value of the second-order product rule,
tested against a velocity coordinate. -/
private theorem envelope_abs_le (A B C D E F G : ℝ) :
    |A * B + 2 * (C * D) + E * F| * |G| ≤
      |A| * |B| * |G| + 2 * |C| * |D| * |G| + |E| * |F * G| := by
  have h₁ : |A * B + 2 * (C * D) + E * F| ≤
      |A * B| + |2 * (C * D)| + |E * F| := by
    have h₁' := abs_add_le (A * B + 2 * (C * D)) (E * F)
    have h₂ := abs_add_le (A * B) (2 * (C * D))
    calc |A * B + 2 * (C * D) + E * F|
        ≤ |A * B + 2 * (C * D)| + |E * F| := h₁'
      _ ≤ (|A * B| + |2 * (C * D)|) + |E * F| := add_le_add h₂ (le_refl _)
  calc |A * B + 2 * (C * D) + E * F| * |G|
      ≤ (|A * B| + |2 * (C * D)| + |E * F|) * |G| :=
        mul_le_mul_of_nonneg_right h₁ (abs_nonneg _)
    _ ≤ |A| * |B| * |G| + 2 * |C| * |D| * |G| + |E| * |F * G| := by
        simp only [abs_mul]
        norm_num
        ring_nf
        exact le_refl _

/-- **Zeroth-order Gaussian leaf.**  Each component of the uncut backward
heat curl is bounded pointwise by the doubled-time Gaussian moment of the
translated heat kernel, scaled by the amplitude. -/
private theorem backwardHeatCurlField_component_le
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    {D : ℝ}
    (hD : ∀ (x₀ y v : Space),
      |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y v| ≤
        D * heatKernel κ (2 * τ) (x₀ - y) * ‖v‖)
    (fieldComponent : Fin 3) (y : Space) :
    |backwardHeatCurlField κ τ x₀ a y fieldComponent| ≤
      2 * D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ := by
  have hDK (q : Fin 3) :
      |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
          (basisVector q)| ≤
        D * heatKernel κ (2 * τ) (x₀ - y) := by
    have h := hD x₀ y (basisVector q)
    rw [Navier.Analysis.CurlDerivativeBridge.norm_basisVector q, mul_one] at h
    exact h
  have ha (q : Fin 3) : |a q| ≤ ‖a‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm a q
  have hG2 : 0 ≤ heatKernel κ (2 * τ) (x₀ - y) :=
    heatKernel_nonneg hκ (by positivity) (x₀ - y)
  have hD₀ : 0 ≤ D * heatKernel κ (2 * τ) (x₀ - y) := by
    have h1 := hD x₀ y (basisVector 1)
    rw [Navier.Analysis.CurlDerivativeBridge.norm_basisVector 1, mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  fin_cases fieldComponent
  · change |backwardHeatCurlField κ τ x₀ a y 0| ≤ _
    have hrew : backwardHeatCurlField κ τ x₀ a y 0 =
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 1) * a 2 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 2) * a 1 :=
      congrFun (backwardHeatCurlField_component_zero κ τ x₀ a) y
    rw [hrew]
    calc |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 1) * a 2 -
            fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 2) * a 1|
        ≤ |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 1) * a 2| +
            |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 2) * a 1| := abs_sub _ _
      _ = |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 1)| * |a 2| +
            |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 2)| * |a 1| := by rw [abs_mul, abs_mul]
      _ ≤ D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ +
            D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ :=
          add_le_add
            ((mul_le_mul_of_nonneg_right (hDK 1) (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (ha 2) hD₀))
            ((mul_le_mul_of_nonneg_right (hDK 2) (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (ha 1) hD₀))
      _ = 2 * D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ := by ring
  · change |backwardHeatCurlField κ τ x₀ a y 1| ≤ _
    have hrew : backwardHeatCurlField κ τ x₀ a y 1 =
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 2) * a 0 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 0) * a 2 :=
      congrFun (backwardHeatCurlField_component_one κ τ x₀ a) y
    rw [hrew]
    calc |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 2) * a 0 -
            fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 0) * a 2|
        ≤ |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 2) * a 0| +
            |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 0) * a 2| := abs_sub _ _
      _ = |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 2)| * |a 0| +
            |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 0)| * |a 2| := by rw [abs_mul, abs_mul]
      _ ≤ D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ +
            D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ :=
          add_le_add
            ((mul_le_mul_of_nonneg_right (hDK 2) (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (ha 0) hD₀))
            ((mul_le_mul_of_nonneg_right (hDK 0) (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (ha 2) hD₀))
      _ = 2 * D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ := by ring
  · change |backwardHeatCurlField κ τ x₀ a y 2| ≤ _
    have hrew : backwardHeatCurlField κ τ x₀ a y 2 =
        fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 0) * a 1 -
          fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
            (basisVector 1) * a 0 :=
      congrFun (backwardHeatCurlField_component_two κ τ x₀ a) y
    rw [hrew]
    calc |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 0) * a 1 -
            fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 1) * a 0|
        ≤ |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 0) * a 1| +
            |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 1) * a 0| := abs_sub _ _
      _ = |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 0)| * |a 1| +
            |fderiv ℝ (fun z : Space => heatKernel κ τ (x₀ - z)) y
              (basisVector 1)| * |a 0| := by rw [abs_mul, abs_mul]
      _ ≤ D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ +
            D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ :=
          add_le_add
            ((mul_le_mul_of_nonneg_right (hDK 0) (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (ha 1) hD₀))
            ((mul_le_mul_of_nonneg_right (hDK 1) (abs_nonneg _)).trans
              (mul_le_mul_of_nonneg_left (ha 0) hD₀))
      _ = 2 * D * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ := by ring

/-- **First-order Gaussian leaf.**  Each directional derivative of one
component of the uncut backward heat curl is bounded by the mixed
second-derivative Gaussian envelope at the reflected point, scaled by twice
the amplitude. -/
private theorem D_backwardHeatCurlFieldComponent_le
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    {E F : ℝ} (hE : 0 < E) (hF : 0 < F)
    (hsecond : ∀ (x : Space) (i j : Fin 3),
      |fderiv ℝ
          (fun y : Space =>
            fderiv ℝ (fun z : Space => heatKernel κ τ z) y (basisVector i))
          x (basisVector j)| ≤
        E * heatKernel κ (4 * τ) x + F * heatKernel κ τ x)
    (direction fieldComponent : Fin 3) (y : Space) :
    |fderiv ℝ
        (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
        y (basisVector direction)| ≤
      2 * ‖a‖ *
        (E * heatKernel κ (4 * τ) (x₀ - y) + F * heatKernel κ τ (x₀ - y)) := by
  have hK : ContDiff ℝ ∞
      (fun w : Space => heatKernel κ τ (x₀ - w)) :=
    Navier.Analysis.WholeSpaceCutoffLimit.heatKernel_translate_contDiff
      κ τ x₀
  have hDKC (q : Fin 3) : ContDiff ℝ ∞
      (fun z : Space =>
        fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
          (basisVector q)) :=
    Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
      hK (basisVector q)
  have hDDK (q : Fin 3) :
      |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
              (basisVector q))
          y (basisVector direction)| ≤
        E * heatKernel κ (4 * τ) (x₀ - y) + F * heatKernel κ τ (x₀ - y) := by
    rw [WholeSpaceSolenoidalHeatConvectionIntegrability.fderiv_fderiv_heatKernel_translate_apply
        κ τ x₀ q direction y]
    exact hsecond (x₀ - y) q direction
  have ha (q : Fin 3) : |a q| ≤ ‖a‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm a q
  have hG : 0 ≤ E * heatKernel κ (4 * τ) (x₀ - y) +
      F * heatKernel κ τ (x₀ - y) :=
    add_nonneg
      (mul_nonneg hE.le (heatKernel_nonneg hκ (by positivity) (x₀ - y)))
      (mul_nonneg hF.le (heatKernel_nonneg hκ hτ (x₀ - y)))
  fin_cases fieldComponent
  · change |(fderiv ℝ (fun z : Space =>
              backwardHeatCurlField κ τ x₀ a z 0) y)
            (basisVector direction)| ≤ _
    rw [backwardHeatCurlField_component_zero]
    rw [directional_constLinearCombination (hDKC 1) (hDKC 2)]
    calc |fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                  (basisVector 1))
              y (basisVector direction) * a 2 -
            fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                  (basisVector 2))
              y (basisVector direction) * a 1|
        ≤ |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 1))
                y (basisVector direction) * a 2| +
            |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 2))
                y (basisVector direction) * a 1| := abs_sub _ _
      _ = |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 1))
                y (basisVector direction)| * |a 2| +
            |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 2))
                y (basisVector direction)| * |a 1| := by
          rw [abs_mul, abs_mul]
      _ ≤ (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) * ‖a‖ +
            (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) * ‖a‖ := by
        gcongr
        · exact hDDK 1
        · exact ha 2
        · exact hDDK 2
        · exact ha 1
      _ = 2 * ‖a‖ *
            (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) := by ring
  · change |(fderiv ℝ (fun z : Space =>
              backwardHeatCurlField κ τ x₀ a z 1) y)
            (basisVector direction)| ≤ _
    rw [backwardHeatCurlField_component_one]
    rw [directional_constLinearCombination (hDKC 2) (hDKC 0)]
    calc |fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                  (basisVector 2))
              y (basisVector direction) * a 0 -
            fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                  (basisVector 0))
              y (basisVector direction) * a 2|
        ≤ |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 2))
                y (basisVector direction) * a 0| +
            |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 0))
                y (basisVector direction) * a 2| := abs_sub _ _
      _ = |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 2))
                y (basisVector direction)| * |a 0| +
            |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 0))
                y (basisVector direction)| * |a 2| := by
          rw [abs_mul, abs_mul]
      _ ≤ (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) * ‖a‖ +
            (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) * ‖a‖ := by
        gcongr
        · exact hDDK 2
        · exact ha 0
        · exact hDDK 0
        · exact ha 2
      _ = 2 * ‖a‖ *
            (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) := by ring
  · change |(fderiv ℝ (fun z : Space =>
              backwardHeatCurlField κ τ x₀ a z 2) y)
            (basisVector direction)| ≤ _
    rw [backwardHeatCurlField_component_two]
    rw [directional_constLinearCombination (hDKC 0) (hDKC 1)]
    calc |fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                  (basisVector 0))
              y (basisVector direction) * a 1 -
            fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                  (basisVector 1))
              y (basisVector direction) * a 0|
        ≤ |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 0))
                y (basisVector direction) * a 1| +
            |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 1))
                y (basisVector direction) * a 0| := abs_sub _ _
      _ = |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 0))
                y (basisVector direction)| * |a 1| +
            |fderiv ℝ
                (fun z : Space =>
                  fderiv ℝ (fun w : Space => heatKernel κ τ (x₀ - w)) z
                    (basisVector 1))
                y (basisVector direction)| * |a 0| := by
          rw [abs_mul, abs_mul]
      _ ≤ (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) * ‖a‖ +
            (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) * ‖a‖ := by
        gcongr
        · exact hDDK 0
        · exact ha 1
        · exact hDDK 1
        · exact ha 0
      _ = 2 * ‖a‖ *
            (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) := by ring

/-- **Spatial dominated convergence for the cutoff viscous transport.**
At every preterminal time of a `SolvesBefore` trajectory, the integral of
the cutoff second-order product `D²(χ_R · curl B)` paired with one velocity
coordinate converges, as `R → ∞`, to the corresponding cutoff-free
integral.  This supplies the uniform integrable envelope whose absence was
recorded in `WholeSpaceSolenoidalHeatViscousCutoffLimit`; the separate
`∇χ_R × A` convection correction remains outside this statement. -/
theorem SolvesBefore.tendsto_integral_secondDirectional_scaledCutoff_backwardHeatCurl_mul_velocity
    {μ T : ℝ} {u : VelocityEvolution} {p : PressureEvolution}
    (hsol : SolvesBefore μ T u p) {s : ℝ} (hs0 : 0 ≤ s) (hsT : s < T)
    {κ τ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ) (x₀ a : Space)
    (direction fieldComponent velocityComponent : Fin 3) :
    Filter.Tendsto
      (fun R : ℝ => ∫ y : Space,
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space =>
                scaledCutoff R w *
                  backwardHeatCurlField κ τ x₀ a w fieldComponent)
                z (basisVector direction))
            y (basisVector direction) * u s y velocityComponent)
      Filter.atTop
      (nhds (∫ y : Space,
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space =>
                backwardHeatCurlField κ τ x₀ a w fieldComponent)
                z (basisVector direction))
            y (basisVector direction) * u s y velocityComponent)) := by
  have hBfc : ContDiff ℝ ∞
      (fun w : Space => backwardHeatCurlField κ τ x₀ a w fieldComponent) :=
    (contDiff_apply ℝ ℝ fieldComponent).comp
      (backwardHeatCurlField_contDiff κ τ x₀ a)
  have hu : ContDiff ℝ ∞ (u s) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      contDiffAt_spatial_slice_before hsol.classical.1 hs0 hsT y
  have hu2 : Integrable (fun y : Space => ‖u s y‖ ^ 2) :=
    hsol.finite_energy s hs0 hsT
  have huNormMeas : Measurable (fun y : Space => ‖u s y‖) :=
    hu.continuous.norm.measurable
  have huNormPow : Integrable (fun y : Space => |‖u s y‖| ^ (2 : ℝ)) := by
    convert hu2 using 1
    funext y
    rw [abs_of_nonneg (norm_nonneg _), Real.rpow_two]
  have hG1 : Integrable (fun y : Space =>
      heatKernel κ τ (x₀ - y) * ‖u s y‖) :=
    integrable_heatKernel_mul_of_integrable_rpow hκ hτ
      (by norm_num : (1 : ℝ) < 2) huNormPow huNormMeas x₀
  have hG2 : Integrable (fun y : Space =>
      heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖) :=
    integrable_heatKernel_mul_of_integrable_rpow hκ (by positivity)
      (by norm_num : (1 : ℝ) < 2) huNormPow huNormMeas x₀
  have hG4 : Integrable (fun y : Space =>
      heatKernel κ (4 * τ) (x₀ - y) * ‖u s y‖) :=
    integrable_heatKernel_mul_of_integrable_rpow hκ (by positivity)
      (by norm_num : (1 : ℝ) < 2) huNormPow huNormMeas x₀
  obtain ⟨M₁, hM₁₀, hM₁⟩ := exists_scaledCutoff_gradient_component_bound
  obtain ⟨M₂, hM₂₀, hM₂⟩ :=
    exists_fderiv_fderiv_bound standardBump standardBump.contDiff
      standardBump.hasCompactSupport
      (basisVector direction) (basisVector direction)
  obtain ⟨Dcst, _, hDcst⟩ :=
    exists_abs_fderiv_heatKernel_translate_le_doubled hκ hτ
  obtain ⟨E, F, hE, hF, hsecond⟩ :=
    WholeSpaceHeatThirdDerivative.exists_abs_second_heatKernel_space_le_gaussians
      hκ hτ
  let H : Space → ℝ := fun y =>
    (M₂ * (2 * Dcst * ‖a‖)) *
        (heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖) +
      ((2 * M₁ * (2 * ‖a‖ * E)) *
          (heatKernel κ (4 * τ) (x₀ - y) * ‖u s y‖) +
        (2 * M₁ * (2 * ‖a‖ * F)) *
          (heatKernel κ τ (x₀ - y) * ‖u s y‖)) +
      |fderiv ℝ
          (fun z : Space =>
            fderiv ℝ (fun w : Space =>
              backwardHeatCurlField κ τ x₀ a w fieldComponent)
              z (basisVector direction))
          y (basisVector direction) * u s y velocityComponent|
  have hHint : Integrable H := by
    have ht1 : Integrable (fun y : Space =>
        (M₂ * (2 * Dcst * ‖a‖)) *
          (heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖)) :=
      hG2.const_mul (M₂ * (2 * Dcst * ‖a‖))
    have ht2 : Integrable (fun y : Space =>
        (2 * M₁ * (2 * ‖a‖ * E)) *
          (heatKernel κ (4 * τ) (x₀ - y) * ‖u s y‖)) :=
      hG4.const_mul (2 * M₁ * (2 * ‖a‖ * E))
    have ht3 : Integrable (fun y : Space =>
        (2 * M₁ * (2 * ‖a‖ * F)) *
          (heatKernel κ τ (x₀ - y) * ‖u s y‖)) :=
      hG1.const_mul (2 * M₁ * (2 * ‖a‖ * F))
    have ht4 : Integrable (fun y : Space =>
        |fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space =>
                backwardHeatCurlField κ τ x₀ a w fieldComponent)
                z (basisVector direction))
            y (basisVector direction) * u s y velocityComponent|) :=
      (WholeSpaceSolenoidalHeatViscousIntegrability.SolvesBefore.integrable_secondDirectional_backwardHeatCurlField_mul_velocity
        hsol hs0 hsT hκ hτ x₀ a direction fieldComponent
        velocityComponent).abs
    refine (((ht1.add ht2).add ht3).add ht4).congr
      (ae_of_all _ (by intro y; simp only [Pi.add_apply, H]; ring_nf))
  apply tendsto_integral_filter_of_dominated_convergence H
  · filter_upwards with R
    have hχB : ContDiff ℝ ∞ (fun w : Space =>
        scaledCutoff R w * backwardHeatCurlField κ τ x₀ a w fieldComponent) :=
      (scaledCutoff_contDiff R).mul hBfc
    have hprod : ContDiff ℝ ∞ (fun y : Space =>
        fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space =>
                scaledCutoff R w *
                  backwardHeatCurlField κ τ x₀ a w fieldComponent)
                z (basisVector direction))
            y (basisVector direction)) :=
      Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
        (Navier.Analysis.CutoffIntegrationByParts.contDiff_fderiv_apply
          hχB (basisVector direction)) (basisVector direction)
    exact (hprod.continuous.mul
      ((continuous_apply velocityComponent).comp hu.continuous)
      ).aestronglyMeasurable
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_mul]
    have hexpand :=
      secondDirectional_mul (scaledCutoff_contDiff R) hBfc direction y
    rw [hexpand]
    have hRinv : R⁻¹ ≤ 1 :=
      (inv_le_one₀ (by linarith : (0 : ℝ) < R)).2 hR
    have hinvR : R⁻¹ * R⁻¹ ≤ 1 := by
      calc R⁻¹ * R⁻¹ ≤ 1 * 1 := by gcongr
        _ = 1 := mul_one 1
    have hA2r :
        |fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (scaledCutoff R) z (basisVector direction))
            y (basisVector direction)| ≤
          R⁻¹ * R⁻¹ * M₂ :=
      abs_fderiv_fderiv_scaled_le standardBump standardBump.contDiff hM₂
        (by linarith : (0 : ℝ) < R) y
    have hA2 :
        |fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (scaledCutoff R) z (basisVector direction))
            y (basisVector direction)| ≤ M₂ :=
      hA2r.trans
        ((mul_le_mul_of_nonneg_right hinvR hM₂₀).trans_eq (one_mul M₂))
    have hDcr :
        |fderiv ℝ (scaledCutoff R) y (basisVector direction)| ≤ R⁻¹ * M₁ :=
      hM₁ (by linarith : (0 : ℝ) < R) y direction
    have hDc : |fderiv ℝ (scaledCutoff R) y (basisVector direction)| ≤ M₁ :=
      hDcr.trans ((mul_le_mul_of_nonneg_right hRinv hM₁₀).trans_eq
        (one_mul M₁))
    have hB : |backwardHeatCurlField κ τ x₀ a y fieldComponent| ≤
        2 * Dcst * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖ :=
      backwardHeatCurlField_component_le hκ hτ x₀ a hDcst fieldComponent y
    have hDB :
        |fderiv ℝ
            (fun z : Space =>
              backwardHeatCurlField κ τ x₀ a z fieldComponent)
            y (basisVector direction)| ≤
          2 * ‖a‖ *
            (E * heatKernel κ (4 * τ) (x₀ - y) +
              F * heatKernel κ τ (x₀ - y)) :=
      D_backwardHeatCurlFieldComponent_le hκ hτ x₀ a hE hF hsecond
        direction fieldComponent y
    have hχ01 : |scaledCutoff R y| ≤ 1 := by
      rw [abs_of_nonneg (scaledCutoff_nonneg R y)]
      exact scaledCutoff_le_one R y
    have huc : |u s y velocityComponent| ≤ ‖u s y‖ := by
      simpa [Real.norm_eq_abs] using
        norm_le_pi_norm (u s y) velocityComponent
    have h1 :
        |fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (scaledCutoff R) z (basisVector direction))
            y (basisVector direction)| *
          |backwardHeatCurlField κ τ x₀ a y fieldComponent| *
          |u s y velocityComponent| ≤
        (M₂ * (2 * Dcst * ‖a‖)) *
          (heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖) := by
      calc |fderiv ℝ (fun z : Space =>
              fderiv ℝ (scaledCutoff R) z (basisVector direction))
            y (basisVector direction)| *
          |backwardHeatCurlField κ τ x₀ a y fieldComponent| *
          |u s y velocityComponent|
        ≤ M₂ * |backwardHeatCurlField κ τ x₀ a y fieldComponent| *
            ‖u s y‖ :=
          by gcongr
      _ ≤ M₂ * (2 * Dcst * heatKernel κ (2 * τ) (x₀ - y) * ‖a‖) *
            ‖u s y‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hB hM₂₀) (norm_nonneg _)
      _ = (M₂ * (2 * Dcst * ‖a‖)) *
            (heatKernel κ (2 * τ) (x₀ - y) * ‖u s y‖) := by ring
    have h2 :
        2 *
          |fderiv ℝ (scaledCutoff R) y (basisVector direction)| *
          |fderiv ℝ
              (fun z : Space =>
                backwardHeatCurlField κ τ x₀ a z fieldComponent)
              y (basisVector direction)| *
          |u s y velocityComponent| ≤
        (2 * M₁ * (2 * ‖a‖ * E)) *
            (heatKernel κ (4 * τ) (x₀ - y) * ‖u s y‖) +
          (2 * M₁ * (2 * ‖a‖ * F)) *
            (heatKernel κ τ (x₀ - y) * ‖u s y‖) := by
      have hmid : 2 * |fderiv ℝ (scaledCutoff R) y
            (basisVector direction)| ≤
          2 * M₁ :=
        mul_le_mul_of_nonneg_left hDc (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * |fderiv ℝ (scaledCutoff R) y (basisVector direction)| *
            |fderiv ℝ (fun z : Space =>
              backwardHeatCurlField κ τ x₀ a z fieldComponent)
              y (basisVector direction)| *
            |u s y velocityComponent|
        ≤ 2 * M₁ *
              |fderiv ℝ (fun z : Space =>
                backwardHeatCurlField κ τ x₀ a z fieldComponent)
                y (basisVector direction)| *
              ‖u s y‖ :=
          by gcongr
      _ ≤ 2 * M₁ *
              (2 * ‖a‖ *
                (E * heatKernel κ (4 * τ) (x₀ - y) +
                  F * heatKernel κ τ (x₀ - y))) *
              ‖u s y‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDB
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM₁₀))
            (norm_nonneg _)
      _ = (2 * M₁ * (2 * ‖a‖ * E)) *
            (heatKernel κ (4 * τ) (x₀ - y) * ‖u s y‖) +
          (2 * M₁ * (2 * ‖a‖ * F)) *
            (heatKernel κ τ (x₀ - y) * ‖u s y‖) := by ring
    have h3 :
        |scaledCutoff R y| *
          |fderiv ℝ
              (fun z : Space =>
                fderiv ℝ (fun w : Space =>
                  backwardHeatCurlField κ τ x₀ a w fieldComponent)
                  z (basisVector direction))
              y (basisVector direction) * u s y velocityComponent| ≤
        |fderiv ℝ
            (fun z : Space =>
              fderiv ℝ (fun w : Space =>
                backwardHeatCurlField κ τ x₀ a w fieldComponent)
                z (basisVector direction))
            y (basisVector direction) * u s y velocityComponent| :=
      (mul_le_mul_of_nonneg_right hχ01 (abs_nonneg _)).trans_eq
        (one_mul _)
    refine le_trans (envelope_abs_le
      (fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (scaledCutoff R) z (basisVector direction))
        y (basisVector direction))
      (backwardHeatCurlField κ τ x₀ a y fieldComponent)
      (fderiv ℝ (scaledCutoff R) y (basisVector direction))
      (fderiv ℝ
        (fun z : Space => backwardHeatCurlField κ τ x₀ a z fieldComponent)
        y (basisVector direction))
      (scaledCutoff R y)
      (fderiv ℝ
        (fun z : Space =>
          fderiv ℝ (fun w : Space =>
            backwardHeatCurlField κ τ x₀ a w fieldComponent)
            z (basisVector direction))
        y (basisVector direction))
      (u s y velocityComponent)) ?_
    refine le_trans (add_le_add (add_le_add h1 h2) h3) ?_
    exact le_of_eq (by simp only [H])
  · exact hHint
  · filter_upwards with y
    exact (tendsto_secondDirectional_scaledCutoff_backwardHeatCurlField
      κ τ x₀ a direction fieldComponent y).mul_const
      (u s y velocityComponent)

#print axioms SolvesBefore.tendsto_integral_secondDirectional_scaledCutoff_backwardHeatCurl_mul_velocity

end Navier.Analysis.WholeSpaceSolenoidalHeatViscousDomination
