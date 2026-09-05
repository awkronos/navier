import Navier.Analysis.BiotSavartPrincipalValue

/-!
# Translated Biot--Savart principal values

The scalar distributional identity is specialized here to the actual
convolution test `z ↦ φ (x - z)`.  This is the form consumed by the
Biot--Savart recovery of a velocity from its Schwartz vorticity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators LineDeriv

namespace Navier.Analysis.BiotSavartConvolution

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartPuncture
open Navier.Analysis.BiotSavartPrincipalValue
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.Vorticity

/-- Reflection and translation preserve Schwartz decay. -/
def reflectedTranslate (φ : SchwartzMap Space ℝ) (x : Space) :
    SchwartzMap Space ℝ :=
  (SchwartzMap.compCLM ℝ
    (g := fun z : Space => x - z)
    (by fun_prop)
    (by
      refine ⟨1, 1 + ‖x‖, fun z => ?_⟩
      have htri : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
        calc
          ‖z‖ = ‖x - (x - z)‖ := by congr 1; abel
          _ ≤ ‖x‖ + ‖x - z‖ := norm_sub_le _ _
      have hprod : 0 ≤ ‖x‖ * ‖x - z‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      calc
        ‖z‖ ≤ ‖x‖ + ‖x - z‖ := htri
        _ ≤ (1 + ‖x‖) * (1 + ‖x - z‖) := by nlinarith
        _ = (1 + ‖x‖) * (1 + ‖(fun y : Space => x - y) z‖) ^ 1 := by ring)) φ

@[simp] theorem reflectedTranslate_apply
    (φ : SchwartzMap Space ℝ) (x z : Space) :
    reflectedTranslate φ x z = φ (x - z) := rfl

theorem fderiv_reflectedTranslate_basis
    (φ : SchwartzMap Space ℝ) (x z : Space) (i : Fin 3) :
    fderiv ℝ (reflectedTranslate φ x) z (basisVector i) =
      -fderiv ℝ φ (x - z) (basisVector i) := by
  have hinner : HasFDerivAt (fun y : Space => x - y)
      (0 - ContinuousLinearMap.id ℝ Space) z :=
    (hasFDerivAt_const x z).sub (hasFDerivAt_id z)
  have hcomp := φ.differentiableAt.hasFDerivAt.comp z hinner
  have hfun : (⇑(reflectedTranslate φ x) : Space → ℝ) =
      fun y => φ (x - y) := by
    funext y
    rfl
  change HasFDerivAt (fun y => φ (x - y)) _ z at hcomp
  rw [hfun, hcomp.fderiv]
  simp

/-- The principal-value tensor convolution at `x`, including the
distributional local term. -/
def principalValueConvolution (i j : Fin 3)
    (φ : SchwartzMap Space ℝ) (x : Space) : ℝ :=
  (∫ z : Space,
      fderiv ℝ φ (x - z) (basisVector i) * bsVectorKernel z j) -
    (1 / 3 : ℝ) * basisVector i j * φ x

theorem principalValueValue_reflectedTranslate
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    principalValueValue i j (reflectedTranslate φ x) =
      principalValueConvolution i j φ x := by
  rw [principalValueValue, principalValueConvolution]
  have hint := integrable_fderiv_mul_bsVectorKernel i j (reflectedTranslate φ x)
  rw [integral_congr_ae (ae_of_all _ fun z => by
    rw [fderiv_reflectedTranslate_basis])]
  rw [show (fun z : Space =>
      -fderiv ℝ φ (x - z) (basisVector i) * bsVectorKernel z j) =
      fun z => -(fderiv ℝ φ (x - z) (basisVector i) * bsVectorKernel z j) by
    funext z
    ring]
  rw [integral_neg]
  simp only [reflectedTranslate_apply, sub_zero]
  ring

/-- The sharp principal value of the translated kernel convolution exists at
every observation point. -/
theorem hasBiotSavartPrincipalValue_reflectedTranslate
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    HasBiotSavartPrincipalValue i j (reflectedTranslate φ x)
      (principalValueConvolution i j φ x) := by
  rw [← principalValueValue_reflectedTranslate]
  exact hasBiotSavartPrincipalValue_schwartz i j (reflectedTranslate φ x)

/-- A scalar component of the actual Schwartz vorticity. -/
def curlComponentSchwartz (u : SchwartzVelocity) (k : Fin 3) :
    SchwartzMap Space ℝ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ)
    (ContinuousLinearMap.proj k) (staticCurlSchwartz u)

@[simp] theorem curlComponentSchwartz_apply
    (u : SchwartzVelocity) (k : Fin 3) (x : Space) :
    curlComponentSchwartz u k x = staticCurl (⇑u) x k := by
  rw [curlComponentSchwartz, SchwartzMap.postcompCLM_apply,
    staticCurlSchwartz_apply]
  rfl

/-- Every component of the actual Schwartz curl therefore has the sharp
translated Biot--Savart tensor principal value at every observation point. -/
theorem hasBiotSavartPrincipalValue_curlComponent
    (u : SchwartzVelocity) (x : Space) (i j k : Fin 3) :
    HasBiotSavartPrincipalValue i j
      (reflectedTranslate (curlComponentSchwartz u k) x)
      (principalValueConvolution i j (curlComponentSchwartz u k) x) :=
  hasBiotSavartPrincipalValue_reflectedTranslate i j
    (curlComponentSchwartz u k) x

end Navier.Analysis.BiotSavartConvolution
