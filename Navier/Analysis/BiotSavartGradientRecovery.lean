import Navier.Analysis.BiotSavartVelocityRecovery

/-!
# Biot--Savart recovery of the velocity gradient

Directional derivatives of a divergence-free Schwartz velocity remain
divergence free.  Applying velocity recovery to those derivatives and then
using the translated principal-value identity gives the actual gradient as a
finite contraction of sharp Calderón--Zygmund principal values and their
one-third local terms.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Matrix LineDeriv

namespace Navier.Analysis.BiotSavartGradientRecovery

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartPuncture
open Navier.Analysis.BiotSavartPrincipalValue
open Navier.Analysis.BiotSavartConvolution
open Navier.Analysis.BiotSavartVelocityRecovery
open Navier.Analysis.BealeKatoMajda
open Navier.Analysis.Vorticity

private theorem fderiv_lineDeriv
    (u : SchwartzVelocity) (m : Space) (x v : Space) :
    fderiv ℝ (LineDeriv.lineDerivOp m u) x v =
      (fderiv ℝ (fderiv ℝ (⇑u)) x v) m := by
  let eval : (Space →L[ℝ] Space) →L[ℝ] Space :=
    ContinuousLinearMap.apply ℝ Space m
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (⇑u)) x := by
    have hu2 : ContDiff ℝ 2 (⇑u) := u.smooth 2
    have h : ContDiff ℝ 1 (fderiv ℝ (⇑u)) :=
      hu2.fderiv_right (by norm_num)
    exact h.contDiffAt.differentiableAt (by norm_num)
  have hcomp := eval.hasFDerivAt.comp x hdiff.hasFDerivAt
  have hfun : (⇑(LineDeriv.lineDerivOp m u) : Space → Space) =
      eval ∘ fderiv ℝ (⇑u) := by
    funext y
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rfl
  rw [hfun, hcomp.fderiv]
  rfl

private theorem lineDeriv_comm
    (u : SchwartzVelocity) (i j : Fin 3) :
    ∂_{basisVector i} (∂_{basisVector j} u) =
      ∂_{basisVector j} (∂_{basisVector i} u) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [fderiv_lineDeriv, fderiv_lineDeriv]
  have hu2 : ContDiff ℝ 2 (⇑u) := u.smooth 2
  exact congrArg (fun w : Space => w _) <|
    hu2.contDiffAt.isSymmSndFDerivAt (by norm_num)
      (basisVector i) (basisVector j)

private theorem lineDeriv_postcomp
    (L : Space →L[ℝ] Space) (u : SchwartzVelocity) (m : Space) :
    LineDeriv.lineDerivOp m (SchwartzMap.postcompCLM (𝕜 := ℝ) L u) =
      SchwartzMap.postcompCLM (𝕜 := ℝ) L
        (LineDeriv.lineDerivOp m u) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.postcompCLM_apply]
  have hcomp := L.hasFDerivAt.comp x u.differentiableAt.hasFDerivAt
  have hfun : (⇑(SchwartzMap.postcompCLM (𝕜 := ℝ) L u) : Space → Space) =
      L ∘ (⇑u) := rfl
  rw [hfun, hcomp.fderiv]
  exact congrArg (fun w : Space => w _) <|
    ContinuousLinearMap.comp_apply L (fderiv ℝ (⇑u) x) m

private theorem lineDeriv_postcomp_scalar
    (L : Space →L[ℝ] ℝ) (u : SchwartzVelocity) (m : Space) :
    LineDeriv.lineDerivOp m (SchwartzMap.postcompCLM (𝕜 := ℝ) L u) =
      SchwartzMap.postcompCLM (𝕜 := ℝ) L
        (LineDeriv.lineDerivOp m u) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.postcompCLM_apply]
  have hcomp := L.hasFDerivAt.comp x u.differentiableAt.hasFDerivAt
  have hfun : (⇑(SchwartzMap.postcompCLM (𝕜 := ℝ) L u) : Space → ℝ) =
      L ∘ (⇑u) := rfl
  rw [hfun, hcomp.fderiv]
  exact ContinuousLinearMap.comp_apply L (fderiv ℝ (⇑u) x) m

/-- The divergence retained as a Schwartz scalar map. -/
def divergenceSchwartz (u : SchwartzVelocity) : SchwartzMap Space ℝ :=
  ∑ j : Fin 3, SchwartzMap.postcompCLM (𝕜 := ℝ)
    (ContinuousLinearMap.proj j) (∂_{basisVector j} u)

@[simp] theorem divergenceSchwartz_apply
    (u : SchwartzVelocity) (x : Space) :
    divergenceSchwartz u x = staticDivergence (⇑u) x := by
  simp [divergenceSchwartz, staticDivergence,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

private theorem divergenceSchwartz_lineDeriv
    (u : SchwartzVelocity) (i : Fin 3) :
    divergenceSchwartz (∂_{basisVector i} u) =
      ∂_{basisVector i} (divergenceSchwartz u) := by
  rw [divergenceSchwartz, divergenceSchwartz]
  calc
    (∑ j : Fin 3, SchwartzMap.postcompCLM (𝕜 := ℝ)
        (ContinuousLinearMap.proj j)
          (∂_{basisVector j} (∂_{basisVector i} u))) =
        ∑ j : Fin 3, ∂_{basisVector i}
          (SchwartzMap.postcompCLM (𝕜 := ℝ)
            (ContinuousLinearMap.proj j) (∂_{basisVector j} u)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [lineDeriv_postcomp_scalar, lineDeriv_comm]
    _ = ∂_{basisVector i}
        (∑ j : Fin 3, SchwartzMap.postcompCLM (𝕜 := ℝ)
          (ContinuousLinearMap.proj j) (∂_{basisVector j} u)) := by
          simp only [Fin.sum_univ_three, LineDeriv.lineDerivOp_add]

/-- A coordinate derivative of a divergence-free Schwartz velocity is again
divergence free. -/
theorem divergenceFree_lineDeriv (u : SchwartzVelocity)
    (hdiv : DivergenceFreeInitial u) (i : Fin 3) :
    DivergenceFreeInitial (∂_{basisVector i} u) := by
  have hzero : divergenceSchwartz u = 0 := by
    ext x
    simpa using hdiv x
  intro x
  rw [← divergenceSchwartz_apply, divergenceSchwartz_lineDeriv, hzero]
  simp

private theorem staticCurlSchwartz_lineDeriv
    (u : SchwartzVelocity) (i : Fin 3) :
    staticCurlSchwartz (∂_{basisVector i} u) =
      ∂_{basisVector i} (staticCurlSchwartz u) := by
  rw [staticCurlSchwartz, staticCurlSchwartz]
  calc
    (∑ j : Fin 3,
        SchwartzMap.postcompCLM (𝕜 := ℝ)
          (LinearMap.toContinuousLinearMap (crossProduct (basisVector j)))
          (∂_{basisVector j} (∂_{basisVector i} u))) =
        ∑ j : Fin 3, ∂_{basisVector i}
          (SchwartzMap.postcompCLM (𝕜 := ℝ)
            (LinearMap.toContinuousLinearMap (crossProduct (basisVector j)))
            (∂_{basisVector j} u)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [lineDeriv_postcomp, lineDeriv_comm]
    _ = ∂_{basisVector i}
        (∑ j : Fin 3,
          SchwartzMap.postcompCLM (𝕜 := ℝ)
            (LinearMap.toContinuousLinearMap (crossProduct (basisVector j)))
            (∂_{basisVector j} u)) := by
          simp only [Fin.sum_univ_three, LineDeriv.lineDerivOp_add]

theorem staticCurl_lineDeriv_apply
    (u : SchwartzVelocity) (i : Fin 3) (x : Space) :
    staticCurl
        (⇑(LineDeriv.lineDerivOp (basisVector i) u)) x =
      fderiv ℝ (staticCurlSchwartz u) x (basisVector i) := by
  rw [← staticCurlSchwartz_apply, staticCurlSchwartz_lineDeriv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- The curl component retained as a Schwartz function has the corresponding
component of the Fréchet derivative of the vector-valued curl. -/
theorem fderiv_curlComponentSchwartz
    (u : SchwartzVelocity) (k : Fin 3) (x v : Space) :
    fderiv ℝ (curlComponentSchwartz u k) x v =
      fderiv ℝ (staticCurlSchwartz u) x v k := by
  let proj : Space →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hcomp := proj.hasFDerivAt.comp x
    (staticCurlSchwartz u).differentiableAt.hasFDerivAt
  have hfun : (⇑(curlComponentSchwartz u k) : Space → ℝ) =
      proj ∘ (⇑(staticCurlSchwartz u)) := rfl
  rw [hfun, hcomp.fderiv]
  rfl

/-- Applying velocity recovery to a coordinate derivative gives an absolutely
convergent formula for the corresponding row of the velocity gradient. -/
theorem integral_staticCurlDerivative_cross_bsVectorKernel
    (u : SchwartzVelocity) (hdiv : DivergenceFreeInitial u)
    (i : Fin 3) (x : Space) :
    (∫ z : Space,
      fderiv ℝ (staticCurlSchwartz u) (x - z) (basisVector i) ⨯₃
        bsVectorKernel z) =
      fderiv ℝ u x (basisVector i) := by
  have h := integral_staticCurl_cross_bsVectorKernel
    (LineDeriv.lineDerivOp (basisVector i) u)
    (divergenceFree_lineDeriv u hdiv i) x
  simpa only [staticCurl_lineDeriv_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv] using h

private theorem integrable_curlDerivative_mul_bsVectorKernel
    (u : SchwartzVelocity) (x : Space) (i j k : Fin 3) :
    Integrable (fun z : Space =>
      fderiv ℝ (curlComponentSchwartz u k) (x - z) (basisVector i) *
        bsVectorKernel z j) := by
  have h := integrable_fderiv_mul_bsVectorKernel i j
    (reflectedTranslate (curlComponentSchwartz u k) x)
  exact h.neg.congr (ae_of_all _ fun z => by
    change -(fderiv ℝ
      (reflectedTranslate (curlComponentSchwartz u k) x) z
        (basisVector i) * bsVectorKernel z j) = _
    rw [fderiv_reflectedTranslate_basis]
    ring)

private theorem curlDerivative_cross_kernel_coord
    (u : SchwartzVelocity) (x z : Space) (i l : Fin 3) :
    (fderiv ℝ (staticCurlSchwartz u) (x - z) (basisVector i) ⨯₃
        bsVectorKernel z) l =
      ∑ k : Fin 3, ∑ j : Fin 3,
        (basisVector k ⨯₃ basisVector j) l *
          (fderiv ℝ (curlComponentSchwartz u k) (x - z)
            (basisVector i) * bsVectorKernel z j) := by
  simp_rw [fderiv_curlComponentSchwartz]
  fin_cases l <;> simp [basisVector, cross_apply, Fin.sum_univ_three] <;> ring

private theorem integrable_curlDerivative_cross_kernel
    (u : SchwartzVelocity) (x : Space) (i : Fin 3) :
    Integrable (fun z : Space =>
      fderiv ℝ (staticCurlSchwartz u) (x - z) (basisVector i) ⨯₃
        bsVectorKernel z) := by
  rw [integrable_pi_iff]
  intro l
  have hkj : ∀ k j : Fin 3, Integrable (fun z : Space =>
      (basisVector k ⨯₃ basisVector j) l *
        (fderiv ℝ (curlComponentSchwartz u k) (x - z)
          (basisVector i) * bsVectorKernel z j)) := fun k j =>
    (integrable_curlDerivative_mul_bsVectorKernel u x i j k).const_mul _
  have hsum : Integrable (fun z : Space =>
      ∑ k : Fin 3, ∑ j : Fin 3,
        (basisVector k ⨯₃ basisVector j) l *
          (fderiv ℝ (curlComponentSchwartz u k) (x - z)
            (basisVector i) * bsVectorKernel z j)) :=
    integrable_finsetSum Finset.univ fun k _ =>
      integrable_finsetSum Finset.univ fun j _ => hkj k j
  exact hsum.congr (ae_of_all _ fun z =>
    (curlDerivative_cross_kernel_coord u x z i l).symm)

/-- **Gradient Biot--Savart recovery.**  Each coordinate of the velocity
gradient is the finite cross-product contraction of the actual sharp
principal values of the vorticity components, together with the three
distributional one-third local terms. -/
theorem fderiv_eq_principalValueConvolution_curl
    (u : SchwartzVelocity) (hdiv : DivergenceFreeInitial u)
    (x : Space) (i l : Fin 3) :
    fderiv ℝ u x (basisVector i) l =
      ∑ k : Fin 3, ∑ j : Fin 3,
        (basisVector k ⨯₃ basisVector j) l *
          (principalValueConvolution i j (curlComponentSchwartz u k) x +
            (1 / 3 : ℝ) * basisVector i j * staticCurl (⇑u) x k) := by
  have hint := integrable_curlDerivative_cross_kernel u x i
  have hvec := integral_staticCurlDerivative_cross_bsVectorKernel u hdiv i x
  have hproj := (ContinuousLinearMap.proj l : Space →L[ℝ] ℝ).integral_comp_comm hint
  have hcomponent : (∫ z : Space,
      (fderiv ℝ (staticCurlSchwartz u) (x - z) (basisVector i) ⨯₃
        bsVectorKernel z) l) = fderiv ℝ u x (basisVector i) l := by
    calc
      _ = (ContinuousLinearMap.proj l : Space →L[ℝ] ℝ)
          (∫ z : Space,
            fderiv ℝ (staticCurlSchwartz u) (x - z) (basisVector i) ⨯₃
              bsVectorKernel z) := hproj
      _ = _ := congrArg (fun w : Space => w l) hvec
  rw [← hcomponent]
  rw [integral_congr_ae (ae_of_all _ fun z =>
    curlDerivative_cross_kernel_coord u x z i l)]
  have hkj : ∀ k j : Fin 3, Integrable (fun z : Space =>
      (basisVector k ⨯₃ basisVector j) l *
        (fderiv ℝ (curlComponentSchwartz u k) (x - z)
          (basisVector i) * bsVectorKernel z j)) := fun k j =>
    (integrable_curlDerivative_mul_bsVectorKernel u x i j k).const_mul _
  rw [integral_finsetSum Finset.univ (fun k _ =>
    integrable_finsetSum Finset.univ fun j _ => hkj k j)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun j _ => hkj k j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  rw [principalValueConvolution, curlComponentSchwartz_apply]
  ring

end Navier.Analysis.BiotSavartGradientRecovery
