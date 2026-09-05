import Navier.Analysis.BealeKatoMajda
import Navier.Analysis.BiotSavartKernel
import Navier.Analysis.CZNearField
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Off-origin integration by parts for the Biot--Savart kernel

This upstream file connects the coordinate derivative of the vector kernel to
the Calderón--Zygmund tensor and proves the whole-space integration-by-parts
identity for test functions supported away from the origin.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped BigOperators Matrix LineDeriv

namespace Navier.Analysis.BealeKatoMajda

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.CZNearField

/-- The tensor used by the physical-space BKM split is exactly the off-origin
coordinate derivative of the actual vector Biot--Savart kernel. -/
theorem bsVectorKernel_coordinateLine_hasDerivAt_gradKernel
    {x : Space} (hx : x ≠ 0) (i j : Fin 3) :
    HasDerivAt (fun t : ℝ => bsVectorKernel (x + t • basisVector i) j)
      ((1 / (4 * Real.pi)) * bsGradKernel i j x) 0 := by
  by_cases hij : i = j
  · subst j
    simpa [bsGradKernel, hx, basisVector, Pi.single_apply] using
      bsVectorKernel_coordinateLine_hasDerivAt hx i i
  · have hji : j ≠ i := Ne.symm hij
    simpa [bsGradKernel, hx, basisVector, Pi.single_apply, hij, hji] using
      bsVectorKernel_coordinateLine_hasDerivAt hx i j

/-- The origin-supported coefficient in the distributional kernel derivative. -/
def bsKernelDistributionLocalTerm (i j : Fin 3) : ℝ :=
  (1 / 3 : ℝ) * basisVector i j

/-- The diagonal local coefficients have unit trace. -/
theorem bsKernelDistributionLocalTerm_trace :
    (∑ i : Fin 3, bsKernelDistributionLocalTerm i i) = 1 := by
  simp [bsKernelDistributionLocalTerm, basisVector]

/-- Product rule for the vector kernel away from the origin. -/
theorem bsVectorKernel_testFactor_coordinateLine_hasDerivAt
    {φ : Space → ℝ} {x : Space} (hx : x ≠ 0) (i j : Fin 3) (dφ : ℝ)
    (hφ : HasDerivAt (fun t : ℝ => φ (x + t • basisVector i)) dφ 0) :
    HasDerivAt
      ((fun t : ℝ => φ (x + t • basisVector i)) *
        (fun t : ℝ => bsVectorKernel (x + t • basisVector i) j))
      (dφ * bsVectorKernel x j +
        φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x)) 0 := by
  simpa only [zero_smul, add_zero] using
    hφ.mul (bsVectorKernel_coordinateLine_hasDerivAt_gradKernel hx i j)

/-- Punctured-space integration by parts for the Biot--Savart kernel. -/
theorem integral_bsGradKernel_testFactor_ibp_away
    {φ ψ : Space → ℝ} (i j : Fin 3)
    (haway : ∀ x ∈ tsupport ψ, x ≠ 0)
    (hφdiff : ∀ x ∈ tsupport ψ, DifferentiableAt ℝ φ x)
    (hψdiff : ∀ x ∈ tsupport
      (φ * fun z : Space => bsVectorKernel z j), DifferentiableAt ℝ ψ x)
    (hgdiff : ∀ x ∈ tsupport ψ,
      DifferentiableAt ℝ (φ * fun z : Space => bsVectorKernel z j) x)
    (hintLeft : Integrable (fun x : Space =>
      ψ x * (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
        φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))))
    (hintRight : Integrable (fun x : Space =>
      fderiv ℝ ψ x (basisVector i) *
        (φ * fun z : Space => bsVectorKernel z j) x))
    (hintProduct : Integrable (fun x : Space =>
      ψ x * (φ * fun z : Space => bsVectorKernel z j) x)) :
    (∫ x : Space,
      ψ x * (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
        φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x))) =
      - ∫ x : Space, fderiv ℝ ψ x (basisVector i) *
        (φ * fun z : Space => bsVectorKernel z j) x := by
  let g : Space → ℝ := φ * fun z : Space => bsVectorKernel z j
  have hline : ∀ x : Space,
      HasDerivAt (fun t : ℝ => x + t • basisVector i) (basisVector i) 0 := by
    intro x
    simpa only [id_eq, one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (basisVector i) |>.const_add x
  have hdirection : ∀ x ∈ tsupport ψ,
      fderiv ℝ g x (basisVector i) =
        fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
          φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x) := by
    intro x hx
    have hφline : HasDerivAt (fun t : ℝ => φ (x + t • basisVector i))
        (fderiv ℝ φ x (basisVector i)) 0 := by
      have hφat : HasFDerivAt φ (fderiv ℝ φ x)
          (x + (0 : ℝ) • basisVector i) := by
        simpa only [zero_smul, add_zero] using (hφdiff x hx).hasFDerivAt
      simpa [Function.comp_def] using hφat.comp_hasDerivAt 0 (hline x)
    have hproduct := bsVectorKernel_testFactor_coordinateLine_hasDerivAt
      (haway x hx) i j _ hφline
    have hgat : HasFDerivAt g (fderiv ℝ g x)
        (x + (0 : ℝ) • basisVector i) := by
      simpa only [zero_smul, add_zero] using (hgdiff x hx).hasFDerivAt
    have hgline : HasDerivAt (fun t : ℝ => g (x + t • basisVector i))
        (fderiv ℝ g x (basisVector i)) 0 := by
      simpa [Function.comp_def] using hgat.comp_hasDerivAt 0 (hline x)
    have hsame :
        ((fun t : ℝ => φ (x + t • basisVector i)) *
          (fun t : ℝ => bsVectorKernel (x + t • basisVector i) j)) =ᶠ[nhds 0]
          (fun t : ℝ => g (x + t • basisVector i)) :=
      Filter.Eventually.of_forall fun _ => rfl
    exact (hgline.congr_of_eventuallyEq hsame.symm).unique hproduct
  have hpoint : ∀ x : Space,
      ψ x * fderiv ℝ g x (basisVector i) =
        ψ x * (fderiv ℝ φ x (basisVector i) * bsVectorKernel x j +
          φ x * ((1 / (4 * Real.pi)) * bsGradKernel i j x)) := by
    intro x
    by_cases hψ : ψ x = 0
    · simp [hψ]
    · have hx : x ∈ tsupport ψ :=
        subset_closure (by simpa [Function.mem_support] using hψ)
      rw [hdirection x hx]
  have hintDerivative : Integrable (fun x : Space =>
      ψ x * fderiv ℝ g x (basisVector i)) := by
    exact hintLeft.congr (Filter.Eventually.of_forall fun x => (hpoint x).symm)
  have hcore := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hintRight hintDerivative hintProduct hψdiff hgdiff
  change (∫ x : Space, ψ x * fderiv ℝ g x (basisVector i)) =
      - ∫ x : Space, fderiv ℝ ψ x (basisVector i) * g x at hcore
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)] at hcore
  simpa [g] using hcore

end Navier.Analysis.BealeKatoMajda
