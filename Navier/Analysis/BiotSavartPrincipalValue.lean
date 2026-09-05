import Navier.Analysis.BiotSavartTruncationComparison

/-!
# Principal values of the Biot--Savart gradient on Schwartz data

This file closes the two remaining analytic inputs in the distributional
Biot--Savart identity.  The derivative-side kernel product is integrable for
every Schwartz test function, and the exact smooth finite-radius identity,
together with smooth--sharp truncation comparison, constructs the sharp
principal value with its one-third local term.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators LineDeriv

namespace Navier.Analysis.BiotSavartPrincipalValue

open Navier
open Navier.Analysis.BiotSavartKernel
open Navier.Analysis.BiotSavartPuncture
open Navier.Analysis.BiotSavartFiniteRadius
open Navier.Analysis.BiotSavartTruncationComparison
open Navier.Analysis.CZNearField
open Navier.Analysis.OfficialABEncoding
open Navier.Analysis.BealeKatoMajda

private theorem measurable_bsKernelScalar : Measurable bsKernelScalar := by
  unfold bsKernelScalar
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact measurable_const.div
    (measurable_const.mul
      ((show Continuous officialEuclideanNorm by
        rw [show officialEuclideanNorm = fun x : Space =>
            Real.sqrt (∑ k : Fin 3, |x k| ^ 2) by
          funext x
          exact officialEuclideanNorm_eq_sqrt_sum_sq x]
        fun_prop).measurable.pow_const 3))

private theorem measurable_bsVectorKernel_coord (j : Fin 3) :
    Measurable (fun x : Space => bsVectorKernel x j) := by
  unfold bsVectorKernel
  simp only [Pi.smul_apply, smul_eq_mul]
  exact measurable_bsKernelScalar.mul (measurable_pi_apply j)

private theorem bsVectorKernel_coord_abs_le_norm_mul
    (x : Space) (j : Fin 3) :
    |bsVectorKernel x j| ≤
      Real.sqrt 3 * (‖x‖ * bsKernelScalar x) := by
  rw [bsVectorKernel, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (bsKernelScalar_nonneg x)]
  calc
    bsKernelScalar x * |x j| ≤
        bsKernelScalar x * officialEuclideanNorm x :=
      mul_le_mul_of_nonneg_left (coord_abs_le_officialEuclideanNorm x j)
        (bsKernelScalar_nonneg x)
    _ ≤ bsKernelScalar x * (Real.sqrt 3 * ‖x‖) :=
      mul_le_mul_of_nonneg_left (officialEuclideanNorm_le x)
        (bsKernelScalar_nonneg x)
    _ = Real.sqrt 3 * (‖x‖ * bsKernelScalar x) := by ring

private theorem bsVectorKernel_coord_abs_le_one_of_one_le_norm
    {x : Space} (hx : 1 ≤ ‖x‖) (j : Fin 3) :
    |bsVectorKernel x j| ≤ 1 := by
  have hxrad : 1 ≤ officialEuclideanNorm x :=
    hx.trans (norm_le_officialEuclideanNorm x)
  have hx0 : x ≠ 0 := by
    intro hzero
    subst x
    norm_num at hx
  rw [bsVectorKernel, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_nonneg (bsKernelScalar_nonneg x),
    bsKernelScalar_apply_of_ne_zero hx0]
  have hrpos : 0 < officialEuclideanNorm x := lt_of_lt_of_le zero_lt_one hxrad
  calc
    1 / (4 * Real.pi * officialEuclideanNorm x ^ 3) * |x j| ≤
        1 / (4 * Real.pi * officialEuclideanNorm x ^ 3) *
          officialEuclideanNorm x :=
      mul_le_mul_of_nonneg_left (coord_abs_le_officialEuclideanNorm x j)
        (by positivity)
    _ = 1 / (4 * Real.pi * officialEuclideanNorm x ^ 2) := by
      field_simp
    _ ≤ 1 / (4 * Real.pi) := by
      apply one_div_le_one_div_of_le (by positivity)
      have hsq : 1 ≤ officialEuclideanNorm x ^ 2 := by nlinarith
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hsq
          (show 0 ≤ 4 * Real.pi by positivity)
    _ ≤ 1 := by
      have hpi : 1 ≤ 4 * Real.pi := by
        nlinarith [Real.pi_gt_three]
      exact (div_le_one (by positivity)).2 hpi

private theorem fderiv_basis_norm_le_seminorm
    (i : Fin 3) (φ : SchwartzMap Space ℝ) (x : Space) :
    ‖fderiv ℝ φ x (basisVector i)‖ ≤
      (SchwartzMap.seminorm ℝ 0 1) φ * ‖basisVector i‖ := by
  calc
    ‖fderiv ℝ φ x (basisVector i)‖ ≤
        ‖fderiv ℝ φ x‖ * ‖basisVector i‖ :=
      (fderiv ℝ φ x).le_opNorm (basisVector i)
    _ ≤ (SchwartzMap.seminorm ℝ 0 1) φ * ‖basisVector i‖ := by
      gcongr
      rw [← norm_iteratedFDeriv_one]
      exact φ.norm_iteratedFDeriv_le_seminorm ℝ 1 x

/-- The derivative-side term in the distributional Biot--Savart identity is
absolutely integrable for every Schwartz test function. -/
theorem integrable_fderiv_mul_bsVectorKernel
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Integrable (fun x : Space =>
      fderiv ℝ φ x (basisVector i) * bsVectorKernel x j) := by
  let C : ℝ :=
    (SchwartzMap.seminorm ℝ 0 1) φ * ‖basisVector i‖ * Real.sqrt 3
  let g : Space → ℝ := fun x =>
    fderiv ℝ φ x (basisVector i) * bsVectorKernel x j
  have hgMeas : AEStronglyMeasurable g := by
    have hd : Measurable (fun x : Space => fderiv ℝ φ x (basisVector i)) := by
      have hline : Continuous (fun x : Space =>
          (∂_{basisVector i} φ : SchwartzMap Space ℝ) x) :=
        (∂_{basisVector i} φ : SchwartzMap Space ℝ).continuous
      simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using hline.measurable
    exact (hd.mul (measurable_bsVectorKernel_coord j)).aestronglyMeasurable
  have hlocalMajorant : IntegrableOn
      (fun x : Space => C * (‖x‖ * bsKernelScalar x))
      (Metric.ball (0 : Space) 1) :=
    (integrableOn_norm_mul_bsKernelScalar_ball (by norm_num)).const_mul C
  have hlocal : IntegrableOn g (Metric.ball (0 : Space) 1) := by
    apply hlocalMajorant.mono'
    · exact hgMeas.restrict
    · filter_upwards [] with x
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hd := fderiv_basis_norm_le_seminorm i φ x
      have hk := bsVectorKernel_coord_abs_le_norm_mul x j
      have hseminorm : 0 ≤ (SchwartzMap.seminorm ℝ 0 1) φ :=
        apply_nonneg _ _
      calc
        ‖fderiv ℝ φ x (basisVector i)‖ * |bsVectorKernel x j| ≤
            ((SchwartzMap.seminorm ℝ 0 1) φ * ‖basisVector i‖) *
              (Real.sqrt 3 * (‖x‖ * bsKernelScalar x)) := by gcongr
        _ = C * (‖x‖ * bsKernelScalar x) := by
          dsimp only [C]
          ring
  have hfar : IntegrableOn g (Metric.ball (0 : Space) 1)ᶜ := by
    have hdInt : Integrable (fun x : Space =>
        fderiv ℝ φ x (basisVector i)) := by
      have h :=
        (∂_{basisVector i} φ : SchwartzMap Space ℝ).integrable (μ := volume)
      exact h.congr (ae_of_all _ fun x => by
        rw [SchwartzMap.lineDerivOp_apply_eq_fderiv])
    apply hdInt.norm.integrableOn.mono'
    · exact hgMeas.restrict
    · filter_upwards [self_mem_ae_restrict measurableSet_ball.compl] with x hxfar
      rw [norm_mul, Real.norm_eq_abs]
      have hxnorm : 1 ≤ ‖x‖ := by
        simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right,
          not_lt] using hxfar
      calc
        ‖fderiv ℝ φ x (basisVector i)‖ * |bsVectorKernel x j| ≤
            ‖fderiv ℝ φ x (basisVector i)‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (bsVectorKernel_coord_abs_le_one_of_one_le_norm hxnorm j)
            (norm_nonneg _)
        _ = ‖fderiv ℝ φ x (basisVector i)‖ := mul_one _
  have hall := hlocal.union hfar
  simpa only [union_compl_self, integrableOn_univ, g] using hall

/-- The sharp principal-value value dictated by distributional integration by
parts, including the isotropic local coefficient. -/
def principalValueValue (i j : Fin 3) (φ : SchwartzMap Space ℝ) : ℝ :=
  -(∫ x : Space, fderiv ℝ φ x (basisVector i) * bsVectorKernel x j) -
    (1 / 3 : ℝ) * basisVector i j * φ 0

/-- Smooth finite-radius truncations converge to the distributional
Biot--Savart value for every Schwartz test function. -/
theorem tendsto_smoothPuncturedGradient_schwartz
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    Tendsto (fun ε : ℝ => smoothPuncturedGradientIntegral ε i j φ)
      (nhdsWithin 0 (Ioi 0)) (nhds (principalValueValue i j φ)) := by
  have hintDerivative := integrable_fderiv_mul_bsVectorKernel i j φ
  have hderivative :=
    (tendsto_smoothPuncturedDerivativeIntegral i j φ hintDerivative).neg
  have hflux := tendsto_smoothPunctureFlux i j φ φ.continuous
    ((SchwartzMap.seminorm ℝ 0 0) φ)
    (fun x => by simpa using φ.norm_iteratedFDeriv_le_seminorm ℝ 0 x)
  have htarget := hderivative.sub hflux
  apply htarget.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hid := smoothPunctured_biotSavart_identity ε hε i j φ.differentiable
    (hintDerivative.bdd_mul
      (continuous_smoothExteriorCutoff ε).aestronglyMeasurable
      (ae_of_all _ fun x => by
        change |Real.smoothTransition (radiusSq x / ε ^ 2 - 1)| ≤ 1
        rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _))
    (integrable_smoothPuncturedGradient_schwartz hε i j φ)
    (integrable_smoothPunctureFlux_schwartz hε i j φ)
    (integrable_smoothPuncturedProduct_schwartz hε j φ)
  linarith

/-- Every Schwartz test function has the sharp Biot--Savart principal value
specified by the distributional derivative formula. -/
theorem hasBiotSavartPrincipalValue_schwartz
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    HasBiotSavartPrincipalValue i j φ (principalValueValue i j φ) := by
  have hsmooth := tendsto_smoothPuncturedGradient_schwartz i j φ
  have hdiff := tendsto_smoothPuncturedGradient_sub_puncturedGradient
    i j φ
    (fun ε hε => integrable_smoothPuncturedGradient_schwartz hε i j φ)
    (fun ε hε => integrable_sharpPuncturedGradient_schwartz hε i j φ)
  have hsharp := hsmooth.sub hdiff
  have heq : (fun ε : ℝ =>
      smoothPuncturedGradientIntegral ε i j φ -
        (smoothPuncturedGradientIntegral ε i j φ -
          puncturedGradientIntegral ε i j φ)) =
      fun ε => puncturedGradientIntegral ε i j φ := by
    funext ε
    ring
  rw [heq, sub_zero] at hsharp
  exact hsharp

/-- Unconditional distributional Biot--Savart gradient identity on Schwartz
test functions, with an explicitly constructed sharp principal value. -/
theorem biotSavartPrincipalValue_identity_schwartz
    (i j : Fin 3) (φ : SchwartzMap Space ℝ) :
    -(∫ x : Space, fderiv ℝ φ x (basisVector i) * bsVectorKernel x j) =
      principalValueValue i j φ +
        (1 / 3 : ℝ) * basisVector i j * φ 0 := by
  exact biotSavartPrincipalValue_identity_schwartz_full i j φ
    (principalValueValue i j φ)
    (integrable_fderiv_mul_bsVectorKernel i j φ)
    (hasBiotSavartPrincipalValue_schwartz i j φ)

end Navier.Analysis.BiotSavartPrincipalValue
